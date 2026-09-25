#!/usr/bin/python3
#
# Pure-Python creation of Microsoft VHD (dynamic) / VHDX disk images holding a
# FAT12/16/32 filesystem with files inside. This makes it possible to build
# those Windows container formats on Linux/macOS, without DISKPART or any
# external tooling (no qemu-img, mkfs.vfat or mtools required).
#
# Layouts implemented after:
#   - "Virtual Hard Disk Image Format Specification" (Oct 11, 2006),
#     mirroring QEMU's block/vpc.c behaviour (one's-complement byte-sum
#     checksums, CHS geometry rounding, dynamic disk layout).
#   - "[MS-VHDX] v2 File Format" specification, mirroring QEMU's block/vhdx.c
#     behaviour (CRC-32C checksums, region/metadata tables, BAT layout).
#

import os
import struct
import time
import math
import uuid as uuidlib

SECTOR = 512
MB = 1024 * 1024

VHD_BLOCK_SIZE = 2 * MB
VHDX_BLOCK_SIZE = 1 * MB

VHD_TIMESTAMP_BASE = 946684800  # seconds between epoch and 2000-01-01 00:00 UTC


class VhdError(Exception):
    pass


class VhdTooSmall(VhdError):
    '''Requested disk size cannot hold the payload (or the filesystem type).
    needed_bytes == 0 means growing the disk will not help.'''

    def __init__(self, needed_bytes, message=''):
        super().__init__(message or f'Required disk size is at least {needed_bytes} bytes.')
        self.needed_bytes = needed_bytes


# ============================================================================
# CRC-32C (Castagnoli), as required by VHDX headers / region & metadata tables.
# Initial value 0xffffffff, no final xor, stored little-endian (like QEMU).
# Payload blocks are not checksummed, so this only ever runs on small buffers.
# ============================================================================

def _make_crc32c_table():
    poly = 0x82F63B78
    table = []
    for i in range(256):
        crc = i
        for _ in range(8):
            crc = (crc >> 1) ^ (poly if crc & 1 else 0)
        table.append(crc)
    return tuple(table)


_CRC32C_TABLE = _make_crc32c_table()


def crc32c(data, crc=0xffffffff):
    '''Standard CRC-32C (Castagnoli): init 0xffffffff, final xor 0xffffffff.
    Same value QEMU's crc32c() and 7-Zip's Crc32c_Calc() produce.'''
    table = _CRC32C_TABLE
    for b in data:
        crc = table[(crc ^ b) & 0xff] ^ (crc >> 8)
    return crc ^ 0xffffffff


def _crc32c_field(buf, offset=4):
    '''Computes CRC-32C over buf with the 4 bytes at `offset` treated as zero,
    storing the checksum into those bytes (little-endian).'''
    buf = bytearray(buf)
    pre = bytes(buf[:offset])
    post = bytes(buf[offset + 4:])
    struct.pack_into('<I', buf, offset, crc32c(pre + b'\x00\x00\x00\x00' + post))
    return bytes(buf)


def _vhd_checksum(data):
    return (~sum(data)) & 0xffffffff


# ============================================================================
# Sparse raw disk image: non-overlapping byte extents at absolute offsets,
# everything in between reads back as zeroes. Lets the VHD/VHDX writers skip
# all-zero blocks so the resulting container stays as small as the payload.
# ============================================================================

class SparseRaw(object):
    def __init__(self, size):
        self.size = size
        self.extents = []

    def add(self, offset, data):
        if len(data) > 0:
            self.extents.append((offset, bytes(data)))

    def add_file(self, offset, path, chunk=4 * MB):
        with open(path, 'rb') as f:
            pos = 0
            while True:
                buf = f.read(chunk)
                if not buf:
                    break
                self.add(offset + pos, buf)
                pos += len(buf)

    def read_range(self, start, length):
        buf = bytearray(length)
        end = start + length
        for off, data in self.extents:
            if off >= end or off + len(data) <= start:
                continue
            s = max(off, start) - off
            e = min(off + len(data), end) - off
            dst = off + s - start
            buf[dst:dst + (e - s)] = data[s:e]
        return bytes(buf)

    def iter_blocks(self, block_size):
        '''Yields (block_index, block_bytes) for every block that contains at
        least one non-zero byte. All-zero blocks are skipped.'''
        if not self.extents:
            return

        extents = sorted(self.extents, key=lambda e: e[0])
        first = extents[0][0] // block_size
        last = (extents[-1][0] + len(extents[-1][1]) - 1) // block_size

        for idx in range(first, last + 1):
            blk = self.read_range(idx * block_size, block_size)
            if blk.count(0) != len(blk):
                yield idx, blk


# ============================================================================
# MBR with a single primary partition (like DISKPART's
# "create partition primary" + "assign")
# ============================================================================

PARTITION_TYPE_FAT16 = 0x06
PARTITION_TYPE_FAT16_LBA = 0x0e
PARTITION_TYPE_FAT32 = 0x0c


def build_mbr(disk_sectors, part_start, part_sectors, part_type):
    mbr = bytearray(SECTOR)
    mbr[0x1b8:0x1bc] = os.urandom(4)  # disk signature

    chs = b'\xfe\xff\xff'             # CHS unused with LBA partition types

    entry = struct.pack(
        '<B3sB3sII',
        0x00,                          # not active - not needed for automount
        chs,
        part_type,
        chs,
        part_start,
        min(part_sectors, 0xffffffff),
    )

    mbr[446:446 + 16] = entry
    mbr[510:512] = b'\x55\xaa'
    return bytes(mbr)


# ============================================================================
# FAT12/16/32 filesystem image builder (with LFN and subdirectories).
# Only used to construct fresh volumes, never to modify existing ones.
# ============================================================================

def _dos_datetime(timestamp=None):
    t = time.localtime(timestamp)
    year = max(1980, min(2107, t.tm_year))
    ddate = ((year - 1980) << 9) | (t.tm_mon << 5) | min(31, t.tm_mday)
    dtime = (t.tm_hour << 11) | (t.tm_min << 5) | (t.tm_sec // 2)
    tenth = (t.tm_sec % 2) * 100
    return ddate, dtime, tenth


_SFN_ALLOWED_EXTRA = set(b"!#$%&'()-@^_`{}~")


def _sfn_sanitize(name):
    '''Uppercases and maps characters invalid in 8.3 names onto '_'.'''
    out = bytearray()
    for ch in name.upper():
        o = ord(ch)
        if ch == ' ':
            continue
        if 0x41 <= o <= 0x5a or 0x30 <= o <= 0x39 or o in _SFN_ALLOWED_EXTRA or 0x7f <= o <= 0xff:
            out.append(o)
        else:
            out.append(0x5f)
    return out.decode('latin-1')


def _sfn_checksum(sfn):
    s = 0
    for ch in sfn:
        s = (((s & 1) << 7) + (s >> 1) + ch) & 0xff
    return s


def _lfn_entries_count(name):
    ucs_len = len(name.encode('utf-16-le')) + 2
    return max(1, math.ceil(ucs_len / 26))


def _make_short_name(name, used):
    '''Returns (11-char SFN string, needs_lfn).'''
    base, _, ext = name.rpartition('.')
    if not base:
        base, ext = ext, ''

    clean_base = _sfn_sanitize(base.replace('.', '_'))
    clean_ext = _sfn_sanitize(ext)[:3]

    plain = clean_base + ('.' + clean_ext if clean_ext else '')
    sfn_exact = clean_base.ljust(8) + clean_ext.ljust(3)
    is_exact = (
        name.upper() == plain and
        len(clean_base) <= 8 and len(clean_ext) <= 3 and
        ' ' not in name and
        name.count('.') <= (1 if ext else 0) and
        not name.endswith('.') and
        all(ord(c) >= 32 for c in name)
    )

    if is_exact and clean_base and sfn_exact not in used:
        used.add(sfn_exact)
        return sfn_exact, False

    root = clean_base[:6] or '_'
    num = 1
    while True:
        tail = f'~{num}'
        if len(root) + len(tail) > 8:
            root = root[:8 - len(tail)]
        sfn = (root + tail).ljust(8) + clean_ext.ljust(3)
        if sfn not in used:
            used.add(sfn)
            return sfn, True
        num += 1


def _lfn_entries(name, sfn):
    '''Builds LFN directory entries in on-disk order (sequence n|0x40 first,
    sequence 1 - holding the first 13 characters - right before the SFN).'''
    ucs = name.encode('utf-16-le') + b'\x00\x00'
    while len(ucs) % 26 != 0:
        ucs += b'\xff\xff'

    checksum = _sfn_checksum(sfn.encode('ascii'))
    n = len(ucs) // 26
    entries = []

    for pos in range(n):
        i = n - 1 - pos                    # chunk index, last chunk stored first
        seq = i + 1
        flag = 0x40 if i == n - 1 else 0    # 0x40 marks the first physical entry
        chunk = ucs[i * 26:(i + 1) * 26]

        entries.append(struct.pack(
            '<B10sBBB12sH4s',
            seq | flag,
            chunk[0:10],                            # name chars 1-5
            0x0f,                                   # ATTR_LONG_NAME
            0,                                      # type
            checksum,
            chunk[10:22],                           # name chars 6-11
            0,                                      # first cluster, always zero
            chunk[22:26],                           # name chars 12-13
        ))

    return entries


class FatNode(object):
    def __init__(self, name):
        self.name = name
        self.children = {}
        self.local_path = None             # set for files
        self.size = 0
        self.hidden = False                # FAT ATTR_HIDDEN (0x02)
        self.cluster = 0
        self.clusters = []
        self.parent_cluster = 0


class FatBuilder(object):
    '''Builds a fresh FAT volume from a set of input files.

    add_file(volume_path, local_path) collects files (volume_path may contain
    '/'-separated subdirectories). finalize() computes the entire filesystem
    and returns its contents as (offset, bytes) extents relative to the
    beginning of the partition.'''

    def __init__(self, part_sectors, fat_type='fat32', heads=16, spt=63, part_start=2048):
        self.part_sectors = part_sectors
        self.fat_type = 32 if fat_type == 'fat32' else 16
        self.heads = heads
        self.spt = spt
        self.part_start = part_start
        self.volume_label = None
        self._files = []
        self._root = FatNode('')

    def add_file(self, volume_path, local_path, hidden=False):
        volume_path = volume_path.replace('\\', '/').strip('/')
        node = self._root
        for part in volume_path.split('/')[:-1]:
            if part not in node.children:
                node.children[part] = FatNode(part)
            node = node.children[part]
        leaf = volume_path.split('/')[-1]
        f = FatNode(leaf)
        f.local_path = local_path
        f.size = os.path.getsize(local_path)
        f.hidden = hidden
        node.children[leaf] = f
        self._files.append(local_path)

    # -- sizing --------------------------------------------------------------

    def _cluster_sectors(self, part_sectors):
        if self.fat_type == 32:
            for s in (64, 32, 16, 8, 4, 2, 1):
                if part_sectors // s >= 65525:
                    return s
            return 1
        else:
            for s in (1, 2, 4, 8, 16, 32, 64, 128):
                if part_sectors // s <= 65524:
                    return s
            raise VhdTooSmall(0,
                'FAT16 volume would exceed 4GB. Use --vhd-filesystem fat32 instead.')

    def _layout(self, part_sectors):
        s = self._cluster_sectors(part_sectors)
        nfats = 2
        reserved = 32 if self.fat_type == 32 else 1
        root_entries = 0 if self.fat_type == 32 else 512
        root_sectors = (root_entries * 32 + SECTOR - 1) // SECTOR
        fesize = 4 if self.fat_type == 32 else 2

        fat_sectors = 4
        while True:
            data_sectors = part_sectors - reserved - nfats * fat_sectors - root_sectors
            clusters = data_sectors // s
            need = ((clusters + 2) * fesize + SECTOR - 1) // SECTOR
            if need <= fat_sectors or clusters <= 0:
                break
            fat_sectors = need

        data_sectors = part_sectors - reserved - nfats * fat_sectors - root_sectors
        clusters = data_sectors // s

        min_clusters = 65525 if self.fat_type == 32 else 4085
        if clusters < min_clusters:
            # rough solve for a partition size that satisfies the cluster minimum
            needed = reserved + root_sectors + nfats * fat_sectors + min_clusters * s
            raise VhdTooSmall(needed * SECTOR,
                f'Volume too small for FAT{self.fat_type} (needs at least '
                f'{min_clusters} clusters). Increase --vhd-size.')

        return {
            'cluster_sectors': s,
            'reserved': reserved,
            'nfats': nfats,
            'fat_sectors': fat_sectors,
            'root_sectors': root_sectors,
            'clusters': clusters,
            'fat_start': reserved,
            'root_start': reserved + nfats * fat_sectors,
            'data_start': reserved + nfats * fat_sectors + root_sectors,
        }

    def minimum_sectors(self):
        '''Smallest partition size (in sectors) able to hold collected files.'''
        total = sum(os.path.getsize(f) for f in self._files)
        need = total + (len(self._files) + 32) * SECTOR + 4 * MB
        sectors = math.ceil(need / SECTOR) + 2048
        for _ in range(24):
            try:
                self._layout(sectors)
                return sectors
            except VhdTooSmall as e:
                if e.needed_bytes == 0:
                    raise
                sectors = max(sectors * 2, e.needed_bytes // SECTOR)
        raise VhdError('Could not find a volume size fitting all input files.')

    # -- cluster bookkeeping ---------------------------------------------------

    def _alloc(self, nbytes):
        s = self.layout['cluster_sectors']
        cb = s * SECTOR
        n = max(1, math.ceil(nbytes / cb)) if nbytes else 0
        if self.next_cluster + n - 2 > self.layout['clusters']:
            raise VhdTooSmall(
                (self.layout['data_start'] + self.layout['clusters'] * s + 64) * SECTOR,
                'Input files do not fit into the requested VHD size. Increase --vhd-size.')
        first = self.next_cluster
        self.next_cluster += n
        return list(range(first, first + n))

    def _fat_chain(self, clusters):
        fat = self.fat
        fesize = 4 if self.fat_type == 32 else 2
        eoc = 0x0fffffff if self.fat_type == 32 else 0xffff
        for i, c in enumerate(clusters):
            nxt = clusters[i + 1] if i + 1 < len(clusters) else eoc
            off = c * fesize
            fat[off:off + fesize] = nxt.to_bytes(fesize, 'little')

    def _cluster_offset(self, cluster):
        s = self.layout['cluster_sectors']
        return (self.layout['data_start'] + (cluster - 2) * s) * SECTOR

    # -- directory entries -----------------------------------------------------

    def _pack_entry_header(self, entry, ddate, dtime, tenth):
        entry[12] = 0
        entry[13] = tenth
        struct.pack_into('<H', entry, 14, dtime)     # creation time
        struct.pack_into('<H', entry, 16, ddate)     # creation date
        struct.pack_into('<H', entry, 18, ddate)     # last access date
        struct.pack_into('<H', entry, 22, dtime)     # write time
        struct.pack_into('<H', entry, 24, ddate)     # write date

    def _dot_entry(self, name, cluster):
        entry = bytearray(32)
        entry[0:11] = name.ljust(11).encode('ascii')
        entry[11] = 0x10
        self._pack_entry_header(entry, *_dos_datetime())
        struct.pack_into('<H', entry, 26, cluster & 0xffff)
        return bytes(entry)

    def _dir_entry(self, name, attr, cluster, size, used):
        sfn, needs_lfn = _make_short_name(name, used)
        entry = bytearray(32)
        entry[0:11] = sfn.encode('ascii')
        entry[11] = attr
        self._pack_entry_header(entry, *_dos_datetime())
        struct.pack_into('<H', entry, 20, (cluster >> 16) & 0xffff if self.fat_type == 32 else 0)
        struct.pack_into('<H', entry, 26, cluster & 0xffff)
        struct.pack_into('<I', entry, 28, size)
        entries = _lfn_entries(name, sfn) if needs_lfn else []
        entries.append(bytes(entry))
        return entries

    def _dir_bytes(self, node):
        '''Renders the contents of a directory. Children cluster numbers must
        already be assigned.'''
        used = set()
        data = bytearray()

        if node is self._root:
            if self.volume_label:
                entry = bytearray(32)
                entry[0:11] = self.volume_label[:11].ljust(11).encode('ascii', errors='replace')
                entry[11] = 0x08
                data += entry
        else:
            data += self._dot_entry('.', node.cluster)
            data += self._dot_entry('..', node.parent_cluster)

        for name in sorted(node.children.keys()):
            child = node.children[name]
            if child.local_path is not None:
                attr = 0x20 | (0x02 if child.hidden else 0)   # ATTR_ARCHIVE | ATTR_HIDDEN
                data += b''.join(self._dir_entry(name, attr, child.cluster, child.size, used))
            else:
                data += b''.join(self._dir_entry(name, 0x10, child.cluster, 0, used))

        cb = self.layout['cluster_sectors'] * SECTOR
        if len(data) % cb:
            data += b'\x00' * (cb - len(data) % cb)
        return bytes(data)

    def _dir_alloc_size(self, node):
        size = 0
        if node is self._root:
            if self.volume_label:
                size += 32
        else:
            size += 64                       # '.' and '..'
        for name in node.children:
            size += 32 * (_lfn_entries_count(name) + 1)
        return size + 32                     # slack

    # -- assembly ----------------------------------------------------------------

    def finalize(self):
        self.layout = self._layout(self.part_sectors)
        self.next_cluster = 2
        self.fat = bytearray(self.layout['fat_sectors'] * SECTOR)

        if self.fat_type == 32:
            self.fat[0:8] = struct.pack('<II', 0x0ffffff8, 0x0fffffff)
        else:
            self.fat[0:4] = struct.pack('<HH', 0xfff8, 0xffff)

        # pass 1: allocate clusters depth-first so directories know where
        # their children live
        def allocate(node, parent_cluster):
            if node is not self._root or self.fat_type == 32:
                node.clusters = self._alloc(self._dir_alloc_size(node))
                node.cluster = node.clusters[0] if node.clusters else 0
            node.parent_cluster = parent_cluster

            for child in node.children.values():
                if child.local_path is not None:
                    child.clusters = self._alloc(child.size)
                    child.cluster = child.clusters[0] if child.clusters else 0
                else:
                    allocate(child, node.cluster)

        allocate(self._root, 0)

        # pass 2: render directory contents and build FAT chains
        self.dirs = []          # (first_cluster, clusters, bytes)
        self.file_extents = []  # (offset, bytes)

        def render(node):
            data = self._dir_bytes(node)
            if node is self._root and self.fat_type == 16:
                self.root_dir_bytes = data[:self.layout['root_sectors'] * SECTOR].ljust(
                    self.layout['root_sectors'] * SECTOR, b'\x00')
            else:
                self._fat_chain(node.clusters)
                self.dirs.append((node.cluster, node.clusters, data))

            for child in node.children.values():
                if child.local_path is None:
                    render(child)

        render(self._root)

        def files(node):
            for child in node.children.values():
                if child.local_path is not None:
                    yield child
                else:
                    for leaf in files(child):
                        yield leaf

        cb = self.layout['cluster_sectors'] * SECTOR
        for leaf in files(self._root):
            if not leaf.clusters:
                continue
            self._fat_chain(leaf.clusters)
            with open(leaf.local_path, 'rb') as f:
                for c in leaf.clusters:
                    buf = f.read(cb)
                    if not buf:
                        break
                    self.file_extents.append((self._cluster_offset(c), buf))

        self.free_clusters = self.layout['clusters'] - (self.next_cluster - 2)
        self.next_free = min(self.next_cluster, self.layout['clusters'] + 1)
        return self.extents()

    def extents(self):
        layout = self.layout
        out = [(0, self._boot_sector())]

        if self.fat_type == 32:
            out.append((SECTOR, self._fsinfo()))
            out.append((6 * SECTOR, self._boot_sector()))
            out.append((7 * SECTOR, self._fsinfo()))

        fat_off = layout['fat_start'] * SECTOR
        for i in range(layout['nfats']):
            out.append((fat_off + i * layout['fat_sectors'] * SECTOR, bytes(self.fat)))

        if self.fat_type == 16:
            out.append((layout['root_start'] * SECTOR, self.root_dir_bytes))

        s = layout['cluster_sectors']
        for cluster, clusters, data in self.dirs:
            for i, c in enumerate(clusters):
                out.append((self._cluster_offset(c), data[i * s * SECTOR:(i + 1) * s * SECTOR]))

        out.extend(self.file_extents)
        return out

    def _boot_sector(self):
        layout = self.layout
        bs = bytearray(SECTOR)
        bs[0:3] = b'\xeb\x58\x90'
        bs[3:11] = b'MSDOS5.0'
        struct.pack_into('<H', bs, 11, SECTOR)
        struct.pack_into('B', bs, 13, layout['cluster_sectors'])
        struct.pack_into('<H', bs, 14, layout['reserved'])
        struct.pack_into('B', bs, 16, layout['nfats'])
        struct.pack_into('<H', bs, 17, 0 if self.fat_type == 32 else 512)
        total = self.part_sectors
        if self.fat_type == 32:
            struct.pack_into('<H', bs, 19, 0)
        else:
            struct.pack_into('<H', bs, 19, total if total < 0x10000 else 0)
        bs[21] = 0xf8
        struct.pack_into('<H', bs, 22, 0 if self.fat_type == 32 else layout['fat_sectors'])
        struct.pack_into('<H', bs, 24, self.spt)
        struct.pack_into('<H', bs, 26, self.heads)
        struct.pack_into('<I', bs, 28, self.part_start)
        struct.pack_into('<I', bs, 32, 0 if self.fat_type != 32 and total < 0x10000 else total)

        if self.fat_type == 32:
            struct.pack_into('<I', bs, 36, layout['fat_sectors'])
            struct.pack_into('<H', bs, 40, 0)          # ext flags: both FATs clean
            struct.pack_into('<H', bs, 42, 0)          # fs version
            struct.pack_into('<I', bs, 44, 2)          # root directory cluster
            struct.pack_into('<H', bs, 48, 1)          # FSInfo sector
            struct.pack_into('<H', bs, 50, 6)          # backup boot sector
            bs[64] = 0x80
            bs[66] = 0x29
            bs[67:71] = os.urandom(4)
            bs[71:82] = b'NO NAME    '
            bs[82:90] = b'FAT32   '
        else:
            bs[36] = 0x80
            bs[38] = 0x29
            bs[39:43] = os.urandom(4)
            bs[43:54] = b'NO NAME    '
            bs[54:62] = b'FAT16   '

        bs[510:512] = b'\x55\xaa'
        return bytes(bs)

    def _fsinfo(self):
        fs = bytearray(SECTOR)
        struct.pack_into('<I', fs, 0, 0x41615252)      # lead signature 'RRaA'
        struct.pack_into('<I', fs, 484, 0x61417272)    # struct signature 'rrAa'
        struct.pack_into('<I', fs, 488, self.free_clusters)
        struct.pack_into('<I', fs, 492, self.next_free)
        fs[510:512] = b'\x55\xaa'
        return bytes(fs)


# ============================================================================
# VHD (dynamic) writer
# ============================================================================

VHD_TYPE_DYNAMIC = 3


def vhd_geometry(total_sectors):
    '''CHS geometry per the VHD specification (as implemented by QEMU).'''
    total_sectors = min(total_sectors, 65535 * 16 * 255)

    if total_sectors >= 65535 * 16 * 63:
        spt = 255
        heads = 16
        cth = total_sectors // spt
    else:
        spt = 17
        cth = total_sectors // spt
        heads = max(4, (cth + 1023) // 1024)
        if cth >= heads * 1024 or heads > 16:
            spt = 31
            heads = 16
            cth = total_sectors // spt
        if cth >= heads * 1024:
            spt = 63
            heads = 16
            cth = total_sectors // spt

    cyls = min(cth // heads, 16383)
    return cyls, heads, spt


def _vhd_footer(disk_type, current_size):
    cyls, heads, spt = vhd_geometry(current_size // SECTOR)

    footer = bytearray(SECTOR)
    footer[0:8] = b'conectix'
    struct.pack_into('>I', footer, 8, 0x00000002)      # features
    struct.pack_into('>I', footer, 12, 0x00010000)     # file format version
    struct.pack_into('>Q', footer, 16, SECTOR)         # dynamic disk header offset
    struct.pack_into('>I', footer, 24, int(time.time()) - VHD_TIMESTAMP_BASE)
    footer[28:32] = b'pmpy'                            # creator application
    struct.pack_into('>H', footer, 32, 0x0005)
    struct.pack_into('>H', footer, 34, 0x0003)
    footer[36:40] = b'Wi2k'
    struct.pack_into('>Q', footer, 40, current_size)   # original size
    struct.pack_into('>Q', footer, 48, current_size)   # current size
    struct.pack_into('>H', footer, 56, cyls)
    footer[58] = heads
    footer[59] = spt
    struct.pack_into('>I', footer, 60, disk_type)
    footer[68:84] = uuidlib.uuid4().bytes
    footer[84] = 0                                     # not in saved state

    struct.pack_into('>I', footer, 64, _vhd_checksum(footer))
    return bytes(footer)


def _vhd_dynamic_header(max_table_entries, table_offset, block_size):
    hdr = bytearray(1024)
    hdr[0:8] = b'cxsparse'
    struct.pack_into('>Q', hdr, 8, 0xffffffffffffffff)  # data offset (unused)
    struct.pack_into('>Q', hdr, 16, table_offset)
    struct.pack_into('>I', hdr, 24, 0x00010000)         # version
    struct.pack_into('>I', hdr, 28, max_table_entries)
    struct.pack_into('>I', hdr, 32, block_size)
    struct.pack_into('>I', hdr, 36, _vhd_checksum(hdr))
    return bytes(hdr)


def write_dynamic_vhd(fh, raw):
    '''Writes a dynamic (sparse) VHD whose content is `raw` (SparseRaw).'''
    capacity_sectors = raw.size // SECTOR
    spb = VHD_BLOCK_SIZE // SECTOR
    bat_entries = math.ceil(capacity_sectors / spb)
    bat_bytes = math.ceil(bat_entries * 4 / SECTOR) * SECTOR

    footer = _vhd_footer(VHD_TYPE_DYNAMIC, raw.size)
    header = _vhd_dynamic_header(bat_entries, 3 * SECTOR, VHD_BLOCK_SIZE)

    fh.seek(0)
    fh.write(footer)
    fh.write(header)

    # BAT placeholder - rewritten once block locations are known
    bat_pos = 3 * SECTOR
    fh.seek(bat_pos)
    fh.write(b'\xff' * bat_bytes)

    blocks_pos = bat_pos + bat_bytes
    fh.seek(blocks_pos)
    fh.write(footer)                                    # footer copy after BAT (like QEMU)

    bitmap = b'\xff' * (VHD_BLOCK_SIZE // SECTOR // 8)
    bat = [0xffffffff] * bat_entries
    pos = blocks_pos + SECTOR

    for idx, blk in raw.iter_blocks(VHD_BLOCK_SIZE):
        bat[idx] = pos // SECTOR
        fh.seek(pos)
        fh.write(bitmap)
        fh.write(blk)
        pos += SECTOR + VHD_BLOCK_SIZE

    fh.seek(bat_pos)
    fh.write(b''.join(struct.pack('>I', e) for e in bat))

    # Footer copy at end of file, as required by the VHD specification
    fh.seek(pos)
    fh.write(footer)
    return pos + SECTOR


# ============================================================================
# VHDX (dynamic) writer
# ============================================================================

VHDX_HEADER_SECTION_END = 1 * MB
VHDX_LOG_SIZE = 1 * MB

_VHDX_GUIDS = {
    'bat_region': bytes.fromhex('6677c22d23f600429d64115e9bfd4a08'),
    'metadata_region': bytes.fromhex('06a27c8b90479a4bb8fe575f050f886e'),
    'file_parameters': bytes.fromhex('3767a1ca36fa434db3b633f0aa44e76b'),
    'virtual_disk_size': bytes.fromhex('2442a52f1bcd7648b2115dbed83bf4b8'),
    'page83_data': bytes.fromhex('ab12cabee6b2234593efc309e000c746'),
    'logical_sector_size': bytes.fromhex('1dbf41816fa90947ba47f233a8faab5f'),
    'physical_sector_size': bytes.fromhex('c748a3cd5d4471449cc9e9885251c556'),
}

VHDX_METADATA_REQUIRED = 0x04
VHDX_METADATA_VIRTUAL_DISK = 0x02
VHDX_PAYLOAD_BLOCK_FULLY_PRESENT = 6


def _vhdx_header(sequence_number, file_write_guid, data_write_guid):
    buf = bytearray(4 * 1024)
    buf[0:4] = b'head'
    # checksum at offset 4 - zeroed while computing by _crc32c_field
    struct.pack_into('<Q', buf, 8, sequence_number)
    buf[16:32] = file_write_guid
    buf[32:48] = data_write_guid
    # log_guid at 48 stays zero - no valid log entries to replay
    struct.pack_into('<H', buf, 64, 0)     # log version
    struct.pack_into('<H', buf, 66, 1)     # version
    struct.pack_into('<I', buf, 68, VHDX_LOG_SIZE)
    struct.pack_into('<Q', buf, 72, VHDX_HEADER_SECTION_END)
    return _crc32c_field(buf, 4)


def _vhdx_region_table(bat_offset, bat_length, metadata_offset, metadata_length):
    buf = bytearray(64 * 1024)
    buf[0:4] = b'regi'
    struct.pack_into('<I', buf, 8, 2)      # entry count
    buf[16:32] = _VHDX_GUIDS['bat_region']
    struct.pack_into('<Q', buf, 32, bat_offset)
    struct.pack_into('<I', buf, 40, bat_length)
    buf[48:64] = _VHDX_GUIDS['metadata_region']
    struct.pack_into('<Q', buf, 64, metadata_offset)
    struct.pack_into('<I', buf, 72, metadata_length)
    return _crc32c_field(buf, 4)


def _vhdx_metadata(virtual_size, block_size):
    table = bytearray(64 * 1024)
    table[0:8] = b'metadata'
    struct.pack_into('<H', table, 10, 5)   # entry count

    offset = 64 * 1024
    items = [
        (_VHDX_GUIDS['file_parameters'],
         struct.pack('<II', block_size, 0), VHDX_METADATA_REQUIRED),
        (_VHDX_GUIDS['virtual_disk_size'],
         struct.pack('<Q', virtual_size), VHDX_METADATA_REQUIRED | VHDX_METADATA_VIRTUAL_DISK),
        (_VHDX_GUIDS['page83_data'],
         uuidlib.uuid4().bytes, VHDX_METADATA_REQUIRED | VHDX_METADATA_VIRTUAL_DISK),
        (_VHDX_GUIDS['logical_sector_size'],
         struct.pack('<I', SECTOR), VHDX_METADATA_REQUIRED | VHDX_METADATA_VIRTUAL_DISK),
        (_VHDX_GUIDS['physical_sector_size'],
         struct.pack('<I', SECTOR), VHDX_METADATA_REQUIRED | VHDX_METADATA_VIRTUAL_DISK),
    ]

    data = bytearray()
    for i, (guid, value, flags) in enumerate(items):
        entry_pos = 32 + i * 32
        table[entry_pos:entry_pos + 16] = guid
        struct.pack_into('<I', table, entry_pos + 16, offset + len(data))
        struct.pack_into('<I', table, entry_pos + 20, len(value))
        struct.pack_into('<I', table, entry_pos + 24, flags)
        data += value

    return bytes(table) + bytes(data)


def write_vhdx(fh, raw):
    '''Writes a dynamic (sparse) VHDX whose content is `raw` (SparseRaw).'''
    virtual_size = raw.size
    block_size = VHDX_BLOCK_SIZE

    chunk_ratio = (1 << 23) * SECTOR // block_size
    chunk_ratio_bits = chunk_ratio.bit_length() - 1

    data_blocks = math.ceil(virtual_size / block_size)
    bat_entries = data_blocks + ((data_blocks - 1) >> chunk_ratio_bits)

    bat_offset = ((VHDX_HEADER_SECTION_END + VHDX_LOG_SIZE + MB - 1) // MB) * MB
    bat_length = math.ceil(bat_entries * 8 / MB) * MB
    metadata_offset = bat_offset + bat_length
    metadata_length = 1 * MB
    data_offset = metadata_offset + metadata_length

    fh.seek(0)
    fh.truncate()

    # File type identifier block
    ident = bytearray(64 * 1024)
    ident[0:8] = b'vhdxfile'
    creator = 'PackMyPayload'.encode('utf-16-le')
    ident[8:8 + len(creator)] = creator
    fh.write(ident)

    seq = int.from_bytes(os.urandom(6), 'big') or 1
    file_write_guid = uuidlib.uuid4().bytes
    data_write_guid = uuidlib.uuid4().bytes

    fh.seek(1 * 64 * 1024)
    fh.write(_vhdx_header(seq, file_write_guid, data_write_guid))
    fh.seek(2 * 64 * 1024)
    fh.write(_vhdx_header(seq + 1, file_write_guid, data_write_guid))

    regions = _vhdx_region_table(bat_offset, bat_length, metadata_offset, metadata_length)
    fh.seek(3 * 64 * 1024)
    fh.write(regions)
    fh.seek(4 * 64 * 1024)
    fh.write(regions)

    fh.seek(metadata_offset)
    fh.write(_vhdx_metadata(virtual_size, block_size))

    bat = bytearray(bat_length)
    pos = data_offset

    for idx, blk in raw.iter_blocks(block_size):
        bat_idx = idx + (idx >> chunk_ratio_bits)
        struct.pack_into('<Q', bat, bat_idx * 8,
                         (pos & 0xfffffffffff00000) | VHDX_PAYLOAD_BLOCK_FULLY_PRESENT)
        fh.seek(pos)
        fh.write(blk)
        pos += block_size

    fh.seek(bat_offset)
    fh.write(bat)
    return pos


# ============================================================================
# High-level helper: raw partitioned disk holding input files
# ============================================================================

def build_raw_disk(files, disk_size, filesystem='fat32', image_format='vhd'):
    '''Builds a raw, MBR-partitioned disk of `disk_size` bytes containing a FAT
    filesystem with `files` = [(volume_path, local_path[, hidden]), ...].

    Returns (SparseRaw, info_dict). Raises VhdTooSmall when the disk cannot
    hold requested files.'''
    if image_format == 'vhd':
        cyls, heads, spt = vhd_geometry(disk_size // SECTOR)
        # VHD capacity is defined by CHS geometry, which may round the size up
        disk_sectors = cyls * heads * spt
        disk_size = disk_sectors * SECTOR
    else:
        heads, spt = 255, 63
        disk_sectors = disk_size // SECTOR

    part_start = 2048
    part_sectors = disk_sectors - part_start

    builder = FatBuilder(part_sectors, filesystem, heads=heads, spt=spt, part_start=part_start)
    for entry in files:
        volume_path, local_path = entry[0], entry[1]
        hidden = len(entry) > 2 and bool(entry[2])
        builder.add_file(volume_path, local_path, hidden=hidden)

    extents = builder.finalize()

    if filesystem == 'fat32':
        part_type = PARTITION_TYPE_FAT32
    else:
        part_type = PARTITION_TYPE_FAT16_LBA if part_sectors >= 32768 else PARTITION_TYPE_FAT16

    raw = SparseRaw(disk_size)
    raw.add(0, build_mbr(disk_sectors, part_start, part_sectors, part_type))
    for offset, data in extents:
        raw.add(part_start * SECTOR + offset, data)

    info = {
        'filesystem': f'FAT{builder.fat_type}',
        'cluster_size': builder.layout['cluster_sectors'] * SECTOR,
        'disk_sectors': disk_sectors,
        'geometry': (cyls, heads, spt) if image_format == 'vhd' else None,
    }
    return raw, info
