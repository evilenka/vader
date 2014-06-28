#!/usr/bin/python
# -*- coding: utf-8 -*-

import cookielib
import datetime
import math
import os
import re
import readline
import struct
import subprocess
import sys
import urllib2

from Crypto.Cipher import ARC4, DES
from Crypto.Hash import MD4, MD5


BUF_SIZE = 4096
DATE_FMT = '%d.%m.%Y %H:%M:%S'
REGISTERS = ('Eax', 'Ebx', 'Ecx', 'Edx', 'Esi', 'Edi', 'Ebp', 'Eip', 'EFlags')
REGISTERS_64 = ('Rax', 'Rbx', 'Rcx', 'Rdx', 'Rsi', 'Rdi', 'Rbp', 'Rip', 'EFlags')


class GetVersion64:

    def __init__(self, buffer):
        (
            self.major_version,
            self.minor_version,
            self.protocol_version,
            self.kd_secondary_version,
            self.flags,
            self.machine_type,
            self.max_packet_type,
            self.max_state_change,
            self.max_manipulate,
            self.simulation,
            self.unused,
            self.kern_base,
            self.ps_loaded_module_list,
            self.debugger_data_list
        ) = struct.unpack('HHBBHHBBBBHQQQ', buffer)

    def print_version_info(self):
        version_tuple = (self.major_version, self.minor_version)
        print('Build version: %d.%d' %
              version_tuple)
        if version_tuple == (15, 7600):
            print('Windows 7')


class NoRedirectDownloader(urllib2.HTTPErrorProcessor):
    def http_response(self, request, response):
        return response


class DebugInfoHolder():
    block_size = 0x400
    handle = None
    root_stream = b''
    types_stream = b''
    symbols_stream = b''

    def __init__(self, filename):
        try:
            self.handle = open(filename, 'rb')
        except IOError as ex:
            print(ex)
            exit(1)
        header_block = self.handle.read(self.block_size)
        signature = header_block[:header_block.find(b'\x1a')]
        print('Debug info file signature is %s' % signature)
        if signature != 'Microsoft C/C++ MSF 7.00\r\n':
            print('Unsupprorted signature!')
            exit(1)
        (self.block_size, self.root_size, self.root_block) = struct.unpack(
            'IxxxxxxxxIxxxxI', header_block[0x20:0x38]
        )
        print('Root PDB stream directory found at %s' %
              hex(self.root_block * self.block_size).replace('L', ''))
        blocks_count = int(math.ceil(float(self.root_size) / self.block_size))
        self.handle.seek(self.root_block * self.block_size)
        root_stream_blocks = struct.unpack('I' * blocks_count,
                                           self.handle.read(4 * blocks_count))
        self.root_stream = self.get_stream(root_stream_blocks, self.root_size)
        stream_params = self.get_stream_params()
        types_found = False
        for blocks, size in stream_params:
            cand_stream = self.get_stream(blocks, size)
            if (
                struct.unpack('I', cand_stream[4:8])[0] == 0x38 and
                '_EPROCESS' in cand_stream
            ):
                types_found = True
                self.types_stream = cand_stream
                print('Types PDB stream found at %s' %
                      hex(blocks[0] * self.block_size).replace('L', ''))
                break
        if not types_found:
            print('Could not locate types PDB stream')
        self.handle.close()

    def get_stream_params(self):
        stream_count = struct.unpack('I', self.root_stream[:4])[0]
        stream_sizes = struct.unpack('I' * stream_count,
                                     self.root_stream[4:stream_count * 4 + 4])
        blocks_idx = stream_count * 4 + 4
        res = []
        for size in stream_sizes:
            if size in (0, 0xffffffff):
                continue
            block_count = int(math.ceil(float(size) / self.block_size))
            blocks = struct.unpack(
                'I' * block_count,
                self.root_stream[blocks_idx:blocks_idx + block_count * 4]
            )
            res.append((blocks, size))
            blocks_idx += block_count * 4
        return res

    def get_stream(self, blocks, size):
        res = b''
        for block in blocks:
            self.handle.seek(self.block_size * block)
            res = b''.join((res,
                            self.handle.read(min(self.block_size, size))))
            size -= self.block_size
        return res


class ModifierType:
    modifiers = []
    base_type = ''

    def __init__(self, types_info_holder, data):
        base_type_id = struct.unpack('I', data[:4])[0]
        self.base_type = types_info_holder.get_type_string(base_type_id)
        all_modifiers = ['const', 'unaligned', 'volatile']
        modifier_byte = struct.unpack('B', data[4:5])[0]
        self.modifiers = [all_modifiers[i]
                          for i in (0, 1, 2)
                          if (modifier_byte & (1 << i))]

    def __str__(self):
        return ' '.join(self.modifiers + [self.base_type])


class PointerType:
    base_type = ''

    def __init__(self, types_info_holder, data):
        base_type_id = struct.unpack('I', data[:4])[0]
        self.base_type = types_info_holder.get_type_string(base_type_id)

    def __str__(self):
        return ' '.join(('Pointer to', self.base_type))


class ArgListType:
    def __init__(self, types_info_holder, data):
        self.arg_count = struct.unpack('I', data[:4])[0]
        if self.arg_count:
            arg_type_id = struct.unpack('I', data[4:8])[0]
            self.arg_type = types_info_holder.get_type_string(arg_type_id)

    def __str__(self):
        if self.arg_count:
            return 'List of %d arguments of type %s' % (self.arg_count,
                                                        self.arg_type)
        return 'Empty list of arguments'


class ArrayType:
    def __init__(self, types_info_holder, data):
        elem_type_id = struct.unpack('I', data[:4])[0]
        self.elem_type = types_info_holder.get_type_string(elem_type_id)

    def __str__(self):
        return 'Array of %s' % self.elem_type


class BitFieldType:
    def __init__(self, types_info_holder, data):
        base_type_id = struct.unpack('I', data[:4])[0]
        (self.length, self.position) = struct.unpack('=BB', data[4:6])
        self.base_type = types_info_holder.get_type_string(base_type_id)

    def __str__(self):
        return 'Bit field on %s: length %d, offset %d' % (self.base_type,
                                                          self.length,
                                                          self.position)


class ProcedureType:
    def __init__(self, types_info_holder, data):
        (return_type_id, arg_list_id) = struct.unpack('IxxxxI', data[:0xc])
        self.return_type = types_info_holder.get_type_string(return_type_id)
        self.arg_list = types_info_holder.get_type_string(arg_list_id)
                          
    def __str__(self):
        return 'Procedure returning type %s taking %s' % (self.return_type,
                                                          self.arg_list)


class StructureType:
    name = ''
    forward_declared = False
    member_count = 0
    size = 0
    fieldlist_id = 0
    
    def __init__(self, types_info_holder, data):
        struct_fmt = 'HHIxxxxxxxxH'
        header_size = struct.calcsize(struct_fmt)
        (self.member_count, property,
         self.fieldlist_id, self.size) = struct.unpack(
            struct_fmt, data[:header_size]
        )
        self.forward_declared = bool(property & (1 << 7))
        self.name = data[header_size:data.find(b'\x00', header_size)]
        self.types_info_holder = types_info_holder

    def __str__(self):
        return ' '.join(('struct', self.name))
        
    def get_offset(self, field_name):
        fieldlist = self.types_info_holder.types[self.fieldlist_id]
        offset = -1
        for field in fieldlist.fields:
            if offset == -1 and field.name == field_name:
                offset = field.offset
            if offset != -1 and field.offset > offset:
                return (offset, field.offset - offset)
        if offset != -1:
            return (offset, self.size - offset)
        raise KeyError('Field %s not found' % field_name)
        
    def extract_number(self, field_name, buffer, length=0):
        (number_off, number_len) = self.get_offset(field_name)
        if length:
            number_len = length
        if number_len == 8:
            fmt = 'Q'
        elif number_len == 4:
            fmt = 'I'
        elif number_len == 2:
            fmt = 'H'
        elif number_len == 1:
            fmt = 'B'
        return struct.unpack(
            fmt, buffer[number_off:number_off + number_len]
        )[0]


class UnionType:
    name = ''
    forward_declared = False
    member_count = 0
    size = 0
    fieldlist_id = 0
    
    def __init__(self, types_info_holder, data):
        struct_fmt = 'HHIH'
        header_size = struct.calcsize(struct_fmt)
        (self.member_count, property,
         self.fieldlist_id, self.size) = struct.unpack(
            struct_fmt, data[:header_size]
        )
        self.forward_declared = bool(property & (1 << 7))
        self.name = data[header_size:data.find(b'\x00', header_size)]

    def __str__(self):
        return ' '.join(('union', self.name))


class EnumType:
    name = ''
    forward_declared = False
    member_count = 0
    fieldlist_id = 0
    base_type = ''
    
    def __init__(self, types_info_holder, data):
        struct_fmt = 'HHII'
        header_size = struct.calcsize(struct_fmt)
        (self.member_count, property,
         base_type_id, self.fieldlist_id) = struct.unpack(
            struct_fmt, data[:header_size]
        )
        self.forward_declared = bool(property & (1 << 7))
        self.base_type = types_info_holder.get_type_string(base_type_id)
        self.name = data[header_size:data.find(b'\x00', header_size)]

    def __str__(self):
        return ' '.join(('enum', self.name, '// base:', self.base_type))

class FieldListType:
    def __init__(self, types_info_holder, data):
        self.fields = []
        idx = 0
        while idx < len(data):
            if data[idx] > '\xf0':
                idx += ord(data[idx]) - 0xf0
                continue
            leaf_type = struct.unpack('H', data[idx:idx + 2])[0]
            new_field = types_info_holder.PARSER_CLASSES[leaf_type](
                types_info_holder, data[idx + 2:]
            )
            self.fields.append(new_field)
            idx += 2 + len(new_field)
                          
    def __str__(self):
        return '\n'.join([str(field) for field in self.fields])


class MemberType:
    name = ''
    offset = 0
    attrs = 0
    type = ''
    struct_fmt = '=HIH'
    
    def __init__(self, types_info_holder, data):
        header_size = struct.calcsize(self.struct_fmt)
        (self.attrs, type_id, self.offset) = struct.unpack(
            self.struct_fmt, data[:header_size]
        )
        self.type = types_info_holder.get_type_string(type_id)
        self.name = data[header_size:data.find(b'\x00', header_size)]

    def __str__(self):
        return '%s %s // offset: %d bytes' % (self.type, self.name,
                                              self.offset)
        
    def __len__(self):
        return struct.calcsize(self.struct_fmt) + len(self.name) + 1


class EnumerateType:
    name = ''
    value = 0
    attrs = 0
    struct_fmt = 'H'
    
    def __init__(self, types_info_holder, data):
        header_size = struct.calcsize(self.struct_fmt)
        self.attrs = struct.unpack(
            self.struct_fmt, data[:header_size]
        )[0]
        self.value = data[header_size:header_size + 2]
        if struct.unpack('H', self.value)[0] == 0x8004:
            self.value += data[header_size + 2:header_size + 6]
        header_size += len(self.value)
        self.name = data[header_size:data.find(b'\x00', header_size)]

    def __str__(self):
        return self.name
        
    def __len__(self):
        return (struct.calcsize(self.struct_fmt)+ len(self.value) +
                len(self.name) + 1)


class TypesInfoHolder:
    BASE_TYPES = {
        0x00000000: 'T_NOTYPE',
        0x00000001: 'T_ABS',
        0x00000002: 'T_SEGMENT',
        0x00000003: 'T_VOID',
        
        0x00000008: 'T_HRESULT',
        0x00000408: 'T_32PHRESULT',
        0x00000608: 'T_64PHRESULT',
        
        0x00000103: 'T_PVOID',
        0x00000203: 'T_PFVOID',
        0x00000303: 'T_PHVOID',
        0x00000403: 'T_32PVOID',
        0x00000503: 'T_32PFVOID',
        0x00000603: 'T_64PVOID',
        
        0x00000004: 'T_CURRENCY',
        0x00000005: 'T_NBASICSTR',
        0x00000006: 'T_FBASICSTR',
        0x00000007: 'T_NOTTRANS',
        0x00000060: 'T_BIT',
        0x00000061: 'T_PASCHAR',
        
        0x00000010: 'T_CHAR',
        0x00000110: 'T_PCHAR',
        0x00000210: 'T_PFCHAR',
        0x00000310: 'T_PHCHAR',
        0x00000410: 'T_32PCHAR',
        0x00000510: 'T_32PFCHAR',
        0x00000610: 'T_64PCHAR',
        
        0x00000020: 'T_UCHAR',
        0x00000120: 'T_PUCHAR',
        0x00000220: 'T_PFUCHAR',
        0x00000320: 'T_PHUCHAR',
        0x00000420: 'T_32PUCHAR',
        0x00000520: 'T_32PFUCHAR',
        0x00000620: 'T_64PUCHAR',
        
        0x00000070: 'T_RCHAR',
        0x00000170: 'T_PRCHAR',
        0x00000270: 'T_PFRCHAR',
        0x00000370: 'T_PHRCHAR',
        0x00000470: 'T_32PRCHAR',
        0x00000570: 'T_32PFRCHAR',
        0x00000670: 'T_64PRCHAR',
        
        0x00000071: 'T_WCHAR',
        0x00000171: 'T_PWCHAR',
        0x00000271: 'T_PFWCHAR',
        0x00000371: 'T_PHWCHAR',
        0x00000471: 'T_32PWCHAR',
        0x00000571: 'T_32PFWCHAR',
        0x00000671: 'T_64PWCHAR',
        
        0x00000068: 'T_INT1',
        0x00000168: 'T_PINT1',
        0x00000268: 'T_PFINT1',
        0x00000368: 'T_PHINT1',
        0x00000468: 'T_32PINT1',
        0x00000568: 'T_32PFINT1',
        0x00000668: 'T_64PINT1',
        
        0x00000069: 'T_UINT1',
        0x00000169: 'T_PUINT1',
        0x00000269: 'T_PFUINT1',
        0x00000369: 'T_PHUINT1',
        0x00000469: 'T_32PUINT1',
        0x00000569: 'T_32PFUINT1',
        0x00000669: 'T_64PUINT1',
        
        0x00000011: 'T_SHORT',
        0x00000111: 'T_PSHORT',
        0x00000211: 'T_PFSHORT',
        0x00000311: 'T_PHSHORT',
        0x00000411: 'T_32PSHORT',
        0x00000511: 'T_32PFSHORT',
        0x00000611: 'T_64PSHORT',
        
        0x00000021: 'T_USHORT',
        0x00000121: 'T_PUSHORT',
        0x00000221: 'T_PFUSHORT',
        0x00000321: 'T_PHUSHORT',
        0x00000421: 'T_32PUSHORT',
        0x00000521: 'T_32PFUSHORT',
        0x00000621: 'T_64PUSHORT',
        
        0x00000072: 'T_INT2',
        0x00000172: 'T_PINT2',
        0x00000272: 'T_PFINT2',
        0x00000372: 'T_PHINT2',
        0x00000472: 'T_32PINT2',
        0x00000572: 'T_32PFINT2',
        0x00000672: 'T_64PINT2',
        
        0x00000073: 'T_UINT2',
        0x00000173: 'T_PUINT2',
        0x00000273: 'T_PFUINT2',
        0x00000373: 'T_PHUINT2',
        0x00000473: 'T_32PUINT2',
        0x00000573: 'T_32PFUINT2',
        0x00000673: 'T_64PUINT2',
        
        0x00000012: 'T_LONG',
        0x00000112: 'T_PLONG',
        0x00000212: 'T_PFLONG',
        0x00000312: 'T_PHLONG',
        0x00000412: 'T_32PLONG',
        0x00000512: 'T_32PFLONG',
        0x00000612: 'T_64PLONG',
        
        0x00000022: 'T_ULONG',
        0x00000122: 'T_PULONG',
        0x00000222: 'T_PFULONG',
        0x00000322: 'T_PHULONG',
        0x00000422: 'T_32PULONG',
        0x00000522: 'T_32PFULONG',
        0x00000622: 'T_64PULONG',
        
        0x00000074: 'T_INT4',
        0x00000174: 'T_PINT4',
        0x00000274: 'T_PFINT4',
        0x00000374: 'T_PHINT4',
        0x00000474: 'T_32PINT4',
        0x00000574: 'T_32PFINT4',
        0x00000674: 'T_64PINT4',
        
        0x00000075: 'T_UINT4',
        0x00000175: 'T_PUINT4',
        0x00000275: 'T_PFUINT4',
        0x00000375: 'T_PHUINT4',
        0x00000475: 'T_32PUINT4',
        0x00000575: 'T_32PFUINT4',
        0x00000675: 'T_64PUINT4',
        
        0x00000013: 'T_QUAD',
        0x00000113: 'T_PQUAD',
        0x00000213: 'T_PFQUAD',
        0x00000313: 'T_PHQUAD',
        0x00000413: 'T_32PQUAD',
        0x00000513: 'T_32PFQUAD',
        0x00000613: 'T_64PQUAD',
        
        0x00000023: 'T_UQUAD',
        0x00000123: 'T_PUQUAD',
        0x00000223: 'T_PFUQUAD',
        0x00000323: 'T_PHUQUAD',
        0x00000423: 'T_32PUQUAD',
        0x00000523: 'T_32PFUQUAD',
        0x00000623: 'T_64PUQUAD',
        
        0x00000076: 'T_INT8',
        0x00000176: 'T_PINT8',
        0x00000276: 'T_PFINT8',
        0x00000376: 'T_PHINT8',
        0x00000476: 'T_32PINT8',
        0x00000576: 'T_32PFINT8',
        0x00000676: 'T_64PINT8',
        
        0x00000077: 'T_UINT8',
        0x00000177: 'T_PUINT8',
        0x00000277: 'T_PFUINT8',
        0x00000377: 'T_PHUINT8',
        0x00000477: 'T_32PUINT8',
        0x00000577: 'T_32PFUINT8',
        0x00000677: 'T_64PUINT8',
        
        0x00000014: 'T_OCT',
        0x00000114: 'T_POCT',
        0x00000214: 'T_PFOCT',
        0x00000314: 'T_PHOCT',
        0x00000414: 'T_32POCT',
        0x00000514: 'T_32PFOCT',
        0x00000614: 'T_64POCT',
        
        0x00000024: 'T_UOCT',
        0x00000124: 'T_PUOCT',
        0x00000224: 'T_PFUOCT',
        0x00000324: 'T_PHUOCT',
        0x00000424: 'T_32PUOCT',
        0x00000524: 'T_32PFUOCT',
        0x00000624: 'T_64PUOCT',
        
        0x00000078: 'T_INT16',
        0x00000178: 'T_PINT16',
        0x00000278: 'T_PFINT16',
        0x00000378: 'T_PHINT16',
        0x00000478: 'T_32PINT16',
        0x00000578: 'T_32PFINT16',
        0x00000678: 'T_64PINT16',
        
        0x00000079: 'T_UINT16',
        0x00000179: 'T_PUINT16',
        0x00000279: 'T_PFUINT16',
        0x00000379: 'T_PHUINT16',
        0x00000479: 'T_32PUINT16',
        0x00000579: 'T_32PFUINT16',
        0x00000679: 'T_64PUINT16',
        
        0x00000040: 'T_REAL32',
        0x00000140: 'T_PREAL32',
        0x00000240: 'T_PFREAL32',
        0x00000340: 'T_PHREAL32',
        0x00000440: 'T_32PREAL32',
        0x00000540: 'T_32PFREAL32',
        0x00000640: 'T_64PREAL32',
        
        0x00000044: 'T_REAL48',
        0x00000144: 'T_PREAL48',
        0x00000244: 'T_PFREAL48',
        0x00000344: 'T_PHREAL48',
        0x00000444: 'T_32PREAL48',
        0x00000544: 'T_32PFREAL48',
        0x00000644: 'T_64PREAL48',
        
        0x00000041: 'T_REAL64',
        0x00000141: 'T_PREAL64',
        0x00000241: 'T_PFREAL64',
        0x00000341: 'T_PHREAL64',
        0x00000441: 'T_32PREAL64',
        0x00000541: 'T_32PFREAL64',
        0x00000641: 'T_64PREAL64',
        
        0x00000042: 'T_REAL80',
        0x00000142: 'T_PREAL80',
        0x00000242: 'T_PFREAL80',
        0x00000342: 'T_PHREAL80',
        0x00000442: 'T_32PREAL80',
        0x00000542: 'T_32PFREAL80',
        0x00000642: 'T_64PREAL80',
        
        0x00000043: 'T_REAL128',
        0x00000143: 'T_PREAL128',
        0x00000243: 'T_PFREAL128',
        0x00000343: 'T_PHREAL128',
        0x00000443: 'T_32PREAL128',
        0x00000543: 'T_32PFREAL128',
        0x00000643: 'T_64PREAL128',
        
        0x00000050: 'T_CPLX32',
        0x00000150: 'T_PCPLX32',
        0x00000250: 'T_PFCPLX32',
        0x00000350: 'T_PHCPLX32',
        0x00000450: 'T_32PCPLX32',
        0x00000550: 'T_32PFCPLX32',
        0x00000650: 'T_64PCPLX32',
        
        0x00000051: 'T_CPLX64',
        0x00000151: 'T_PCPLX64',
        0x00000251: 'T_PFCPLX64',
        0x00000351: 'T_PHCPLX64',
        0x00000451: 'T_32PCPLX64',
        0x00000551: 'T_32PFCPLX64',
        0x00000651: 'T_64PCPLX64',
        
        0x00000052: 'T_CPLX80',
        0x00000152: 'T_PCPLX80',
        0x00000252: 'T_PFCPLX80',
        0x00000352: 'T_PHCPLX80',
        0x00000452: 'T_32PCPLX80',
        0x00000552: 'T_32PFCPLX80',
        0x00000652: 'T_64PCPLX80',
        
        0x00000053: 'T_CPLX128',
        0x00000153: 'T_PCPLX128',
        0x00000253: 'T_PFCPLX128',
        0x00000353: 'T_PHCPLX128',
        0x00000453: 'T_32PCPLX128',
        0x00000553: 'T_32PFCPLX128',
        0x00000653: 'T_64PCPLX128',
        
        0x00000030: 'T_BOOL08',
        0x00000130: 'T_PBOOL08',
        0x00000230: 'T_PFBOOL08',
        0x00000330: 'T_PHBOOL08',
        0x00000430: 'T_32PBOOL08',
        0x00000530: 'T_32PFBOOL08',
        0x00000630: 'T_64PBOOL08',
        
        0x00000031: 'T_BOOL16',
        0x00000131: 'T_PBOOL16',
        0x00000231: 'T_PFBOOL16',
        0x00000331: 'T_PHBOOL16',
        0x00000431: 'T_32PBOOL16',
        0x00000531: 'T_32PFBOOL16',
        0x00000631: 'T_64PBOOL16',
        
        0x00000032: 'T_BOOL32',
        0x00000132: 'T_PBOOL32',
        0x00000232: 'T_PFBOOL32',
        0x00000332: 'T_PHBOOL32',
        0x00000432: 'T_32PBOOL32',
        0x00000532: 'T_32PFBOOL32',
        0x00000632: 'T_64PBOOL32',
        
        0x00000033: 'T_BOOL64',
        0x00000133: 'T_PBOOL64',
        0x00000233: 'T_PFBOOL64',
        0x00000333: 'T_PHBOOL64',
        0x00000433: 'T_32PBOOL64',
        0x00000533: 'T_32PFBOOL64',
        0x00000633: 'T_64PBOOL64',
        
        0x000001F0: 'T_NCVPTR',
        0x000002F0: 'T_FCVPTR',
        0x000003F0: 'T_HCVPTR',
        0x000004F0: 'T_32NCVPTR',
        0x000005F0: 'T_32FCVPTR',
        0x000006F0: 'T_64NCVPTR',
    }
    LF_MODIFIER_16t         = 0x00000001
    LF_POINTER_16t          = 0x00000002
    LF_ARRAY_16t            = 0x00000003
    LF_CLASS_16t            = 0x00000004
    LF_STRUCTURE_16t        = 0x00000005
    LF_UNION_16t            = 0x00000006
    LF_ENUM_16t             = 0x00000007
    LF_PROCEDURE_16t        = 0x00000008
    LF_MFUNCTION_16t        = 0x00000009
    LF_VTSHAPE              = 0x0000000A
    LF_COBOL0_16t           = 0x0000000B
    LF_COBOL1               = 0x0000000C
    LF_BARRAY_16t           = 0x0000000D
    LF_LABEL                = 0x0000000E
    LF_NULL                 = 0x0000000F
    LF_NOTTRAN              = 0x00000010
    LF_DIMARRAY_16t         = 0x00000011
    LF_VFTPATH_16t          = 0x00000012
    LF_PRECOMP_16t          = 0x00000013
    LF_ENDPRECOMP           = 0x00000014
    LF_OEM_16t              = 0x00000015
    LF_TYPESERVER_ST        = 0x00000016
    LF_SKIP_16t             = 0x00000200
    LF_ARGLIST_16t          = 0x00000201
    LF_DEFARG_16t           = 0x00000202
    LF_LIST                 = 0x00000203
    LF_FIELDLIST_16t        = 0x00000204
    LF_DERIVED_16t          = 0x00000205
    LF_BITFIELD_16t         = 0x00000206
    LF_METHODLIST_16t       = 0x00000207
    LF_DIMCONU_16t          = 0x00000208
    LF_DIMCONLU_16t         = 0x00000209
    LF_DIMVARU_16t          = 0x0000020A
    LF_DIMVARLU_16t         = 0x0000020B
    LF_REFSYM               = 0x0000020C
    LF_BCLASS_16t           = 0x00000400
    LF_VBCLASS_16t          = 0x00000401
    LF_IVBCLASS_16t         = 0x00000402
    LF_ENUMERATE_ST         = 0x00000403
    LF_FRIENDFCN_16t        = 0x00000404
    LF_INDEX_16t            = 0x00000405
    LF_MEMBER_16t           = 0x00000406
    LF_STMEMBER_16t         = 0x00000407
    LF_METHOD_16t           = 0x00000408
    LF_NESTTYPE_16t         = 0x00000409
    LF_VFUNCTAB_16t         = 0x0000040A
    LF_FRIENDCLS_16t        = 0x0000040B
    LF_ONEMETHOD_16t        = 0x0000040C
    LF_VFUNCOFF_16t         = 0x0000040D
    LF_TI16_MAX             = 0x00001000
    LF_MODIFIER             = 0x00001001
    LF_POINTER              = 0x00001002
    LF_ARRAY_ST             = 0x00001003
    LF_CLASS_ST             = 0x00001004
    LF_STRUCTURE_ST         = 0x00001005
    LF_UNION_ST             = 0x00001006
    LF_ENUM_ST              = 0x00001007
    LF_PROCEDURE            = 0x00001008
    LF_MFUNCTION            = 0x00001009
    LF_COBOL0               = 0x0000100A
    LF_BARRAY               = 0x0000100B
    LF_DIMARRAY_ST          = 0x0000100C
    LF_VFTPATH              = 0x0000100D
    LF_PRECOMP_ST           = 0x0000100E
    LF_OEM                  = 0x0000100F
    LF_ALIAS_ST             = 0x00001010
    LF_OEM2                 = 0x00001011
    LF_SKIP                 = 0x00001200
    LF_ARGLIST              = 0x00001201
    LF_DEFARG_ST            = 0x00001202
    LF_FIELDLIST            = 0x00001203
    LF_DERIVED              = 0x00001204
    LF_BITFIELD             = 0x00001205
    LF_METHODLIST           = 0x00001206
    LF_DIMCONU              = 0x00001207
    LF_DIMCONLU             = 0x00001208
    LF_DIMVARU              = 0x00001209
    LF_DIMVARLU             = 0x0000120A
    LF_BCLASS               = 0x00001400
    LF_VBCLASS              = 0x00001401
    LF_IVBCLASS             = 0x00001402
    LF_FRIENDFCN_ST         = 0x00001403
    LF_INDEX                = 0x00001404
    LF_MEMBER_ST            = 0x00001405
    LF_STMEMBER_ST          = 0x00001406
    LF_METHOD_ST            = 0x00001407
    LF_NESTTYPE_ST          = 0x00001408
    LF_VFUNCTAB             = 0x00001409
    LF_FRIENDCLS            = 0x0000140A
    LF_ONEMETHOD_ST         = 0x0000140B
    LF_VFUNCOFF             = 0x0000140C
    LF_NESTTYPEEX_ST        = 0x0000140D
    LF_MEMBERMODIFY_ST      = 0x0000140E
    LF_MANAGED_ST           = 0x0000140F
    LF_ST_MAX               = 0x00001500
    LF_TYPESERVER           = 0x00001501
    LF_ENUMERATE            = 0x00001502
    LF_ARRAY                = 0x00001503
    LF_CLASS                = 0x00001504
    LF_STRUCTURE            = 0x00001505
    LF_UNION                = 0x00001506
    LF_ENUM                 = 0x00001507
    LF_DIMARRAY             = 0x00001508
    LF_PRECOMP              = 0x00001509
    LF_ALIAS                = 0x0000150A
    LF_DEFARG               = 0x0000150B
    LF_FRIENDFCN            = 0x0000150C
    LF_MEMBER               = 0x0000150D
    LF_STMEMBER             = 0x0000150E
    LF_METHOD               = 0x0000150F
    LF_NESTTYPE             = 0x00001510
    LF_ONEMETHOD            = 0x00001511
    LF_NESTTYPEEX           = 0x00001512
    LF_MEMBERMODIFY         = 0x00001513
    LF_MANAGED              = 0x00001514
    LF_TYPESERVER2          = 0x00001515
    LF_CHAR                 = 0x00008000
    LF_SHORT                = 0x00008001
    LF_USHORT               = 0x00008002
    LF_LONG                 = 0x00008003
    LF_ULONG                = 0x00008004
    LF_REAL32               = 0x00008005
    LF_REAL64               = 0x00008006
    LF_REAL80               = 0x00008007
    LF_REAL128              = 0x00008008
    LF_QUADWORD             = 0x00008009
    LF_UQUADWORD            = 0x0000800A
    LF_REAL48               = 0x0000800B
    LF_COMPLEX32            = 0x0000800C
    LF_COMPLEX64            = 0x0000800D
    LF_COMPLEX80            = 0x0000800E
    LF_COMPLEX128           = 0x0000800F
    LF_VARSTRING            = 0x00008010
    LF_OCTWORD              = 0x00008017
    LF_UOCTWORD             = 0x00008018
    LF_DECIMAL              = 0x00008019
    LF_DATE                 = 0x0000801A
    LF_UTF8STRING           = 0x0000801B
    LF_PAD0                 = 0x000000F0
    LF_PAD1                 = 0x000000F1
    LF_PAD2                 = 0x000000F2
    LF_PAD3                 = 0x000000F3
    LF_PAD4                 = 0x000000F4
    LF_PAD5                 = 0x000000F5
    LF_PAD6                 = 0x000000F6
    LF_PAD7                 = 0x000000F7
    LF_PAD8                 = 0x000000F8
    LF_PAD9                 = 0x000000F9
    LF_PAD10                = 0x000000FA
    LF_PAD11                = 0x000000FB
    LF_PAD12                = 0x000000FC
    LF_PAD13                = 0x000000FD
    LF_PAD14                = 0x000000FE
    LF_PAD15                = 0x000000FF
    PARSER_CLASSES = {
        LF_MODIFIER: ModifierType,
        LF_POINTER: PointerType,
        LF_STRUCTURE: StructureType,
        LF_FIELDLIST: FieldListType,
        LF_MEMBER: MemberType,
        LF_ARGLIST: ArgListType,
        LF_PROCEDURE: ProcedureType,
        LF_ARRAY: ArrayType,
        LF_ENUMERATE: EnumerateType,
        LF_ENUM: EnumType,
        LF_UNION: UnionType,
        LF_BITFIELD: BitFieldType
    }
    stream = b''
    ti_min = 0
    ti_max = 0
    types = {}
    
    def __init__(self, stream):
        self.stream = stream
        print('Types stream Visual Studio signature is %d' % struct.unpack(
            'I', stream[:4]
        ))
        (self.ti_min, self.ti_max) = struct.unpack('II', stream[0x8:0x10])
        print('Parsing kernel types...')
        self.parse()
        
    def parse(self):
        idx = 0x38
        ti = self.ti_min
        while ti < self.ti_max:
            (size, leaf_type) = struct.unpack('HH', self.stream[idx:idx + 4])
            self.types[ti] = self.PARSER_CLASSES[leaf_type](
                self, self.stream[idx + 4:idx + 2 + size]
            )
            idx += 2 + size
            ti += 1
            
    def find_struct(self, name):
        for ti in range(self.ti_min, self.ti_max):
            if str(self.types[ti].__class__) == '__main__.StructureType':
                struct = self.types[ti]
                if struct.name != name or struct.forward_declared:
                    continue
                return struct
        raise KeyError('Struct %s not found' % name)
        
    def show_structs(self):
        for ti in range(self.ti_min, self.ti_max):
            if str(self.types[ti].__class__) == '__main__.StructureType':
                struct = self.types[ti]
                if struct.forward_declared or struct.name == '<unnamed-tag>':
                    continue
                print(struct.name)
            
    def print_struct_info(self, name):
        struct = self.find_struct(name)
        print('%s { // %d bytes total' % (str(struct), struct.size))
        fieldlist = self.types[struct.fieldlist_id]
        for field in fieldlist.fields:
            print('\t%s' % str(field))
        print('}')
            
    def get_type_string(self, type_id):
        if type_id < self.ti_min:
            return self.BASE_TYPES[type_id]
        return str(self.types[type_id])


class Process:
    def __init__(self, origin, eprocess, eprocess_content, eprocess_offset):
        self.origin = origin
        self.threads = []
        self.eprocess_offset = eprocess_offset
        (name_offset, name_len) = eprocess.get_offset('ImageFileName')
        self.name = eprocess_content[name_offset:eprocess_content.find(
                                                     b'\x00', name_offset
                                                 )]
        if len(self.name) > name_len - 1:
            raise TypeError('Invalid process!')
        (apl_offset, apl_len) = eprocess.get_offset('ActiveProcessLinks')
        if apl_len == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        (self.flink, self.blink) = struct.unpack(
            link_fmt * 2, eprocess_content[apl_offset:apl_offset + apl_len]
        )
        self.pid = eprocess.extract_number(
            'UniqueProcessId', eprocess_content
        )
        self.ppid = eprocess.extract_number(
            'InheritedFromUniqueProcessId', eprocess_content
        )
        self.thread_count = eprocess.extract_number(
            'ActiveThreads', eprocess_content
        )
        self.peb = eprocess.extract_number('Peb', eprocess_content)
        timestamp = eprocess.extract_number('CreateTime', eprocess_content)
        self.create_time = self.timestamp_to_date(timestamp)
        timestamp = eprocess.extract_number('ExitTime', eprocess_content)
        self.exit_time = self.timestamp_to_date(timestamp)
        if self.name != 'Idle' and self.create_time.year < 1900:
            raise TypeError('Invalid process!')
        kprocess = eprocess.types_info_holder.find_struct('_KPROCESS')
        self.directory_table_base = kprocess.extract_number(
            'DirectoryTableBase', eprocess_content
        )
        
    def timestamp_to_date(self, timestamp):
        try:
            return datetime.datetime(
                1601, 1, 1, 0, 0, 0, 0
            ) + datetime.timedelta(
                microseconds=timestamp / 10
            ) + (datetime.datetime.now() - datetime.datetime.utcnow())
        except OverflowError:
            raise TypeError('Invalid process!')
        
    def __unicode__(self):
        return u'%s % 5d % 5d % 14s % 14s % 14s %s' % (
            self.origin, self.pid, self.ppid, self.name,
            hex(self.directory_table_base).replace('L', ''),
            hex(self.eprocess_offset).replace('L', ''),
            self.time_string(self.create_time)
        )
        
    def attach_threads(self, threads):
        self.threads = threads
        
    def time_string(self, time):
        try:
            return time.strftime(DATE_FMT)
        except:
            return '0'
        
    def print_verbose_info(self):
        print(u'''
Origin:                 %s
PID:                    %d
PPID:                   %d
Name:                   %s
EPROCESS base:          %s
Page directory:         %s
Create time:            %s
Exit time:              %s
Active threads:         %d
PEB virtual address:    %s
        ''' % ('Kernel list' if self.origin == 'K' else 'Signature scannng',
               self.pid, self.ppid, self.name,
               hex(self.eprocess_offset).replace('L', ''),
               hex(self.directory_table_base).replace('L', ''),
               self.time_string(self.create_time),
               self.time_string(self.exit_time),
               self.thread_count,
               hex(self.peb).replace('L', '')))


class Thread:
    def __init__(self, process, ethread, ethread_content, ethread_offset):
        self.process = process
        self.regs = {}
        self.reg_names = []
        self.ethread_offset = ethread_offset
        (tle_offset, tle_len) = ethread.get_offset('ThreadListEntry')
        if tle_len == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        (self.flink, self.blink) = struct.unpack(
            link_fmt * 2, ethread_content[tle_offset:tle_offset + tle_len]
        )
        timestamp = ethread.extract_number('CreateTime', ethread_content)
        self.create_time = self.timestamp_to_date(timestamp)
        timestamp = ethread.extract_number('ExitTime', ethread_content, 8)
        self.exit_time = self.timestamp_to_date(timestamp)
        kthread = ethread.types_info_holder.find_struct('_KTHREAD')
        self.kernel_stack = kthread.extract_number(
            'KernelStack', ethread_content
        )
        self.trap_va = kthread.extract_number(
            'TrapFrame', ethread_content
        )
        
    def timestamp_to_date(self, timestamp):
        try:
            return datetime.datetime(
                1601, 1, 1, 0, 0, 0, 0
            ) + datetime.timedelta(
                microseconds=timestamp / 10
            ) + (datetime.datetime.now() - datetime.datetime.utcnow())
        except OverflowError:
            return self.timestamp_to_date(0)
        
    def __unicode__(self):
        return u'% 14s % 18s % 23s % 23s' % (
            hex(self.ethread_offset).replace('L', ''),
            hex(self.kernel_stack).replace('L', ''),
            self.time_string(self.create_time),
            self.time_string(self.exit_time)
        )
        
    def attach_regs(self, regs, reg_names):
        self.reg_names = reg_names
        self.regs = regs
        
    def print_regs(self):
        for reg in self.reg_names:
            try:
                print('%s:\t%s' % (reg, hex(self.regs[reg]).replace('L', '')))
            except KeyError:
                pass
        
    def time_string(self, time):
        try:
            return time.strftime(DATE_FMT)
        except:
            return '0'


class Hive:
    def __init__(self, cmhive, hive_content, cmhive_offset):
        self.cmhive_offset = cmhive_offset
        self.time = 0
        self.root_cell = 0
        self.name = ''
        (hle_offset, hle_len) = cmhive.get_offset('HiveList')
        if hle_len == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        (self.flink, self.blink) = struct.unpack(
            link_fmt * 2, hive_content[hle_offset:hle_offset + hle_len]
        )
        hhive = cmhive.types_info_holder.find_struct('_HHIVE')
        self.hbase_va = hhive.extract_number('BaseBlock', hive_content)
        dual = cmhive.types_info_holder.find_struct('_DUAL')
        (storage_offset, storage_len) = hhive.get_offset('Storage')
        storage = hive_content[storage_offset:storage_offset + storage_len]
        self.size = dual.extract_number('Length', storage)
        self.map_va = dual.extract_number('Map', storage)
        
    def set_time(self, timestamp):
        try:
            self.time = datetime.datetime(
                1601, 1, 1, 0, 0, 0, 0
            ) + datetime.timedelta(
                microseconds=timestamp / 10
            ) + (datetime.datetime.now() - datetime.datetime.utcnow())
        except OverflowError:
            self.set_time(0)
            
    def set_name(self, name):
        self.name = name
        
    def set_root_cell(self, root_cell):
        self.root_cell = root_cell
        
    def __unicode__(self):
        return u'% 14s % 18s % 31s % 19s' % (
            hex(self.cmhive_offset).replace('L', ''),
            hex(self.map_va).replace('L', ''),
            self.name, self.time_string(self.time)
        )
        
    def time_string(self, time):
        try:
            return time.strftime(DATE_FMT)
        except:
            return '0'


class KeyNode:
    def __init__(self, dump_info_holder, hive, struct_va):
        self.struct_va = struct_va
        self.dump_info_holder = dump_info_holder
        self.hive = hive
        cm_struct = dump_info_holder.types_info_holder.find_struct(
            '_CM_KEY_NODE'
        )
        content = dump_info_holder.extract_buffer(
            cm_struct.size, struct_va,
            dump_info_holder.kernel_directory_table_base
        )
        timestamp = cm_struct.extract_number('LastWriteTime', content)
        self.time = self.timestamp_to_date(timestamp)
        (counts_offset, counts_len) = cm_struct.get_offset('SubKeyCounts')
        self.subkey_count = struct.unpack('I', content[counts_offset:
                                                       counts_offset + 4])[0]
        self.subkeys = []
        if self.subkey_count:
            (kl_offset, kl_len) = cm_struct.get_offset('ChildHiveReference')
            ref_content = content[kl_offset:kl_offset + kl_len]
            ref_struct = dump_info_holder.types_info_holder.find_struct(
                '_CM_KEY_REFERENCE'
            )
            list_cell_index = ref_struct.extract_number('KeyCell',
                                                        ref_content)
            key_list = dump_info_holder.registry_cell(hive, list_cell_index)
            unclean_subkeys = key_list.list
            for subkey_cell_index in unclean_subkeys:
                subkey_va = dump_info_holder.registry_cell_va(
                    hive, subkey_cell_index
                )
                subkey_signature = dump_info_holder.extract_buffer(
                    2, subkey_va + 4,
                    dump_info_holder.kernel_directory_table_base
                )
                if subkey_signature != '\x00\x00':  # bad paging
                    self.subkeys.append(subkey_cell_index)
                else:
                    self.subkey_count -= 1
        (vl_offset, vl_len) = cm_struct.get_offset('ValueList')
        vl_content = content[vl_offset:vl_offset + vl_len]
        vl_struct = dump_info_holder.types_info_holder.find_struct(
                '_CHILD_LIST'
        )
        self.value_count = vl_struct.extract_number('Count', vl_content)
        self.values = []
        unclean_values = []
        if self.value_count:
            list_cell_index = vl_struct.extract_number('List', vl_content)
            list_va = dump_info_holder.registry_cell_va(hive, list_cell_index)
            unclean_values += struct.unpack(
                'I' * self.value_count,
                dump_info_holder.extract_buffer(
                    4 * self.value_count, list_va + 4,
                    dump_info_holder.kernel_directory_table_base
                )
            )
            for value_cell_index in unclean_values:
                value_va = dump_info_holder.registry_cell_va(
                    hive, value_cell_index
                )
                value_signature = dump_info_holder.extract_buffer(
                    2, value_va + 4,
                    dump_info_holder.kernel_directory_table_base
                )
                if value_signature != '\x00\x00':  # bad paging
                    self.values.append(value_cell_index)
                else:
                    self.value_count -= 1
        security_cell_index = cm_struct.extract_number('Security', content)
        self.security_va = dump_info_holder.registry_cell_va(
            hive, security_cell_index
        )
        name_len = cm_struct.extract_number('NameLength', content)
        (name_offset, fake_name_len) = cm_struct.get_offset('Name')
        self.name = dump_info_holder.extract_buffer(
            name_len, struct_va + name_offset,
            dump_info_holder.kernel_directory_table_base
        )
        flags = cm_struct.extract_number('Flags', content)
        if not flags & 0x20:
            self.name = self.name.decode('utf-16-le')
        self.class_len = cm_struct.extract_number('ClassLength', content)
        if self.class_len:
            class_cell_index = cm_struct.extract_number('Class', content)
            class_va = dump_info_holder.registry_cell_va(hive,
                                                         class_cell_index)
            self.class_name = dump_info_holder.extract_buffer(
                self.class_len, class_va + 4,
                dump_info_holder.kernel_directory_table_base
            ).decode('utf-16-le')

    def __unicode__(self):
        return(u'% 18s %s' % (hex(self.struct_va).replace('L', ''), self.name))

    def print_verbose_info(self):
        print(self.name)
        if self.class_len:
            print(u'Class:               %s' % self.class_name)
        print('struct _CM_KEY_NODE at virtual address %s' %
              hex(self.struct_va).replace('L', ''))
        print('Last write time:     %s' % self.time_string(self.time))
        print('Subkey count:        %d' % self.subkey_count)
        if self.subkey_count:
            print('Cell index      CM_KEY_NODE     Name')
            for cell_index in self.subkeys:
                print(u'% 10s   %s' % (
                    hex(cell_index).replace('L', ''),
                    unicode(self.dump_info_holder.registry_cell(self.hive, cell_index))
                ))
        default_value = None
        print('\nValue count:       %d' % self.value_count)
        if self.value_count:
            print('Cell index      CM_KEY_VALUE     Name')
            for cell_index in self.values:
                value_cell = self.dump_info_holder.registry_cell(self.hive,
                                                                 cell_index)
                if value_cell.name == '':
                    default_value = value_cell
                print('% 10s    %s' % (
                    hex(cell_index).replace('L', ''),
                    unicode(value_cell)
                ))
        if default_value:
            print('\nDefault value:')
            default_value.print_verbose_info()
        print('Security descriptor: struct _CM_KEY_SECURITY at virtual address %s' %
              hex(self.security_va).replace('L', ''))

    def timestamp_to_date(self, timestamp):
        try:
            return datetime.datetime(
                1601, 1, 1, 0, 0, 0, 0
            ) + datetime.timedelta(
                microseconds=timestamp / 10
            ) + (datetime.datetime.now() - datetime.datetime.utcnow())
        except OverflowError:
            return self.timestamp_to_date(0)

    def time_string(self, time):
        try:
            return time.strftime(DATE_FMT)
        except:
            return '0'
            
    def binary_search(self, subkey):
        l = 0;
        r = self.subkey_count
        c = (l + r) / 2
        while l < r:
            cell = self.dump_info_holder.registry_cell(self.hive,
                                                       self.subkeys[c])
            if (subkey.upper() <= cell.name.upper()):
                r = c
            else:
                l = c + 1
            c = (l + r) / 2
        if r >= self.subkey_count:
            raise KeyError('Node %s does not contain subkey %s' % (self.name,
                                                                   subkey))
        cell = self.dump_info_holder.registry_cell(self.hive, self.subkeys[r])
        if cell.name == subkey:
            return cell
        else:
            raise KeyError('Node %s does not contain subkey %s' % (self.name,
                                                                   subkey))

    def get_value(self, subkey):
        for cell_index in self.values:
            cell = self.dump_info_holder.registry_cell(self.hive, cell_index)
            if cell.name == subkey:
                return cell
        raise KeyError('Node %s does not contain value %s' % (self.name,
                                                              subkey))


class KeyLink:
    def __init__(self, dump_info_holder, hive, struct_va):
        self.struct_va = struct_va
        self.dump_info_holder = dump_info_holder
        self.hive = hive
        cm_struct = dump_info_holder.types_info_holder.find_struct(
            '_CM_KEY_NODE'
        )
        content = dump_info_holder.extract_buffer(
            cm_struct.size, struct_va,
            dump_info_holder.kernel_directory_table_base
        )
        timestamp = cm_struct.extract_number('LastWriteTime', content)
        self.time = self.timestamp_to_date(timestamp)
        (ref_offset, ref_len) = cm_struct.get_offset('ChildHiveReference')
        ref_content = content[ref_offset:ref_offset + ref_len]
        ref_struct = dump_info_holder.types_info_holder.find_struct(
            '_CM_KEY_REFERENCE'
        )
        self.orig_cell = None
        self.orig_cell_index = ref_struct.extract_number('KeyCell',
                                                         ref_content)
        orig_hive_va = ref_struct.extract_number('KeyHive', ref_content)
        try:
            orig_hive_pa = dump_info_holder.va_to_physical(
                orig_hive_va, dump_info_holder.kernel_directory_table_base
            )
            for hive_id, hive in enumerate(dump_info_holder.hives):
                if hive.cmhive_offset == orig_hive_pa:
                    self.orig_hive_id = hive_id
                    self.orig_cell = dump_info_holder.registry_cell(
                        hive, self.orig_cell_index
                    )
                    break
        except TypeError:
            pass
        security_cell_index = cm_struct.extract_number('Security', content)
        name_len = cm_struct.extract_number('NameLength', content)
        (name_offset, fake_name_len) = cm_struct.get_offset('Name')
        self.name = dump_info_holder.extract_buffer(
            name_len, struct_va + name_offset,
            dump_info_holder.kernel_directory_table_base
        )
        self.class_len = cm_struct.extract_number('ClassLength', content)
        if self.class_len:
            class_cell_index = cm_struct.extract_number('Class', content)
            class_va = dump_info_holder.registry_cell_va(hive,
                                                         class_cell_index)
            self.class_name = dump_info_holder.extract_buffer(
                self.class_len, class_va + 4,
                dump_info_holder.kernel_directory_table_base
            ).decode('utf-16-le')

    def __unicode__(self):
        if self.orig_cell:
            link_descr = 'link to cell %s in hive #%d' % (
                hex(self.orig_cell_index).replace('L', ''), self.orig_hive_id
            )
        else:
            link_descr = 'broken link'
        return(u'% 18s %s (%s)' %
               (hex(self.struct_va).replace('L', ''), self.name,
                link_descr))

    def print_verbose_info(self):
        print(self.name)
        if self.class_len:
            print(u'Class:               %s' % self.class_name)
        print('struct _CM_KEY_NODE at virtual address %s' %
              hex(self.struct_va).replace('L', ''))
        print('Last write time:     %s' % self.time_string(self.time))
        if self.orig_cell:
            print('Link to cell %s in hive #%d\nOriginal cell:' % (
                hex(self.orig_cell_index).replace('L', ''), self.orig_hive_id
            ))
            self.orig_cell.print_verbose_info()
        else:
            print('Broken link')

    def timestamp_to_date(self, timestamp):
        try:
            return datetime.datetime(
                1601, 1, 1, 0, 0, 0, 0
            ) + datetime.timedelta(
                microseconds=timestamp / 10
            ) + (datetime.datetime.now() - datetime.datetime.utcnow())
        except OverflowError:
            return self.timestamp_to_date(0)

    def time_string(self, time):
        try:
            return time.strftime(DATE_FMT)
        except:
            return '0'
            
    def binary_search(self, subkey):
        if self.orig_cell:
            return self.orig_cell.binary_search(subkey)
        raise KeyError('Node %s is a broken link' % (self.name))

    def get_value(self, subkey):
        if self.orig_cell:
            return self.orig_cell.get_value(subkey)
        raise KeyError('Node %s is a broken link' % (self.name))


class KeyValue:
    REG_NONE                        = 0
    REG_SZ                          = 1
    REG_EXPAND_SZ                   = 2
    REG_BINARY                      = 3
    REG_DWORD                       = 4
    REG_DWORD_BIG_ENDIAN            = 5
    REG_LINK                        = 6
    REG_MULTI_SZ                    = 7
    REG_RESOURCE_LIST               = 8
    REG_FULL_RESOURCE_DESCRIPTOR    = 9
    REG_RESOURCE_REQUIREMENTS_LIST  = 10
    REG_QWORD                       = 11
    TYPES = (
        'REG_NONE',
        'REG_SZ',
        'REG_EXPAND_SZ',
        'REG_BINARY',
        'REG_DWORD',
        'REG_DWORD_BIG_ENDIAN',
        'REG_LINK',
        'REG_MULTI_SZ',
        'REG_RESOURCE_LIST',
        'REG_FULL_RESOURCE_DESCRIPTOR',
        'REG_RESOURCE_REQUIREMENTS_LIST',
        'REG_QWORD'
    )
    
    def __init__(self, dump_info_holder, hive, struct_va):
        self.struct_va = struct_va
        self.dump_info_holder = dump_info_holder
        self.hive = hive
        cm_struct = dump_info_holder.types_info_holder.find_struct(
            '_CM_KEY_VALUE'
        )
        content = dump_info_holder.extract_buffer(
            cm_struct.size, struct_va,
            dump_info_holder.kernel_directory_table_base
        )
        name_len = cm_struct.extract_number('NameLength', content)
        (name_offset, fake_name_len) = cm_struct.get_offset('Name')
        self.name = dump_info_holder.extract_buffer(
            name_len, struct_va + name_offset,
            dump_info_holder.kernel_directory_table_base
        )
        flags = cm_struct.extract_number('Flags', content)
        if not flags & 1:
            self.name = self.name.decode('utf-16-le')
        self.data_length = cm_struct.extract_number('DataLength', content)
        (data_offset, data_len) = cm_struct.get_offset('Data')
        if self.data_length & (1 << 31) and self.data_length - (1 << 31) <= 4:
            self.data_length -= self.data_length & (1 << 31)
            self.data_va = self.struct_va + data_offset
        else:
            data_cell_index = cm_struct.extract_number('Data', content)
            self.data_va = dump_info_holder.registry_cell_va(
                hive, data_cell_index
            ) + 4
        self.type = cm_struct.extract_number('Type', content)

    def __unicode__(self):
        return(u'% 18s %s' % (hex(self.struct_va).replace('L', ''), self.name))

    def print_verbose_info(self):
        print(self.name)
        print('struct _CM_KEY_VALUE at virtual address %s' %
              hex(self.struct_va).replace('L', ''))
        print('Type:     %s' % (self.TYPES[self.type]
                                if self.type < len(self.TYPES)
                                else hex(self.type).replace('L', '')))
        if self.data_length < 80:
            print('Data:')
            data = self.dump_info_holder.extract_buffer(
                self.data_length, self.data_va,
                self.dump_info_holder.kernel_directory_table_base
            )
            if self.type in (self.REG_SZ, self.REG_EXPAND_SZ):
                str_data = data.decode('utf-16-le')
                print(str_data[:str_data.find('\x00')])
            elif self.type == self.REG_MULTI_SZ:
                print('\n'.join(data.decode('utf-16-le').split(b'\x00')))
            elif self.type == self.REG_DWORD and self.data_length == 4:
                print(hex(struct.unpack('I', data)[0]).replace('L', ''))
            elif (
                self.type == self.REG_DWORD_BIG_ENDIAN and
                self.data_length == 4
            ):
                print(hex(struct.unpack('>I', data)[0]).replace('L', ''))
            elif self.type == self.REG_QWORD and self.data_length == 8:
                print(hex(struct.unpack('Q', data)[0]).replace('L', ''))
            else:
                print('[hex dump]')
                self.dump_info_holder.print_hex_dump(data)
        else:
            print('%s bytes of data at virtual address %s' % (
                hex(self.data_length).replace('L', ''),
                hex(self.data_va).replace('L', '')
            ))


class KeyList:
    def __init__(self, dump_info_holder, hive, struct_va):
        self.struct_va = struct_va
        self.count = struct.unpack('H', dump_info_holder.extract_buffer(
            2, struct_va + 2, dump_info_holder.kernel_directory_table_base
        ))[0]
        list_content = dump_info_holder.extract_buffer(
            8 * self.count, struct_va + 4,
            dump_info_holder.kernel_directory_table_base
        )
        self.list = []
        for i in range(self.count):
            self.list.append(struct.unpack('I', list_content[i * 8:
                                                             i * 8 + 4])[0])


class SimpleKeyList:
    def __init__(self, dump_info_holder, hive, struct_va):
        self.struct_va = struct_va
        self.count = struct.unpack('H', dump_info_holder.extract_buffer(
            2, struct_va + 2, dump_info_holder.kernel_directory_table_base
        ))[0]
        list_content = dump_info_holder.extract_buffer(
            4 * self.count, struct_va + 4,
            dump_info_holder.kernel_directory_table_base
        )
        self.list = []
        for i in range(self.count):
            self.list.append(struct.unpack('I', list_content[i * 4:
                                                             i * 4 + 4])[0])


class ReferencedKeyList:
    def __init__(self, dump_info_holder, hive, struct_va):
        self.struct_va = struct_va
        self.ref_count = struct.unpack('H', dump_info_holder.extract_buffer(
            2, struct_va + 2, dump_info_holder.kernel_directory_table_base
        ))[0]
        list_content = dump_info_holder.extract_buffer(
            4 * self.ref_count, struct_va + 4,
            dump_info_holder.kernel_directory_table_base
        )
        self.list = []
        for i in range(self.ref_count):
            cell_index = struct.unpack('I', list_content[i * 4:i * 4 + 4])[0]
            sublist = dump_info_holder.registry_cell(hive, cell_index)
            self.list += sublist.list


class User:
    def __init__(self, cell):
        self.name = cell.name
        for cell_index in cell.values:
            value_cell = cell.dump_info_holder.registry_cell(
                cell.hive, cell_index
            )
            if value_cell.name == '':
                self.rid = value_cell.type
                break
        v_cell = cell.dump_info_holder.registry_cell_by_path(
            cell.hive, r'SAM\Domains\Account\Users\%08X\V' % self.rid
        )
        self.v_data = cell.dump_info_holder.extract_buffer(
            v_cell.data_length, v_cell.data_va,
            cell.dump_info_holder.kernel_directory_table_base
        )
        lm_offset = struct.unpack('I', self.v_data[0x9c:0xa0])[0] + 0xcc + 4
        self.lm_va = v_cell.data_va + lm_offset
        lm_len = struct.unpack('I', self.v_data[0xa0:0xa4])[0] - 4
        self.lm = ''
        if not lm_len:
            self.encrypted_lm = ''
        else:
            self.encrypted_lm = self.v_data[lm_offset:lm_offset + 0x10]
        nt_offset = struct.unpack('I', self.v_data[0xa8:0xac])[0] + 0xcc + 4
        self.nt_va = v_cell.data_va + nt_offset
        nt_len = struct.unpack('I', self.v_data[0xac:0xb0])[0] - 4
        self.nt = ''
        if not nt_len:
            self.encrypted_nt = ''
        else:
            self.encrypted_nt = self.v_data[nt_offset:nt_offset + 0x10]

    def __unicode__(self):
        return u'%15s %08X' % (self.name, self.rid)
        
    def print_verbose_info(self):
        print(self.name)
        print('RID:                     %08X' % self.rid)
        if self.encrypted_lm:
            print('Encrypted LM hash:       %s' %
                  self.encrypted_lm.encode('hex'))
            print('Encrypted LM hash va:    %s' %
                  hex(self.lm_va).replace('L', ''))
        if self.lm:
            print('LM hash:                 %s' % self.lm.encode('hex'))
        if self.encrypted_nt:
            print('Encrypted NT hash:       %s' %
                  self.encrypted_nt.encode('hex'))
            print('Encrypted NT hash va:    %s' %
                  hex(self.nt_va).replace('L', ''))
        if self.nt:
            print('NT hash:                 %s' % self.nt.encode('hex'))
            
    def decrypt_hashes(self, crypto_transformer):
        if self.encrypted_lm:
            self.lm = crypto_transformer.decrypt_hash(self.rid,
                                                      self.encrypted_lm,
                                                      crypto_transformer.ALM)
        if self.encrypted_nt:
            self.nt = crypto_transformer.decrypt_hash(self.rid,
                                                      self.encrypted_nt,
                                                      crypto_transformer.ANT)


class CryptoTransformer:
    DESCRAMBLING = [
        0x8, 0x5, 0x4, 0x2,
        0xb, 0x9, 0xd, 0x3,
        0x0, 0x6, 0x1, 0xc,
        0xe, 0xa, 0xf, 0x7
    ]
    AQWERTY = '!@#$%^&*()qwertyUIOPAzxcvbnmQQQQQQQQQQQQ)(*@&%\0'
    ANUM = '0123456789012345678901234567890123456789\0'
    ANT = 'NTPASSWORD\0'
    ALM = 'LMPASSWORD\0'
    LMKEY = 'KGS!@#$%'

    def __init__(self, scrambled_key, f_data):
        self.boot_key = ''
        for i in range(len(scrambled_key)):
            self.boot_key = ''.join((self.boot_key,
                                     scrambled_key[self.DESCRAMBLING[i]]))
        md5 = MD5.new()
        md5.update(f_data[0x70:0x80] + self.AQWERTY +
                   self.boot_key + self.ANUM)
        rc4_key = md5.digest()
        rc4 = ARC4.new(rc4_key)
        self.hbootkey = rc4.encrypt(f_data[0x80:0xa0])
        
    def decrypt_hash(self, rid, hash, const):
        (des_k1, des_k2) = self.sid_to_key(rid)
        d1 = DES.new(des_k1, DES.MODE_ECB)
        d2 = DES.new(des_k2, DES.MODE_ECB)
        md5 = MD5.new()
        md5.update(self.hbootkey[:0x10] + struct.pack('<I', rid) + const)
        rc4 = ARC4.new(md5.digest())
        obfkey = rc4.encrypt(hash)
        return d1.decrypt(obfkey[:8]) + d2.decrypt(obfkey[8:])

    def sid_to_key(self, sid):
        s1 = ''
        s1 += chr(sid & 0xff)
        s1 += chr((sid >> 8) & 0xff)
        s1 += chr((sid >> 16) & 0xff)
        s1 += chr((sid >> 24) & 0xff)
        s1 += s1[0]
        s1 += s1[1]
        s1 += s1[2]
        s2 = s1[3] + s1[0] + s1[1] + s1[2]
        s2 += s2[0] + s2[1] + s2[2]
        return self.str_to_key(s1), self.str_to_key(s2)
        
    def str_to_key(self, s):
        key = []
        key.append(ord(s[0]) >> 1)
        key.append(((ord(s[0]) & 0x01) << 6) | (ord(s[1]) >> 2))
        key.append(((ord(s[1]) & 0x03) << 5) | (ord(s[2]) >> 3))
        key.append(((ord(s[2]) & 0x07) << 4) | (ord(s[3]) >> 4))
        key.append(((ord(s[3]) & 0x0f) << 3) | (ord(s[4]) >> 5))
        key.append(((ord(s[4]) & 0x1f) << 2) | (ord(s[5]) >> 6))
        key.append(((ord(s[5]) & 0x3f) << 1) | (ord(s[6]) >> 7))
        key.append(ord(s[6]) & 0x7f)
        for i in range(8):
            key[i] = (key[i] << 1)
            key[i] = self.odd_parity(key[i])
        return ''.join([chr(k) for k in key])

    def odd_parity(self, number):
        number = number & 0xfe
        ones = sum([number & (1 << i) for i in range(8)])
        return number + 1 - ones % 2

    def encrypt_password(self, user, password):
        if user.lm and len(password) < 15:
            lm = self.lm_hash(password)
            print('LM hash:                 %s' % lm.encode('hex'))
            enc_lm = self.encrypt_hash(user.rid, lm, self.ALM)
            print('Encrypted LM hash:       %s' % enc_lm.encode('hex'))
        if user.nt:
            nt = self.nt_hash(password)
            print('NT hash:                 %s' % nt.encode('hex'))
            enc_nt = self.encrypt_hash(user.rid, nt, self.ANT)
            print('Encrypted NT hash:       %s' % enc_nt.encode('hex'))

    def lm_hash(self, password):
        password = password.upper()
        password = ''.join((password, b'\x00' * 14 - len(password)))
        d1 = DES.new(self.str_to_key(password[:7]), DES.MODE_ECB)
        d2 = DES.new(self.str_to_key(password[7:]), DES.MODE_ECB)
        return d1.encrypt(self.LMKEY) + d2.encrypt(self.LMKEY)

    def nt_hash(self, password):
        password = password.encode('utf-16-le')
        md4 = MD4.new()
        md4.update(password)
        return md4.digest()

    def encrypt_hash(self, rid, hash, const):
        (des_k1, des_k2) = self.sid_to_key(rid)
        d1 = DES.new(des_k1, DES.MODE_ECB)
        d2 = DES.new(des_k2, DES.MODE_ECB)
        enc_hash = d1.encrypt(hash[:8]) + d2.encrypt(hash[8:])
        md5 = MD5.new()
        md5.update(self.hbootkey[:0x10] + struct.pack('<I', rid) + const)
        rc4 = ARC4.new(md5.digest())
        obfkey = rc4.encrypt(enc_hash)
        return obfkey


class Module:
    def __init__(self, dump_info_holder, content, offset):
        self.offset = offset
        list_entry = dump_info_holder.types_info_holder.find_struct(
            '_LIST_ENTRY'
        )
        if list_entry.size == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        unicode_string = dump_info_holder.types_info_holder.find_struct(
            '_UNICODE_STRING'
        )
        le = content[:list_entry.size]
        (self.flink, self.blink) = struct.unpack(link_fmt * 2, le)
        self.base = struct.unpack(link_fmt, content[3 * list_entry.size:
                                                    3 * list_entry.size +
                                                    list_entry.size / 2])[0]
        names_off = 4 * list_entry.size + list_entry.size / 2
        full_name_us = content[names_off:names_off + unicode_string.size]
        names_off += unicode_string.size
        name_us = content[names_off:names_off + unicode_string.size]
        full_name_len = unicode_string.extract_number('Length', full_name_us)
        full_name_va = unicode_string.extract_number('Buffer', full_name_us)
        self.full_name = dump_info_holder.extract_buffer(
            full_name_len, full_name_va,
            dump_info_holder.kernel_directory_table_base
        ).decode('utf-16-le')
        name_len = unicode_string.extract_number('Length', name_us)
        name_va = unicode_string.extract_number('Buffer', name_us)
        self.name = dump_info_holder.extract_buffer(
            name_len, name_va, dump_info_holder.kernel_directory_table_base
        ).decode('utf-16-le')

    def __unicode__(self):
        return '% 20s  % 10s  % 10s' % (self.name,
                                        hex(self.base).replace('L', ''),
                                        hex(self.offset).replace('L', ''))

    def print_verbose_info(self):
        print(u'Name:             %s' % self.name)
        print(u'Full name:        %s' % self.full_name)
        print('Base:             %s' % hex(self.base).replace('L', ''))
        print('Offset:           %s' % hex(self.offset).replace('L', ''))


class DumpInfoHolder:
    dump = ''
    pagefile = ''
    memory_model = 'x32'
    pae_enabled = 0
    kern_base = 0
    ps_loaded_module_list = 0
    kdbg_page = b''
    kernel_directory_table_base = 0
    debug_filename = ''
    local = False
    REGISTRY_SIGNATURES = {
        'nk': KeyNode,
        'lf': KeyList,
        'lh': KeyList,   #more advanced hashing, same structure
        'ri': ReferencedKeyList,
        'li': SimpleKeyList,
        'vk': KeyValue,
        'lk': KeyLink
    }

    def __init__(self, dump_filename, pagefile_filename, local):
        self.COMMANDS = {
            'help':     DumpInfoHolder.view_help,
            'phys':     DumpInfoHolder.phys,
            'structs':  DumpInfoHolder.show_structs,
            'struct':   DumpInfoHolder.struct,
            'ps':       DumpInfoHolder.ps,
            'dump':     DumpInfoHolder.dump_process,
            'proc':     DumpInfoHolder.proc_info,
            'threads':  DumpInfoHolder.print_threads,
            'regs':     DumpInfoHolder.print_regs,
            'hex':      DumpInfoHolder.hex_dump,
            'hives':    DumpInfoHolder.list_hives,
            'registry': DumpInfoHolder.registry,
            'users':    DumpInfoHolder.list_users,
            'user':     DumpInfoHolder.user_info,
            'pwdump':   DumpInfoHolder.pwdump,
            'pass':     DumpInfoHolder.encrypt_password,
            'modules':  DumpInfoHolder.list_modules,
            'module':   DumpInfoHolder.module_info,
        }
        self.local = local
        try:
            self.dump = open(dump_filename, 'rb')
            self.pagefile = open(pagefile_filename, 'rb')
        except IOError as e:
            print('Can\'t read file: %s' % e)
            exit(1)
        page = self.dump.read(BUF_SIZE)
        kdbg_found = False
        while page:
            kdbg_idx = page.find(b'KDBG')
            if kdbg_idx > 0:
                self.kdbg_page = page
                if self.kdbg_page[kdbg_idx - 4:kdbg_idx] == b'\x00\x00\x00\x00':
                    self.memory_model = 'x32'
                else:
                    self.memory_model = 'x64'
                self.kern_base = struct.unpack(
                    'Q', self.kdbg_page[kdbg_idx + 0x8:kdbg_idx + 0x10]
                )[0]
                self.ps_loaded_module_list = struct.unpack(
                    'Q', self.kdbg_page[kdbg_idx + 0x38:kdbg_idx + 0x40]
                )[0]
                self.ps_active_process_head = struct.unpack(
                    'Q', self.kdbg_page[kdbg_idx + 0x40:kdbg_idx + 0x48]
                )[0]
                self.pae_enabled = struct.unpack(
                    'H', self.kdbg_page[kdbg_idx + 0x26:kdbg_idx + 0x28]
                )[0]
                if self.memory_model == 'x32':
                    self.kern_base &= 0x00000000ffffffff
                    self.ps_loaded_module_list &= 0x00000000ffffffff
                    self.get_version_re = re.compile(b'.{4}'.join((
                        re.escape(struct.pack('I', self.kern_base)),
                        re.escape(struct.pack('I', self.ps_loaded_module_list))
                    )))
                else:
                    self.get_version_re = re.compile(b''.join((
                        re.escape(struct.pack('Q', self.kern_base)),
                        re.escape(struct.pack('Q', self.ps_loaded_module_list))
                    )))
                if self.get_version_re.search(self.kdbg_page):
                    print('KDBG found')
                    kdbg_found = True
                    break
            page = self.dump.read(BUF_SIZE)
        if not kdbg_found:
            self.dump.close()
            self.pagefile.close()
            exit(1)

    def hex_dump(self, handle, offset, count):
        if handle not in ('mem', 'page'):
            print('Invalid file!')
            return
        try:
            offset = int(offset, 16)
        except ValueError:
            print('Invalid offset!')
            return
        try:
            count = int(count, 16)
        except ValueError:
            print('Invalid count!')
            return
        if handle == 'mem':
            handle = self.dump
        else:
            handle = self.pagefile
        handle.seek(offset)
        buffer = handle.read(count)
        self.print_hex_dump(buffer)

    def print_hex_dump(self, buffer):
        sub_re = re.compile(r'[^\x20-\x7f]')
        line = buffer[0:0x10]
        lines = 0
        while line:
            hex_1 = ' '.join(['%02X' % ord(byte) for byte in line[0:8]])
            hex_2 = ' '.join(['%02X' % ord(byte) for byte in line[8:0x10]])
            str_1 = sub_re.sub('.', line[0:8])
            str_2 = sub_re.sub('.', line[8:0x10])
            print('%- 24s  %- 24s    %- 8s   %-8s' % (
                hex_1, hex_2, str_1, str_2
            ))
            lines += 1
            line = buffer[lines * 0x10:(lines + 1) * 0x10]
            
    def show_structs(self):
        self.types_info_holder.show_structs()
            
    def print_threads(self, proc_id):
        try:
            proc_id = int(proc_id)
            process = self.processes[proc_id]
        except (ValueError, IndexError):
            print('Invalid proc_id!')
            return
        print('     ETHREAD        Context ESP           Create time           Exit time')
        for thread in process.threads:
            print(unicode(thread))
            
    def print_regs(self, proc_id):
        try:
            proc_id = int(proc_id)
            process = self.processes[proc_id]
        except (ValueError, IndexError):
            print('Invalid proc_id!')
            return
        for thread in process.threads:
            print('Thread at %s' % 
                  hex(thread.ethread_offset).replace('L', ''))
            thread.print_regs()
            
    def dump_process(self, proc_id):
        try:
            proc_id = int(proc_id)
            process = self.processes[proc_id]
            if process.time_string(process.exit_time) != '0':
                print('Process is terminated, can not dump')
                return
            dtb = process.directory_table_base
        except (ValueError, IndexError):
            print('Invalid proc_id!')
            return
        offset = 0
        if self.memory_model == 'x32':
            proc_file = open('%d.dmp' % proc_id, 'wb')
            while offset < (1 << 31):
                page = self.get_page(offset, dtb)
                proc_file.write(page)
                offset += BUF_SIZE
            proc_file.close()
        else:
            print('Not implemented yet')
            
    def get_page(self, offset, dtb):
        try:
            pa = self.va_to_physical(offset, dtb)
            self.dump.seek(pa)
            return self.dump.read(BUF_SIZE)
        except TypeError as ex:
            if str(ex) == 'Demand zero!':
                return b'\x00' * BUF_SIZE
            elif str(ex).startswith('0x'):
                off = int(str(ex)[2:], 16)
                self.pagefile.seek(off)
                return self.pagefile.read(BUF_SIZE)
            print('%s at %s' % (str(ex), hex(offset).replace('L', '')))
            return b'\x00' * BUF_SIZE
            
    def ps(self):
        print(' ID   Or  PID  PPID        Name         Page DTB        EPROCESS         Create time')
        for proc_id, process in enumerate(self.processes):
            print(u'% 5d %s' % (proc_id, unicode(process)))
            
    def struct(self, name):
        try:
            self.types_info_holder.print_struct_info(name)
        except KeyError as ex:
            print(ex)
            
    def phys(self, va, proc_id=None):
        try:
            va = int(va, 16)
        except ValueError:
            va = 0xffffffffffffffff + 1
        if (
            self.memory_model == 'x32' and va > 0xffffffff
        ) or va > 0xffffffffffffffff:
            print('Invalid va!')
            return
        if proc_id:
            try:
                proc_id = int(proc_id)
                process = self.processes[proc_id]
                if process.time_string(process.exit_time) != '0':
                    print('Process terminated, can not resolve')
                    return
                dtb = self.processes[proc_id].directory_table_base
            except (ValueError, IndexError):
                print('Invalid proc_id!')
                return
        else:
            dtb = self.kernel_directory_table_base
        try:
            print(hex(self.va_to_physical(va, dtb)).replace('L', ''))
        except TypeError as ex:
            if str(ex).startswith('0x'):
                print('Paged out, offset in pagefile:')
            print(ex)
            
    def extract_buffer(self, size, va, dtb):
        buffer = ''
        while(size):
            page_va = va - (va & 0xfff)
            page = self.get_page(page_va, dtb)
            to_read = min(size, BUF_SIZE - (va & 0xfff))
            buffer = ''.join((buffer, page[(va & 0xfff):
                                           (va & 0xfff) + to_read]))
            va += to_read
            size -= to_read
        return buffer
                
    def list_hives(self):
        print(' id      CMHIVE           Directory                   File name           Timestamp')
        for hive_id, hive in enumerate(self.hives):
            print(u'%2d %s' % (hive_id, unicode(hive)))
            
    def registry(self, hive_id, path=''):
        try:
            hive_id = int(hive_id)
            hive = self.hives[hive_id]
        except (ValueError, IndexError):
            print('Invalid hive_id!')
            return
        try:
            cell = self.registry_cell_by_path(hive, path)
        except KeyError as ex:
            print(ex)
            return
        cell.print_verbose_info()

    def list_users(self):
        print(' id     Name             RID')
        for user_id, user in enumerate(self.users):
            print(u'%2d  %s' % (user_id, unicode(user)))

    def user_info(self, user_id):
        try:
            user_id = int(user_id)
            user = self.users[user_id]
        except (ValueError, IndexError):
            print('Invalid user_id!')
            return
        user.print_verbose_info()

    def pwdump(self, filename='pwdump.txt'):
        if not self.crypto_transformer:
            print('Boot key not available!')
            return
        pwdump = open(filename, 'w')
        for user in self.users:
            pwdump.write('%s:%d:%s:%s:::\n' % (user.name.encode('utf-8'),
                                               user.rid,
                                               user.lm.encode('hex'),
                                               user.nt.encode('hex')))
        pwdump.close()

    def encrypt_password(self, user_id, password=''):
        try:
            user_id = int(user_id)
            user = self.users[user_id]
        except (ValueError, IndexError):
            print('Invalid user_id!')
            return
        if not self.crypto_transformer:
            print('Boot key not available!')
            return
        self.crypto_transformer.encrypt_password(user, password)

    def list_modules(self):
        print(' ID            Name        Base        Offset')
        for module_id, module in enumerate(self.modules):
            print(u'%3d  %s' % (module_id, unicode(module)))

    def module_info(self, module_id):
        try:
            module_id = int(module_id)
            module = self.modules[module_id]
        except (ValueError, IndexError):
            print('Invalid module_id!')
            return
        module.print_verbose_info()

    def registry_cell_by_path(self, hive, path):
        root = self.registry_cell(hive, hive.root_cell)
        cell = root
        path_parts = [part for part in path.split('\\') if part]
        for subkey_idx, subkey in enumerate(path_parts):
            try:
                cell = cell.binary_search(subkey)
            except KeyError as ex:
                if subkey_idx == len(path_parts) - 1:
                    cell = cell.get_value(subkey)
                else:
                    raise
        return cell

    def proc_info(self, proc_id):
        try:
            proc_id = int(proc_id)
            process = self.processes[proc_id]
            process.print_verbose_info()
            if process.time_string(process.exit_time) != '0':
                return
            peb_struct = self.types_info_holder.find_struct('_PEB')
            try:
                peb = self.extract_buffer(peb_struct.size, process.peb,
                                          process.directory_table_base)
            except TypeError as ex:
                    print('Unable to get info from PEB')
                    return
            image_va = peb_struct.extract_number('ImageBaseAddress', peb)
            print('Executable image VA:\t%s' % hex(image_va).replace('L', ''))
            params_va = peb_struct.extract_number('ProcessParameters', peb)
            print('Process parameters VA:\t%s' %
                  hex(params_va).replace('L', ''))
            params_struct = self.types_info_holder.find_struct(
                '_RTL_USER_PROCESS_PARAMETERS'
            )
            try:
                params = self.extract_buffer(params_struct.size, params_va,
                                             process.directory_table_base)
            except TypeError as ex:
                    print('Unable to get user process parameters')
                    return
            unicode_string = self.types_info_holder.find_struct(
                '_UNICODE_STRING'
            )
            (path_off, path_len) = params_struct.get_offset('ImagePathName')
            path_struct = params[path_off:path_off + path_len]
            path_strlen = unicode_string.extract_number('Length', path_struct)
            path_va = unicode_string.extract_number('Buffer', path_struct)
            path = self.extract_buffer(path_strlen, path_va,
                                       process.directory_table_base).decode(
                                           'utf-16-le'
                                       )
            print(u'Path:\t\t\t%s' % path)
            (cmd_off, cmd_len) = params_struct.get_offset('CommandLine')
            cmd_struct = params[cmd_off:cmd_off + cmd_len]
            cmd_strlen = unicode_string.extract_number('Length', cmd_struct)
            cmd_va = unicode_string.extract_number('Buffer', cmd_struct)
            cmd = self.extract_buffer(cmd_strlen, cmd_va,
                                      process.directory_table_base).decode(
                                          'utf-16-le'
                                      )
            print(u'Command line:\t\t%s' % cmd)
        except (ValueError, IndexError):
            print('Invalid proc_id!')
            
    def view_help(self):
        print('''
help                            view this help

phys va [proc_id]               convert va (should be in hex) to physical
                                address in context of process #proc_id (should
                                not be terminated) or kernel context (if
                                proc_id not specified)

structs                         show available kernel structures

struct name                     show declaration of kernel structure 'name'

ps                              show list of detected processes

dump proc_id                    dump physical memory of process #proc_id
                                (should not be terminated) into file
                                proc_id.dmp

proc proc_id                    print verbose information about
                                process #proc_id

threads proc_id                 list threads of process #proc_id

regs proc_id                    dump registers for each thread in
                                process #proc_id

hex {mem|page} offset count     print hex dump of count (should be in hex)
                                bytes from memory dump or page file starting
                                from offset (should be in hex)

hives                           list found registry hives

registry hive_id [path]         information about registry key or value
                                identified by path (or hive root if path
                                not specified) in hive #hive_id

users                           list found users

user user_id                    print info about user #user_id

pwdump [file_name]              dump password hashes for crackers
                                into file file_name or pwdump.txt (available
                                only if boot key is found)

pass user_id [password]         calculate encrypted and unencrypted hashes
                                of given password or empty string (available
                                only if boot key is found)

modules                         list loaded kernel modules

module module_id                print info about kernel module #module_id

exit                            exit program
''')
            
    def dump_everything(self):
        print('''
KernelBase: %s
PsLoadedModuleList: %s
PsActiveProcessHead: %s
Memory_model: %s
PaeEnabled: %d
              ''' % (
            hex(self.kern_base).replace('L', ''),
            hex(self.ps_loaded_module_list).replace('L', ''),
            hex(self.ps_active_process_head).replace('L', ''),
            self.memory_model, self.pae_enabled
        ))
        kern_base_idx = self.get_version_re.search(self.kdbg_page).start()
        get_version = GetVersion64(self.kdbg_page[kern_base_idx - 0x10:
                                                  kern_base_idx + 0x18])
        get_version.print_version_info()
        self.kernel_directory_table_base = \
            self.find_kernel_directory_table_base()
        print('Kernel directory table base: %s' %
              hex(self.kernel_directory_table_base).replace('L', ''))
        kernel_phys = self.va_to_physical(self.kern_base,
                                          self.kernel_directory_table_base)
        print('Kernel PE base physical address: %s' %
              hex(kernel_phys).replace('L', ''))
        self.print_kernel_info(kernel_phys)
        print(
            'Primary information collection finished. Type "help" for command list'
        )
        self.main_loop()
        self.dump.close()
        self.pagefile.close()
        
    def print_kernel_info(self, kernel_phys):
        self.print_pe_info(kernel_phys, 'Kernel',
                           self.kernel_directory_table_base, self.kern_base)
        debug_info_holder = DebugInfoHolder(self.debug_filename)
        if not debug_info_holder.types_stream:
            exit(1)
        self.types_info_holder = TypesInfoHolder(debug_info_holder.types_stream)
        self.types_info_holder.print_struct_info('_EPROCESS')
        print('_EPROCESS structure found, building process list...')
        self.build_process_list()
        print('Scanning for registry hives...')
        self.find_hives()
        print('Extracting info about users...')
        self.find_users()
        print('Traversing loaded kernel module list...')
        self.build_module_list()
        
    def print_pe_info(self, base_pa, name, dtb, base):
        self.dump.seek(base_pa)
        page = self.dump.read(BUF_SIZE)
        pe_offset = struct.unpack('I', page[0x3c:0x40])[0]
        if page[pe_offset:pe_offset + 2] != b'PE':
            print('%s PE not located' % name)
            return
        timestamp = struct.unpack(
            'I', page[pe_offset + 8:pe_offset + 0xc]
        )[0]
        print('%s linking timestamp: %s' %
              (name,
               datetime.datetime.fromtimestamp(timestamp).strftime(DATE_FMT)))
        magic_number = struct.unpack(
            'H', page[pe_offset + 0x18:pe_offset + 0x1a]
        )[0]
        print('%s PE is PE32%s' % (name,
                                   '' if magic_number == 0x10b else '+'))
        # 0x30 in PE32+, but size of image base is 8 bytes there
        windows_specific_offset = pe_offset + 0x34
        print(('%s image version: %%d.%%d' % name) % struct.unpack(
            'HH', page[windows_specific_offset + 0x10:
                       windows_specific_offset + 0x14]
        ))
        number_off = 0x40 if magic_number == 0x10b else 0x50
        number_of_data_directories = struct.unpack(
            'I', page[windows_specific_offset + number_off:
                      windows_specific_offset + number_off + 4]
        )[0]
        if number_of_data_directories < 6:
            print('Unable to locate debug data directory!')
            exit(1)
        if name == 'Kernel':
            (edata_va, edata_size) = struct.unpack(
                'II', page[windows_specific_offset + number_off + 4:
                           windows_specific_offset + number_off + 0xc]
            )
            edata_va += self.kern_base
            print('Kernel .edata section virtual address is %s' %
                  hex(edata_va).replace('L', ''))
            self.get_process_type(edata_va, edata_size)
        (debug_data_directory_va,
         debug_data_directory_size) = struct.unpack(
            'II', page[windows_specific_offset + number_off + 4 + 6 * 8:
                       windows_specific_offset + number_off + 4 + 7 * 8]
        )
        debug_data_directory_va += base
        print('%s debug data directory virtual address is %s' %
              (name, hex(debug_data_directory_va).replace('L', '')))
        debug_data_directory_pa = self.va_to_physical(
            debug_data_directory_va, dtb
        )
        print('%s debug data directory physical address is %s' %
              (name, hex(debug_data_directory_pa).replace('L', '')))
        self.dump.seek(debug_data_directory_pa)
        debug_data = self.dump.read(debug_data_directory_size)
        debug_idx = 0
        guid_found = False
        while debug_idx < debug_data_directory_size:
            if struct.unpack(
                'I', debug_data[debug_idx + 0xc:debug_idx + 0x10]
            )[0] == 2:
                (debug_data_size, debug_data_va) = struct.unpack(
                    'II', debug_data[debug_idx + 0x10:debug_idx + 0x18]
                )
                debug_data_va += base
                debug_data_pa = self.va_to_physical(
                    debug_data_va, dtb
                )
                self.dump.seek(debug_data_pa)
                debug_info = self.dump.read(debug_data_size)
                if debug_info[0:4] == 'RSDS':
                    guid_found = True
                    guid_parts = struct.unpack(
                        'IHHBBBBBBBB', debug_info[4:0x14]
                    )
                    guid = (
                        '%08X-%04X-%04X-%02X%02X-%02X%02X%02X%02X%02X%02X' %
                        guid_parts
                    )
                    print('%s PE guid is %s' % (name, guid))
                    age = struct.unpack(
                        'I', debug_info[0x14:0x18]
                    )[0]
                    print('%s PE revision is %d' % (name, age))
                    filename = str(debug_info[0x18:-1])
                    print('%s PE debug info filename is %s' % (name,
                                                               filename))
                    debug_filename = self.download_debug_info(guid, age,
                                                              filename)
                    if name == 'Kernel':
                        self.debug_filename = debug_filename
            debug_idx += 0x1c
        if not guid_found:
            print('Could not locate %s debugging GUID' % name)
            if name == 'Kernel':
                exit(1)

    def main_loop(self):
        while(1):
            command = raw_input('> ').strip()
            if command:
                command_args = command.split()
                command = command_args[0]
                if command == 'exit':
                    return
                args = command_args[1:]
                try:
                    self.COMMANDS[command](self, *args)
                except TypeError:
                    print('Invalid arguments!')
                except KeyError:
                    print('Invalid command!')
        
    def get_process_type(self, edata_va, edata_size):
        edata_rva = edata_va - self.kern_base
        page = self.get_page(edata_va, self.kernel_directory_table_base)
        section = page[edata_va & 0xfff:]
        read = len(section)
        edata_size -= read
        while edata_size > 0:
            edata_va += read
            page = self.get_page(edata_va, self.kernel_directory_table_base)
            page = page[:edata_size]
            read = len(page)
            edata_size -= read
            section = b''.join((section, page))
        edata_va -= len(section)
        (flags, timestamp, major_version, minor_version,
         name_rva, ordinal_base, addrs_number, names_number,
         address_table_rva, name_table_rva,
         ordinal_table_rva) = struct.unpack(
            'IIHHIIIIIII', section[:0x28]
        )
        offset = 0x28 + 4 * addrs_number
        processed = 0
        while processed < names_number:
            str_va = struct.unpack('I', section[offset:offset + 4])[0]
            str_va -= edata_rva
            str = section[str_va:section.find('\x00', str_va)]
            if str == 'PsProcessType':
                break
            processed += 1
            offset += 4
        if processed == names_number:
            print('PsProcessType not found')
            self.ps_process_type = None
            return
        ordinal_table_rva -= edata_rva
        ordinal = struct.unpack(
            'H', section[ordinal_table_rva + processed * 2:
                         ordinal_table_rva + processed * 2 + 2]
        )[0] - ordinal_base
        ps_process_type_va = struct.unpack(
            'I', section[0x28 + ordinal * 4: 0x2c + ordinal * 4]
        )[0] + self.kern_base
        print('PsProcessType virtual address is %s' %
              hex(ps_process_type_va).replace('L', ''))
        ps_process_type_pa = self.va_to_physical(
            ps_process_type_va, self.kernel_directory_table_base
        )
        print('PsProcessType physical address is %s' %
              hex(ps_process_type_pa).replace('L', ''))
        self.ps_process_type = ps_process_type_pa

    def find_users(self):
        self.users = []
        sam_hive = None
        for hive in self.hives:
            root_cell = self.registry_cell(hive, hive.root_cell)
            if (
                root_cell.subkey_count == 1 and
                self.registry_cell(hive, root_cell.subkeys[0]).name == 'SAM'
            ):
                sam_hive = hive
                break
        if not sam_hive:
            print('Can\'t locate SAM hive')
            return
        usernames_cell = self.registry_cell_by_path(
            sam_hive, r'SAM\Domains\Account\Users\Names'
        )
        print(' id     Name             RID')
        for cell_index in usernames_cell.subkeys:
            new_user = User(self.registry_cell(sam_hive, cell_index))
            print(u'%2d  %s' % (len(self.users), unicode(new_user)))
            self.users.append(new_user)
        self.extract_syskey()
        if not self.syskey:
            self.crypto_transformer = None
            return
        f_cell = self.registry_cell_by_path(sam_hive,
                                            r'SAM\Domains\Account\F')
        f_data = self.extract_buffer(f_cell.data_length, f_cell.data_va,
                                     self.kernel_directory_table_base)
        self.crypto_transformer = CryptoTransformer(self.syskey, f_data)
        for user in self.users:
            user.decrypt_hashes(self.crypto_transformer)
        
    def extract_syskey(self):
        self.syskey = ''
        sys_hive = None
        for hive in self.hives:
            if hive.name == 'SYSTEM':
                sys_hive = hive
                break
        if not sys_hive:
            print(
                'Can\'t locate SYSTEM hive: will be unable to extract hashes'
            )
            return
        control_set_cell = self.registry_cell_by_path(
            sys_hive, r'Select\Current'
        )
        control_set_id = struct.unpack('I', self.extract_buffer(
            4, control_set_cell.data_va, self.kernel_directory_table_base
        ))[0]
        nodes_for_key = ('JD', 'Skew1', 'GBG', 'Data')
        for node in nodes_for_key:
            cell = self.registry_cell_by_path(
                sys_hive, r'ControlSet%03d\Control\Lsa\%s' % (control_set_id,
                                                              node)
            )
            self.syskey += cell.class_name
        print('Syskey is %s' % self.syskey)
        self.syskey = self.syskey.decode('hex')

    def find_hives(self):
        print(' id      CMHIVE           Directory                   File name           Timestamp')
        self.hives = []
        sign_re = re.compile(re.escape('\xe0\xbe\xe0\xbe'))
        self.dump.seek(0)
        base = 0
        page = self.dump.read(BUF_SIZE)
        base = 0
        cmhive = self.types_info_holder.find_struct('_CMHIVE')
        hhive = self.types_info_holder.find_struct('_HHIVE')
        if self.memory_model == 'x32':
            kernel_border = 1 << 31
        else:
            kernel_border = 1 << 63
        while page:
            for occurency in sign_re.finditer(page):
                offset = occurency.start()
                if offset & 3 or offset + cmhive.size > len(page):
                    continue
                hive_cand = page[offset:offset + cmhive.size]
                node_va = hhive.extract_number('BaseBlock', hive_cand)
                if (
                    node_va < kernel_border or
                    self.extract_buffer(
                        4, node_va, self.kernel_directory_table_base
                    ) != 'regf'
                ):
                    continue
                new_hive = Hive(cmhive, hive_cand, base + offset)
                self.parse_hbase_block(new_hive)
                self.hives.append(new_hive)
                print(u'%2d %s' % (len(self.hives) - 1, unicode(new_hive)))
                break
            if self.hives:
                break
            base += len(page)
            self.dump.seek(base)
            page = self.dump.read(BUF_SIZE)
        if not self.hives:
            print('Could not locate any hives')
            return
        (hl_offset, hl_len) = cmhive.get_offset('HiveList')
        if hl_len == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        head_pa = self.hives[0].cmhive_offset + hl_offset
        flink_pa = self.va_to_physical(self.hives[0].flink,
                                       self.kernel_directory_table_base)
        while flink_pa != head_pa:
            hive_off = flink_pa - hl_offset
            self.dump.seek(hive_off)
            hive_cand = self.dump.read(cmhive.size)
            if hive_cand[:4] == b'\xe0\xbe\xe0\xbe':
                new_hive = Hive(cmhive, hive_cand, hive_off)
                self.parse_hbase_block(new_hive)
                self.hives.append(new_hive)
                print(u'%2d %s' % (len(self.hives) - 1, unicode(new_hive)))
                flink_pa = self.va_to_physical(
                    new_hive.flink, self.kernel_directory_table_base
                )
            else:
                (flink, blink) = (flink, blink) = struct.unpack(
                    link_fmt * 2, hive_cand[hl_offset:hl_offset + hl_len]
                )
                flink_pa = self.va_to_physical(
                    flink, self.kernel_directory_table_base
                )
                
    def parse_hbase_block(self, hive):
        hbase_block = self.types_info_holder.find_struct('_HBASE_BLOCK')
        block = self.extract_buffer(hbase_block.size, hive.hbase_va,
                                    self.kernel_directory_table_base)
        hive.set_time(hbase_block.extract_number('TimeStamp', block))
        (name_offset, name_len) = hbase_block.get_offset('FileName')
        name = block[name_offset:name_offset + name_len].decode('utf-16-le')
        hive.set_name(name[:name.find(b'\x00')])
        hive.set_root_cell(hbase_block.extract_number('RootCell', block))
        
    def registry_cell_va(self, hive, cell_index):
        if cell_index & (1 << 31):
            print('Cell is non-volatile!')
            return
        if self.memory_model == 'x32':
            fmt = 'I'
            length = 4
        else:
            fmt = 'Q'
            length = 8
        hmap_entry = self.types_info_holder.find_struct('_HMAP_ENTRY')
        map_offset = ((cell_index & 0x7fe00000) >> 21) * length
        table_va = struct.unpack(fmt, self.extract_buffer(
            length, hive.map_va + map_offset, self.kernel_directory_table_base
        ))[0]
        table_offset = ((cell_index & 0x1ff000) >> 12) * hmap_entry.size
        entry = self.extract_buffer(hmap_entry.size, table_va + table_offset,
                                    self.kernel_directory_table_base)
        block_va = hmap_entry.extract_number('BlockAddress', entry)
        block_offset = cell_index & 0xfff
        return block_va + block_offset
        
    def registry_cell(self, hive, cell_index):
        cell_va = self.registry_cell_va(hive, cell_index)
        signature = self.extract_buffer(2, cell_va + 4,
                                        self.kernel_directory_table_base)
        return self.REGISTRY_SIGNATURES[signature](self, hive, cell_va + 4)

    # fields of interest in _EPROCESS: VadRoot + used here
    def build_process_list(self):
        self.processes = []
        process_head_pa = self.va_to_physical(
            self.ps_active_process_head, self.kernel_directory_table_base
        )
        print('Kernel active process list head physical address is %s' %
              hex(process_head_pa).replace('L', ''))
        list_entry = self.types_info_holder.find_struct('_LIST_ENTRY')
        if list_entry.size == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        eprocess = self.types_info_holder.find_struct('_EPROCESS')
        (apl_offset, apl_len) = eprocess.get_offset('ActiveProcessLinks')
        self.dump.seek(process_head_pa)
        (flink, blink) = struct.unpack(
            link_fmt * 2, self.dump.read(list_entry.size)
        )
        eprocess_offsets = []
        print(' ID   Or  PID  PPID        Name         Page DTB        EPROCESS         Create time')
        while flink != self.ps_active_process_head:
            next_pa = self.va_to_physical(flink,
                                          self.kernel_directory_table_base)
            next_pa -= apl_offset
            self.dump.seek(next_pa)
            eprocess_content = self.dump.read(eprocess.size)
            new_process = Process('K', eprocess, eprocess_content, next_pa)
            self.build_thread_list(new_process)
            print(u'% 5d %s' % (len(self.processes), unicode(new_process)))
            self.processes.append(new_process)
            eprocess_offsets.append(next_pa)
            (flink, blink) = (new_process.flink, new_process.blink)
        print('Scanning memory for hidden processes...')
        kprocess = self.types_info_holder.find_struct('_KPROCESS')
        (tdh_offset, tdh_len) = kprocess.get_offset('ThreadListHead')
        sign_size = kprocess.size / 4
        sign_re = re.compile('.'.join((b'\x03', chr(sign_size))))
        if self.memory_model == 'x32':
            if self.pae_enabled:
                zeroed_part = (8 << 2) - 1
            else:
                zeroed_part = (4 << 10) - 1
        else:
            zeroed_part = (8 << 9) - 1
        self.dump.seek(0)
        base = 0
        page = self.dump.read(BUF_SIZE)
        while page:
            for occurency in sign_re.finditer(page):
                offset = occurency.start()
                if not (offset & 3 or offset + base in eprocess_offsets or
                        offset + eprocess.size > len(page)):
                    eprocess_content = page[offset:offset + eprocess.size]
                    dtb = kprocess.extract_number(
                        'DirectoryTableBase', eprocess_content
                    )
                    if dtb == 0 or dtb & zeroed_part:
                        continue
                    (tdh_flink, tdh_blink) = struct.unpack(
                        link_fmt * 2,
                        eprocess_content[tdh_offset:tdh_offset + tdh_len]
                    )
                    if (
                        tdh_flink < self.kern_base or
                        tdh_blink < self.kern_base
                    ):
                        continue
                    try:
                        new_process = Process('H', eprocess, eprocess_content,
                                              offset + base)
                        print(u'% 5d %s' %
                              (len(self.processes), unicode(new_process)))
                        self.processes.append(new_process)
                    except TypeError:
                        continue
                    except:
                        print(hex(offset + base).replace('L', ''))
                        raise
            base += len(page)
            page = self.dump.read(BUF_SIZE)
            
    def build_thread_list(self, process):
        list_entry = self.types_info_holder.find_struct('_LIST_ENTRY')
        if list_entry.size == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        eprocess = self.types_info_holder.find_struct('_EPROCESS')
        (tl_offset, tl_len) = eprocess.get_offset('ThreadListHead')
        head_pa = process.eprocess_offset + tl_offset
        self.dump.seek(head_pa)
        (flink, blink) = struct.unpack(
            link_fmt * 2, self.dump.read(list_entry.size)
        )
        flink_pa = self.va_to_physical(flink,
                                       self.kernel_directory_table_base)
        ethread = self.types_info_holder.find_struct('_ETHREAD')
        (tle_offset, tle_len) = ethread.get_offset('ThreadListEntry')
        threads = []
        if self.memory_model == 'x32':
            reg_names = REGISTERS
        else:
            reg_names = REGISTERS_64
        while flink_pa != head_pa:
            ethread_offset = flink_pa - tle_offset
            self.dump.seek(ethread_offset)
            ethread_content = self.dump.read(ethread.size)
            new_thread = Thread(process, ethread, ethread_content,
                                ethread_offset)
            if new_thread.time_string(new_thread.exit_time) == '0':
                trap_struct = self.types_info_holder.find_struct(
                    '_KTRAP_FRAME'
                )
                trap_frame = self.extract_buffer(
                    trap_struct.size, new_thread.trap_va,
                    process.directory_table_base
                )
                regs = {}
                for reg in reg_names:
                    regs[reg] = trap_struct.extract_number(reg, trap_frame)
                new_thread.attach_regs(regs, reg_names)
            flink_pa = self.va_to_physical(new_thread.flink,
                                           self.kernel_directory_table_base)
            threads.append(new_thread)
        process.attach_threads(threads)

    def build_module_list(self):
        self.modules = []
        module_head_pa = self.va_to_physical(
            self.ps_loaded_module_list, self.kernel_directory_table_base
        )
        print('Kernel loaded list head physical address is %s' %
              hex(module_head_pa).replace('L', ''))
        list_entry = self.types_info_holder.find_struct('_LIST_ENTRY')
        unicode_string = self.types_info_holder.find_struct('_UNICODE_STRING')
        if list_entry.size == 8:
            link_fmt = 'I'
        else:
            link_fmt = 'Q'
        # specific coding: could not find appropriate struct
        (base_offset, base_len) = (3 * list_entry.size, list_entry.size / 2)
        self.dump.seek(module_head_pa)
        (flink, blink) = struct.unpack(
            link_fmt * 2, self.dump.read(list_entry.size)
        )
        print(' ID            Name        Base        Offset')
        while flink != self.ps_loaded_module_list:
            next_pa = self.va_to_physical(flink,
                                          self.kernel_directory_table_base)
            self.dump.seek(next_pa)
            content = self.dump.read(4 * list_entry.size +
                                              list_entry.size / 2 +
                                              2 * unicode_string.size)
            new_module = Module(self, content, next_pa)
            print(u'%3d %s' % (len(self.modules), unicode(new_module)))
            self.modules.append(new_module)
            (flink, blink) = (new_module.flink, new_module.blink)

    def download_debug_info(self, guid, age, filename):
        url = 'http://msdl.microsoft.com/download/symbols/%s/%s%d/%s_' % (
            filename, guid.replace('-', ''), age, filename[:-1]
        )
        if not self.local:
            print('Fetching %s to %s.cab...' % (url, filename))
            req = urllib2.Request(
                url, None, {'User-Agent': 'Microsoft-Symbol-Server'}
            )
            cj = cookielib.CookieJar()
            opener = urllib2.build_opener(NoRedirectDownloader,
                                          urllib2.HTTPCookieProcessor(cj))
            response = opener.open(req)
            cabname = '.'.join((filename, 'cab'))
            cabfile = open(cabname, 'wb')
            buffer = response.read(BUF_SIZE)
            while buffer:
                cabfile.write(buffer)
                buffer = response.read(BUF_SIZE)
            response.close()
            cabfile.close()
            print('Extracting %s from cab...' % filename)
            subprocess.call(('cabextract', cabname))
        else:
            print(
                'Working in local mode. You should have file fetched from %s' %
                url
            )
            dir_name = '%s%d' % (guid.replace('-', ''), age)
            filename = os.path.join(
                os.path.dirname(os.path.realpath(__file__)), dir_name, filename
            )
            print('Trying to open %s' % filename)
        return filename

    def find_kernel_directory_table_base(self):
        self.dump.seek(BUF_SIZE)
        page = self.dump.read(BUF_SIZE)
        while(page):
            base = self.dump.tell() - BUF_SIZE
            if self.memory_model == 'x32':
                if self.pae_enabled:
                    str = b''.join((
                        br'(?:.{4}\x00{4}){3}.{2}',
                        re.escape(struct.pack('I', base)[2:]),
                        br'\x00{4}'
                    ))
                    cand_len = 0x20
                    entry_len = 8
                else:
                    str = b''.join((
                        br'.{3074}',
                        re.escape(struct.pack('I', base)[2:])
                    ))
                    cand_len = 0xc04
                    entry_len = 4
            else:
                str = b''.join((
                    br'.{3946}',
                    re.escape(struct.pack('Q', base)[2:])
                ))
                cand_len = 0xf70
                entry_len = 8
            dtb_re = re.compile(str)
            if (
                re.match(dtb_re, page[:cand_len]) and
                ord(page[cand_len - entry_len + 1]) & 0xf0 ==
                (base & 0xf000) >> 8
            ):
                return base
            page = self.dump.read(BUF_SIZE)
        
    def get_prototype_page(self, va, directory_table_base):
        if self.memory_model == 'x32':
            try:
                pa = self.va_to_physical(va, directory_table_base)
                self.dump.seek(pa)
                if self.pae_enabled:
                    (pte, next_word) = struct.unpack('II', self.dump.read(8))
                else:
                    pte = struct.unpack('I', self.dump.read(4))[0]
            except TypeError as ex:
                if str(ex) == 'Demand zero!':
                    return (b'\x00' * BUF_SIZE, 0, self.dump)
                elif str(ex).startswith('0x'):
                    off = int(str(ex)[2:], 16)
                    self.pagefile.seek(off)
                    if self.pae_enabled:
                        (pte, next_word) = struct.unpack(
                            'II', self.pagefile.read(8)
                        )
                    else:
                        pte = struct.unpack('I', self.pagefile.read(4))[0]
                else:
                    raise
            if pte & 1 or pte & (1 << 10) or (self.pae_enabled and
                                              (pte & (1 << 11))):
                self.dump.seek(pte & 0xfffff000)
                return (self.dump.read(BUF_SIZE), pte & 0xfffff000,
                        self.dump)
            if self.pae_enabled:
                off = (next_word << 12) & 0xfffff000
            else:
                off = pte & 0xfffff000
            self.pagefile.seek(off)
            return (self.pagefile.read(BUF_SIZE), off, self.pagefile)
        else:
            try:
                pa = self.va_to_physical(va, directory_table_base)
                self.dump.seek(pa)
                pte = struct.unpack('Q', self.dump.read(8))[0]
            except TypeError as ex:
                if str(ex) == 'Demand zero!':
                    return (b'\x00' * BUF_SIZE, 0, self.dump)
                elif str(ex).startswith('0x'):
                    off = int(str(ex)[2:], 16)
                    self.pagefile.seek(off)
                    pte = struct.unpack('Q', self.pagefile.read(8))[0]
                else:
                    raise
            if pte & 1 or pte & (1 << 10) or pte & (1 << 11):
                self.dump.seek(pte & 0x0000fffffffff000)
                return (self.dump.read(BUF_SIZE), pte & 0x0000fffffffff000,
                        self.dump)
            off = (pte >> 32) << 12
            print('Prototype paged %s' % hex(va))
            self.pagefile.seek(off)
            return (self.pagefile.read(BUF_SIZE), off, self.pagefile)

    def va_to_physical(self, va, directory_table_base):
        self.dump.seek(directory_table_base)
        directory_table = self.dump.read(BUF_SIZE)
        if self.memory_model == 'x32':
            if self.pae_enabled:
                pd_pointer_table_off = (va & (3 << 30)) >> 27
                directory_table = self.get_directory_table(
                    directory_table, pd_pointer_table_off, 
                    directory_table_base
                )
                pd_table_off = (va & (0x1ff << 21)) >> 18
            else:
                pd_table_off = (va & (0x3ff << 22)) >> 20
            pd_table_entry = struct.unpack(
                'I', directory_table[pd_table_off:pd_table_off + 4]
            )[0]
            if (
                pd_table_entry & 1 or (
                    (self.pae_enabled or not pd_table_entry & (1 << 10)) and
                    pd_table_entry & (1 << 11)
                )
            ):
                # large page
                if pd_table_entry & (1 << 7):
                    if self.pae_enabled:
                        return (pd_table_entry & 0xffe00000) + (va & 0x1fffff)
                    return (pd_table_entry & 0xffc00000) + (va & 0x3fffff)
                page_table_base = pd_table_entry & 0xfffff000
                self.dump.seek(page_table_base)
                page_table = self.dump.read(BUF_SIZE)
            else:
                if self.pae_enabled:
                    next_word = struct.unpack(
                        'I', directory_table[pd_table_off + 4:
                                             pd_table_off + 8]
                    )[0]
                    proto_va = next_word
                else:
                    proto_va = ((
                        (pd_table_entry & 0xfe) >> 1
                    ) + (
                        (pd_table_entry & 0xfffff800) >> 16
                    ) * 4) + 0xe1000000
                if pd_table_entry & (1 << 10):
                    (page_table, p_offset,
                     handle) = self.get_prototype_page(
                        proto_va, directory_table_base
                    )
                elif pd_table_entry & 0xfffffc00 == 0:
                    if (
                        self.pae_enabled and next_word == 0
                    ) or (
                        not self.pae_enabled
                    ):
                        raise TypeError('Demand zero!')
                elif pd_table_entry & (1 << 7):
                    if self.pae_enabled:
                        off = ((next_word << 12) &
                                0xffe00000) + (va & 0x1fffff)
                    else:
                        off = (pd_table_entry & 0xffc00000) + (va & 0x3fffff)
                    raise TypeError(hex(off).replace('L', ''))
                else:
                    if self.pae_enabled:
                        page_table_base = (next_word << 12) & 0xfffff000
                    else:
                        page_table_base = pd_table_entry & 0xfffff000
                    self.pagefile.seek(page_table_base)
                    page_table = self.pagefile.read(BUF_SIZE)
            if self.pae_enabled:
                pt_off = (va & (0x1ff << 12)) >> 9
            else:
                pt_off = (va & (0x3ff << 12)) >> 10
            pt_entry = struct.unpack(
                'I', page_table[pt_off:pt_off + 4]
            )[0]
            if (
                pt_entry & 1 or
                (self.pae_enabled and pt_entry & (1 << 11)) or
                (not self.pae_enabled and not pt_entry & (1 << 10) and
                 pt_entry & (1 << 11))
            ):
                return (pt_entry & 0xfffff000) + (va & 0xfff)
            else:
                if self.pae_enabled:
                    next_word = struct.unpack(
                        'I', page_table[pt_off + 4:pt_off + 8]
                    )[0]
                    proto_va = next_word
                    page_offset = (next_word << 12) & 0xfffff000
                else:
                    proto_va = ((
                        (pt_entry & 0xfe) >> 1
                    ) + (
                        (pt_entry & 0xfffff800) >> 16
                    ) * 4) + 0xe1000000
                    page_offset = pt_entry & 0xfffff000
                if pt_entry & (1 << 10):
                    (page, offset, handle) = self.get_prototype_page(
                        proto_va, directory_table_base
                    )
                    if handle == self.dump:
                        return offset + (va & 0xfff)
                    raise TypeError(hex(offset +
                                    (va & 0xfff)).replace('L', ''))
                if (
                    self.pae_enabled and next_word == 0
                ) or (
                    not self.pae_enabled and page_offset == 0
                ):
                    raise TypeError('Demand zero!')
                raise TypeError(hex(page_offset +
                                    (va & 0xfff)).replace('L', ''))
        else:
            pm_level_table_off = (va & (0x1ff << 39)) >> 36
            directory_table = self.get_directory_table(
                directory_table, pm_level_table_off, 
                directory_table_base
            )
            pd_pointer_table_off = (va & (0x1ff << 30)) >> 27
            directory_table = self.get_directory_table(
                directory_table, pd_pointer_table_off, 
                directory_table_base
            )
            pd_table_off = (va & (0x1ff << 21)) >> 18
            pd_table_entry = struct.unpack(
                'Q', directory_table[pd_table_off:pd_table_off + 8]
            )[0]
            if pd_table_entry & 1:
                # large page
                if pd_table_entry & (1 << 7):
                    return (pd_table_entry & 0x0000ffffffe00000) + (va &
                                                                    0x1fffff)
                page_table_base = pd_table_entry & 0x0000fffffffff000
                self.dump.seek(page_table_base)
                page_table = self.dump.read(BUF_SIZE)
            else:
                if pd_table_entry & (1 << 10):
                    proto_va = pd_table_entry >> 16
                    (page_table, p_offset,
                     handle) = self.get_prototype_page(
                        proto_va, directory_table_base
                    )
                elif pd_table_entry & 0xffffffff00000c00 == 0:
                    raise TypeError('Demand zero!')
                elif pd_table_entry & (1 << 7):
                    if pd_table_entry & (1 << 11):
                        return (pd_table_entry &
                                0x0000ffffffe00000) + (va & 0x1fffff)
                    off = ((pd_table_entry >> 32) << 21) + (va & 0x1fffff)
                    print('Large page paged %s' % hex(pd_table_off))
                    raise TypeError(hex(off).replace('L', ''))
                elif pd_table_entry & (1 << 11):
                    page_table_base = pd_table_entry & 0x0000fffffffff000
                    self.dump.seek(page_table_base)
                    page_table = self.dump.read(BUF_SIZE)
                else:
                    print('PD paged %s' % hex(pd_table_off))
                    page_table_base = (pd_table_entry >> 32) << 12
                    self.pagefile.seek(page_table_base)
                    page_table = self.pagefile.read(BUF_SIZE)
            pt_off = (va & (0x1ff << 12)) >> 9
            pt_entry = struct.unpack('Q', page_table[pt_off:pt_off + 8])[0]
            if pt_entry & 1:
                return (pt_entry & 0x0000fffffffff000) + (va & 0xfff)
            proto_va = pt_entry >> 16
            if pt_entry & (1 << 10):
                (page, offset, handle) = self.get_prototype_page(
                    proto_va, directory_table_base
                )
                if handle == self.dump:
                    return offset + (va & 0xfff)
                raise TypeError(hex(offset +
                                (va & 0xfff)).replace('L', ''))
            if pt_entry & (1 << 11):
                return (pt_entry & 0x0000fffffffff000) + (va & 0xfff)
            if pt_entry >> 32 == 0:
                raise TypeError('Demand zero!')
            print('Page paged %s' % hex(pt_off))
            raise TypeError(hex(((pt_entry >> 32) << 12) +
                                (va & 0xfff)).replace('L', ''))

    def get_directory_table(self, parent_table, offset, directory_table_base):
        if self.memory_model == 'x32':
            tpl = 'I'
            entry_len = 4
        else:
            tpl = 'Q'
            entry_len = 8
        pd_pointer_table_entry = struct.unpack(
            tpl, parent_table[offset:offset + entry_len]
        )[0]
        if pd_pointer_table_entry & 1:
            page_directory_table_base = (pd_pointer_table_entry &
                                         0x0000fffffffff000)
            self.dump.seek(page_directory_table_base)
            return self.dump.read(BUF_SIZE)
        if self.memory_model == 'x32':
            if self.pae_enabled:
                if pd_pointer_table_entry & (1 << 11):
                    page_directory_table_base = (pd_pointer_table_entry &
                                                 0xfffff000)
                    self.dump.seek(page_directory_table_base)
                    return self.dump.read(BUF_SIZE)
                next_word = struct.unpack(
                    tpl, parent_table[offset + 4:offset + 8]
                )[0]
                if pd_pointer_table_entry & 0xfffffc00 == 0:
                    if next_word == 0:
                        raise TypeError('Demand zero!')
                    page_directory_table_base = (next_word << 12) & 0xfffff000
                    self.pagefile.seek(page_directory_table_base)
                    return self.pagefile.read(BUF_SIZE)
                else:
                    (directory_table, p_offset,
                     handle) = self.get_prototype_page(
                        next_word, directory_table_base
                    )
                    return directory_table
            else:
                if pd_pointer_table_entry & (1 << 10):
                    proto_va = ((
                        (pd_pointer_table_entry & 0xfe) >> 1
                    ) + (
                        (pd_pointer_table_entry & 0xfffff800) >> 16
                    ) * 4) + 0xe1000000
                    (directory_table, p_offset,
                     handle) = self.get_prototype_page(
                        proto_va, directory_table_base
                    )
                    return directory_table
                if pd_pointer_table_entry & 0xfffffc1e == 0:
                    raise TypeError('Demand zero')
                page_directory_table_base = (pd_pointer_table_entry &
                                             0xfffff000)
                if pd_pointer_table_entry & (1 << 11):
                    self.dump.seek(page_directory_table_base)
                    return self.dump.read(BUF_SIZE)
                self.pagefile.seek(page_directory_table_base)
                return self.pagefile.read(BUF_SIZE)
        else:
            if pd_pointer_table_entry & (1 << 10):
                proto_va = pd_pointer_table_entry >> 16
                (directory_table, p_offset,
                 handle) = self.get_prototype_page(
                    proto_va, directory_table_base
                )
                return directory_table
            if pd_pointer_table_entry & 0xffffffff00000c00 == 0:
                raise TypeError('Demand zero')
            page_directory_table_base = (pd_pointer_table_entry &
                                         0x0000fffffffff000)
            if pd_pointer_table_entry & (1 << 11):
                self.dump.seek(page_directory_table_base)
                return self.dump.read(BUF_SIZE)
            self.pagefile.seek((pd_pointer_table_entry >> 32) << 12)
            print(hex(parent_table), hex(offset))
            return self.pagefile.read(BUF_SIZE)


def main():
    local = False
    if '--local' in sys.argv:
        sys.argv.remove('--local')
        local = True
    if len(sys.argv) < 3:
        usage()
    dump_holder = DumpInfoHolder(sys.argv[1], sys.argv[2], local)
    dump_holder.dump_everything()


def usage():
    print('''
Usage: vader.py memory_dump_file page_file [--local]
    --local     search for pdb files in current directory (./guid+age/)
''')
    exit(1)


if __name__ == '__main__':
    main()
