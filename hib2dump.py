#!/usr/bin/python
#-*- coding: utf-8 -*-


import datetime
import struct
import sys


BUF_SIZE = 0x1000


class Extractor:
    def __init__(self, hibname, dumpname):
        self.dumpname = dumpname
        try:
            self.hiber = open(hibname, 'rb')
        except IOError as ex:
            print('Can\'t open %s: %s' % hibname, str(ex))
            self.hiber = None
            return
        try:
            self.dump = open(dumpname, 'wb')
        except IOError as ex:
            print('Can\'t open %s: %s' % dumpname, str(ex))
            self.dump = None
            self.hiber.close()
            return
        try:
            self.determine_memory_model()
        except TypeError as ex:
            print(str(ex))
            self.hiber.close()
            self.dump.close()
            self.hiber = None
            self.dump = None
            return

    def determine_memory_model(self):
        page = self.hiber.read(BUF_SIZE)
        if page[:4] not in ('HIBR', 'RSTR', 'WAKE'):
            print('Invalid hibernation signature')
            self.determine_heuristically()
            return
        if (
            struct.unpack('Q', page[0x18:0x20])[0] == 0x1000 and
            self.likely_timestamp(struct.unpack('Q', page[0x20:0x28])[0])
        ):
            self.memory_model = 'x64'
            first_page = struct.unpack('Q', page[0x60:0x68])[0]
        elif (
            struct.unpack('I', page[0x14:0x18])[0] == 0x1000 and
            self.likely_timestamp(struct.unpack('Q', page[0x18:0x20])[0])
        ):
            self.memory_model = 'x32' 
            first_page = struct.unpack('I', page[0x4c:0x50])[0]
        else:
            raise TypeError('Can\'t determine memory model')
        self.populate_pages(first_page)

    def determine_heuristically(self):
        first_page = 0
        print('Trying to determine memory model heuristically...')
        page = self.hiber.read(BUF_SIZE)
        while page[:8] != '\x81\x81xpress':
            prev_page = page
            page = self.hiber.read(BUF_SIZE)
            first_page += 1
            if not page:
                raise TypeError('Can\'t find first valid xpress block')
        if struct.unpack('I', prev_page[4:8])[0] == 0x1ff:
            self.memory_model = 'x32'
            second_page = struct.unpack('I', prev_page[:4])[0]
        elif struct.unpack('I', prev_page[8:0xc])[0] == 0xff:
            self.memory_model = 'x64'
            second_page = struct.unpack('Q', prev_page[:8])[0]
        else:
            raise TypeError('Can\'t find likely page ranges count!')
        print('Memory model seems to be %s, first page is at %s' % (
            self.memory_model, hex(first_page * BUF_SIZE).replace('L', '')
        ))
        if second_page:
            self.hiber.seek(second_page * BUF_SIZE)
            prev_page = self.hiber.read(BUF_SIZE)
            page = self.hiber.read(BUF_SIZE)
            if page[:8] != '\x81\x81xpress':
                raise TypeError('Second set of xpress blocks not found!')
            if (
                self.memory_model == 'x32' and
                struct.unpack('I', prev_page[4:8])[0] != 0x1ff
            ) or (
                self.memory_model == 'x64' and
                struct.unpack('I', prev_page[8:0xc])[0] != 0xff
            ):
                raise TypeError('Unlikely ranges count on second page!')
        self.populate_pages(first_page)

    def likely_timestamp(self, timestamp):
        try:
            date = datetime.datetime(
                1601, 1, 1, 0, 0, 0, 0
            ) + datetime.timedelta(
                microseconds=timestamp / 10
            ) + (datetime.datetime.now() - datetime.datetime.utcnow())
        except OverflowError:
            return False
        return (
            datetime.datetime(2008, 1, 1, 0, 0, 0, 0) <
            date <
            datetime.datetime.now() + datetime.timedelta(days=1)
        )

    def populate_pages(self, first_page):
        if self.memory_model == 'x32':
            addr_fmt = 'I'
            addr_len = 4
        else:
            addr_fmt = 'Q'
            addr_len = 8
        self.tables = [first_page]
        self.ranges = []
        self.max_page = 0
        self.pages_to_write = 0
        while 1:
            page_num = self.tables[-1]
            self.hiber.seek(page_num * BUF_SIZE)
            page = self.hiber.read(BUF_SIZE)
            (page_num, range_count) = struct.unpack(addr_fmt * 2,
                                                    page[:addr_len * 2])
            range_count &= 0xffff
            if (range_count + 1) * 2 * addr_len > BUF_SIZE:
                raise TypeError('Too many page ranges!')
            pos = addr_len * 2
            for i in range(range_count):
                self.ranges.append(struct.unpack(
                    addr_fmt * 2, page[pos:pos + addr_len * 2]
                ))
                if self.ranges[-1][1] <= self.ranges[-1][0]:
                    raise TypeError('Invalid range: tail >= head')
                if self.ranges[-1][1] > self.max_page:
                    self.max_page = self.ranges[-1][1]
                self.pages_to_write += self.ranges[-1][1] - self.ranges[-1][0]
                pos += addr_len * 2
            if not page_num:
                break
            self.tables.append(page_num)

    def page_numbers(self):
        for page_range in self.ranges:
            for page in range(page_range[0], page_range[1]):
                yield page

    def work(self):
        for page_num in range(self.max_page):
            self.dump.write('\x00' * BUF_SIZE)
        self.dump.close()
        self.dump = open(self.dumpname, 'r+b')
        page_nums = self.page_numbers()
        xpress_offset = (self.tables[0] + 1) * BUF_SIZE
        written_pages = 0
        percentage = 0
        sys.stdout.write('0% complete...\r')
        sys.stdout.flush()
        table_idx = 1
        while 1:
            self.hiber.seek(xpress_offset)
            xpress_header = self.hiber.read(0x20)
            if xpress_header[:8] != '\x81\x81xpress':
                xpress_offset += (BUF_SIZE - (xpress_offset &
                                              (BUF_SIZE - 1))) & (BUF_SIZE - 1)
                try:
                    if (xpress_offset >> 12) != self.tables[table_idx]:
                        print(hex(xpress_offset))
                    table_idx += 1
                    xpress_offset += BUF_SIZE
                    continue
                except IndexError:
                    break
            xpress_counts = struct.unpack('I', xpress_header[8:0xc])[0]
            page_count = (xpress_counts & 0xf) + 1
            xpress_len = (xpress_counts >> 10) + 1
            if (
                table_idx < len(self.tables) and
                xpress_offset + 0x20 + xpress_len >
                (self.tables[table_idx] << 12)
            ):
                xpress_offset += 8
                continue
            xpress_block = self.hiber.read(xpress_len)
            if len(xpress_block) < (page_count << 12):
                decompressed = self.decompress(xpress_block)
            else:
                decompressed = xpress_block
            xpress_offset += 0x20 + xpress_len
            xpress_offset += (8 - (xpress_offset & 7)) & 7
            for i in range(len(decompressed) >> 12):
                try:
                    page_num = page_nums.next()
                    self.dump.seek(page_num * BUF_SIZE)
                    self.dump.write(decompressed[i * BUF_SIZE:(i + 1) * BUF_SIZE])
                    written_pages += 1
                except StopIteration:
                    break
            if written_pages * 100 / self.pages_to_write > percentage:
                percentage = written_pages * 100 / self.pages_to_write
                sys.stdout.write('%d%% complete...\r' % percentage)
                sys.stdout.flush()
        self.dump.close()
        if written_pages < self.pages_to_write:
            print(
                'Warning! Could not locate %d pages, something may have gone wrong' %
                (self.pages_to_write - written_pages)
            )

    def decompress(self, data):
        output_dict = {}
        output_index = 0
        input_index = 0
        bitmask_bit = 0
        nibble_index = 0
        while input_index < len(data):
            if bitmask_bit == 0:
                try:
                    bitmask = struct.unpack(
                        'I', data[input_index:input_index + 4]
                    )[0]
                except struct.error:
                    return self.dict2buff(output_dict)
                input_index += 4
                bitmask_bit = 32
            bitmask_bit -= 1
            if not (bitmask & (1 << bitmask_bit)):
                try:
                    output_dict[output_index] = data[input_index]
                except IndexError:
                    return self.dict2buff(output_dict)
                input_index += 1
                output_index += 1
            else:
                try:
                    length = struct.unpack(
                        'H', data[input_index:input_index + 2]
                    )[0]
                except struct.error:
                    return self.dict2buff(output_dict)
                input_index += 2
                offset = length >> 3
                length = length & 7
                if length == 7:
                    if nibble_index == 0:
                        nibble_index = input_index
                        length = ord(data[input_index]) & 0xf
                        input_index += 1
                    else:
                        length = ord(data[nibble_index]) >> 4
                        nibble_index = 0
                    if length == 0xf:
                        length = ord(data[input_index])
                        input_index += 1
                        if length == 0xff:
                            try:
                                length = struct.unpack(
                                    'H', data[input_index:input_index + 2]
                                )[0]
                            except struct.error:
                                return self.dict2buff(output_dict)
                            input_index = input_index + 2
                            length -= 15 + 7
                        length += 15
                    length += 7
                length += 3
                while length != 0:
                    try:
                        output_dict[output_index] = output_dict[
                            output_index - offset - 1
                        ]
                    except KeyError:
                        return self.dict2buff(output_dict)
                    output_index += 1
                    length -= 1
        return self.dict2buff(output_dict)

    def dict2buff(self, output_dict):
        return ''.join([output_dict[key]
                        for key in sorted(output_dict.keys())])


def main():
    args = get_args()
    try:
        if args['action'] == 'compress':
            print('Not implemented yet!')
            exit(1)
        else:
            worker = Extractor(args['hib'], args['dump'])
            if not worker.hiber or not worker.dump:
                exit(1)
    except KeyError:
        usage()
        exit(1)
    worker.work()


def get_args():
    if len(sys.argv) != 4 or sys.argv[1] not in ('compress', 'extract'):
        return {}
    return {'action': sys.argv[1], 'hib': sys.argv[2], 'dump': sys.argv[3]}


def usage():
    print('''
Usage:
hib2dump.py {compress|extract} hibfile dumpfile
''')


if __name__ == '__main__':
    main()
