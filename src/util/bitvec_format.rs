use crate::*;

impl util::BitVec {
    pub fn format_binary(&self) -> Vec<u8> {
        let mut result = Vec::new();

        let mut index = 0;
        while index < self.len() {
            let mut byte: u8 = 0;
            for _ in 0..8 {
                byte <<= 1;
                byte |= if self.read(index) { 1 } else { 0 };
                index += 1;
            }

            result.push(byte);
        }

        result
    }

    pub fn parse_binary(bytes: Vec<u8>, wordsize: usize) -> Self {
        let mut result = Self::new();
        let mut index = 0;
        for byte in bytes.clone() {
            let mut n = util::BigInt::from(byte);
            n.size = Some(8);
            result.write_bigint(index, n);
            index += 8;
        }

        for _ in 0..(bytes.len() * 8 % wordsize) {
            result.bits.pop();
        }

        result
    }

    pub fn format_binstr(&self) -> String {
        self.format_str(1)
    }

    pub fn parse_binstr(string: String, wordsize: usize) -> Self {
        Self::parse_str(string, 1, wordsize)
    }

    pub fn format_binline(&self, wordsize: usize) -> String {
        self.format_str(1)
            .chars()
            .enumerate()
            .flat_map(|(i, c)| {
                if i != 0 && i % wordsize == 0 {
                    Some('\n')
                } else {
                    None
                }
                .into_iter()
                .chain(std::iter::once(c))
            })
            .collect::<String>()
    }

    pub fn parse_binline(string: String, wordsize: usize) -> Self {
        Self::parse_str(string.replace("\n", ""), 1, wordsize)
    }

    pub fn format_coe(&self, wordsize: usize) -> String {
        "memory_initialization_radix=2;\nmemory_initialization_vector=\n".to_owned()
            + &self
                .format_str(1)
                .chars()
                .enumerate()
                .flat_map(|(i, c)| {
                    if i != 0 && i % wordsize == 0 {
                        vec![',', '\n']
                    } else {
                        vec![]
                    }
                    .into_iter()
                    .chain(std::iter::once(c))
                })
                .collect::<String>()
            + ";"
    }

    pub fn format_hexstr(&self) -> String {
        self.format_str(4)
    }

    pub fn parse_hexstr(string: String, wordsize: usize) -> Self {
        Self::parse_str(string, 4, wordsize)
    }

    pub fn format_hexline(&self, wordsize: usize) -> String {
        self.bits
            .chunks(wordsize)
            .map(|bits| {
                (Self {
                    bits: bits.to_vec(),
                    spans: vec![],
                })
                .format_hexstr()
            })
            .reduce(|acc, e| acc + "\n" + &e)
            .unwrap_or("".to_string())
    }

    pub fn parse_hexline(string: String, wordsize: usize) -> Self {
        string
            .split("\n")
            .map(|s| Self::parse_hexstr(s.to_string(), wordsize))
            .fold(&mut Self::new(), |acc, e| {
                acc.write_bitvec(acc.len(), &e);
                acc
            })
            .clone()
    }

    pub fn format_str(&self, bits_per_digit: usize) -> String {
        let mut result = String::new();

        let mut index = 0;
        while index < self.len() {
            let mut digit: u8 = 0;
            for _ in 0..bits_per_digit {
                digit <<= 1;
                digit |= if self.read(index) { 1 } else { 0 };
                index += 1;
            }

            let c = if digit < 10 {
                ('0' as u8 + digit) as char
            } else {
                ('a' as u8 + digit - 10) as char
            };

            result.push(c);
        }

        result
    }

    pub fn parse_str(string: String, bits_per_digit: usize, wordsize: usize) -> Self {
        let mut result = Self::new();
        let mut index = 0;
        for c in string.as_bytes() {
            let byte = c - '0' as u8;

            let digit = if byte < 10 { byte } else { c - 'a' as u8 + 10 };

            let mut n = util::BigInt::from(digit);
            n.size = Some(bits_per_digit);
            result.write_bigint(index, n);
            index += bits_per_digit;
        }

        for _ in 0..(result.bits.len() * bits_per_digit % wordsize) {
            result.bits.pop();
        }

        result
    }

    pub fn format_bindump(&self) -> String {
        self.format_dump(1, 8, 8)
    }

    pub fn format_hexdump(&self) -> String {
        self.format_dump(4, 8, 16)
    }

    pub fn format_dump(
        &self,
        digit_bits: usize,
        byte_bits: usize,
        bytes_per_line: usize,
    ) -> String {
        let mut result = String::new();

        let line_start = 0 / (byte_bits * bytes_per_line);
        let line_end =
            (self.len() + (bytes_per_line - 1) * byte_bits) / (byte_bits * bytes_per_line);

        let line_end = if self.len() < byte_bits {
            line_start + 1
        } else {
            line_end
        };

        let addr_max_width = format!("{:x}", (line_end - 1) * bytes_per_line).len();

        for line_index in line_start..line_end {
            result.push_str(&format!(
                " {:01$x} | ",
                line_index * bytes_per_line,
                addr_max_width
            ));

            for byte_index in 0..bytes_per_line {
                for digit_index in 0..(byte_bits / digit_bits) {
                    let digit_first_bit = (line_index * bytes_per_line + byte_index) * byte_bits
                        + digit_index * digit_bits;

                    if digit_first_bit >= self.len() {
                        result.push('.');
                        continue;
                    }

                    let mut digit = 0;
                    for bit_index in 0..digit_bits {
                        digit <<= 1;
                        digit |= if self.read(digit_first_bit + bit_index) {
                            1
                        } else {
                            0
                        };
                    }

                    let c = if digit < 10 {
                        ('0' as u8 + digit) as char
                    } else {
                        ('a' as u8 + digit - 10) as char
                    };

                    result.push(c);
                }

                result.push(' ');

                if byte_index % 4 == 3 && byte_index < bytes_per_line - 1 {
                    result.push(' ');
                }
            }

            result.push_str("| ");

            if byte_bits == 8 {
                for byte_index in 0..bytes_per_line {
                    let byte_first_bit = (line_index * bytes_per_line + byte_index) * byte_bits;

                    if byte_first_bit >= self.len() {
                        result.push('.');
                        continue;
                    }

                    let mut byte = 0u8;
                    for bit_index in 0..byte_bits {
                        byte <<= 1;
                        byte |= if self.read(byte_first_bit + bit_index) {
                            1
                        } else {
                            0
                        };
                    }

                    let c = byte as char;

                    if c == ' ' || c == '\t' || c == '\r' || c == '\n' {
                        result.push(' ');
                    } else if c as u8 >= 0x80 || c < ' ' || c == '|' {
                        result.push('.');
                    } else {
                        result.push(c);
                    }
                }

                result.push_str(" |");
            }

            result.push('\n');
        }

        result
    }

    pub fn format_mif(&self, data_radix: usize, wordsize: usize) -> String {
        let mut result = String::new();

        let byte_num = self.len() / wordsize + if self.len() % wordsize != 0 { 1 } else { 0 };

        result.push_str(&format!("DEPTH = {};\n", byte_num));
        result.push_str(&format!("WIDTH = {};\n", wordsize));
        result.push_str("ADDRESS_RADIX = HEX;\n");
        result.push_str(&format!(
            "DATA_RADIX = {};\n",
            match data_radix {
                1 => "BIN",
                2 => "OCT",
                4 => "HEX",
                _ => "HEX",
            }
        ));
        result.push_str("\n");
        result.push_str("CONTENT\n");
        result.push_str("BEGIN\n");

        let addr_max_width = format!("{:x}", byte_num - 1).len();

        let word_length = (wordsize + data_radix - 1) / data_radix;
        let fmt_word: _ = match data_radix {
            1 => |word: usize| format!("{:b}", word),
            2 => |word: usize| format!("{:o}", word),
            4 => |word: usize| format!("{:X}", word),
            _ => |word: usize| format!("{:X}", word),
        };

        let mut index = 0;
        while index < self.len() {
            result.push_str(&format!(" {:1$X}: ", index / 8, addr_max_width));

            let mut word: usize = 0;
            for _ in 0..wordsize {
                word <<= 1;
                word |= if self.read(index) { 1 } else { 0 };
                index += 1;
            }

            result.push_str(&format!("{:0>1$};\n", fmt_word(word), word_length));
        }

        result.push_str("END;");
        result
    }

    pub fn format_intelhex(&self) -> String {
        let mut result = String::new();

        let mut bytes_left = self.len() / 8 + if self.len() % 8 != 0 { 1 } else { 0 };

        let mut index = 0;
        while index < self.len() {
            let bytes_in_row = if bytes_left > 32 { 32 } else { bytes_left };

            result.push(':');
            result.push_str(&format!("{:02X}", bytes_in_row));
            result.push_str(&format!("{:04X}", index / 8));
            result.push_str("00");

            let mut checksum = 0_u8;
            checksum = checksum.wrapping_add(bytes_in_row as u8);
            checksum = checksum.wrapping_add(((index / 8) >> 8) as u8);
            checksum = checksum.wrapping_add((index / 8) as u8);

            for _ in 0..bytes_in_row {
                let mut byte: u8 = 0;
                for _ in 0..8 {
                    byte <<= 1;
                    byte |= if self.read(index) { 1 } else { 0 };
                    index += 1;
                }

                result.push_str(&format!("{:02X}", byte));
                checksum = checksum.wrapping_add(byte);
            }

            bytes_left -= bytes_in_row;
            result.push_str(&format!("{:02X}", (!checksum).wrapping_add(1)));
            result.push('\n');
        }

        result.push_str(":00000001FF");
        result
    }

    pub fn format_comma(&self, radix: usize) -> String {
        let mut result = String::new();

        let mut index = 0;
        while index < self.len() {
            let mut byte: u8 = 0;
            for _ in 0..8 {
                byte <<= 1;
                byte |= if self.read(index) { 1 } else { 0 };
                index += 1;
            }

            match radix {
                10 => result.push_str(&format!("{}", byte)),
                16 => result.push_str(&format!("0x{:02x}", byte)),
                _ => panic!("invalid radix"),
            }

            if index < self.len() {
                result.push_str(", ");

                if (index / 8) % 16 == 0 {
                    result.push('\n');
                }
            }
        }

        result
    }

    pub fn format_c_array(&self, radix: usize) -> String {
        let mut result = String::new();

        result.push_str("const unsigned char data[] = {\n");

        let byte_num = self.len() / 8 + if self.len() % 8 != 0 { 1 } else { 0 };
        let addr_max_width = format!("{:x}", byte_num - 1).len();

        let mut index = 0;
        result.push_str(&format!("\t/* 0x{:01$x} */ ", 0, addr_max_width));

        while index < self.len() {
            let mut byte: u8 = 0;
            for _ in 0..8 {
                byte <<= 1;
                byte |= if self.read(index) { 1 } else { 0 };
                index += 1;
            }

            match radix {
                10 => result.push_str(&format!("{}", byte)),
                16 => result.push_str(&format!("0x{:02x}", byte)),
                _ => panic!("invalid radix"),
            }

            if index < self.len() {
                result.push_str(", ");

                if (index / 8) % 16 == 0 {
                    result.push_str(&format!("\n\t/* 0x{:01$x} */ ", index / 8, addr_max_width));
                }
            }
        }

        result.push_str("\n};");
        result
    }

    pub fn format_vhdl_b_array(&self, wordsize: usize) -> String {
        "(\n  \"".to_owned()
            + &self
                .format_str(1)
                .chars()
                .enumerate()
                .flat_map(|(i, c)| {
                    if i != 0 && i % wordsize == 0 {
                        vec!['"', ',', '\n', ' ', ' ', '"']
                    } else {
                        vec![]
                    }
                    .into_iter()
                    .chain(std::iter::once(c))
                })
                .collect::<String>()
            + "\"\n)"
    }

    pub fn format_vhdl_h_array(&self, wordsize: usize) -> String {
        "(\n  x\"".to_owned()
            + &self
                .format_str(4)
                .chars()
                .enumerate()
                .flat_map(|(i, c)| {
                    if i != 0 && i % (wordsize / 4) == 0 {
                        vec!['"', ',', '\n', ' ', ' ', 'x', '"']
                    } else {
                        vec![]
                    }
                    .into_iter()
                    .chain(std::iter::once(c))
                })
                .collect::<String>()
            + "\"\n)"
    }

    // From: https://github.com/milanvidakovic/customasm/blob/master/src/asm/binary_output.rs#L84
    pub fn format_logisim(&self, bits_per_chunk: usize) -> String {
        let mut result = String::new();
        result.push_str("v2.0 raw\n");

        let mut index = 0;
        while index < self.len() {
            let mut value: u16 = 0;
            for _ in 0..bits_per_chunk {
                value <<= 1;
                value |= if self.read(index) { 1 } else { 0 };
                index += 1;
            }

            result.push_str(&format!("{:01$x} ", value, bits_per_chunk / 4));
            if (index / 8) % 16 == 0 {
                result.push('\n');
            }
        }

        result
    }

    pub fn format_annotated_bin(
        &self,
        fileserver: &dyn util::FileServer,
        wordsize: usize,
    ) -> String {
        self.format_annotated(fileserver, 1, wordsize)
    }

    pub fn format_annotated_hex(
        &self,
        fileserver: &dyn util::FileServer,
        wordsize: usize,
    ) -> String {
        self.format_annotated(fileserver, 4, wordsize)
    }

    pub fn format_annotated(
        &self,
        fileserver: &dyn util::FileServer,
        digit_bits: usize,
        wordsize: usize,
    ) -> String {
        let mut result = String::new();

        let word_digits = (wordsize + digit_bits - 1) / digit_bits;

        let mut outp_width = 2;
        let outp_bit_width = (digit_bits as f32 - 1f32).log(16f32).ceil() as usize;
        let mut addr_width = 4;
        let mut content_width = (word_digits + 1) * 1 - 1;

        let mut sorted_spans = self.spans.clone();
        sorted_spans.sort_by(|a, b| a.offset.cmp(&b.offset));

        for span in &sorted_spans {
            if let Some(offset) = span.offset {
                outp_width = std::cmp::max(outp_width, format!("{:x}", offset / wordsize).len());

                addr_width = std::cmp::max(addr_width, format!("{:x}", span.addr).len());

                let data_digits =
                    span.size / digit_bits + if span.size % digit_bits == 0 { 0 } else { 1 };
                let this_content_width = data_digits + data_digits / word_digits;

                if this_content_width > 1 && this_content_width <= (word_digits + 1) * 5 {
                    content_width = std::cmp::max(content_width, this_content_width - 1);
                }
            }
        }

        result.push_str(&format!(
            " {:>1$} |",
            "outp",
            outp_width + outp_bit_width + 1
        ));
        result.push_str(&format!(" {:>1$} | data", "addr", addr_width));
        result.push_str("\n");
        result.push_str("\n");

        let mut prev_filename = "";
        let mut prev_file_chars = Vec::new();

        let digit_num = wordsize / digit_bits + if wordsize % digit_bits == 0 { 0 } else { 1 };
        for span in &sorted_spans {
            if let Some(offset) = span.offset {
                result.push_str(&format!(" {:1$x}", offset / word_digits, outp_width));
                result.push_str(&format!(":{:1$x} | ", offset % word_digits, outp_bit_width));
            } else {
                result.push_str(&format!(" {:>1$}", "--", outp_width));
                result.push_str(&format!(":{:>1$} | ", "-", outp_bit_width));
            }

            result.push_str(&format!("{:1$x} | ", span.addr, addr_width));

            let mut contents_str = String::new();

            let word_num = span.size / wordsize;
            for word_index in 0..word_num {
                if word_index > 0 {
                    contents_str.push_str(" ");
                }

                for digit_index in 0..digit_num {
                    let mut digit = 0;
                    for bit_index in 0..digit_bits {
                        let j = digit_index * digit_bits + bit_index;
                        let bit = if j < wordsize {
                            self.read(span.offset.unwrap() + word_index * wordsize + j)
                        } else {
                            false
                        };

                        digit <<= 1;
                        digit |= if bit { 1 } else { 0 };
                    }

                    let c = if digit < 10 {
                        ('0' as u8 + digit) as char
                    } else {
                        ('a' as u8 + digit - 10) as char
                    };

                    contents_str.push(c);
                }
            }

            if &*span.span.file != prev_filename {
                prev_filename = &*span.span.file;
                prev_file_chars = fileserver
                    .get_chars(diagn::RcReport::new(), &prev_filename, None)
                    .ok()
                    .unwrap();
            }

            let span_location = span.span.location.unwrap();
            let char_counter = util::CharCounter::new(&prev_file_chars);

            result.push_str(&format!("{:1$}", contents_str, content_width));
            result.push_str(&format!(
                " ; {}",
                char_counter
                    .get_excerpt(span_location.0, span_location.1)
                    .iter()
                    .collect::<String>()
            ));
            result.push_str("\n");
        }

        result
    }

    pub fn format_addrspan(&self, fileserver: &dyn util::FileServer) -> String {
        let mut result = String::new();

        let mut sorted_spans = self.spans.clone();
        sorted_spans.sort_by(|a, b| a.offset.cmp(&b.offset));

        result.push_str("; ");
        result.push_str("physical address : bit offset | ");
        result.push_str("logical address | ");
        result.push_str("file : line start : column start : line end : column end\n");

        for span in &sorted_spans {
            let chars = fileserver
                .get_chars(diagn::RcReport::new(), &span.span.file, None)
                .ok()
                .unwrap();
            let counter = util::CharCounter::new(&chars);

            if let Some(offset) = span.offset {
                result.push_str(&format!("{:x}:{:x} | ", offset / 8, offset % 8));
            } else {
                result.push_str(&format!("-:- | "));
            }

            result.push_str(&format!("{:x} | ", span.addr));

            if let Some((start, end)) = span.span.location {
                let (line_start, col_start) = counter.get_line_column_at_index(start);
                let (line_end, col_end) = counter.get_line_column_at_index(end);

                result.push_str(&format!(
                    "{}:{}:{}:{}:{}",
                    &span.span.file, line_start, col_start, line_end, col_end
                ));
            } else {
                result.push_str(&format!("{}:-:-:-:-", &span.span.file));
            };

            result.push_str("\n");
        }

        result
    }
}
