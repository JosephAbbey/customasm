# customasm
This is an assembler that takes custom, user-defined instruction sets
and uses them to assemble source files.  
It can be useful, for example, if you're trying to test the bytecode of a new virtual machine,
or if you're eager to write programs for that new microprocessor architecture 
you just implemented in an FPGA chip!

[![crates.io](https://img.shields.io/crates/v/customasm)](https://crates.io/crates/customasm)
[![Latest Release](https://img.shields.io/github/v/release/josephabbey/customasm)](https://github.com/josephabbey/customasm/releases)
[![Releases](https://img.shields.io/github/downloads/josephabbey/customasm/total)](https://github.com/josephabbey/customasm/releases)
[![Release workflow](https://github.com/JosephAbbey/customasm/actions/workflows/release.yml/badge.svg)](https://github.com/JosephAbbey/customasm/actions/workflows/release.yml)
[![Coverage Status](https://coveralls.io/repos/github/JosephAbbey/customasm/badge.svg?branch=main)](https://coveralls.io/github/JosephAbbey/customasm?branch=main)

[🖥️ Try it right now on your browser!](https://hlorenzi.github.io/customasm/)

[🕹️ Check out an example project](/examples/nes/) which targets the NES!

[⌨️ Install the VSCode syntax highlight extension!](https://marketplace.visualstudio.com/items?itemName=hlorenzi.customasm-vscode)

[❤️ Support me!](https://accounts.hlorenzi.com/supporters)

## Documentation

[📚 Check out the wiki](https://github.com/hlorenzi/customasm/wiki)
for a changelog, details on advanced features, and a how-to guide!

## Installation

You can install directly from crates.io by running `cargo install customasm`.
Then the `customasm` application should automatically become available in your
command-line environment.

You can also download pre-built executables from the
[Releases section](https://github.com/hlorenzi/customasm/releases).

You can compile from source yourself by first cloning the repository and
then simply running `cargo build`.
There's also a battery of tests available at `cargo test`.

## Upgrade to v0.11

[📖 Check out instructions for migration from older versions to v0.11!](https://github.com/hlorenzi/customasm/wiki/Migrating-to-v0.11)

## Example

Given the following file:

```asm
#ruledef
{
    load r1, {value} => 0x11 @ value`8
    load r2, {value} => 0x12 @ value`8
    load r3, {value} => 0x13 @ value`8
    add  r1, r2      => 0x21
    sub  r3, {value} => 0x33 @ value`8
    jnz  {address}   => 0x40 @ address`16
    ret              => 0x50
}

multiply3x4:
    load r1, 0
    load r2, 3
    load r3, 4
    
    .loop:
        add r1, r2
        sub r3, 1
        jnz .loop
    
    ret
```

...the assembler will use the `#ruledef` directive to convert the
instructions into binary code:

```asm
 outp | addr | data

  0:0 |    0 |          ; multiply3x4:
  0:0 |    0 | 11 00    ; load r1, 0
  2:0 |    2 | 12 03    ; load r2, 3
  4:0 |    4 | 13 04    ; load r3, 4
  6:0 |    6 |          ; .loop:
  6:0 |    6 | 21       ; add r1, r2
  7:0 |    7 | 33 01    ; sub r3, 1
  9:0 |    9 | 40 00 06 ; jnz .loop
  c:0 |    c | 50       ; ret
```

## Command-Line Usage

```
Usage: customasm [options] <asm-file-1> ... <asm-file-N>

Options:
    -f, --format FORMAT The format of the output file. Possible formats:
                        binary, annotated, annotatedbin, binstr, binline,
                        hexstr, hexline, bindump, hexdump, mif, intelhex,
                        deccomma, hexcomma, decc, hexc, logisim8, logisim16,
                        addrspan
    -o, --output [FILE] The name of the output file.
        --symbol-format SYMBOL-FORMAT
                        The format of the symbol file. Possible formats:
                        default, mesen-mlb
    -s, --symbol [FILE] The name of the output symbol file.
    -t, --iter [NUM]    The max number of passes the assembler will attempt
                        (default: 10).
    -p, --print         Print output to stdout instead of writing to a file.
    -q, --quiet         Suppress progress reports.
    -v, --version       Display version information.
    -h, --help          Display this information.
```
