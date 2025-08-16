#subruledef reg
{
    r{reg: u4} => {reg}
}

#ruledef
{
    load {r: reg}, {value: i8} => 0x1 @ r @ value
    add  {r: reg}, r2          => 0x2 @ r
    sub  {r: reg}, {value: i8} => 0x3 @ r @ value
    jnz  {address: u16}  => 0x40 @ address
    ret                  => 0x50
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