#ruledef test
{
    halt => 0x55
}

start:
halt
loop:
halt
.inner:
halt

; command: main.asm -f symbols -o out.txt
; output: out.txt