; :::
#d8 0 ; = 0x00
; :::
#d8 0x00 ; = 0x00
; :::
#d8 0xff ; = 0xff
; :::
#d8 0x5 ; = 0x05
; :::
#d8 0x5 ; = 0x05
#d8 0x6 ; = 0x06
#d8 0x7 ; = 0x07


; :::
#d24 0x0 ; = 0x000000
; :::
#d24 0x8 ; = 0x000008
; :::
#d24 0x123 ; = 0x000123
; :::
#d24 0x3, 0x4567 ; = 0x000003004567
; :::
#d24 0x3 ; = 0x000003
#d24 0x4567 ; = 0x004567


; :::
#d8 0x8 ; = 0x08
#d16 0x16 ; = 0x0016
#d24 0x24 ; = 0x000024
#d32 0x32 ; = 0x00000032


; :::
#d8 0x00, ; = 0x00
; :::
#d8 0x1, 0x2, 0x3 ; = 0x010203
; :::
#d8 0x1, 0x2, 0x3, ; = 0x010203
; :::
#d8 0x00, 0xff, 0x12, 0xee ; = 0x00ff12ee
; :::
#d8 0, 255, 18, 238 ; = 0x00ff12ee
; :::
#d8 2 + 3 ; = 0x05
; :::
#d8 2 + 3, 2 * 3, 3 + 4 ; = 0x050607


; :::
#d8 -1 ; = 0xff
; :::
#d8 -128 ; = 0x80


; :::
x = 0x55
#d16 x ; = 0x0055


; :::
#d8 ; error: expected expression
; :::
#d8 0x00 0xff ; error: expected line break
; :::
#d0 0x0 ; error: unknown directive
; :::
#d0x8 0x0 ; error: unknown directive
; :::
#d8 0x100 ; error: larger
; :::
#d8 0x00, 0xff, 0x100 ; error: larger
; :::
#d8 256 ; error: larger
; :::
#d8 0, 255, 256 ; error: larger
; :::
#d8 -129 ; error: larger
; :::
x = 0x5555
#d8 x ; error: larger
; :::
#d8 2 > 1 ; error: wrong type