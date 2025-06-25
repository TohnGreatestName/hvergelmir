generate-out: 
    cargo test simple_emit_test

link: generate-out
    x86_64-linux-musl-gcc -static local/fileout.o -o local/a.out

readelf: generate-out
    x86_64-linux-musl-readelf -a local/fileout.o


disassemble: link
    objdump -d local/a.out | less -p "<main>"

copy-to-vm: link
    cp a.out ~/Documents/SecondVMShare/