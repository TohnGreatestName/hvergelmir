generate-out: 
    cargo test brainfrick_test -- --nocapture

link: generate-out
    x86_64-linux-musl-gcc -static local/fileout.o -o local/a.out

readelf: generate-out
    x86_64-linux-musl-readelf -a local/fileout.o


disassemble: link
    objdump --x86-asm-syntax=intel -d local/a.out | less -p "<main>"

copy-to-vm: link
    cp local/a.out ~/Documents/SecondVMShare/