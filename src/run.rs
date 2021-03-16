use crate::*;

use std::path::PathBuf;



pub fn run() {
    let mut args = std::env::args_os();
    let _exe = args.next();
    let wasm = PathBuf::from(args.next().expect("no wasm file specified"));
    let wasm = std::fs::read(&wasm).expect("unable to read .wasm file");
    let mut decoder = Decoder::new(&wasm[..]);
    decoder.module();
    for err in decoder.errors.borrow().iter().take(10) {
        eprintln!("error: {}", err);
    }
}
