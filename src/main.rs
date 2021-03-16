#![allow(dead_code)]

use wasm::*;
mod wasm {
    mod instructions;   pub use instructions::*;
    mod modules;        pub use modules::*;
    mod types;          pub use types::*;
    mod values;         pub use values::*;
}

mod decoder;    pub use decoder::*;
mod run;
mod util;       pub use util::*;



fn main() { run::run() }
