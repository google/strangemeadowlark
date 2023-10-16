
use anyhow::{anyhow, Result};
use bumpalo::Bump;
use strangemeadowlark::MODE_PLAIN;
use std::{env, fs::read_to_string};

// E.g. cargo run --example test_parse /google/src/head/depot/google3/third_party/mangle/BUILD
fn main() -> Result<()> {
    if env::args().len() != 2 {
        return Err(anyhow!("need exactly one arg"));
    }

    let path = env::args().into_iter().nth(1).unwrap();

    let src = read_to_string(&path)?;
    let bump = Bump::new();
    let res = strangemeadowlark::parse(&bump, &path, &src, MODE_PLAIN)?;
    for stmt in res.stmts {
        println!("{}", stmt.data);
    }
    Ok(())
}