#[allow(dead_code)]
mod parse;
mod quote;
mod scan;
mod syntax;
mod token;
mod walk;

pub use parse::parse;
pub use parse::MODE_PLAIN;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}
