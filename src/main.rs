#![allow(clippy::needless_return)]
#![allow(dead_code)]

mod lexer;
mod repl;

fn main() {
    println!("Hello! This is the Monkey programming language!");
    println!("Feel free to type in commands");
    repl::repl(std::io::stdin(), std::io::stdout()).unwrap();
}
