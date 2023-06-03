//! Read, Eval, Print, Loop

use crate::lexer::Lexer;
use std::io::{Result, Stdin, Stdout, Write};

const PROMPT: &str = ">> ";

pub fn repl(r: Stdin, mut w: Stdout) -> Result<()> {
    writeln!(w, "Hello! This is the Monkey programming language!")?;

    loop {
        // print the prompt
        write!(w, "{}", PROMPT)?;
        _ = w.flush();

        // read a line
        let mut line = String::new();
        let len = r.read_line(&mut line)?;
        debug_assert!(line.len() == len);

        // handle special commands
        if line.trim() == "\\exit" || line.trim() == "\\quit" {
            break;
        }

        let lexer = Lexer::new(&line);
        for token in lexer {
            writeln!(w, "{:?}", token)?;
        }
    }

    return Ok(());
}
