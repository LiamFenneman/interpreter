#![allow(clippy::needless_return)]
#![allow(dead_code)]

/// The token type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Identifiers + literals
    Ident(String),
    Int(String),

    // Operators
    Assign,
    Plus,

    // Delimiters
    Comma,
    Semicolon,
    LParen,
    RParen,
    LBrace,
    RBrace,

    // Keywords
    Function,
    Let,

    // Special
    Illegal,
}

impl Token {
    pub(crate) fn keyword(str: &str) -> Option<Token> {
        use Token::*;
        return match str {
            "fn" => Some(Function),
            "let" => Some(Let),
            _ => None,
        };
    }
}

/// A lexer instance.
///
/// The lexer is responsible for tokenizing the input source code.
/// The lexer is implemented as a state machine.
#[derive(Clone, Copy)]
pub struct Lexer<'a> {
    input: &'a str,
    pos: usize,
    ch: Option<char>,
}

impl std::fmt::Debug for Lexer<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        return write!(
            f,
            "Lexer({:?} at {:?} ch {:?})",
            self.input, self.pos, self.ch
        );
    }
}

impl<'a> Lexer<'a> {
    /// Create a new lexer instance.
    pub fn new(input: &'a str) -> Self {
        #[allow(clippy::iter_nth_zero)]
        return match input {
            s if s.is_empty() => Lexer {
                input,
                pos: 0,
                ch: None,
            },
            _ => Lexer {
                input,
                pos: 0,
                ch: input.chars().nth(0),
            },
        };
    }

    /// Advance the lexer and return the token.
    pub fn next_token(self) -> (Self, Option<Token>) {
        use Token::*;

        // skip whitespace
        return match self.ch {
            None => (self, None),
            Some(ch) => match ch {
                '=' => (self.advance(), Some(Assign)),
                '+' => (self.advance(), Some(Plus)),
                ',' => (self.advance(), Some(Comma)),
                ';' => (self.advance(), Some(Semicolon)),
                '(' => (self.advance(), Some(LParen)),
                ')' => (self.advance(), Some(RParen)),
                '{' => (self.advance(), Some(LBrace)),
                '}' => (self.advance(), Some(RBrace)),
                _ch => (self.advance(), Some(Illegal)),
            },
        };
    }

    /// Advance the lexer.
    pub(crate) fn advance(self) -> Self {
        let mut lexer = self;
        lexer.pos += 1;
        lexer.ch = lexer.input.chars().nth(lexer.pos);
        return lexer;
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn single_chars() {
        let input = "=+(){},;";

        let tests = vec![
            Token::Assign,
            Token::Plus,
            Token::LParen,
            Token::RParen,
            Token::LBrace,
            Token::RBrace,
            Token::Comma,
            Token::Semicolon,
        ];

        let mut lexer = Lexer::new(input);

        for (i, expected) in tests.iter().enumerate() {
            let (lex, tok) = lexer.next_token();
            assert_eq!(tok, Some(expected.clone()), "tests[{}]", i);
            lexer = lex;
        }

        let (_, tok) = lexer.next_token();
        assert_eq!(tok, None)
    }
}
