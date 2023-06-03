//! The Lexer module.
//!
//! The lexer reads the input source code and turns it into tokens.

/// The token type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Identifiers + Literals
    Ident(String),
    Int(String),
    Boolean(bool),

    // Operators
    Assign,
    Plus,
    Minus,
    Bang,
    Asterisk,
    Slash,
    LessThan,
    GreaterThan,
    Equal,
    NotEqual,

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
    If,
    Else,
    Return,

    // Special
    Illegal,
}

impl Token {
    pub(crate) fn lookup_ident(str: &str) -> Option<Token> {
        use Token::*;
        return match str {
            "fn" => Some(Function),
            "let" => Some(Let),
            "if" => Some(If),
            "else" => Some(Else),
            "return" => Some(Return),
            "true" => Some(Boolean(true)),
            "false" => Some(Boolean(false)),
            _ => Some(Ident(str.to_string())),
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

        let lexer = self.skip_whitespace();

        // skip whitespace
        return match lexer.ch {
            None => (lexer, None),
            Some(ch) => match ch {
                // Operators
                '+' => (lexer.advance(), Some(Plus)),
                '-' => (lexer.advance(), Some(Minus)),
                '*' => (lexer.advance(), Some(Asterisk)),
                '/' => (lexer.advance(), Some(Slash)),
                '<' => (lexer.advance(), Some(LessThan)),
                '>' => (lexer.advance(), Some(GreaterThan)),
                '=' => lexer.if_peeked('=', Assign, Equal),
                '!' => lexer.if_peeked('=', Bang, NotEqual),

                // Delimiters
                ',' => (lexer.advance(), Some(Comma)),
                ';' => (lexer.advance(), Some(Semicolon)),
                '(' => (lexer.advance(), Some(LParen)),
                ')' => (lexer.advance(), Some(RParen)),
                '{' => (lexer.advance(), Some(LBrace)),
                '}' => (lexer.advance(), Some(RBrace)),

                // Keywords + Identifiers + Literals
                ch if Lexer::is_identifier(ch) => lexer.read_identifier(),
                ch if Lexer::is_number(ch) => lexer.read_number(),

                // Special
                _ch => (lexer.advance(), Some(Illegal)),
            },
        };
    }

    /// Advance the lexer.
    pub(crate) fn advance(self) -> Self {
        return match self.pos {
            p if p >= self.input.len() => Lexer {
                input: self.input,
                pos: self.pos,
                ch: None,
            },
            _ => Lexer {
                input: self.input,
                pos: self.pos + 1,
                ch: self.input.chars().nth(self.pos + 1),
            },
        };
    }

    /// Advance the lexer until the next non-whitespace character.
    pub(crate) fn skip_whitespace(self) -> Self {
        let mut lexer = self;

        // TODO: replace with pattern matching
        while lexer.ch.is_some() && lexer.ch.unwrap().is_whitespace() {
            lexer = lexer.advance();
        }

        return lexer;
    }

    pub(crate) fn peek_char(self) -> Option<char> {
        return match self.pos {
            p if p + 1 >= self.input.len() => None,
            _ => self.input.chars().nth(self.pos + 1),
        };
    }

    /// Advance the lexer until the condition is false.
    pub(crate) fn seek_while(self, cond: impl Fn(char) -> bool) -> Self {
        let mut lexer = self;

        // recursively loop until the condition is false or there are no characters left
        if let Some(ch) = lexer.ch {
            if cond(ch) {
                lexer = lexer.advance();
                return lexer.seek_while(cond);
            }
        }

        return lexer;
    }

    /// Read characters while the condition is true.
    pub(crate) fn read_while(self, cond: impl Fn(char) -> bool) -> (Self, String) {
        let pos_start = self.pos;
        let lexer = self.seek_while(cond);
        let pos_end = lexer.pos;
        return (lexer, lexer.input[pos_start..pos_end].to_string());
    }

    /// Read an identifier.
    pub(crate) fn read_identifier(self) -> (Self, Option<Token>) {
        let (lexer, ident) = self.read_while(Lexer::is_identifier);
        assert!(!ident.is_empty());
        return (lexer, Token::lookup_ident(&ident));
    }

    /// Read a number.
    pub(crate) fn read_number(self) -> (Self, Option<Token>) {
        let (lexer, number) = self.read_while(Lexer::is_number);
        assert!(!number.is_empty());
        return (lexer, Some(Token::Int(number)));
    }

    /// Check if the current character *could* be a part of an identifier.
    pub(crate) fn is_identifier(ch: char) -> bool {
        return ch == '_' || ch.is_alphabetic();
    }

    /// Check if the current character *could* be a part of a number.
    pub(crate) fn is_number(ch: char) -> bool {
        return ch.is_numeric();
    }

    /// Check if the next character is `next_ch`. If it is, return `matched`, otherwise return `default`.
    pub(crate) fn if_peeked(
        self,
        next_ch: char,
        default: Token,
        matched: Token,
    ) -> (Self, Option<Token>) {
        let (lexer, token) = match self.peek_char() {
            Some(peeked) if peeked == next_ch => (self.advance(), Some(matched)),
            _ => (self, Some(default)),
        };
        return (lexer.advance(), token);
    }
}

pub struct IntoIter<'a>(Lexer<'a>);

impl<'a> Iterator for IntoIter<'a> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let (lex, tok) = self.0.next_token();
        self.0 = lex;
        return tok;
    }
}

impl<'a> IntoIterator for Lexer<'a> {
    type Item = Token;

    type IntoIter = IntoIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        return IntoIter(self);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use Token::*;

    fn run_test(input: &str, tests: Vec<Token>) {
        let mut lexer = Lexer::new(input);

        for (i, expected) in tests.iter().enumerate() {
            let (lex, tok) = lexer.next_token();
            assert_eq!(tok, Some(expected.clone()), "tests[{}]", i);
            lexer = lex;
        }

        let (_, tok) = lexer.next_token();
        assert_eq!(tok, None)
    }

    #[test]
    fn single_chars() {
        let input = "=+-!*/<>(){},;";

        let tests = vec![
            Assign,
            Plus,
            Minus,
            Bang,
            Asterisk,
            Slash,
            LessThan,
            GreaterThan,
            LParen,
            RParen,
            LBrace,
            RBrace,
            Comma,
            Semicolon,
        ];

        run_test(input, tests);
    }

    #[test]
    fn code() {
        let input = r"
            let five = 5;
            let ten = 10;
            let add = fn(x, y) {
                x + y;
            };
            let result = add(five, ten);
        ";

        let tests = vec![
            Let,
            Ident("five".into()),
            Assign,
            Int("5".into()),
            Semicolon,
            Let,
            Ident("ten".into()),
            Assign,
            Int("10".into()),
            Semicolon,
            Let,
            Ident("add".into()),
            Assign,
            Function,
            LParen,
            Ident("x".into()),
            Comma,
            Ident("y".into()),
            RParen,
            LBrace,
            Ident("x".into()),
            Plus,
            Ident("y".into()),
            Semicolon,
            RBrace,
            Semicolon,
            Let,
            Ident("result".into()),
            Assign,
            Ident("add".into()),
            LParen,
            Ident("five".into()),
            Comma,
            Ident("ten".into()),
            RParen,
            Semicolon,
        ];

        run_test(input, tests);
    }

    #[test]
    fn code2() {
        let input = r"
            if (5 < 10) {
                return true;
            } else {
                return false;
            }
        ";

        let tests = vec![
            If,
            LParen,
            Int("5".into()),
            LessThan,
            Int("10".into()),
            RParen,
            LBrace,
            Return,
            Boolean(true),
            Semicolon,
            RBrace,
            Else,
            LBrace,
            Return,
            Boolean(false),
            Semicolon,
            RBrace,
        ];

        run_test(input, tests);
    }
    #[test]
    fn code3() {
        let input = r"
            let a = 5 == 5;
            let b = 5 != 6;
        ";

        let tests = vec![
            Let,
            Ident("a".into()),
            Assign,
            Int("5".into()),
            Equal,
            Int("5".into()),
            Semicolon,
            Let,
            Ident("b".into()),
            Assign,
            Int("5".into()),
            NotEqual,
            Int("6".into()),
            Semicolon,
        ];

        run_test(input, tests);
    }
}
