//! The parser for the Monkey programming language.

use crate::lexer::{Lexer, Token};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    // IfStatement(IfStatement),
    LetStatement(LetStatement),
    // ReturnStatement(ReturnStatement),
}

impl From<LetStatement> for Statement {
    fn from(s: LetStatement) -> Self {
        return Self::LetStatement(s);
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expression(Vec<Token>);

/// The abstract syntax tree (AST).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Ast {
    statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LetStatement {
    token: Token, // must be Token::Let
    ident: Ident,
    expr: Expression,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Ident {
    token: Token, // must be Token::Ident
}

/// A single state of a parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parser<'a> {
    pub(crate) lexer: Lexer<'a>,
    pub(crate) cur: Option<Token>,
    pub(crate) errors: Vec<Error>,
}

impl<'a> Parser<'a> {
    /// Create a new parser from source code.
    pub fn new(source: &'a str) -> Self {
        let lexer = Lexer::new(source);
        return Self {
            lexer,
            cur: None,
            errors: Vec::new(),
        }
        .next_token();
    }

    fn next_token(self) -> Self {
        let (lexer, cur) = self.lexer.next_token();
        return Self {
            lexer,
            cur,
            errors: self.errors,
        };
    }

    /// Parse the source code into an AST using a recursive descent parser strategy.
    pub fn parse(self) -> (Ast, Vec<Error>) {
        let mut ast = Ast {
            statements: Vec::new(),
        };

        let mut p = self;
        let mut stmt;
        while p.cur.is_some() {
            (p, stmt) = p.parse_statement();
            if let Some(s) = stmt {
                ast.statements.push(s);
            }
            p = p.next_token();
        }

        return (ast, p.errors);
    }

    fn parse_statement(self) -> (Self, Option<Statement>) {
        return match self.cur {
            Some(Token::Let) => {
                let (p, s) = self.parse_let_statement();
                return (p, s.map(|s| s.into()));
            }
            _ => match self.cur.clone() {
                None => (self.with_err(Error::UnexpectedEof), None),
                Some(tok) => (self.with_err(Error::InvalidToken(tok)), None),
            },
        };
    }

    fn parse_let_statement(self) -> (Self, Option<LetStatement>) {
        let p = self;

        // the current token is `Let`
        let p = p.expect_token(Token::Let);

        // the next token should always be an `Ident`
        let Some(Token::Ident(ident)) = p.cur.clone() else {
            let err = match p.cur.clone() {
                None => Error::UnexpectedEof,
                Some(tok) => Error::InvalidToken(tok),
            };

            return (p.with_err(err), None);
        };

        let mut p = p.next_token();
        let mut expr = Expression(Vec::new());
        loop {
            let Some(tok) = p.cur.clone() else {
                p.errors.push(Error::UnexpectedEof);
                return (p, None);
            };

            if tok == Token::Semicolon {
                break;
            }

            expr.0.push(tok);
            p = p.next_token();
        }

        return (
            p,
            Some(LetStatement {
                token: Token::Let,
                ident: Ident {
                    token: Token::Ident(ident),
                },
                expr,
            }),
        );
    }

    fn expect_token(self, tok: Token) -> Self {
        return match self.cur.clone() {
            None => self.with_err(Error::UnexpectedEof),
            Some(cur) if cur != tok => self.with_err(Error::UnexpectedToken(cur, tok)),
            _ => self.next_token(),
        };
    }

    /// Add an error to the parser.
    pub(crate) fn with_err(self, err: Error) -> Self {
        let mut p = self;
        p.errors.push(err);
        return p;
    }
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum Error {
    /// An unexpected token was found.
    ///
    /// Left: found token, Right: expected token.
    #[error("unexpected token: {0:?}, expected: {1:?}")]
    UnexpectedToken(Token, Token),

    /// An unexpected end of file was found.
    #[error("unexpected end of file")]
    UnexpectedEof,

    /// An invalid token was found.
    ///
    /// This should be used when the expected token contains a value (e.g. Ident)
    /// or when there is a range of valid tokens.
    #[error("invalid identifier: {0:?}")]
    InvalidToken(Token),
}

#[cfg(test)]
mod test {
    use super::*;
    use Statement as S;
    use Token as T;

    #[test]
    fn let_stmts() {
        let source = r"
            let x = 5;
            let _y = 10;
            let foobar = 838383;
        ";

        let expected = Ast {
            statements: vec![
                S::LetStatement(LetStatement {
                    token: T::Let,
                    ident: Ident {
                        token: T::Ident("x".into()),
                    },
                    expr: Expression(vec![T::Assign, T::Int("5".into())]),
                }),
                S::LetStatement(LetStatement {
                    token: T::Let,
                    ident: Ident {
                        token: T::Ident("_y".into()),
                    },
                    expr: Expression(vec![T::Assign, T::Int("10".into())]),
                }),
                S::LetStatement(LetStatement {
                    token: T::Let,
                    ident: Ident {
                        token: T::Ident("foobar".into()),
                    },
                    expr: Expression(vec![T::Assign, T::Int("838383".into())]),
                }),
            ],
        };

        let (ast, err) = Parser::new(source).parse();
        assert_eq!(ast, expected);
        assert!(err.is_empty());
    }

    #[test]
    fn errors() {
        use Error::*;

        let source = r"
            let x 5;
            let = 10;
            let 838383;
        ";

        let expected = vec![
            UnexpectedToken(T::Int("5".into()), T::Assign),
            InvalidToken(T::Assign),
            InvalidToken(T::Int("838383".into())),
        ];

        let (ast, err) = Parser::new(source).parse();
        assert_eq!(err, expected);
        assert!(ast.statements.is_empty());
    }
}
