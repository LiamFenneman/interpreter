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
}

impl<'a> Parser<'a> {
    /// Create a new parser from source code.
    pub fn new(source: &'a str) -> Self {
        let lexer = Lexer::new(source);
        return Self { lexer, cur: None }.next_token();
    }

    fn next_token(self) -> Self {
        let (lexer, cur) = self.lexer.next_token();
        return Self { lexer, cur };
    }

    /// Parse the source code into an AST using a recursive descent parser strategy.
    pub fn parse(self) -> Result<Ast> {
        let mut ast = Ast {
            statements: Vec::new(),
        };

        let mut p = self;
        let mut stmt;
        while p.cur.is_some() {
            (p, stmt) = p.parse_statement();
            ast.statements.push(dbg!(stmt?));
            p = p.next_token();
        }

        return Ok(ast);
    }

    fn parse_statement(self) -> (Self, Result<Statement>) {
        return match self.cur {
            Some(Token::Let) => {
                let (p, s) = self.parse_let_statement();
                return (p, s.map(|s| s.into()));
            }
            _ => {
                let tok = self.cur.clone();
                (self, Err(StatementError::InvalidToken(tok).into()))
            }
        };
    }

    fn parse_let_statement(self) -> (Self, Result<LetStatement>) {
        let p = self;

        // the current token is `Let`
        let Some(cur) = p.cur.clone() else {
            return (p, Err(LetStatementError::MissingLet.into()));
        };
        let p = p.next_token();

        // the next token should always be an `Ident`
        let Some(Token::Ident(ident)) = p.cur.clone() else {
            let tok = p.cur.clone();
            return (p, Err(LetStatementError::InvalidIdent(tok).into()));
        };

        let mut p = p.next_token();
        let mut expr = Expression(Vec::new());
        loop {
            let Some(tok) = p.cur.clone() else {
                return (p, Err(LetStatementError::InvalidEof.into()));
            };

            if tok == Token::Semicolon {
                break;
            }

            expr.0.push(tok);
            p = p.next_token();
        }

        return (
            p,
            Ok(LetStatement {
                token: cur,
                ident: Ident {
                    token: Token::Ident(ident),
                },
                expr,
            }),
        );
    }
}

pub type Result<T> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("parse statement error: {0}")]
    StatementError(#[from] StatementError),
    #[error("parse let statement error: {0}")]
    LetStatementError(#[from] LetStatementError),
}

#[derive(Debug, Error)]
pub enum StatementError {
    #[error("invalid token: {0:?}")]
    InvalidToken(Option<Token>),
}

#[derive(Debug, Error)]
pub enum LetStatementError {
    #[error("missing `let` keyword")]
    MissingLet,
    #[error("invalid identifier: {0:?}")]
    InvalidIdent(Option<Token>),
    #[error("invalid end of file")]
    InvalidEof,
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

        let ast = Parser::new(source).parse();

        if ast.is_err() {
            println!("ERROR: {}", ast.unwrap_err());
            panic!("AST is ERROR");
        }

        assert_eq!(ast.unwrap(), expected);
    }
}
