use std::fmt;
use std::num;
use std::iter::Peekable;
use std::str::FromStr;

use super::*;

impl fmt::Display for IdTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            IdTree::Leaf {i} => {
                write!(f, "{}", if i { 1 } else { 0 })
            },
            IdTree::Node {ref left, ref right} => {
                write!(f, "({},{})", left, right)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseError {
    EndOfString,
    Error,
    UnexpectedChar(char),
    ParseIntError(num::ParseIntError)
}

impl From<num::ParseIntError> for ParseError {
    fn from(e: num::ParseIntError) -> ParseError {
        ParseError::ParseIntError(e)
    }
}

pub struct Parser;

impl Parser {
    pub fn take_number<I>(i: &mut Peekable<I>) -> Result<u32, ParseError> where I: Iterator<Item=char> {
        let mut s = String::new();

        loop {
            match i.peek().map(|c| *c) {
                Some(c) if c >= '0' && c <= '9' => {
                    i.next();
                    s.push(c);
                },
                _ => {
                    break;
                }
            }
        }
        
        s.parse::<u32>().map_err(ParseError::from)
    }

    pub fn take_char<I>(i: &mut I, expected: char) -> Result<(), ParseError> where I: Iterator<Item=char> {
        match i.next() {
            None => {
                Err(ParseError::EndOfString)
            },
            Some(c) if c == expected => {
                Ok(())
            },
            Some(c) => {
                Err(ParseError::UnexpectedChar(c))
            }
        }
    }

    pub fn take_id_tree<I>(i: &mut Peekable<I>) -> Result<IdTree, ParseError> where I: Iterator<Item=char> {
        match i.peek().map(|c| *c) {
            Some('(') => {
                Self::take_char(i, '(')?;
                let left = Self::take_id_tree(i)?;
                Self::take_char(i, ',')?;
                let right = Self::take_id_tree(i)?;
                Self::take_char(i, ')')?;
                Ok(IdTree::node(Box::new(left), Box::new(right)))
            },
            None => {
                Err(ParseError::EndOfString)
            },
            _ => {
                let n = Self::take_number(i)?;
                Ok(IdTree::leaf(n != 0))
            }
        }
    }

    pub fn take_event_tree<I>(i: &mut Peekable<I>) -> Result<EventTree, ParseError> where I: Iterator<Item=char> {
        match i.peek().map(|c| *c) {
            Some('(') => {
                Self::take_char(i, '(')?;
                let n = Self::take_number(i)?;
                Self::take_char(i, ',')?;
                let left = Self::take_event_tree(i)?;
                Self::take_char(i, ',')?;
                let right = Self::take_event_tree(i)?;
                Self::take_char(i, ')')?;
                Ok(EventTree::node(n, Box::new(left), Box::new(right)))
            },
            None => {
                Err(ParseError::EndOfString)
            },
            _ => {
                let n = Self::take_number(i)?;
                Ok(EventTree::leaf(n))
            }
        }
    }

    pub fn take_stamp<I>(p: &mut Peekable<I>) -> Result<Stamp, ParseError> where I: Iterator<Item=char> {
        Self::take_char(p, '(')?;
        let i = Self::take_id_tree(p)?;
        Self::take_char(p, ',')?;
        let e = Self::take_event_tree(p)?;
        Self::take_char(p, ')')?;
        Ok(Stamp::new(i, e))
    }
}

impl FromStr for IdTree {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = s.chars().peekable();
        Parser::take_id_tree(&mut p)
    } 
}

impl FromStr for EventTree {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = s.chars().peekable();
        Parser::take_event_tree(&mut p)
    }
}

impl FromStr for Stamp {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut p = s.chars().peekable();
        Parser::take_stamp(&mut p)
    }
}

impl fmt::Display for EventTree {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            EventTree::Leaf {n} => {
                write!(f, "{}", n)
            },
            EventTree::Node {n, ref left, ref right} => {
                write!(f, "({},{},{})", n, left, right)
            }
        }
    }
}

impl fmt::Display for Stamp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({},{})", self.i, self.e)
    }
}

#[cfg(test)]
mod tests {
    use ::{IdTree,EventTree,Stamp};
    use std::str::FromStr;
    use super::*;

    #[test]
    fn id_tree_display() {
        assert_eq!("0", format!("{}", IdTree::zero()));
        assert_eq!("(0,(1,0))", format!("{}", IdTree::node(Box::new(IdTree::zero()), Box::new(IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::zero()))))));
    }

    #[test]
    fn event_tree_display() {
        assert_eq!("0", format!("{}", EventTree::zero()));
        assert_eq!("(0,1,(2,1,0))", format!("{}", EventTree::node(0, Box::new(EventTree::leaf(1)), Box::new(EventTree::node(2, Box::new(EventTree::leaf(1)), Box::new(EventTree::zero()))))));
    }

    #[test]
    fn stamp_display() {
        let i = IdTree::node(Box::new(IdTree::zero()), Box::new(IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::zero()))));
        let e = EventTree::node(0, Box::new(EventTree::leaf(1)), Box::new(EventTree::node(2, Box::new(EventTree::leaf(1)), Box::new(EventTree::zero()))));
        let s = Stamp::new(i, e);
        assert_eq!("((0,(1,0)),(0,1,(2,1,0)))", format!("{}", s));
    }

    #[test]
    fn test_parser_take_number() {
        let mut p = "0".chars().peekable();
        assert_eq!(0, Parser::take_number(&mut p).expect("parse number"));

        let mut p = "1234".chars().peekable();
        assert_eq!(1234, Parser::take_number(&mut p).expect("parse number"));

        let mut p = "1234,(foo)".chars().peekable();
        assert_eq!(1234, Parser::take_number(&mut p).expect("parse number"));
    }

    #[test]
    fn test_parser_take_id_tree() {
        assert_eq!(IdTree::zero(), IdTree::from_str("0").expect("parse idtree"));
        assert_eq!(IdTree::one(), IdTree::from_str("1").expect("parse idtree"));
        assert_eq!(IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::zero())), IdTree::from_str("(1,0)").expect("parse idtree"));
        assert_eq!(IdTree::node(Box::new(IdTree::one()), Box::new(IdTree::zero())), IdTree::from_str("(1,0),foo").expect("parse idtree"));
    }

    #[test]
    fn test_parser_id_string_round_trip() {
        let s1 = "(1,(0,1))";
        let i = IdTree::from_str(s1).expect("parse idtree");
        let s2 = i.to_string();
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_parser_event_tree_string_round_trip() {
        let s1 = "(2,1,(0,0,1))";
        let i = EventTree::from_str(s1).expect("parse eventtree");
        let s2 = i.to_string();
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_parser_stamp_string_round_trip() {
        let s1 = "((1,(0,1)),(2,1,(0,0,1)))";
        let i = Stamp::from_str(s1).expect("parse stamp");
        let s2 = i.to_string();
        assert_eq!(s1, s2);
    }
}