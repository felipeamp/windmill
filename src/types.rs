//! This file should have all types that do not have a separade module.
//!
//! It should include (at least) the following structs:
//! * Square
//! * Move
//! * Killer Moves
//! * GameInfo
//!
//! And maybe some (global) consts (castling, color, pieces, etc).

use std::ascii::AsciiExt;
use std::char;
use std::fmt;
use std::iter::Iterator;

/// Struct for square notation. Should be between 0 (h1) and 63 (a8)
///
/// Since we still can't implement a trait for a type alias, we need
/// a tuple struct here. It's not elegant, but it works.
///
/// # Examples
///
/// ```
/// let sq_h1 = Square(0);
/// println!("{}", sq_h1) // prints h1
///
/// let sq_a8 = Square(63);
/// println!("{}", sq_a8) // prints a8
/// ```
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Square(u8);

/// Prints the square in the human notation (eg: 'e4').
impl fmt::Display for Square {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        assert!(self.0 < 64u8);
        let file: char = ('h' as u8 - self.0 % 8) as char;
        let rank: char = char::from_digit(1 + (self.0 / 8) as u32, 10).unwrap();
        write!(f, "{}{}", file, rank)
    }
}

impl Square {
    /// If the input string is a valid square, creates the corresponding `Square`
    /// struct inside a `Result`.
    ///
    /// # Arguments
    ///
    /// * `input` - String containing two chars, one letter between 'a' and 'h'
    /// (may be lower or uppercase) and one number between '1' and '8'.
    pub fn from_string(input: String) -> Result<Square, String> {
        let input_char_vec: Vec<char> = input.chars()
            .filter(|ref c| c.is_ascii())
            .collect();
        if input_char_vec.len() != 2 {
            return Err(format!("String \"{}\" is not a legal square name.", input));
        }
        let mut ret_u8 = 0u8;
        match input_char_vec[0] {
            c @ 'a'...'h' => ret_u8 += 7 - (c as u8 - 'a' as u8),
            c @ 'A'...'H' => ret_u8 += 7 - (c as u8 - 'A' as u8),
            _ => return Err(format!("String \"{}\" is not a legal square name.", input)),
        }
        match input_char_vec[1] {
            c @ '1'...'8' => ret_u8 += 8 * (c.to_digit(10).unwrap() as u8 - 1),
            _ => return Err(format!("String \"{}\" is not a legal square name.", input)),
        }
        Ok(Square(ret_u8))
    }
}

/// Type for move notation.
///
/// bits  0- 5: origin square (from 0 to 63)
/// bits  6-11: destination square (from 0 to 63)
/// bits 12-13: promotion piece type (Knight = 0, Bishop = 1, Rook = 2, Queen = 3)
/// bits 14-15: special move flags (promotion = 1, en passent = 2, castling = 3)
///
/// Note that, if we need to create a NULL_MOVE, we can use 0 (since there is no
/// legal move where the origin and destination squares are the same).
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Move(u16);

/// Empty/Null `Move`
pub const NULL_MOVE: Move = Move(0);

// TODO: implement methods to edit moves and to get the information inside.
impl Move {
    pub fn from(&self) -> Square {
        unimplemented!();
    }

    pub fn to(&self) -> Square {
        unimplemented!();
    }

    pub fn is_promotion(&self) -> bool {
        unimplemented!();
    }

    pub fn is_en_passent(&self) -> bool {
        unimplemented!();
    }

    pub fn is_castle(&self) -> bool {
        unimplemented!();
    }

    pub fn promoted_piece(&self) -> Piece {
        unimplemented!();
    }
}

/// Queue of four killer moves. The first entry is the newest.
pub struct Killer(pub Move, pub Move, pub Move, pub Move);

/// Empty killer moves' list.
pub const EMPTY_KILLER: Killer = Killer(NULL_MOVE, NULL_MOVE, NULL_MOVE, NULL_MOVE);

impl Killer {
    /// Inserts a new move in the first position of the Killer Move queue.
    pub fn insert(&mut self, new_killer_move: Move) {
        self.3 = self.2;
        self.2 = self.1;
        self.1 = self.0;
        self.0 = new_killer_move;
    }
}

pub enum Piece {
    Pawn,
    Knight,
    Bishop,
    Rook,
    Queen,
    King,
}

impl fmt::Display for Piece {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Piece::Pawn => write!(f, "♙"),
            Piece::Knight => write!(f, "♘"),
            Piece::Bishop => write!(f, "♗"),
            Piece::Rook => write!(f, "♖"),
            Piece::Queen => write!(f, "♕"),
            Piece::King => write!(f, "♔"),
        }

    }
}

pub enum Color {
    White,
    Black,
}

pub enum CastleSide {
    Kingside,
    Queenside,
}

impl fmt::Display for CastleSide {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CastleSide::Kingside => write!(f, "O-O"),
            CastleSide::Queenside => write!(f, "O-O-O"),
        }

    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn square_display() {
        assert_eq!(format!("{}", Square(0u8)), "h1");
        assert_eq!(format!("{}", Square(7u8)), "a1");
        assert_eq!(format!("{}", Square(8u8)), "h2");
        assert_eq!(format!("{}", Square(63u8)), "a8");
    }

    #[test]
    fn square_from_string() {
        assert_eq!(Square(0u8), Square::from_string("h1".to_string()).unwrap());
        assert_eq!(Square(7u8), Square::from_string("a1".to_string()).unwrap());
        assert_eq!(Square(8u8), Square::from_string("h2".to_string()).unwrap());
        assert_eq!(Square(63u8), Square::from_string("a8".to_string()).unwrap());

        assert_eq!(Square(0u8), Square::from_string("H1".to_string()).unwrap());
        assert_eq!(Square(7u8), Square::from_string("A1".to_string()).unwrap());

        assert!(Square::from_string("i1".to_string()).is_err());
        assert!(Square::from_string("a0".to_string()).is_err());
        assert!(Square::from_string("a11".to_string()).is_err());
        assert!(Square::from_string(String::new()).is_err());
    }

    #[test]
    fn piece_display() {
        assert_eq!(format!("{}", Piece::Pawn), "♙".to_string());
        assert_eq!(format!("{}", Piece::Knight), "♘".to_string());
        assert_eq!(format!("{}", Piece::Bishop), "♗".to_string());
        assert_eq!(format!("{}", Piece::Rook), "♖".to_string());
        assert_eq!(format!("{}", Piece::Queen), "♕".to_string());
        assert_eq!(format!("{}", Piece::King), "♔".to_string());
    }

    #[test]
    fn castleside_display() {
        assert_eq!(format!("{}", CastleSide::Kingside), "O-O".to_string());
        assert_eq!(format!("{}", CastleSide::Queenside), "O-O-O".to_string());
    }
}
