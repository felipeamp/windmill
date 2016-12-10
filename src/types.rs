//! This file should have all types that do not have a separade module.
//!
//! It should include (at least) the following structs:
//! * Square
//! * Move
//! * Killer Moves
//! * Game Info
//!
//! And maybe some (global) consts (castling, color, pieces, etc).

use std::ascii::AsciiExt;
use std::char;
use std::fmt;
use std::iter::Iterator;
use std::panic;


#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum File {
    A,
    B,
    C,
    D,
    E,
    F,
    G,
    H,
}

impl fmt::Display for File {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            File::A => write!(f, "a"),
            File::B => write!(f, "b"),
            File::C => write!(f, "c"),
            File::D => write!(f, "d"),
            File::E => write!(f, "e"),
            File::F => write!(f, "f"),
            File::G => write!(f, "g"),
            File::H => write!(f, "h"),
        }
    }
}


#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Rank {
    _1,
    _2,
    _3,
    _4,
    _5,
    _6,
    _7,
    _8,
}

impl fmt::Display for Rank {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Rank::_1 => write!(f, "1"),
            Rank::_2 => write!(f, "2"),
            Rank::_3 => write!(f, "3"),
            Rank::_4 => write!(f, "4"),
            Rank::_5 => write!(f, "5"),
            Rank::_6 => write!(f, "6"),
            Rank::_7 => write!(f, "7"),
            Rank::_8 => write!(f, "8"),
        }
    }
}

/// Struct for square notation. Should be between 0 (a1) and 63 (h8)
///
/// Since we still can't implement a trait for a type alias, we need
/// a tuple struct here. It's not elegant, but it works.
///
/// # Examples
///
/// ```
/// let sq_h1 = Square(0);
/// println!("{}", sq_a1) // prints a1
///
/// let sq_a8 = Square(63);
/// println!("{}", sq_h8) // prints h8
/// ```
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Square(pub u8);

impl Square {
    pub fn file(&self) -> File {
        match self.0 % 8 {
            0 => File::A,
            1 => File::B,
            2 => File::C,
            3 => File::D,
            4 => File::E,
            5 => File::F,
            6 => File::G,
            7 => File::H,
            _ => panic!("should never get here"),
        }
    }

    pub fn rank(&self) -> Rank {
        assert!(self.0 < 64);
        match self.0 / 8 {
            0 => Rank::_1,
            1 => Rank::_2,
            2 => Rank::_3,
            3 => Rank::_4,
            4 => Rank::_5,
            5 => Rank::_6,
            6 => Rank::_7,
            7 => Rank::_8,
            _ => panic!("Invalid rank (> 8)"),
        }
    }

    /// If the input string is a valid square, creates the corresponding `Square`
    /// struct inside a `Result`.
    ///
    /// # Arguments
    ///
    /// * `input` - String containing two chars, one letter between 'a' and 'h'
    /// (may be lower or uppercase) and one number between '1' and '8'.
    pub fn from_string(input: String) -> Result<Square, String> {
        let input_char_vec: Vec<char> = input.chars()
            .filter(|c| c.is_ascii())
            .collect();
        if input_char_vec.len() != 2 {
            return Err(format!("String \"{}\" is not a legal square name.", input));
        }
        let mut ret_u8 = 0u8;
        match input_char_vec[0] {
            c @ 'a'...'h' => ret_u8 += c as u8 - b'a',
            c @ 'A'...'H' => ret_u8 += c as u8 - b'A',
            _ => return Err(format!("String \"{}\" is not a legal square name.", input)),
        }
        match input_char_vec[1] {
            c @ '1'...'8' => ret_u8 += 8 * (c.to_digit(10).unwrap() as u8 - 1),
            _ => return Err(format!("String \"{}\" is not a legal square name.", input)),
        }
        Ok(Square(ret_u8))
    }

    pub fn from_file_rank(file: File, rank: Rank) -> Square {
        let mut ret = 0u8;
        match file {
            File::A => (),
            File::B => ret += 1,
            File::C => ret += 2,
            File::D => ret += 3,
            File::E => ret += 4,
            File::F => ret += 5,
            File::G => ret += 6,
            File::H => ret += 7,
        }
        match rank {
            Rank::_1 => (),
            Rank::_2 => ret += 8,
            Rank::_3 => ret += 16,
            Rank::_4 => ret += 24,
            Rank::_5 => ret += 32,
            Rank::_6 => ret += 40,
            Rank::_7 => ret += 48,
            Rank::_8 => ret += 56,
        }
        Square(ret)
    }
}

/// Prints the square in the human notation (eg: 'e4').
impl fmt::Display for Square {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        assert!(self.0 < 64u8);
        write!(f, "{}{}", self.file(), self.rank())
    }
}

/// Type for move notation.
///
/// bits  0- 5: origin square (from 0 to 63)
/// bits  6-11: destination square (from 0 to 63)
/// bits 12-13: promotion piece type (Knight = 0, Bishop = 1, Rook = 2, Queen = 3)
/// bits 14-15: special move flags (promotion = 1, en passent = 2, castling = 3)
///
/// Note that, if we need to create a `NULL_MOVE`, we can use 0 (since there is no
/// legal move where the origin and destination squares are the same).
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Move(u16);

/// Empty/Null `Move`
pub const NULL_MOVE: Move = Move(0);
pub const PROMOTION_FLAG: u16 = 0b01 << 14;
pub const EN_PASSENT_FLAG: u16 = 0b10 << 14;
pub const CASTLING_FLAG: u16 = 0b11 << 14;

impl Move {
    pub fn new(sq_from: Square,
               sq_to: Square,
               promoted_piece: Piece,
               castle_side: CastleSide,
               is_en_passent: bool)
               -> Move {
        assert!(sq_from.0 < 64);
        assert!(sq_to.0 < 64);
        let mut ret = Move(sq_from.0 as u16 | ((sq_to.0 as u16) << 6));
        match promoted_piece {
            Piece::None => (),
            Piece::Knight => ret.0 |= PROMOTION_FLAG,
            Piece::Bishop => ret.0 |= (1 << 12) | PROMOTION_FLAG,
            Piece::Rook => ret.0 |= (2 << 12) | PROMOTION_FLAG,
            Piece::Queen => ret.0 |= (3 << 12) | PROMOTION_FLAG,
            piece => panic!(format!("Invalid promoted piece: {}", piece)),
        }
        match castle_side {
            CastleSide::None => (),
            CastleSide::Kingside | CastleSide::Queenside => ret.0 |= CASTLING_FLAG,
        }
        if is_en_passent {
            ret.0 |= EN_PASSENT_FLAG;
        }
        ret
    }

    pub fn is_valid(&self) -> bool {
        let sq_from = self.sq_from();
        let sq_to = self.sq_to();
        let sq_from_rank = sq_from.rank();
        let sq_from_file = sq_from.file();
        let sq_to_rank = sq_to.rank();
        let sq_to_file = sq_to.file();
        let castle_side: CastleSide;
        match panic::catch_unwind(|| self.castle_side()) {
            Ok(temp_cs) => castle_side = temp_cs,
            Err(_) => return false,
        }
        let is_castle = self.is_castle();
        let is_promotion = self.is_promotion();
        let is_en_passent = self.is_en_passent();
        // Wrong promotion squares
        if is_promotion &&
           ((sq_from_rank != Rank::_2 && sq_from_rank != Rank::_7) ||
            (sq_to_rank != Rank::_1 && sq_to_rank != Rank::_8)) {
            return false;
        }
        // Wrong castle squares
        if is_castle {
            if !((sq_from_rank == Rank::_1 && sq_to_rank == Rank::_1) ||
                 (sq_from_rank == Rank::_8 && sq_to_rank == Rank::_8)) {
                return false;
            }
            if sq_from_file != File::E || (sq_to_file != File::C && sq_to_file != File::G) {
                return false;
            }
        }
        // Wrong castle side
        if is_castle &&
           ((castle_side == CastleSide::Kingside && sq_to_file != File::G) ||
            (castle_side == CastleSide::Queenside && sq_to_file != File::C)) {
            return false;
        }
        // Wrong en passent squares
        if is_en_passent {
            if !((sq_from_rank == Rank::_4 && sq_to_rank == Rank::_3) ||
                 (sq_from_rank == Rank::_5 && sq_to_rank == Rank::_6)) {
                return false;
            }
            match sq_from_file {
                File::A if sq_to_file != File::B => return false,
                File::B if sq_to_file != File::A && sq_to_file != File::C => return false,
                File::C if sq_to_file != File::B && sq_to_file != File::D => return false,
                File::D if sq_to_file != File::C && sq_to_file != File::E => return false,
                File::E if sq_to_file != File::D && sq_to_file != File::F => return false,
                File::F if sq_to_file != File::E && sq_to_file != File::G => return false,
                File::G if sq_to_file != File::F && sq_to_file != File::H => return false,
                File::H if sq_to_file != File::G => return false,
                _ => (),
            }
        }
        // Incompatible flags
        if (is_en_passent && is_castle) || (is_en_passent && is_promotion) ||
           (is_castle && is_promotion) {
            return false;
        }
        // No promotion flag with promoting piece
        if !is_promotion && (self.0 & (0b11 << 12)) != 0 {
            return false;
        }
        // Same from and to squares
        sq_from != sq_to
    }

    pub fn sq_from(&self) -> Square {
        Square((self.0 & 0b111111) as u8)
    }

    pub fn sq_to(&self) -> Square {
        Square(((self.0 >> 6) & 0b111111) as u8)
    }

    pub fn is_promotion(&self) -> bool {
        (self.0 & (0b11 << 14)) == PROMOTION_FLAG
    }

    pub fn is_en_passent(&self) -> bool {
        (self.0 & (0b11 << 14)) == EN_PASSENT_FLAG
    }

    pub fn is_castle(&self) -> bool {
        (self.0 & (0b11 << 14)) == CASTLING_FLAG
    }

    pub fn castle_side(&self) -> CastleSide {
        if !self.is_castle() {
            return CastleSide::None;
        }
        match self.sq_to().file() {
            File::C => CastleSide::Queenside,
            File::G => CastleSide::Kingside,
            file => panic!(format!("Illegal file in castle move: {}", file)),
        }
    }

    pub fn promoted_piece(&self) -> Piece {
        if !self.is_promotion() {
            return Piece::None;
        }
        match (self.0 >> 12) & 0b11 {
            0b00 => Piece::Knight,
            0b01 => Piece::Bishop,
            0b10 => Piece::Rook,
            0b11 => Piece::Queen,
            promotion => {panic!(format!("Wrong promotion value after shift and bitwise-and: {}",
                                         promotion))
            }
        }
    }
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_castle() {
            write!(f, "{}", self.castle_side())
        } else if self.is_promotion() {
            write!(f,
                   "{}-{}={}",
                   self.sq_from().to_string(),
                   self.sq_to().to_string(),
                   self.promoted_piece().to_string())
        } else if self.is_en_passent() {
            write!(f,
                   "{}-{} e.p.",
                   self.sq_from().to_string(),
                   self.sq_to().to_string())
        } else {
            write!(f,
                   "{}-{}",
                   self.sq_from().to_string(),
                   self.sq_to().to_string())
        }
    }
}


/// Queue of four killer moves. The first entry is the newest.
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
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

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Piece {
    None,
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
            _ => write!(f, ""),
        }

    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum Color {
    White,
    Black,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum CastleSide {
    None,
    Kingside,
    Queenside,
}

impl fmt::Display for CastleSide {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            CastleSide::Kingside => write!(f, "O-O"),
            CastleSide::Queenside => write!(f, "O-O-O"),
            _ => write!(f, ""),
        }

    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use std::panic;

    #[test]
    fn rank_display() {
        assert_eq!(format!("{}", Rank::_1), "1");
        assert_eq!(format!("{}", Rank::_2), "2");
        assert_eq!(format!("{}", Rank::_3), "3");
        assert_eq!(format!("{}", Rank::_4), "4");
        assert_eq!(format!("{}", Rank::_5), "5");
        assert_eq!(format!("{}", Rank::_6), "6");
        assert_eq!(format!("{}", Rank::_7), "7");
        assert_eq!(format!("{}", Rank::_8), "8");
    }

    #[test]
    fn file_display() {
        assert_eq!(format!("{}", File::A), "a");
        assert_eq!(format!("{}", File::B), "b");
        assert_eq!(format!("{}", File::C), "c");
        assert_eq!(format!("{}", File::D), "d");
        assert_eq!(format!("{}", File::E), "e");
        assert_eq!(format!("{}", File::F), "f");
        assert_eq!(format!("{}", File::G), "g");
        assert_eq!(format!("{}", File::H), "h");
    }

    #[test]
    fn move_creation() {
        // Null move
        assert_eq!(Move::new(Square(0u8),
                             Square(0u8),
                             Piece::None,
                             CastleSide::None,
                             false),
                   NULL_MOVE);
        // Regular moves
        // Same rank, includes a1
        assert_eq!(Move::new(Square::from_file_rank(File::A, Rank::_1),
                             Square::from_file_rank(File::B, Rank::_1),
                             Piece::None,
                             CastleSide::None,
                             false),
                   Move(0u16 | (1u16 << 6)));
        // Same file, includes h8
        assert_eq!(Move::new(Square::from_file_rank(File::H, Rank::_8),
                             Square::from_file_rank(File::H, Rank::_6),
                             Piece::None,
                             CastleSide::None,
                             false),
                   Move((7u16 + 56u16) | ((7u16 + 40u16) << 6)));
        // Different files and ranks
        assert_eq!(Move::new(Square::from_file_rank(File::G, Rank::_1),
                             Square::from_file_rank(File::F, Rank::_3),
                             Piece::None,
                             CastleSide::None,
                             false),
                   Move(6u16 | ((5u16 + 16u16) << 6)));
        // En passent
        // En passent with white
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_5),
                             Square::from_file_rank(File::D, Rank::_6),
                             Piece::None,
                             CastleSide::None,
                             true),
                   Move((4u16 + 32u16) | ((3u16 + 40u16) << 6) | EN_PASSENT_FLAG));
        // En passent with black
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_4),
                             Square::from_file_rank(File::D, Rank::_3),
                             Piece::None,
                             CastleSide::None,
                             true),
                   Move((4u16 + 24u16) | ((3u16 + 16u16) << 6) | EN_PASSENT_FLAG));
        // Castling
        // Castling Kingside white
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                             Square::from_file_rank(File::G, Rank::_1),
                             Piece::None,
                             CastleSide::Kingside,
                             false),
                   Move(4u16 | (6u16 << 6) | CASTLING_FLAG));
        // Castling Queenside white
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                             Square::from_file_rank(File::C, Rank::_1),
                             Piece::None,
                             CastleSide::Queenside,
                             false),
                   Move(4u16 | (2u16 << 6) | CASTLING_FLAG));
        // Castling Kingside black
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_8),
                             Square::from_file_rank(File::G, Rank::_8),
                             Piece::None,
                             CastleSide::Kingside,
                             false),
                   Move((4u16 + 56u16) | ((6u16 + 56u16) << 6) | CASTLING_FLAG));
        // Castling Queenside black
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_8),
                             Square::from_file_rank(File::C, Rank::_8),
                             Piece::None,
                             CastleSide::Queenside,
                             false),
                   Move((4u16 + 56u16) | ((2u16 + 56u16) << 6) | CASTLING_FLAG));
        // Promotion
        // To white Knight
        assert_eq!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                             Square::from_file_rank(File::A, Rank::_8),
                             Piece::Knight,
                             CastleSide::None,
                             false),
                   Move((0u16 + 48u16) | ((0u16 + 56u16) << 6) | PROMOTION_FLAG));
        // To black Bishop
        assert_eq!(Move::new(Square::from_file_rank(File::B, Rank::_2),
                             Square::from_file_rank(File::B, Rank::_1),
                             Piece::Bishop,
                             CastleSide::None,
                             false),
                   Move((1u16 + 8u16) | ((1u16 + 0u16) << 6) | (0b01 << 12) | PROMOTION_FLAG));
        // To Rook, with capture by white
        assert_eq!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                             Square::from_file_rank(File::B, Rank::_8),
                             Piece::Rook,
                             CastleSide::None,
                             false),
                   Move((0u16 + 48u16) | ((1u16 + 56u16) << 6) | (0b10 << 12) | PROMOTION_FLAG));
        // To Queen, with capture by black
        assert_eq!(Move::new(Square::from_file_rank(File::B, Rank::_2),
                             Square::from_file_rank(File::C, Rank::_1),
                             Piece::Queen,
                             CastleSide::None,
                             false),
                   Move((1u16 + 8u16) | ((2u16 + 0u16) << 6) | (0b11 << 12) | PROMOTION_FLAG));
        // Move's with any square having a value too big (> 63) should panic
        assert!(panic::catch_unwind(|| {
                Move::new(Square(64u8),
                          Square(0u8),
                          Piece::None,
                          CastleSide::None,
                          false)
            })
            .is_err());
        assert!(panic::catch_unwind(|| {
                Move::new(Square(0u8),
                          Square(64u8),
                          Piece::None,
                          CastleSide::None,
                          false)
            })
            .is_err());
        assert!(panic::catch_unwind(|| {
                Move::new(Square(255u8),
                          Square(255u8),
                          Piece::None,
                          CastleSide::None,
                          false)
            })
            .is_err());
    }

    #[test]
    fn move_is_valid() {
        // Moves with same from and to squares should NOT be valid
        assert!(!NULL_MOVE.is_valid());
        assert!(!Move::new(Square::from_file_rank(File::D, Rank::_1),
                           Square::from_file_rank(File::D, Rank::_1),
                           Piece::None,
                           CastleSide::None,
                           false)
            .is_valid());
        // Regular moves
        // Same rank, includes a1
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_1),
                          Square::from_file_rank(File::B, Rank::_1),
                          Piece::None,
                          CastleSide::None,
                          false)
            .is_valid());
        // Same file, includes h8
        assert!(Move::new(Square::from_file_rank(File::H, Rank::_8),
                          Square::from_file_rank(File::H, Rank::_6),
                          Piece::None,
                          CastleSide::None,
                          false)
            .is_valid());
        // Different files and ranks
        assert!(Move::new(Square::from_file_rank(File::G, Rank::_1),
                          Square::from_file_rank(File::F, Rank::_3),
                          Piece::None,
                          CastleSide::None,
                          false)
            .is_valid());
        // En passent
        // En passent with white
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_5),
                          Square::from_file_rank(File::D, Rank::_6),
                          Piece::None,
                          CastleSide::None,
                          true)
            .is_valid());
        // En passent with white, wrong rank (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_6),
                           Square::from_file_rank(File::D, Rank::_7),
                           Piece::None,
                           CastleSide::None,
                           true)
            .is_valid());
        // En passent with white, wrong file (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_5),
                           Square::from_file_rank(File::E, Rank::_6),
                           Piece::None,
                           CastleSide::None,
                           true)
            .is_valid());
        // En passent with black
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_4),
                          Square::from_file_rank(File::D, Rank::_3),
                          Piece::None,
                          CastleSide::None,
                          true)
            .is_valid());
        // En passent with black, wrong rank (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_5),
                           Square::from_file_rank(File::D, Rank::_4),
                           Piece::None,
                           CastleSide::None,
                           true)
            .is_valid());
        // En passent with black, wrong file (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_4),
                           Square::from_file_rank(File::B, Rank::_3),
                           Piece::None,
                           CastleSide::None,
                           true)
            .is_valid());
        // Castling
        // Castling Kingside white
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                          Square::from_file_rank(File::G, Rank::_1),
                          Piece::None,
                          CastleSide::Kingside,
                          false)
            .is_valid());
        // Castling Kingside white wrong rank (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_1),
                           Square::from_file_rank(File::G, Rank::_2),
                           Piece::None,
                           CastleSide::Kingside,
                           false)
            .is_valid());
        // Castling Kingside white wrong file (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_1),
                           Square::from_file_rank(File::F, Rank::_1),
                           Piece::None,
                           CastleSide::Kingside,
                           false)
            .is_valid());
        // Castling Queenside white
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                          Square::from_file_rank(File::C, Rank::_1),
                          Piece::None,
                          CastleSide::Queenside,
                          false)
            .is_valid());
        // Castling Queenside white wrong file (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_1),
                           Square::from_file_rank(File::B, Rank::_1),
                           Piece::None,
                           CastleSide::Queenside,
                           false)
            .is_valid());
        // Castling Queenside white wrong rank (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_2),
                           Square::from_file_rank(File::C, Rank::_1),
                           Piece::None,
                           CastleSide::Queenside,
                           false)
            .is_valid());
        // Castling Kingside black
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_8),
                          Square::from_file_rank(File::G, Rank::_8),
                          Piece::None,
                          CastleSide::Kingside,
                          false)
            .is_valid());
        // Castling Kingside black wrong rank (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_8),
                           Square::from_file_rank(File::G, Rank::_7),
                           Piece::None,
                           CastleSide::Kingside,
                           false)
            .is_valid());
        // Castling Kingside black wrong file (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_8),
                           Square::from_file_rank(File::F, Rank::_8),
                           Piece::None,
                           CastleSide::Kingside,
                           false)
            .is_valid());
        // Castling Queenside black
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_8),
                          Square::from_file_rank(File::C, Rank::_8),
                          Piece::None,
                          CastleSide::Queenside,
                          false)
            .is_valid());
        // Castling Queenside black wrong file (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_8),
                           Square::from_file_rank(File::B, Rank::_8),
                           Piece::None,
                           CastleSide::Queenside,
                           false)
            .is_valid());
        // Castling Queenside black wrong rank (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_7),
                           Square::from_file_rank(File::C, Rank::_8),
                           Piece::None,
                           CastleSide::Queenside,
                           false)
            .is_valid());
        // Promotion
        // To white Knight
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                          Square::from_file_rank(File::A, Rank::_8),
                          Piece::Knight,
                          CastleSide::None,
                          false)
            .is_valid());
        // To black Bishop
        assert!(Move::new(Square::from_file_rank(File::B, Rank::_2),
                          Square::from_file_rank(File::B, Rank::_1),
                          Piece::Bishop,
                          CastleSide::None,
                          false)
            .is_valid());
        // To Rook, with capture by white
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                          Square::from_file_rank(File::B, Rank::_8),
                          Piece::Rook,
                          CastleSide::None,
                          false)
            .is_valid());
        // To Queen, with capture by black
        assert!(Move::new(Square::from_file_rank(File::B, Rank::_2),
                          Square::from_file_rank(File::C, Rank::_1),
                          Piece::Queen,
                          CastleSide::None,
                          false)
            .is_valid());
        // To wrong rank, white (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::B, Rank::_7),
                           Square::from_file_rank(File::C, Rank::_6),
                           Piece::Queen,
                           CastleSide::None,
                           false)
            .is_valid());
        // To wrong rank, black (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::B, Rank::_2),
                           Square::from_file_rank(File::C, Rank::_2),
                           Piece::Queen,
                           CastleSide::None,
                           false)
            .is_valid());
        // Mixture of self excluding flags
        // en passent + castle (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::B, Rank::_2),
                           Square::from_file_rank(File::C, Rank::_2),
                           Piece::None,
                           CastleSide::Kingside,
                           true)
            .is_valid());
        // en passent + promotion (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::C, Rank::_7),
                           Square::from_file_rank(File::C, Rank::_8),
                           Piece::Knight,
                           CastleSide::None,
                           true)
            .is_valid());
        // castle + promotion (should NOT be legal)
        assert!(!Move::new(Square::from_file_rank(File::F, Rank::_7),
                           Square::from_file_rank(File::G, Rank::_8),
                           Piece::Knight,
                           CastleSide::Kingside,
                           true)
            .is_valid());
    }

    #[test]
    fn move_sq_from() {
        assert_eq!(Move::new(Square::from_file_rank(File::A, Rank::_1),
                             Square::from_file_rank(File::A, Rank::_2),
                             Piece::None,
                             CastleSide::None,
                             false)
                       .sq_from(),
                   Square::from_file_rank(File::A, Rank::_1));
        assert_eq!(Move::new(Square::from_file_rank(File::B, Rank::_2),
                             Square::from_file_rank(File::B, Rank::_3),
                             Piece::None,
                             CastleSide::None,
                             false)
                       .sq_from(),
                   Square::from_file_rank(File::B, Rank::_2));
        assert_eq!(Move::new(Square::from_file_rank(File::H, Rank::_8),
                             Square::from_file_rank(File::G, Rank::_6),
                             Piece::None,
                             CastleSide::None,
                             false)
                       .sq_from(),
                   Square::from_file_rank(File::H, Rank::_8));
    }

    #[test]
    fn move_sq_to() {
        assert_eq!(Move::new(Square::from_file_rank(File::A, Rank::_2),
                             Square::from_file_rank(File::A, Rank::_1),
                             Piece::None,
                             CastleSide::None,
                             false)
                       .sq_to(),
                   Square::from_file_rank(File::A, Rank::_1));
        assert_eq!(Move::new(Square::from_file_rank(File::B, Rank::_3),
                             Square::from_file_rank(File::B, Rank::_2),
                             Piece::None,
                             CastleSide::None,
                             false)
                       .sq_to(),
                   Square::from_file_rank(File::B, Rank::_2));
        assert_eq!(Move::new(Square::from_file_rank(File::G, Rank::_6),
                             Square::from_file_rank(File::H, Rank::_8),
                             Piece::None,
                             CastleSide::None,
                             false)
                       .sq_to(),
                   Square::from_file_rank(File::H, Rank::_8));
    }

    #[test]
    fn move_is_promotion() {
        // Move to 8th rank but NOT promotion
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_7),
                           Square::from_file_rank(File::A, Rank::_8),
                           Piece::None,
                           CastleSide::None,
                           false)
            .is_promotion());
        // Move to 1st rank but NOT promotion
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_2),
                           Square::from_file_rank(File::A, Rank::_1),
                           Piece::None,
                           CastleSide::None,
                           false)
            .is_promotion());
        // White promotion with all possible pieces
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                          Square::from_file_rank(File::A, Rank::_8),
                          Piece::Knight,
                          CastleSide::None,
                          false)
            .is_promotion());
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                          Square::from_file_rank(File::A, Rank::_8),
                          Piece::Bishop,
                          CastleSide::None,
                          false)
            .is_promotion());
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                          Square::from_file_rank(File::A, Rank::_8),
                          Piece::Rook,
                          CastleSide::None,
                          false)
            .is_promotion());
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_7),
                          Square::from_file_rank(File::A, Rank::_8),
                          Piece::Queen,
                          CastleSide::None,
                          false)
            .is_promotion());
        // Black promotion with all possible pieces
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_2),
                          Square::from_file_rank(File::A, Rank::_1),
                          Piece::Knight,
                          CastleSide::None,
                          false)
            .is_promotion());
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_2),
                          Square::from_file_rank(File::A, Rank::_1),
                          Piece::Bishop,
                          CastleSide::None,
                          false)
            .is_promotion());
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_2),
                          Square::from_file_rank(File::A, Rank::_1),
                          Piece::Rook,
                          CastleSide::None,
                          false)
            .is_promotion());
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_2),
                          Square::from_file_rank(File::A, Rank::_1),
                          Piece::Queen,
                          CastleSide::None,
                          false)
            .is_promotion());
    }

    #[test]
    fn move_is_en_passent() {
        // Right squares, NOT en passent
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_5),
                           Square::from_file_rank(File::B, Rank::_6),
                           Piece::None,
                           CastleSide::None,
                           false)
            .is_en_passent());
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_4),
                           Square::from_file_rank(File::B, Rank::_3),
                           Piece::None,
                           CastleSide::None,
                           false)
            .is_en_passent());
        // Right squares, is en passent
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_5),
                          Square::from_file_rank(File::B, Rank::_6),
                          Piece::None,
                          CastleSide::None,
                          true)
            .is_en_passent());
        assert!(Move::new(Square::from_file_rank(File::A, Rank::_4),
                          Square::from_file_rank(File::B, Rank::_3),
                          Piece::None,
                          CastleSide::None,
                          true)
            .is_en_passent());
        // Tests using promotion and castling (to test for side effects).
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_4),
                           Square::from_file_rank(File::A, Rank::_3),
                           Piece::Knight,
                           CastleSide::None,
                           false)
            .is_en_passent());
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_4),
                           Square::from_file_rank(File::A, Rank::_3),
                           Piece::Bishop,
                           CastleSide::None,
                           false)
            .is_en_passent());
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_4),
                           Square::from_file_rank(File::A, Rank::_3),
                           Piece::Rook,
                           CastleSide::None,
                           false)
            .is_en_passent());
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_4),
                           Square::from_file_rank(File::A, Rank::_3),
                           Piece::Queen,
                           CastleSide::None,
                           false)
            .is_en_passent());
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_4),
                           Square::from_file_rank(File::A, Rank::_3),
                           Piece::None,
                           CastleSide::Kingside,
                           false)
            .is_en_passent());
        assert!(!Move::new(Square::from_file_rank(File::A, Rank::_4),
                           Square::from_file_rank(File::A, Rank::_3),
                           Piece::None,
                           CastleSide::Queenside,
                           false)
            .is_en_passent());
    }

    #[test]
    fn move_is_castle() {
        // Basic testing using null moves.
        assert!(!Move::new(Square::from_file_rank(File::E, Rank::_1),
                           Square::from_file_rank(File::G, Rank::_1),
                           Piece::None,
                           CastleSide::None,
                           false)
            .is_castle());
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                          Square::from_file_rank(File::G, Rank::_1),
                          Piece::None,
                          CastleSide::Kingside,
                          false)
            .is_castle());
        assert!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                          Square::from_file_rank(File::C, Rank::_1),
                          Piece::None,
                          CastleSide::Queenside,
                          false)
            .is_castle());
    }

    #[test]
    fn move_castle_side() {
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                             Square::from_file_rank(File::G, Rank::_1),
                             Piece::None,
                             CastleSide::None,
                             false)
                       .castle_side(),
                   CastleSide::None);
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                             Square::from_file_rank(File::G, Rank::_1),
                             Piece::None,
                             CastleSide::Kingside,
                             false)
                       .castle_side(),
                   CastleSide::Kingside);
        assert_eq!(Move::new(Square::from_file_rank(File::E, Rank::_1),
                             Square::from_file_rank(File::C, Rank::_1),
                             Piece::None,
                             CastleSide::Queenside,
                             false)
                       .castle_side(),
                   CastleSide::Queenside);
    }

    #[test]
    fn square_display() {
        assert_eq!(format!("{}", Square(0u8)), "a1");
        assert_eq!(format!("{}", Square(7u8)), "h1");
        assert_eq!(format!("{}", Square(8u8)), "a2");
        assert_eq!(format!("{}", Square(63u8)), "h8");
    }

    #[test]
    fn square_from_string() {
        assert_eq!(Square(0u8), Square::from_string("a1".to_string()).unwrap());
        assert_eq!(Square(7u8), Square::from_string("h1".to_string()).unwrap());
        assert_eq!(Square(8u8), Square::from_string("a2".to_string()).unwrap());
        assert_eq!(Square(63u8), Square::from_string("h8".to_string()).unwrap());

        assert_eq!(Square(0u8), Square::from_string("A1".to_string()).unwrap());
        assert_eq!(Square(7u8), Square::from_string("H1".to_string()).unwrap());

        assert!(Square::from_string("i1".to_string()).is_err());
        assert!(Square::from_string("a0".to_string()).is_err());
        assert!(Square::from_string("a11".to_string()).is_err());
        assert!(Square::from_string(String::new()).is_err());
    }

    #[test]
    fn square_from_file_rank() {
        assert_eq!(Square(0u8), Square::from_file_rank(File::A, Rank::_1));
        assert_eq!(Square(9u8), Square::from_file_rank(File::B, Rank::_2));
        assert_eq!(Square(18u8), Square::from_file_rank(File::C, Rank::_3));
        assert_eq!(Square(27u8), Square::from_file_rank(File::D, Rank::_4));
        assert_eq!(Square(36u8), Square::from_file_rank(File::E, Rank::_5));
        assert_eq!(Square(45u8), Square::from_file_rank(File::F, Rank::_6));
        assert_eq!(Square(54u8), Square::from_file_rank(File::G, Rank::_7));
        assert_eq!(Square(63u8), Square::from_file_rank(File::H, Rank::_8));
    }

    #[test]
    fn move_display() {
        // Regular move
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::B, Rank::_1),
                                     Square::from_file_rank(File::C, Rank::_3),
                                     Piece::None,
                                     CastleSide::None,
                                     false)),
                   "b1-c3");
        // Promotions
        // Knight
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::B, Rank::_7),
                                     Square::from_file_rank(File::B, Rank::_8),
                                     Piece::Knight,
                                     CastleSide::None,
                                     false)),
                   "b7-b8=♘");
        // Bishop
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::B, Rank::_7),
                                     Square::from_file_rank(File::B, Rank::_8),
                                     Piece::Bishop,
                                     CastleSide::None,
                                     false)),
                   "b7-b8=♗");
        // Rook
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::B, Rank::_7),
                                     Square::from_file_rank(File::B, Rank::_8),
                                     Piece::Rook,
                                     CastleSide::None,
                                     false)),
                   "b7-b8=♖");
        // Queen
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::B, Rank::_7),
                                     Square::from_file_rank(File::B, Rank::_8),
                                     Piece::Queen,
                                     CastleSide::None,
                                     false)),
                   "b7-b8=♕");
        // Castling
        // Kingside
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::E, Rank::_1),
                                     Square::from_file_rank(File::G, Rank::_1),
                                     Piece::None,
                                     CastleSide::Kingside,
                                     false)),
                   "O-O");
        // Queenside
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::E, Rank::_8),
                                     Square::from_file_rank(File::C, Rank::_8),
                                     Piece::None,
                                     CastleSide::Queenside,
                                     false)),
                   "O-O-O");
        // En passent
        assert_eq!(format!("{}",
                           Move::new(Square::from_file_rank(File::E, Rank::_5),
                                     Square::from_file_rank(File::D, Rank::_6),
                                     Piece::None,
                                     CastleSide::None,
                                     true)),
                   "e5-d6 e.p.");

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
