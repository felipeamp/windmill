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

impl Square {
    pub fn file(&self) -> File {
        match self.0 % 8 {
            0 => File::H,
            1 => File::G,
            2 => File::F,
            3 => File::E,
            4 => File::D,
            5 => File::C,
            6 => File::B,
            7 => File::A,
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
/// Note that, if we need to create a NULL_MOVE, we can use 0 (since there is no
/// legal move where the origin and destination squares are the same).
///
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Move(u16);

/// Empty/Null `Move`
pub const NULL_MOVE: Move = Move(0);
pub const PROMOTION_FLAG: u16 = 1 << 14;
pub const EN_PASSENT_FLAG: u16 = 1 << 15;
pub const CASTLING_FLAG: u16 = 0b11 << 14;

// TODO: implement methods (and their documentation) to edit moves and to get the
// information inside. Only use bitwise operations, avoid creating Square, Rank and File enums
// (it is ok to use them if they were an argument to the method)
impl Move {
    pub fn new(from_sq: Square, to_sq: Square, promoted_piece: Piece, castle_side: CastleSide,
               is_en_passent: bool) -> Move {
        assert!(from_sq.0 < 64);
        assert!(to_sq.0 < 64);
        let mut ret = Move(from_sq.0 as u16 | ((to_sq.0 as u16) << 6 ));
        match promoted_piece {
            Piece::None => (),
            Piece::Knight => ret.0 |= PROMOTION_FLAG,
            Piece::Bishop => ret.0 |= (1 << 12) | PROMOTION_FLAG,
            Piece::Rook => ret.0 |= (2 << 12) | PROMOTION_FLAG,
            Piece::Queen => ret.0 |= (3 << 12) | PROMOTION_FLAG,
            piece @ _ => panic!(format!("Invalid promoted piece: {}", piece)),
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

    pub fn is_valid_move(&self) -> bool {
        let from_sq = self.from_sq();
        let to_sq = self.to_sq();
        let from_sq_rank = from_sq.rank();
        let from_sq_file = from_sq.file();
        let to_sq_rank = to_sq.rank();
        let to_sq_file = to_sq.file();
        let castle_side = self.castle_side();
        let is_castle = self.is_castle();
        let is_promotion = self.is_promotion();
        let is_en_passent = self.is_en_passent();
        // Wrong promotion squares
        if is_promotion &&
            ((from_sq_rank != Rank::_2 && from_sq_rank != Rank::_7) ||
             (to_sq_rank != Rank::_1 && to_sq_rank != Rank::_8)) {
            return false;
        }
        // Wrong castle squares
        if is_castle &&
            ((from_sq_rank != Rank::_1 && from_sq_rank != Rank::_8) ||
             (to_sq_rank != Rank::_1 && to_sq_rank != Rank::_8) ||
             from_sq_file != File::E ||
             (to_sq_file != File::C && to_sq_file != File::G)) {
            return false;
        }
        // Wrong castle side
        if is_castle &&
            ((castle_side == CastleSide::Kingside && to_sq_file != File::G) ||
             (castle_side == CastleSide::Queenside && to_sq_file != File::C)) {
            return false;
        }
        // Wrong en passent squares
        if is_en_passent &&
            ((from_sq_rank != Rank::_4 && from_sq_rank != Rank::_5) ||
             (to_sq_rank == Rank::_3 && to_sq_rank != Rank::_6)) {
            return false;
        }
        // Incompatible flags
        if (is_en_passent && is_castle) ||
            (is_en_passent && is_promotion) ||
            (is_castle && is_promotion) {
            return false;
        }
        // No promotion flag with promoting piece
        if !is_en_passent && (self.0 & (0b11 << 12)) != 0 {
            return false;
        }
        // Same from and to squares
        from_sq != to_sq
    }

    pub fn from_sq(&self) -> Square {
        unimplemented!();
    }

    pub fn to_sq(&self) -> Square {
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

    pub fn castle_side(&self) -> CastleSide {
        // se flag for nula, retorna CastleSide::None, senão retorna pela coluna que foi.
        unimplemented!();
    }

    pub fn promoted_piece(&self) -> Piece {
        // se flag de promoção for false, retorna Piece::None, senão retorna pelo match
        // cuidado pois o cavalo tem entrada 0, que é igual a quando não é promoção
        unimplemented!();
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
    #[should_panic]
    fn move_creation() {
        unimplemented!();
        // lance vazio
        // lance com cada um dos squares com valor grande demais (> 63) -> panic
        // lance normal
        // en passent com as 2 cores
        // roque pros 2 lados com as 2 cores
        // promoção pra todos os tipos de peça
        // promoção com captura
    }

    #[test]
    #[should_panic]
    fn move_is_valid() {
        unimplemented!();
        // cada um dos lances acima deveria passar, exceto vazio e square errado (panic)
        // lance com de e para iguais (não nulos)
        // roque de e para a casa (rank & file) errada, pros 2 lados com as 2 cores
        // en passent de e para a casa(rank & file) errada, pros 2 lados com as 2 cores
        // promoção de e para a casa (rank) errada
        // mistura de flags impossíveis (en passent + castle,
        // en passent + promotion, castle + promotion, todos)
        // não promoção com peça de promoção não nula
    }

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
    #[should_panic]
    fn move_display() {
        unimplemented!();
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