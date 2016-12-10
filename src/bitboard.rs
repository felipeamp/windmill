//! This file should have all details related to a bitboard struct.
//!
//! It should include (at least) the following methods:
//! * new (static)
//! * Display trait
//! * Iterator over ones
//! * least and most significant bits
//! * population count
//!
//! and the following consts:
//! * Dark squares (contained in an array)
//! * Files A ... H (and also contained in an array)
//! * Rank 1 ... 8 (and also contained in an array)
//! * Square a1 ... h8 (contained in an array)
//! * Adjacent File (used for pawns)
//! * In front (used for pawns)
//! * Between (contained in an array)
//! * Line (contained in an array)
//! * Forward (contained in an array)
//! * Passed pawn mask (contained in an array)
//! * Pawn attacked squares (contained in an array)
//! * Square distance (contained in an array)
//!
//! and all binary operators.
//!
//! Later it should also contain Magic Moves details and basic endgame tablebase.

use std::collections::VecDeque;
use std::fmt;
use std::iter::*;

use types::*;

/// Struct for Bitboard.
///
/// Since we still can't implement a trait for a type alias, we need
/// a tuple struct here. It's not elegant, but it works.
///
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub struct Bitboard(pub u64);

pub const EMPTY_BITBOARD: Bitboard = Bitboard(0);
pub const BITBOARD_STRING_SIZE: usize = 578;

impl Bitboard {
    pub fn from_square(sq: &Square) -> Bitboard {
        Bitboard(1 << sq.0)
    }

    pub fn from_squares(squares: &VecDeque<Square>) -> Bitboard {
        let val = squares.iter().fold(0u64, |acc, &sq| acc | (1 << sq.0));
        Bitboard(val)
    }

    pub fn pop_count(&self) -> u32 {
        self.0.count_ones()
    }

    pub fn lsb_bb(&self) -> Bitboard {
        if self.0 == 0 {
            return Bitboard(0);
        }
        Bitboard(1 << self.0.trailing_zeros())
    }

    /// Assumes the bitboard is non-empty
    pub fn lsb_sq(&self) -> Square {
        assert!(self.0 != 0);
        Square(self.0.trailing_zeros() as u8)
    }

    pub fn msb_bb(&self) -> Bitboard {
        if self.0 == 0 {
            return Bitboard(0);
        }
        Bitboard(1 << (63 - self.0.leading_zeros()))
    }

    /// Assumes the bitboard is non-empty
    pub fn msb_sq(&self) -> Square {
        assert!(self.0 != 0);
        Square((63 - self.0.leading_zeros()) as u8)
    }
}

/// Prints the bitboard in a visually understandable form.
impl fmt::Display for Bitboard {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut s = String::with_capacity(BITBOARD_STRING_SIZE);
        s.push_str("+---+---+---+---+---+---+---+---+\n");
        for rank in (0..8).rev() {
            for file in 0..8 {
                if (self.0 & (1 << (8 * rank + file))) != 0 {
                    s.push_str("| X ");
                } else {
                    s.push_str("|   ");
                }
            }
            s.push_str("|\n+---+---+---+---+---+---+---+---+\n");
        }
        write!(f, "{}", s)
    }
}

impl Iterator for Bitboard {
    type Item = Square;

    fn next(&mut self) -> Option<Square> {
        if self.0 == 0 {
            return None;
        }
        let lsb_sq = self.lsb_sq();
        self.0 ^= Bitboard::from_square(&lsb_sq).0;
        Some(lsb_sq)
    }
}


#[cfg(test)]
mod tests {
    use std::collections::VecDeque;
    use std::panic;
    use std::vec::*;

    use super::*;
    use types::*;

    #[test]
    fn bitboard_from_square() {
        assert_eq!(Bitboard(1),
                   Bitboard::from_square(&Square::from_file_rank(File::A, Rank::_1)));
        assert_eq!(Bitboard(1 << 7),
                   Bitboard::from_square(&Square::from_file_rank(File::H, Rank::_1)));
        assert_eq!(Bitboard(1 << 63),
                   Bitboard::from_square(&Square::from_file_rank(File::H, Rank::_8)));
    }

    #[test]
    fn bitboard_from_squares() {
        let mut squares = VecDeque::new();
        {
            assert_eq!(Bitboard(0), Bitboard::from_squares(&squares));
        }
        squares.push_back(Square::from_file_rank(File::A, Rank::_1));
        {
            assert_eq!(Bitboard(1), Bitboard::from_squares(&squares));
        }
        squares.push_back(Square::from_file_rank(File::A, Rank::_1));
        squares.push_back(Square::from_file_rank(File::A, Rank::_1));
        {
            assert_eq!(Bitboard(1), Bitboard::from_squares(&squares));
        }
        squares.push_back(Square::from_file_rank(File::H, Rank::_1));
        squares.push_back(Square::from_file_rank(File::H, Rank::_8));
        {
            assert_eq!(Bitboard(1 | (1 << 7) | (1 << 63)),
                       Bitboard::from_squares(&squares));
        }
    }

    #[test]
    fn bitboard_pop_count() {
        assert_eq!(Bitboard(0).pop_count(), 0);
        assert_eq!(Bitboard(1).pop_count(), 1);
        assert_eq!(Bitboard(1 << 8).pop_count(), 1);
        assert_eq!(Bitboard((1 << 8) | 1).pop_count(), 2);
        assert_eq!(Bitboard(!0).pop_count(), 64);
    }

    #[test]
    fn bitboard_lsb_bb() {
        assert_eq!(Bitboard(0).lsb_bb(), Bitboard(0));
        assert_eq!(Bitboard(1).lsb_bb(), Bitboard(1));
        assert_eq!(Bitboard(1 << 8).lsb_bb(), Bitboard(1 << 8));
        assert_eq!(Bitboard((1 << 8) | 1).lsb_bb(), Bitboard(1));
        assert_eq!(Bitboard(!0).lsb_bb(), Bitboard(1));
    }

    #[test]
    fn bitboard_lsb_sq() {
        assert!(panic::catch_unwind(|| Bitboard(0).lsb_sq()).is_err());
        assert_eq!(Bitboard(1).lsb_sq(),
                   Square::from_file_rank(File::A, Rank::_1));
        assert_eq!(Bitboard(1 << 8).lsb_sq(),
                   Square::from_file_rank(File::A, Rank::_2));
        assert_eq!(Bitboard((1 << 8) | 1).lsb_sq(),
                   Square::from_file_rank(File::A, Rank::_1));
        assert_eq!(Bitboard(!0).lsb_sq(),
                   Square::from_file_rank(File::A, Rank::_1));
    }

    #[test]
    fn bitboard_msb_bb() {
        assert_eq!(Bitboard(0).msb_bb(), Bitboard(0));
        assert_eq!(Bitboard(1).msb_bb(), Bitboard(1));
        assert_eq!(Bitboard(1 << 8).msb_bb(), Bitboard(1 << 8));
        assert_eq!(Bitboard((1 << 8) | 1).msb_bb(), Bitboard(1 << 8));
        assert_eq!(Bitboard(!0).msb_bb(), Bitboard(1 << 63));
    }

    #[test]
    fn bitboard_msb_sq() {
        assert!(panic::catch_unwind(|| Bitboard(0).msb_sq()).is_err());
        assert_eq!(Bitboard(1).msb_sq(),
                   Square::from_file_rank(File::A, Rank::_1));
        assert_eq!(Bitboard(1 << 8).msb_sq(),
                   Square::from_file_rank(File::A, Rank::_2));
        assert_eq!(Bitboard((1 << 8) | 1).msb_sq(),
                   Square::from_file_rank(File::A, Rank::_2));
        assert_eq!(Bitboard(!0).msb_sq(),
                   Square::from_file_rank(File::H, Rank::_8));
    }

    #[test]
    fn bitboard_display() {
        let mut squares = VecDeque::new();
        {
            assert_eq!(format!("{}", Bitboard::from_squares(&squares)).len(),
                       BITBOARD_STRING_SIZE);
            assert_eq!(format!("{}", Bitboard::from_squares(&squares)), {
                let mut s = String::with_capacity(BITBOARD_STRING_SIZE);
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s
            })
        }
        squares.push_back(Square::from_file_rank(File::A, Rank::_1));
        {
            assert_eq!(format!("{}", Bitboard::from_squares(&squares)), {
                let mut s = String::with_capacity(BITBOARD_STRING_SIZE);
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("| X |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s
            })
        }
        squares.push_back(Square::from_file_rank(File::H, Rank::_8));
        squares.push_back(Square::from_file_rank(File::H, Rank::_8));
        {
            assert_eq!(format!("{}", Bitboard::from_squares(&squares)), {
                let mut s = String::with_capacity(BITBOARD_STRING_SIZE);
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   | X |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("| X |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s
            })
        }
        squares.push_back(Square::from_file_rank(File::C, Rank::_3));
        {
            assert_eq!(format!("{}", Bitboard::from_squares(&squares)), {
                let mut s = String::with_capacity(BITBOARD_STRING_SIZE);
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   | X |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   | X |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("|   |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s.push_str("| X |   |   |   |   |   |   |   |\n");
                s.push_str("+---+---+---+---+---+---+---+---+\n");
                s
            })
        }
    }

    #[test]
    fn bitboard_iterator() {
        assert_eq!(Bitboard(0).collect::<Vec<_>>(), Vec::new());
        assert_eq!(Bitboard(1).collect::<Vec<_>>(),
                   vec![Square::from_file_rank(File::A, Rank::_1)]);
        assert_eq!(Bitboard(1 | (1 << 8)).collect::<Vec<_>>(),
                   vec![Square::from_file_rank(File::A, Rank::_1),
                        Square::from_file_rank(File::A, Rank::_2)]);
    }
}
