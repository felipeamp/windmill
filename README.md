# <center>windmill</center>


Welcome to windmill, a new chess engine written exclusively in [Rust](https://www.rust-lang.org).
<br>

### License


Until now, the project still does not have a license. We should choose it at some point (and before this repository becomes public, if it ever does).
<br>

### New Contributors


New people are always welcome, as long they are easy to deal with and can contribute positively to this project.
<br>

### Sources

* [Chess Programming Wiki](https://chessprogramming.wikispaces.com)
* [Stockfish](https://github.com/mcostalba/Stockfish), the second best chess engine in the world (and the best open source)
* [Crabby](https://github.com/Johnson-A/Crabby), one of the first chess engines implemented in Rust (although not feature complete).
<br>
<br>

## <center>Rust Programming Language</center>


### Why Rust?


Rust is a new systems programming language developed by Mozilla. Its three goals are Safety, Speed and Concurrency, which makes it perfect to use in chess engine development. For more information, check [The Rust Book](https://doc.rust-lang.org/book) and [Rust by Example](http://rustbyexample.org).
<br>

### How to install Rust

The best way to install it is to use the rustup installer. Although it is still in beta version, it should work fine.

Download the software in [rustup.rs](https://www.rustup.rs) and install via `rustup install stable`. Rust always has 3 different versions available: stable, beta and nightly. Every 6 weeks the beta version becomes the stable version, the nightly becomes beta and a new nightly is available. One should choose the version desired based on a newest-features-versus-stability tradeoff. When a new version is available, you just need to call `rustup update`.
<br>

### Code Conventions and Hints

* Variables should be named according to the [Rust Language Style Guidelines](https://doc.rust-lang.org/style). In general words, this means lines with up to 99 characters, snake_case for modules, crates, functions and local variables; and CamelCase for Types, Traits, Enums and Type Parameters.

* Before commiting code, you should run `rustfmt` in your code. You should also run the appropriate test cases using cargo test.

* Avoid implicit type coersion (in the rare cases they are allowed).

* If necessary, use `//TODO:` or `//FIXME:`

* Please, **ALWAYS** use meaningful variable names and commit messages

* We should use a CI Tool like [Travis](https://travis-ci.org) to make sure that no commit breaks the code. 

* Use `#[bench]` tests to check for speed and `mem::size_of::<T>` to check a data structure memory size
<br>
<br>

## <center>Implementation</center>


The idea is to first make a working chess playing engine and then focus on making each part of the code better.
<br>

### First Release

- [ ] Basic Data Structures and Debugging code
  - [ ] Bitboard data structure and related methods
  - [ ] Position trait and related data structure (implemented using bitboards)
  - [ ] Game Info data structure (Moves, Player Names, side to move, castle possibilities, en passent possibilities, etc --- similar to a PGN File)
  - [ ] FEN and PGN reader/writer
  - [ ] Move (internal) data structure
  - [ ] Printing a position and/or game in a readable format in stdout
- [ ] Move Generation (should be defined in Position trait and implemented in position data structure)
  - [ ] Hash Tables for Knights and Kings
  - [ ] Sliding pieces (Bishops, Rooks and Queens) using while
  - [ ] Pawn moves, captures and en passent
  - [ ] isCheck, isMate, isPositionLegal, etc
  - [ ] Implement tests with Perft (and also simpler ones, one for each piece/function)
- [ ] Basic Position Evaluation (probably just counting material and checking for mate)
- [ ] Simple Time Management (maybe use a fixed percentage amount)
- [ ] Move Search using Min-max (Negamax version, single threaded, no optimization)
- [ ] UCI Protocol
<br>
<br>

### Enhancements for Future Releases

- [ ] Optimize Move Generation
  - [ ] Magic Move Generation
  - [ ] Use intrinsics (and flag `-C target_cpu=native`) to allow for better code optimization during compilation

- [ ] Optimize Move Search
  - [ ] Alpha-Beta prunning
  - [ ] Multithreading + thread pool
  - [ ] Transposition Table (table is static mut using mutex or spinlocks in each entry, then using unsafe + XOR trick)
  - [ ] Static Exchange Evaluation
  - [ ] Quiescence Search
  - [ ] Iterative Deepening
  - [ ] Principal Variation Search (or negascout)
  - [ ] Null move prunning
  - [ ] Late move reduction
  - [ ] Killer move heuristics
  - [ ] Aspiration window
  - [ ] Futility prunning

- [ ] Optimize Evaluation
  - [ ] Piece-square score
  - [ ] Include strategic notions
  - [ ] Separate evaluation for middlegames and endgames
  - [ ] Parameter Tuning (maybe using spsa or something similar)

- [ ] Better Time Management

- [ ] Endgame Tablebase

- [ ] Others
  - [ ] Faster Hashing for hash tables (maybe use RKISS as RNG)
  - [ ] Cache Line optimizations (try to fit in multiples of 64 bytes)
<br>
<br>

## <center>Benchmarks</center>

* For move generation, use PERFT (see [this](https://chessprogramming.wikispaces.com/Perft) and [this](https://chessprogramming.wikispaces.com/Perft+Results)) to check for correctness and speed

* For parameter tuning, we can implement spsa or something similar (see [this](https://chessprogramming.wikispaces.com/Stockfish's+Tuning+Method) for ideas)

* For game playing ability, just play a lot (thousands) of very fast games (a few seconds per game) between itself to check for improvements, using statistical tests (hypothesis tests + confidence intervals).

* After achieving a good playing ability, we can enter in a chess engine competition (like [TCEC](http://tcec.chessdom.com)) or just upload it in a website (like [ComputerChess.org.uk](http://computerchess.org.uk)) to compare it with other engines.

* We can also (initially) play ourselves against the engine to check its correctness and strength.
