# impartial
A proof of the Sprague-Grundy theorem and other results related to impartial games in Lean

This repository consists of 3 files, `src/position.lean`, `src/impartial.lean` and `src/nim.lean`

## `position.lean`
This includes definitions and basic facts about P-, N-, L- and R-positions, i.e. sating who has a winning stratergy for a game, no matter who starts.

## `impartial.lean`
Here I define an impartial game which I have defined as a game which is equivalent to its negative and all subsequent games are also impartial. This file also shows that the positions defined in earlier become much simpler for impartial games and can be used to show equivalence.

## `nim.lean`
This is where the game of nim is defined for any ordinal. It also contains the proof of the Sprague-Grundy theorem, that every impartial game is equivalent to a game of nim for some ordinal, named the Grundy value of the game.
