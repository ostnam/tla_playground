----------------------------- MODULE tictactoe -----------------------------
EXTENDS Naturals, FiniteSets, TLC, Sequences

Replace(s, idx, val) == [s EXCEPT ![idx] = val]

Board == <<0, 0, 0, 0, 0, 0, 0, 0, 0>>
Indices == (1..9)
\* 1 | 2 | 3
\* 4 | 5 | 6
\* 7 | 8 | 9

Players == 1..2
Step == 0

OppPlayer(player) == IF player = 1 THEN 2 ELSE 1

PossiblePlayerMoves(board) == {x \in Indices: board[x] = 0}
    
HorizontalWin(board, player) == \E x \in {1, 4, 7}: 
    /\ board[x] = board[x+1]
    /\ board[x] = board[x+2]
    /\ board[x] = player

VerticalWin(board, player) == \E x \in 1..3: 
    /\ board[x] = board[x+3]
    /\ board[x] = board[x+6]
    /\ board[x] = player    

DiagonalWin(board, player) == \E x \in {2, 4}:
    /\ board[5] = board[5 - x]
    /\ board[5] = board[5 + x]
    /\ board[5] = player
    
IsWinner(board, player) ==
    \/ HorizontalWin(board, player)
    \/ VerticalWin(board, player)
    \/ DiagonalWin(board, player)
     
GameOver(board) ==
    \/ \A idx \in Indices: board[idx] # 0
    \/ IsWinner(board, 1)
    \/ IsWinner(board, 2)    
    
\* Returns a set of every index which will directly lead to a win for the given player.
WinningMoves(board, player) ==
    LET combinations ==
        {{x, x+1, x+2}: x \in {1, 4, 7}} \union
        {{x, x+3, x+6}: x \in {1, 2, 3}} \union
        {{1, 5, 9}, {3, 5, 7}}
    IN
    LET winning == {
        c \in combinations:
            /\ Cardinality({x \in c: board[x] = 0}) = 1
            /\ Cardinality({x \in c: board[x] = player}) = 2
        }
    IN
    {x \in UNION(winning): board[x] = 0}  

(*
* AI functions.
* They take a board and player, and return 0 if there is no possible move, or the index of a move satisfying their logic. 
*)
WinningMove(board, player) ==
    LET moves == WinningMoves(board, player) IN
    IF Cardinality(moves) = 0
    THEN 0
    ELSE CHOOSE idx \in moves: TRUE
    
BlockOpp(board, player) == WinningMove(board, OppPlayer(player))

Forks(board, player) == {
    x \in Indices:
        /\ board[x] = 0
        /\ Cardinality(WinningMoves(Replace(board, x, player), player)) > 1
}

Makes2InALine(board, player) ==
    LET combinations ==
        {{x, x+1, x+2}: x \in {1, 4, 7}} \union
        {{x, x+3, x+6}: x \in {1, 2, 3}} \union
        {{1, 5, 9}, {3, 5, 7}}
    IN
    LET possible == {
        c \in combinations:
            /\ Cardinality({x \in c: board[x] = 0}) = 2
            /\ Cardinality({x \in c: board[x] = player}) = 1
        }
    IN
    {x \in UNION(possible): board[x] = 0}  

(* Returns whether there's a way to block all opponent forks in a way that makes 2 in a line. *)
WinningBlockingForks(board, player) ==
    LET possible == Makes2InALine(board, player) IN
    {
        x \in possible: Forks(
            Replace(board, x, player),
            OppPlayer(player)
        ) = {}
    }

Fork(board, player) ==
    LET forks == Forks(board, player) IN
    IF forks = {}
    THEN 0
    ELSE CHOOSE x \in forks: TRUE

(* This is the trickiest bit of logic.
  According to wikipedia, if the opp has a fork (play that allows more than 1 way to win), the optimal strategy is to:
     1. If there is only one fork for the opp, block it.
     2. Otherwise, block all forks in a way that simultaneously allows to make two in a line.
     3. Otherwise, make two in a row to force the opponent to defend, as long as it does not result in them producing a fork.
*) 
BlockFork(board, player) ==
    LET opp == OppPlayer(player) IN
    LET opp_forks == Forks(board, opp) IN
    IF Cardinality(opp_forks) = 0
    THEN 0
    ELSE
        LET winning_blocking_forks == WinningBlockingForks(board, player) IN
        IF Cardinality(opp_forks) = 1 
        THEN CHOOSE x \in opp_forks: TRUE
        ELSE IF winning_blocking_forks # {}
        THEN CHOOSE x \in winning_blocking_forks: TRUE
        ELSE
          \* make two in a row that forces a defense which does not create a fork
          LET possible == Makes2InALine(board, player) IN
          LET defense_does_not_create_fork == {
             x \in possible:
               LET after_move == Replace(board, x, player) IN
               LET defense == BlockOpp(after_move, opp) IN
               LET after_defense == Replace(after_move, defense, opp) IN
               Cardinality(WinningMoves(after_defense, opp)) < 2
            }
          IN IF defense_does_not_create_fork = {}
          THEN 0
          ELSE CHOOSE x \in defense_does_not_create_fork: TRUE
    

OppositeCorner(board, player) ==
    LET corner_idx == {1, 3, 7, 9} IN
    LET opp_corner_idx == (1 :> 9 @@ 9 :> 1 @@ 3 :> 7 @@ 7 :> 3) IN
    LET opp_taken == {
        x \in corner_idx:
            /\ board[x] = OppPlayer(player)
            /\ board[opp_corner_idx[x]] = 0
    } IN
    IF opp_taken = {}
    THEN 0
    ELSE opp_corner_idx[CHOOSE x \in opp_taken: TRUE]
    
EmptyCorner(board) ==
    LET corner_idx == {1, 3, 7, 9} IN
    LET playable == corner_idx \intersect PossiblePlayerMoves(board) IN
    IF playable = {}
    THEN 0
    ELSE CHOOSE x \in playable: TRUE

EmptySide(board) ==
    LET side_idx == {2, 4, 6, 8} IN
    IF 0 \in {board[x]: x \in side_idx}
    THEN CHOOSE x \in side_idx: board[x] = 0
    ELSE 0
    
ComputeAiMove(board, player) ==
    CASE WinningMove(board, player) # 0    -> WinningMove(board, player)
      [] BlockOpp(board, player) # 0       -> BlockOpp(board, player)
      [] Fork(board, player) # 0           -> Fork(board, player)
      [] BlockFork(board, player) # 0      -> BlockFork(board, player)
      [] board[5] = 0                      -> 5
      [] OppositeCorner(board, player) # 0 -> OppositeCorner(board, player)
      [] EmptyCorner(board) # 0            -> EmptyCorner(board)
      [] EmptySide(board) # 0              -> EmptySide(board)
    
(*
--algorithm tictactoe

variables
    player \in Players;
    num_round = 1;
    board = Board;
    
define
    AiHasntLost == GameOver(board) => ~IsWinner(board, 2)
end define;

begin
loop:
    while ~GameOver(board) do
      if player = 1 then
        board[ComputeAiMove(board, 1)] := 1;
      else
        with x \in PossiblePlayerMoves(board) do
          board[x] := 2;
        end with;
      end if;
      num_round := num_round + 1;
      player := OppPlayer(player);
    end while;
end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "efa63c7f" /\ chksum(tla) = "f70c1d94")
VARIABLES player, num_round, board, pc

(* define statement *)
AiHasntLost == GameOver(board) => ~IsWinner(board, 2)


vars == << player, num_round, board, pc >>

Init == (* Global variables *)
        /\ player \in Players
        /\ num_round = 1
        /\ board = Board
        /\ pc = "loop"

loop == /\ pc = "loop"
        /\ IF ~GameOver(board)
              THEN /\ IF player = 1
                         THEN /\ board' = [board EXCEPT ![ComputeAiMove(board, 1)] = 1]
                         ELSE /\ \E x \in PossiblePlayerMoves(board):
                                   board' = [board EXCEPT ![x] = 2]
                   /\ num_round' = num_round + 1
                   /\ player' = OppPlayer(player)
                   /\ pc' = "loop"
              ELSE /\ pc' = "Done"
                   /\ UNCHANGED << player, num_round, board >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == loop
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Aug 26 16:03:15 CEST 2024 by mansour
\* Created Tue Jun 11 20:42:01 CEST 2024 by mansour
