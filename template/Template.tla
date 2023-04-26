------------------------------ MODULE Template ------------------------------- 
(***************************************************************************)
(*
 * @author Polo (119010079@link.cuhk.edu.cn)
 * @brief
 * @version 0.1
 * @date 2023-04-26
 *
 * @copyright Copyright (c) 2023 The n-hop technologies Limited. All Rights
 * Reserved.
 *
 *)

(* This file is an intro to TLA. For Aesthetics, we write these as comments*)
(* We can also copy this template and cfg when writing other TLA scripts   *)
(*   [Tower of Hanoi]<<https://en.wikipedia.org/wiki/Tower_of_Hanoi>>      *)
(*                                                                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences
  (*************************************************************************)
  (* This statement imports the definitions of the ordinary operators on   *)
  (* natural numbers, such as +.                                           *)
  (*************************************************************************)
  
(***************************************************************************)
(* We next declare the specification's variables.                          *)
(***************************************************************************)

(* The key of TLA is Abstraction. In Hanoi tower, 
The Objects are peg and disks: '''VARIABLES peg1, peg2, peg3, disks'''
The Operations are moving disks between pegs orderly.
It's natural to view pegs as sequence (ordered set)
But we can also label each peg with peak,length instead.
The key is all about what does the state transfer functions look like      *)


VARIABLES peg1, peg2, peg3

Init == /\ peg1 = <<1,2,3>>
        /\ peg2 = <<>>
        /\ peg3 = <<>>

(* Now we find that disks are not necessarily objects. You can even regard disks
as rules of moving.
*)

(* Here Notice that the short-circuit law seems not working
I guess it needs parsing the expression first, then evaluate it.
.*)

Movepeg1 == \/  /\  \/ Len(peg2) = 0 
                    \/ /\ Len(peg2) # 0
                       /\ Head(peg1) < Head(peg2)
                /\  peg1' = Tail(peg1) 
                /\  peg2' = <<Head(peg1)>> \o peg2
                /\  peg3' = peg3
            
            \/  /\  \/ Len(peg3) = 0
                    \/ /\ Len(peg3) # 0
                       /\ Head(peg1) < Head(peg3)
                /\  peg1' = Tail(peg1)
                /\  peg2' = peg2
                /\  peg3' = <<Head(peg1)>> \o peg3
            
            \/  /\  /\ Len(peg1) # 0
                    /\ Len(peg2) # 0
                    /\ Len(peg3) # 0
                    /\ Head(peg1) > Head(peg2)
                    /\ Head(peg1) > Head(peg3)
                /\  peg1' = peg1
                /\  peg2' = peg2
                /\  peg3' = peg3

Movepeg2 == \/  /\  \/ Len(peg1) = 0
                    \/ /\ Len(peg1) # 0 
                        /\ Head(peg2) < Head(peg1) 
                /\  peg1' = <<Head(peg2)>> \o peg1
                /\  peg2' = Tail(peg2)
                /\  peg3' = peg3
            
            \/  /\  \/ Len(peg3) = 0
                    \/ /\ Len(peg3) # 0
                       /\ Head(peg2) < Head(peg3)
                /\  peg1' = peg1
                /\  peg2' = Tail(peg2)
                /\  peg3' = <<Head(peg2)>> \o peg3
            
            \/  /\  /\ Len(peg1) # 0
                    /\ Len(peg2) # 0
                    /\ Len(peg3) # 0
                    /\ Head(peg2) > Head(peg1)
                    /\ Head(peg2) > Head(peg3)
                /\  peg1' = peg1
                /\  peg2' = peg2
                /\  peg3' = peg3

Movepeg3 == \/  /\  \/ Len(peg1) = 0
                    \/ /\ Len(peg1) # 0
                       /\ Head(peg3) < Head(peg1)
                /\  peg1' = <<Head(peg3)>> \o peg1
                /\  peg2' = peg2
                /\  peg3' = Tail(peg3)

            \/  /\  \/ Len(peg2) = 0
                    \/ /\ Len(peg2) # 0
                       /\ Head(peg3) < Head(peg2)
                /\  peg1' = peg1
                /\  peg2' = <<Head(peg3)>> \o peg2
                /\  peg3' = Tail(peg3)

            \/  /\  /\ Len(peg1) # 0
                    /\ Len(peg2) # 0
                    /\ Len(peg3) # 0
                    /\ Head(peg3) > Head(peg1)
                    /\ Head(peg3) > Head(peg2)
                /\  peg1' = peg1
                /\  peg2' = peg2
                /\  peg3' = peg3




Next == \/  /\ Len(peg1) # 0
            /\ Movepeg1
        \/  /\ Len(peg2) # 0
            /\ Movepeg2
        \/  /\ Len(peg3) # 0
            /\ Movepeg3

(* You can add invariants here to constraint the states of peg
such as: at every state, the concat of pegs should equal to {1,2,3} *)        


Spec == Init /\ [][Next]_<<peg1, peg2, peg3>>

FinalState == /\ peg1 = <<>>
              /\ peg2 = <<>>
              /\ peg3 = <<1,2,3>>

NotSolved == ~FinalState

=============================================================================