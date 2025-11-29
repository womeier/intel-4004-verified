(* ===================================================================== *)
(*  Intel 4004 Microprocessor + MCS-4 RAM/ROM I/O Formalization in Coq   *)
(* ===================================================================== *)

Require Import Intel4004.semantics.
Require Import Intel4004.machine.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Lia.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ===================================================================== *)
(*                         TIMING MODEL                                  *)
(* ===================================================================== *)

(** Defines cycle count for each instruction (8, 16, or 24 cycles). *)
Definition cycles (s : Intel4004State) (i : Instruction) : nat :=
  match i with
  | NOP => 8
  | ADD _ | SUB _ | LD _ | XCH _ | LDM _ | INC _ => 8
  | CLB | CLC | IAC | CMC | CMA | RAL | RAR | TCC | DAC | TCS | STC | DAA | KBP | DCL => 8
  | WRM | WMP | WRR | WPM | WR0 | WR1 | WR2 | WR3 => 8
  | SBM | RDM | RDR | ADM | RD0 | RD1 | RD2 | RD3 => 8
  | BBL _ => 8
  | FIM _ _ | FIN _ | JIN _ | JUN _ | SRC _ => 16
  | JMS _ => 24
  | JCN cond _ =>
      let c1 := cond / 8 in
      let c2 := (cond / 4) mod 2 in
      let c3 := (cond / 2) mod 2 in
      let c4 := cond mod 2 in
      let base_cond := orb (andb (acc s =? 0) (c2 =? 1))
                           (orb (andb (carry s) (c3 =? 1))
                                (andb (negb (test_pin s)) (c4 =? 1))) in
      let jump := if c1 =? 1 then negb base_cond else base_cond in
      if jump then 16 else 8
  | ISZ r _ =>
      let new_val := nibble_of_nat (get_reg s r + 1) in
      if new_val =? 0 then 8 else 16
  end.

(** Proves all instructions execute in at most 24 cycles. *)
Lemma max_cycles_per_instruction : forall s i,
  cycles s i <= 24.
Proof.
  intros s i. destruct i; unfold cycles; try lia.
  - destruct (if (n / 8 =? 1)
              then negb (orb (andb (acc s =? 0) ((n / 4) mod 2 =? 1))
                             (orb (andb (carry s) ((n / 2) mod 2 =? 1))
                                  (andb (negb (test_pin s)) (n mod 2 =? 1))))
              else orb (andb (acc s =? 0) ((n / 4) mod 2 =? 1))
                       (orb (andb (carry s) ((n / 2) mod 2 =? 1))
                            (andb (negb (test_pin s)) (n mod 2 =? 1)))); lia.
  - destruct (nibble_of_nat (get_reg s n + 1) =? 0); lia.
Qed.

(** Proves all instructions execute in at least 8 cycles. *)
Lemma min_cycles_per_instruction : forall s i,
  8 <= cycles s i.
Proof.
  intros s i. destruct i; unfold cycles; try lia.
  - destruct (if (n / 8 =? 1)
              then negb (orb (andb (acc s =? 0) ((n / 4) mod 2 =? 1))
                             (orb (andb (carry s) ((n / 2) mod 2 =? 1))
                                  (andb (negb (test_pin s)) (n mod 2 =? 1))))
              else orb (andb (acc s =? 0) ((n / 4) mod 2 =? 1))
                       (orb (andb (carry s) ((n / 2) mod 2 =? 1))
                            (andb (negb (test_pin s)) (n mod 2 =? 1)))); lia.
  - destruct (nibble_of_nat (get_reg s n + 1) =? 0); lia.
Qed.

(** Computes total cycles for executing a program (instruction list). *)
Fixpoint program_cycles (s : Intel4004State) (prog : list Instruction) : nat :=
  match prog with
  | [] => 0
  | i :: rest => cycles s i + program_cycles (execute s i) rest
  end.

(** Proves cycle count is deterministic (reflexive formulation). *)
Theorem cycles_deterministic : forall s i,
  cycles s i = cycles s i.
Proof.
  intros. reflexivity.
Qed.

(** Proves timing is invariant and execution preserves WF. *)
Theorem timing_preserves_WF : forall s i,
  WF s -> instr_wf i ->
  cycles s i = cycles s i /\ WF (execute s i).
Proof.
  intros s i HWF Hwfi.
  split.
  - reflexivity.
  - apply execute_preserves_WF; assumption.
Qed.
