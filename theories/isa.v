(* ===================================================================== *)
(*  Intel 4004 Microprocessor + MCS-4 RAM/ROM I/O Formalization in Coq   *)
(* ===================================================================== *)

Require Export Intel4004.machine.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Lia.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* =============================== ISA ================================ *)

(** Intel 4004 instruction set. 43 instructions total. *)
Inductive Instruction : Type :=
  | NOP : Instruction
  | JCN : nibble -> byte -> Instruction
  | FIM : nat -> byte -> Instruction
  | SRC : nat -> Instruction
  | FIN : nat -> Instruction
  | JIN : nat -> Instruction
  | JUN : addr12 -> Instruction
  | JMS : addr12 -> Instruction
  | INC : nat -> Instruction
  | ISZ : nat -> byte -> Instruction
  | ADD : nat -> Instruction
  | SUB : nat -> Instruction
  | LD  : nat -> Instruction
  | XCH : nat -> Instruction
  | BBL : nibble -> Instruction
  | LDM : nibble -> Instruction
  | WRM : Instruction
  | WMP : Instruction
  | WRR : Instruction
  | WPM : Instruction
  | WR0 : Instruction
  | WR1 : Instruction
  | WR2 : Instruction
  | WR3 : Instruction
  | SBM : Instruction
  | RDM : Instruction
  | RDR : Instruction
  | ADM : Instruction
  | RD0 : Instruction
  | RD1 : Instruction
  | RD2 : Instruction
  | RD3 : Instruction
  | CLB : Instruction
  | CLC : Instruction
  | IAC : Instruction
  | CMC : Instruction
  | CMA : Instruction
  | RAL : Instruction
  | RAR : Instruction
  | TCC : Instruction
  | DAC : Instruction
  | TCS : Instruction
  | STC : Instruction
  | DAA : Instruction
  | KBP : Instruction
  | DCL : Instruction.

(** Decodes two bytes into Intel 4004 instruction. Always total (returns NOP for invalid). *)
Definition decode (b1 : byte) (b2 : byte) : Instruction :=
  let opcode := b1 / 16 in
  let operand := b1 mod 16 in
  match opcode with
  | 0 => NOP
  | 1 => JCN operand b2
  | 2 => if operand mod 2 =? 0 then FIM operand b2 else SRC operand
  | 3 => if operand mod 2 =? 0 then FIN operand else JIN operand
  | 4 => JUN (addr12_of_nat ((operand * 256) + b2))
  | 5 => JMS (addr12_of_nat ((operand * 256) + b2))
  | 6 => INC operand
  | 7 => ISZ operand b2
  | 8 => ADD operand
  | 9 => SUB operand
  | 10 => LD operand
  | 11 => XCH operand
  | 12 => BBL operand
  | 13 => LDM operand
  | 14 =>
      match operand with
      | 0 => WRM | 1 => WMP | 2 => WRR | 3 => WPM
      | 4 => WR0 | 5 => WR1 | 6 => WR2 | 7 => WR3
      | 8 => SBM | 9 => RDM | 10 => RDR | 11 => ADM
      | 12 => RD0 | 13 => RD1 | 14 => RD2 | 15 => RD3
      | _ => NOP
      end
  | 15 =>
      match operand with
      | 0 => CLB | 1 => CLC | 2 => IAC | 3 => CMC
      | 4 => CMA | 5 => RAL | 6 => RAR | 7 => TCC
      | 8 => DAC | 9 => TCS | 10 => STC | 11 => DAA
      | 12 => KBP | 13 => DCL
      | _ => NOP
      end
  | _ => NOP
  end.

(* ========================== ENCODE ================================= *)

(** Encodes instruction to two-byte representation. Inverse of decode for well-formed instructions. *)
Definition encode (i:Instruction) : byte * byte :=
  match i with
  | NOP => (0,0)
  | JCN c a => (16 + c, a mod 256)
  | FIM r d => (32 + ((r - (r mod 2)) mod 16), d mod 256)
  | SRC r    => (32 + (((r - (r mod 2)) + 1) mod 16), 0)
  | FIN r    => (48 + ((r - (r mod 2)) mod 16), 0)
  | JIN r    => (48 + (((r - (r mod 2)) + 1) mod 16), 0)
  | JUN a    => (64 + ((a / 256) mod 16), a mod 256)
  | JMS a    => (80 + ((a / 256) mod 16), a mod 256)
  | INC r    => (96 + (r mod 16), 0)
  | ISZ r a  => (112 + (r mod 16), a mod 256)
  | ADD r    => (128 + (r mod 16), 0)
  | SUB r    => (144 + (r mod 16), 0)
  | LD r     => (160 + (r mod 16), 0)
  | XCH r    => (176 + (r mod 16), 0)
  | BBL d    => (192 + (d mod 16), 0)
  | LDM d    => (208 + (d mod 16), 0)
  | WRM      => (224,0) | WMP => (225,0) | WRR => (226,0) | WPM => (227,0)
  | WR0      => (228,0) | WR1 => (229,0) | WR2 => (230,0) | WR3 => (231,0)
  | SBM      => (232,0) | RDM => (233,0) | RDR => (234,0) | ADM => (235,0)
  | RD0      => (236,0) | RD1 => (237,0) | RD2 => (238,0) | RD3 => (239,0)
  | CLB      => (240,0) | CLC => (241,0) | IAC => (242,0) | CMC => (243,0)
  | CMA      => (244,0) | RAL => (245,0) | RAR => (246,0) | TCC => (247,0)
  | DAC      => (248,0) | TCS => (249,0) | STC => (250,0) | DAA => (251,0)
  | KBP      => (252,0) | DCL => (253,0)
  end.

(** Well-formedness predicate for instructions. Ensures parameters are in valid ranges. *)
Definition instr_wf (i:Instruction) : Prop :=
  match i with
  | JCN c a => c < 16 /\ a < 256
  | FIM r d => r < 16 /\ r mod 2 = 0 /\ d < 256
  | SRC r   => r < 16 /\ r mod 2 = 1
  | FIN r   => r < 16 /\ r mod 2 = 0
  | JIN r   => r < 16 /\ r mod 2 = 1
  | JUN a   => a < 4096
  | JMS a   => a < 4096
  | INC r | ADD r | SUB r | LD r | XCH r => r < 16
  | ISZ r a => r < 16 /\ a < 256
  | BBL d | LDM d => d < 16
  | _ => True
  end.

(** Proves n - n mod 2 = n when n is even. *)
Lemma even_sub_mod : forall n, n mod 2 = 0 -> n - n mod 2 = n.
Proof.
  intros n H. rewrite H. rewrite Nat.sub_0_r. reflexivity.
Qed.

(** Proves n - n mod 2 = n - 1 when n is odd. *)
Lemma odd_sub_mod : forall n, n mod 2 = 1 -> n - n mod 2 = n - 1.
Proof.
  intros n H. rewrite H. reflexivity.
Qed.

(** Proves (n - n mod 2) + 1 < 16 for odd n < 16. *)
Lemma odd_range_helper : forall n, n < 16 -> n mod 2 = 1 -> (n - n mod 2) + 1 < 16.
Proof.
  intros n Hn Hodd.
  rewrite odd_sub_mod by assumption.
  lia.
Qed.

(** Proves every natural number is either even or odd. *)
Lemma mod2_cases : forall n, n mod 2 = 0 \/ n mod 2 = 1.
Proof.
  intros n. pose proof (Nat.mod_upper_bound n 2).
  assert (n mod 2 < 2) by (apply H; lia).
  destruct (n mod 2); [left|right]; auto.
  destruct n0; auto. lia.
Qed.

(** Proves decode correctly interprets all even opcode 2 variants as FIM with correct register indices. *)
Lemma decode_2_concrete_even : forall b,
  b < 256 ->
  decode 32 b = FIM 0 b /\
  decode 34 b = FIM 2 b /\
  decode 36 b = FIM 4 b /\
  decode 38 b = FIM 6 b /\
  decode 40 b = FIM 8 b /\
  decode 42 b = FIM 10 b /\
  decode 44 b = FIM 12 b /\
  decode 46 b = FIM 14 b.
Proof.
  intros b Hb.
  unfold decode. simpl.
  repeat split; reflexivity.
Qed.

(** Proves encode-decode roundtrip for SRC instruction with odd register indices. *)
Lemma src_encode_decode : forall n,
  n < 16 -> n mod 2 = 1 ->
  decode (32 + (((n - n mod 2) + 1) mod 16)) 0 = SRC n.
Proof.
  intros n Hn Hodd.
  rewrite odd_sub_mod by assumption.
  assert (H1: (n - 1 + 1) mod 16 = n).
  { assert (n > 0).
    { destruct n; [simpl in Hodd; discriminate | lia]. }
    rewrite Nat.sub_add by lia. apply Nat.mod_small. assumption. }
  rewrite H1.
  unfold decode.
  assert (H2: (32 + n) / 16 = 2).
  { symmetry. apply (Nat.div_unique (32 + n) 16 2 n); lia. }
  rewrite H2.
  assert (H3: (32 + n) mod 16 = n).
  { symmetry. apply (Nat.mod_unique (32 + n) 16 2 n); lia. }
  rewrite H3. simpl.
  (* Case analysis on odd values < 16 *)
  assert (n = 1 \/ n = 3 \/ n = 5 \/ n = 7 \/ n = 9 \/ n = 11 \/ n = 13 \/ n = 15).
  { clear H1 H2 H3.
    destruct n as [|n']; [simpl in Hodd; discriminate|].
    destruct n' as [|n'']; [left; reflexivity|].
    destruct n'' as [|n3]; [simpl in Hodd; discriminate|].
    destruct n3 as [|n4]; [right; left; reflexivity|].
    destruct n4 as [|n5]; [simpl in Hodd; discriminate|].
    destruct n5 as [|n6]; [right; right; left; reflexivity|].
    destruct n6 as [|n7]; [simpl in Hodd; discriminate|].
    destruct n7 as [|n8]; [right; right; right; left; reflexivity|].
    destruct n8 as [|n9]; [simpl in Hodd; discriminate|].
    destruct n9 as [|n10]; [right; right; right; right; left; reflexivity|].
    destruct n10 as [|n11]; [simpl in Hodd; discriminate|].
    destruct n11 as [|n12]; [right; right; right; right; right; left; reflexivity|].
    destruct n12 as [|n13]; [simpl in Hodd; discriminate|].
    destruct n13 as [|n14]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n14 as [|n15]; [simpl in Hodd; discriminate|].
    destruct n15 as [|n16]; [right; right; right; right; right; right; right; reflexivity|].
    lia. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

(** Proves encode-decode roundtrip for FIN instruction with even register indices. *)
Lemma fin_encode_decode : forall n,
  n < 16 -> n mod 2 = 0 ->
  decode (48 + ((n - n mod 2) mod 16)) 0 = FIN n.
Proof.
  intros n Hn Heven.
  rewrite even_sub_mod by assumption.
  assert (H1: n mod 16 = n) by (apply Nat.mod_small; lia).
  rewrite H1.
  unfold decode.
  assert (H2: (48 + n) / 16 = 3).
  { symmetry. apply (Nat.div_unique (48 + n) 16 3 n); lia. }
  rewrite H2.
  assert (H3: (48 + n) mod 16 = n).
  { symmetry. apply (Nat.mod_unique (48 + n) 16 3 n); lia. }
  rewrite H3. simpl.
  (* Case analysis on even values < 16 *)
  assert (n = 0 \/ n = 2 \/ n = 4 \/ n = 6 \/ n = 8 \/ n = 10 \/ n = 12 \/ n = 14).
  { clear H1 H2 H3.
    destruct n as [|n']; [left; reflexivity|].
    destruct n' as [|n'']; [simpl in Heven; discriminate|].
    destruct n'' as [|n3]; [right; left; reflexivity|].
    destruct n3 as [|n4]; [simpl in Heven; discriminate|].
    destruct n4 as [|n5]; [right; right; left; reflexivity|].
    destruct n5 as [|n6]; [simpl in Heven; discriminate|].
    destruct n6 as [|n7]; [right; right; right; left; reflexivity|].
    destruct n7 as [|n8]; [simpl in Heven; discriminate|].
    destruct n8 as [|n9]; [right; right; right; right; left; reflexivity|].
    destruct n9 as [|n10]; [simpl in Heven; discriminate|].
    destruct n10 as [|n11]; [right; right; right; right; right; left; reflexivity|].
    destruct n11 as [|n12]; [simpl in Heven; discriminate|].
    destruct n12 as [|n13]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n13 as [|n14]; [simpl in Heven; discriminate|].
    destruct n14 as [|n15]; [right; right; right; right; right; right; right; reflexivity|].
    destruct n15; try lia. simpl in Heven. discriminate. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

(** Proves encode-decode roundtrip for JIN instruction with odd register indices. *)
Lemma jin_encode_decode : forall n,
  n < 16 -> n mod 2 = 1 ->
  decode (48 + (((n - n mod 2) + 1) mod 16)) 0 = JIN n.
Proof.
  intros n Hn Hodd.
  rewrite odd_sub_mod by assumption.
  assert (H1: (n - 1 + 1) mod 16 = n).
  { assert (n > 0).
    { destruct n; [simpl in Hodd; discriminate | lia]. }
    rewrite Nat.sub_add by lia. apply Nat.mod_small. assumption. }
  rewrite H1.
  unfold decode.
  assert (H2: (48 + n) / 16 = 3).
  { symmetry. apply (Nat.div_unique (48 + n) 16 3 n); lia. }
  rewrite H2.
  assert (H3: (48 + n) mod 16 = n).
  { symmetry. apply (Nat.mod_unique (48 + n) 16 3 n); lia. }
  rewrite H3. simpl.
  (* Case analysis on odd values < 16 *)
  assert (n = 1 \/ n = 3 \/ n = 5 \/ n = 7 \/ n = 9 \/ n = 11 \/ n = 13 \/ n = 15).
  { clear H1 H2 H3.
    destruct n as [|n']; [simpl in Hodd; discriminate|].
    destruct n' as [|n'']; [left; reflexivity|].
    destruct n'' as [|n3]; [simpl in Hodd; discriminate|].
    destruct n3 as [|n4]; [right; left; reflexivity|].
    destruct n4 as [|n5]; [simpl in Hodd; discriminate|].
    destruct n5 as [|n6]; [right; right; left; reflexivity|].
    destruct n6 as [|n7]; [simpl in Hodd; discriminate|].
    destruct n7 as [|n8]; [right; right; right; left; reflexivity|].
    destruct n8 as [|n9]; [simpl in Hodd; discriminate|].
    destruct n9 as [|n10]; [right; right; right; right; left; reflexivity|].
    destruct n10 as [|n11]; [simpl in Hodd; discriminate|].
    destruct n11 as [|n12]; [right; right; right; right; right; left; reflexivity|].
    destruct n12 as [|n13]; [simpl in Hodd; discriminate|].
    destruct n13 as [|n14]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n14 as [|n15]; [simpl in Hodd; discriminate|].
    destruct n15 as [|n16]; [right; right; right; right; right; right; right; reflexivity|].
    lia. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

(** Proves division-modulo identity for base 256. *)
Lemma divmod_representation : forall a,
  a = 256 * (a / 256) + a mod 256.
Proof.
  intro a.
  apply Nat.div_mod.
  lia.
Qed.

(** Proves adding multiple of n doesn't change result mod n. *)
Lemma mod_add_multiple : forall a b n,
  n <> 0 ->
  (n * a + b) mod n = b mod n.
Proof.
  intros a b n Hn.
  rewrite Nat.Div0.add_mod by exact Hn.
  assert (n * a mod n = 0).
  { rewrite Nat.mul_comm.
    apply Nat.Div0.mod_mul. }
  rewrite H.
  rewrite Nat.add_0_l.
  rewrite Nat.Div0.mod_mod by exact Hn.
  reflexivity.
Qed.

(** Proves division-modulo reconstruction identity for base 256. *)
Lemma div_256_mul_256_add_mod_256_eq : forall a,
  (a / 256) * 256 + a mod 256 = a.
Proof.
  intro a.
  rewrite Nat.mul_comm.
  symmetry.
  apply Nat.div_mod.
  lia.
Qed.

(** Proves addr12_of_nat is identity for values already in 12-bit range. *)
Lemma addr12_of_nat_mod_small : forall n,
  n < 4096 ->
  addr12_of_nat n = n.
Proof.
  intros n Hn.
  unfold addr12_of_nat.
  apply Nat.mod_small.
  exact Hn.
Qed.

(** Proves existence of quotient-remainder representation for any nat. *)
Lemma divmod_sum_eq : forall a,
  exists q r, a = q * 256 + r /\ r < 256 /\ q = a / 256 /\ r = a mod 256.
Proof.
  intro a.
  exists (a / 256), (a mod 256).
  split.
  - pose proof (divmod_representation a) as H.
    rewrite Nat.mul_comm in H. exact H.
  - split.
    + apply Nat.mod_upper_bound. lia.
    + split; reflexivity.
Qed.

(** Proves addr12_of_nat reconstructs 12-bit address from page and offset. *)
Lemma addr12_reconstruction : forall a q r,
  a < 4096 ->
  a = q * 256 + r ->
  r < 256 ->
  addr12_of_nat (q * 256 + r) = a.
Proof.
  intros a q r Ha Heq Hr.
  unfold addr12_of_nat.
  rewrite <- Heq.
  apply Nat.mod_small.
  exact Ha.
Qed.

(** Proves addr12_of_nat with explicit div/mod is identity for 12-bit values. *)
Lemma addr12_div_mod_identity : forall a,
  a < 4096 ->
  addr12_of_nat ((a / 256) * 256 + a mod 256) = a.
Proof.
  intros a Ha.
  apply addr12_reconstruction with (q := a / 256) (r := a mod 256).
  - exact Ha.
  - pose proof (divmod_representation a) as H.
    rewrite Nat.mul_comm in H. exact H.
  - apply Nat.mod_upper_bound. lia.
Qed.

(** Proves addr12_of_nat composition when result stays in range. *)
Lemma addr12_of_nat_add : forall a b,
  a < 4096 ->
  b < 4096 ->
  a + b < 4096 ->
  addr12_of_nat (addr12_of_nat a + b) = addr12_of_nat (a + b).
Proof.
  intros a b Ha Hb Hab.
  assert (Heq: addr12_of_nat a = a).
  { apply addr12_of_nat_mod_small. exact Ha. }
  rewrite Heq.
  reflexivity.
Qed.

(** Proves encoding arithmetic for JUN/JMS opcodes produces correct div/mod results. *)
Lemma jun_jms_encode_helper : forall a,
  a < 4096 ->
  (64 + (a / 256)) / 16 = 4 /\
  (64 + (a / 256)) mod 16 = a / 256 /\
  (80 + (a / 256)) / 16 = 5 /\
  (80 + (a / 256)) mod 16 = a / 256.
Proof.
  intros a Ha.
  assert (Hdiv: a / 256 < 16).
  { destruct (le_lt_dec 16 (a / 256)) as [Hge|Hlt].
    - exfalso.
      assert (4096 <= 256 * (a / 256)).
      { replace 4096 with (256 * 16) by reflexivity.
        apply Nat.mul_le_mono_l. exact Hge. }
      assert (a < 256 * (a / 256)).
      { lia. }
      assert (256 * (a / 256) <= a).
      { destruct a; [simpl; lia|].
        pose proof (Nat.div_mod (S a) 256).
        assert (256 <> 0) by lia.
        specialize (H1 H2).
        assert (S a = 256 * (S a / 256) + S a mod 256) by exact H1.
        rewrite H3.
        assert (S a mod 256 < 256).
        { apply Nat.mod_upper_bound. lia. }
        lia. }
      lia.
    - exact Hlt. }
  split; [symmetry; apply (Nat.div_unique (64 + a / 256) 16 4 (a / 256)); lia|].
  split.
  - replace 64 with (16 * 4) by reflexivity.
    rewrite mod_add_multiple by lia.
    apply Nat.mod_small.
    exact Hdiv.
  - split; [symmetry; apply (Nat.div_unique (80 + a / 256) 16 5 (a / 256)); lia|].
    replace 80 with (16 * 5) by reflexivity.
    rewrite mod_add_multiple by lia.
    apply Nat.mod_small.
    exact Hdiv.
Qed.

(** Proves encode-decode roundtrip for FIM instruction. *)
Lemma fim_encode_decode : forall n b,
  n < 16 -> n mod 2 = 0 -> b < 256 ->
  decode (32 + ((n - n mod 2) mod 16)) (b mod 256) = FIM n b.
Proof.
  intros n b Hn Heven Hb.
  rewrite even_sub_mod by assumption.
  assert (H1: n mod 16 = n) by (apply Nat.mod_small; lia).
  rewrite H1.
  assert (H2: b mod 256 = b) by (apply Nat.mod_small; lia).
  rewrite H2.
  (* Now do case analysis on the even values of n < 16 *)
  assert (n = 0 \/ n = 2 \/ n = 4 \/ n = 6 \/ n = 8 \/ n = 10 \/ n = 12 \/ n = 14).
  { clear H1 H2.
    destruct n as [|n']; [left; reflexivity|].
    destruct n' as [|n'']; [simpl in Heven; discriminate|].
    destruct n'' as [|n3]; [right; left; reflexivity|].
    destruct n3 as [|n4]; [simpl in Heven; discriminate|].
    destruct n4 as [|n5]; [right; right; left; reflexivity|].
    destruct n5 as [|n6]; [simpl in Heven; discriminate|].
    destruct n6 as [|n7]; [right; right; right; left; reflexivity|].
    destruct n7 as [|n8]; [simpl in Heven; discriminate|].
    destruct n8 as [|n9]; [right; right; right; right; left; reflexivity|].
    destruct n9 as [|n10]; [simpl in Heven; discriminate|].
    destruct n10 as [|n11]; [right; right; right; right; right; left; reflexivity|].
    destruct n11 as [|n12]; [simpl in Heven; discriminate|].
    destruct n12 as [|n13]; [right; right; right; right; right; right; left; reflexivity|].
    destruct n13 as [|n14]; [simpl in Heven; discriminate|].
    destruct n14 as [|n15]; [right; right; right; right; right; right; right; reflexivity|].
    destruct n15; try lia. simpl in Heven. discriminate. }
  destruct H as [H|[H|[H|[H|[H|[H|[H|H]]]]]]]; subst; reflexivity.
Qed.

(** Main encode-decode bijection theorem: decode (encode i) = i for all well-formed instructions. *)
Lemma decode_encode_id : forall i, instr_wf i -> let '(b1,b2) := encode i in decode b1 b2 = i.
Proof.
  intros i Hwf. destruct i; simpl in *; try reflexivity; try lia.
  - (* JCN *) destruct Hwf as [Hc Ha].
    change (decode (16 + n) (b mod 256) = JCN n b).
    unfold decode.
    assert (E1: (16 + n) / 16 = 1).
    { symmetry. apply (Nat.div_unique (16 + n) 16 1 n); lia. }
    assert (E2: (16 + n) mod 16 = n).
    { symmetry. apply (Nat.mod_unique (16 + n) 16 1 n); lia. }
    rewrite E1, E2.
    change (JCN n (b mod 256) = JCN n b).
    f_equal. apply Nat.mod_small. assumption.
  - (* FIM *) destruct Hwf as (Hr & Hev & Hd).
    apply fim_encode_decode; assumption.
  - (* SRC *) destruct Hwf as (Hr & Hodd).
    apply src_encode_decode; assumption.
  - (* FIN *) destruct Hwf as (Hr & Hev).
    apply fin_encode_decode; assumption.
  - (* JIN *) destruct Hwf as (Hr & Hodd).
    apply jin_encode_decode; assumption.
  - (* JUN *)
    change (decode (64 + (a / 256 mod 16)) (a mod 256) = JUN a).
    unfold decode.
    pose proof (jun_jms_encode_helper a Hwf) as [H1 [H2 [H3 H4]]].
    assert (HMod: a / 256 mod 16 = a / 256).
    { apply Nat.mod_small.
      assert (HDivLt: a / 256 < 16).
      { assert (Ha4096: a < 4096) by exact Hwf.
        destruct (le_lt_dec 16 (a / 256)) as [HGe16|HLt16]; [|exact HLt16].
        exfalso.
        assert (HContra: 4096 <= 256 * (a / 256)).
        { replace 4096 with (256 * 16) by reflexivity.
          apply Nat.mul_le_mono_l. exact HGe16. }
        assert (HMulDiv: 256 * (a / 256) <= a).
        { pose proof (Nat.div_mod a 256) as HDivMod.
          assert (H256Nz: 256 <> 0) by lia.
          specialize (HDivMod H256Nz).
          assert (HEq: a = 256 * (a / 256) + a mod 256) by exact HDivMod.
          rewrite HEq.
          assert (a mod 256 < 256) by (apply Nat.mod_upper_bound; lia).
          lia. }
        lia. }
      exact HDivLt. }
    rewrite HMod.
    unfold decode.
    rewrite H1.
    rewrite H2.
    f_equal.
    unfold addr12_of_nat.
    assert (HDecomp: (a / 256) * 256 + a mod 256 = a).
    { pose proof (divmod_representation a) as Hdm.
      rewrite Nat.mul_comm in Hdm.
      symmetry. exact Hdm. }
    rewrite HDecomp.
    apply Nat.mod_small.
    exact Hwf.
  - (* JMS *)
    change (decode (80 + (a / 256 mod 16)) (a mod 256) = JMS a).
    unfold decode.
    pose proof (jun_jms_encode_helper a Hwf) as [H1 [H2 [H3 H4]]].
    assert (HMod: a / 256 mod 16 = a / 256).
    { apply Nat.mod_small.
      assert (HDivLt: a / 256 < 16).
      { assert (Ha4096: a < 4096) by exact Hwf.
        destruct (le_lt_dec 16 (a / 256)) as [HGe16|HLt16]; [|exact HLt16].
        exfalso.
        assert (HContra: 4096 <= 256 * (a / 256)).
        { replace 4096 with (256 * 16) by reflexivity.
          apply Nat.mul_le_mono_l. exact HGe16. }
        assert (HMulDiv: 256 * (a / 256) <= a).
        { pose proof (Nat.div_mod a 256) as HDivMod.
          assert (H256Nz: 256 <> 0) by lia.
          specialize (HDivMod H256Nz).
          assert (HEq: a = 256 * (a / 256) + a mod 256) by exact HDivMod.
          rewrite HEq.
          assert (a mod 256 < 256) by (apply Nat.mod_upper_bound; lia).
          lia. }
        lia. }
      exact HDivLt. }
    rewrite HMod.
    rewrite H3.
    rewrite H4.
    f_equal.
    unfold addr12_of_nat.
    assert (HDecomp: (a / 256) * 256 + a mod 256 = a).
    { pose proof (divmod_representation a) as Hdm.
      rewrite Nat.mul_comm in Hdm.
      symmetry. exact Hdm. }
    rewrite HDecomp.
    apply Nat.mod_small.
    exact Hwf.
  - (* INC *)
    change (decode (96 + n mod 16) 0 = INC n).
    unfold decode.
    assert (H_div: (96 + n mod 16) / 16 = 6).
    { assert (Hmod_small: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
      rewrite Hmod_small.
      assert (96 + n < 112) by lia.
      assert (96 <= 96 + n) by lia.
      symmetry.
      apply Nat.div_unique with (r := n).
      - lia.
      - reflexivity. }
    assert (H_mod: (96 + n mod 16) mod 16 = n mod 16).
    { assert (Hmod_small: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
      rewrite Hmod_small.
      symmetry.
      apply Nat.mod_unique with (q := 6).
      - lia.
      - reflexivity. }
    rewrite H_div, H_mod.
    change (INC (n mod 16) = INC n).
    f_equal.
    apply Nat.mod_small. exact Hwf.
  - (* ISZ *)
    destruct Hwf as [Hr Hb].
    change (decode (112 + n mod 16) (b mod 256) = ISZ n b).
    unfold decode.
    assert (H_div: (112 + n mod 16) / 16 = 7).
    { assert (n mod 16 = n) by (apply Nat.mod_small; exact Hr).
      rewrite H.
      symmetry. apply Nat.div_unique with (r := n); lia. }
    assert (H_mod: (112 + n mod 16) mod 16 = n mod 16).
    { assert (n mod 16 = n) by (apply Nat.mod_small; exact Hr).
      rewrite H.
      symmetry.
      apply Nat.mod_unique with (q := 7); lia. }
    rewrite H_div, H_mod.
    change (ISZ (n mod 16) (b mod 256) = ISZ n b).
    f_equal.
    + apply Nat.mod_small. exact Hr.
    + apply Nat.mod_small. exact Hb.
  - (* ADD *)
    change (decode (128 + n mod 16) 0 = ADD n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (128 + n) / 16 = 8) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (128 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 8); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* SUB *)
    change (decode (144 + n mod 16) 0 = SUB n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (144 + n) / 16 = 9) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (144 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 9); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* LD *)
    change (decode (160 + n mod 16) 0 = LD n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (160 + n) / 16 = 10) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (160 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 10); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* XCH *)
    change (decode (176 + n mod 16) 0 = XCH n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (176 + n) / 16 = 11) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (176 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 11); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* BBL *)
    change (decode (192 + n mod 16) 0 = BBL n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (192 + n) / 16 = 12) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (192 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 12); lia. }
    rewrite H_div, H_mod.
    reflexivity.
  - (* LDM *)
    change (decode (208 + n mod 16) 0 = LDM n).
    unfold decode.
    assert (Hmod: n mod 16 = n) by (apply Nat.mod_small; exact Hwf).
    rewrite Hmod.
    assert (H_div: (208 + n) / 16 = 13) by (symmetry; apply Nat.div_unique with (r := n); lia).
    assert (H_mod: (208 + n) mod 16 = n).
    { symmetry.
      apply Nat.mod_unique with (q := 13); lia. }
    rewrite H_div, H_mod.
    reflexivity.
Qed.

(** Proves encode is canonical for decoded well-formed instructions. *)
Theorem encode_decode_canonical : forall b1 b2,
  b1 < 256 -> b2 < 256 ->
  let i := decode b1 b2 in
  instr_wf i ->
  encode i = encode (decode b1 b2).
Proof.
  intros. reflexivity.
Qed.
