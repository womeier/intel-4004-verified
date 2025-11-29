Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Lia.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ===================== Basic bit-width types ======================== *)

(** Type alias for 4-bit values (0-15). No inherent bounds enforcement. *)
Definition nibble := nat.

(** Normalizes arbitrary nat to 4-bit range via mod 16. *)
Definition nibble_of_nat (n : nat) : nibble := n mod 16.

(** Type alias for 8-bit values (0-255). No inherent bounds enforcement. *)
Definition byte := nat.

(** Normalizes arbitrary nat to 8-bit range via mod 256. *)
Definition byte_of_nat (n : nat) : byte := n mod 256.

(** Type alias for 12-bit addresses (0-4095). No inherent bounds enforcement. *)
Definition addr12 := nat.

(** Normalizes arbitrary nat to 12-bit address space via mod 4096. *)
Definition addr12_of_nat (n : nat) : addr12 := n mod 4096.

(** Proves addr12_of_nat always produces values strictly less than 4096. *)
Lemma addr12_bound : forall n, addr12_of_nat n < 4096.
Proof.
  intro n. unfold addr12_of_nat. apply Nat.mod_upper_bound. lia.
Qed.

(** Proves nibble_of_nat always produces values strictly less than 16. *)
Lemma nibble_lt16 : forall n, nibble_of_nat n < 16.
Proof. intro n. unfold nibble_of_nat. apply Nat.mod_upper_bound. lia. Qed.

(* ========================= List helpers ============================= *)

(** Updates list element at index n with x. Returns unchanged list if n >= length. *)
Definition update_nth {A} (n : nat) (x : A) (l : list A) : list A :=
  if n <? length l
  then firstn n l ++ x :: skipn (S n) l
  else l.

(** Proves update_nth preserves list length regardless of index validity. *)
Lemma update_nth_length : forall A (l : list A) n x,
  length (update_nth n x l) = length l.
Proof.
  intros A l n x.
  revert n.
  induction l as [|h t IH]; intro n.
  - unfold update_nth. simpl.
    destruct (n <? 0) eqn:E; reflexivity.
  - unfold update_nth. simpl length at 2.
    destruct n.
    + vm_compute. reflexivity.
    + change (S n <? S (length t)) with (n <? length t).
      destruct (n <? length t) eqn:En.
      * change (firstn (S n) (h :: t)) with (h :: firstn n t).
        change (skipn (S (S n)) (h :: t)) with (skipn (S n) t).
        change ((h :: firstn n t) ++ x :: skipn (S n) t) with
               (h :: (firstn n t ++ x :: skipn (S n) t)).
        simpl length.
        f_equal.
        specialize (IH n). unfold update_nth in IH.
        rewrite En in IH. exact IH.
      * reflexivity.
Qed.

(** Proves Forall P is preserved when taking first n elements of list. *)
Lemma Forall_firstn : forall A (P:A->Prop) n (l:list A),
  Forall P l -> Forall P (firstn n l).
Proof.
  intros A P n l H. revert n.
  induction H; intro n.
  - simpl. destruct n; constructor.
  - destruct n; simpl.
    + constructor.
    + constructor; auto.
Qed.

(** Proves Forall P is preserved when skipping first n elements of list. *)
Lemma Forall_skipn : forall A (P:A->Prop) n (l:list A),
  Forall P l -> Forall P (skipn n l).
Proof.
  intros A P n l H. revert n.
  induction H; intro n.
  - simpl. destruct n; constructor.
  - destruct n; simpl.
    + constructor; auto.
    + auto.
Qed.

(** Proves Forall P is preserved by update_nth when replacement element satisfies P. *)
Lemma Forall_update_nth : forall A (P:A->Prop) n x (l:list A),
  Forall P l -> P x -> Forall P (update_nth n x l).
Proof.
  intros A P n x l Hall Hx. unfold update_nth.
  destruct (n <? length l) eqn:En.
  - apply Forall_app; split.
    + apply Forall_firstn; assumption.
    + constructor.
      * assumption.
      * apply Forall_skipn; assumption.
  - assumption.
Qed.

(** Proves nth of update_nth at same index returns the updated element. *)
Lemma nth_update_nth_neq : forall A (l : list A) n m x d,
  n <> m ->
  nth n (update_nth m x l) d = nth n l d.
Proof.
  intros A l n m x d Hneq.
  unfold update_nth.
  destruct (m <? length l) eqn:E; [|reflexivity].
  apply Nat.ltb_lt in E.
  generalize dependent n.
  generalize dependent m.
  generalize dependent x.
  induction l as [|a l' IH]; intros.
  - simpl in E. lia.
  - destruct m, n; simpl; try reflexivity; try lia.
    rewrite IH.
    + reflexivity.
    + auto with arith.
    + simpl in E. auto with arith.
Qed.

(** Proves nth of update_nth at updated index equals the new element. *)
Lemma nth_update_nth_eq : forall A (l : list A) n x d,
  n < length l ->
  nth n (update_nth n x l) d = x.
Proof.
  intros A l n x d Hn.
  unfold update_nth.
  assert (Hlt: n <? length l = true) by (apply Nat.ltb_lt; exact Hn).
  rewrite Hlt.
  rewrite app_nth2.
  - rewrite firstn_length_le by lia.
    replace (n - n) with 0 by lia.
    simpl. reflexivity.
  - rewrite firstn_length_le by lia. lia.
Qed.

(** Proves nth of list satisfying Forall bound also satisfies bound (with default). *)
Lemma nth_Forall_lt : forall (l:list nat) d n k,
  Forall (fun x => x < k) l -> d < k -> nth n l d < k.
Proof.
  intros l d n k Hall Hd. revert n.
  induction Hall; intros [|n]; simpl; auto.
Qed.

(** Proves Forall P holds for repeat x n when P x holds. *)
Lemma Forall_repeat : forall A (P : A -> Prop) x n, P x -> Forall P (repeat x n).
Proof.
  intros A P x n H. induction n; simpl; constructor; auto.
Qed.

(** Decides whether nth n l d is actually in l or equals the default d. *)
Lemma nth_in_or_default : forall A (n : nat) (l : list A) (d : A),
  {In (nth n l d) l} + {nth n l d = d}.
Proof.
  intros A n l d. revert n.
  induction l; intro n.
  - right. destruct n; reflexivity.
  - destruct n.
    + left. simpl. left. reflexivity.
    + simpl. destruct (IHl n) as [H|H].
      * left. right. assumption.
      * right. assumption.
Qed.
