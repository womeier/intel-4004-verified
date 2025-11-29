(* ===================================================================== *)
(*  Intel 4004 Microprocessor + MCS-4 RAM/ROM I/O Formalization in Coq   *)
(* ===================================================================== *)

Require Import Intel4004.machine.
Require Import Intel4004.semantics.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Lia.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ===================================================================== *)
(*                         HOARE LOGIC LAYER                             *)
(* ===================================================================== *)

(* ==================== Hoare Triple Definition ======================= *)

Definition hoare_triple (P Q : Intel4004State -> Prop) (i : Instruction) : Prop :=
  forall s, WF s -> P s ->
    let s' := execute s i in
    WF s' /\ Q s'.

Notation "{{ P }} i {{ Q }}" := (hoare_triple P Q i) (at level 90, i at next level).

(* ==================== Structural Rules =========================== *)

Lemma hoare_consequence : forall P P' Q Q' i,
  (forall s, P' s -> P s) ->
  {{ P }} i {{ Q }} ->
  (forall s, Q s -> Q' s) ->
  {{ P' }} i {{ Q' }}.
Proof.
  intros P P' Q Q' i Hpre Htriple Hpost.
  unfold hoare_triple in *.
  intros s HWF HP'.
  specialize (Htriple s HWF (Hpre s HP')).
  destruct Htriple as [HWF' HQ].
  split; auto.
Qed.

Lemma hoare_conj : forall P P' Q Q' i,
  {{ P }} i {{ Q }} ->
  {{ P' }} i {{ Q' }} ->
  {{ fun s => P s /\ P' s }} i {{ fun s => Q s /\ Q' s }}.
Proof.
  intros P P' Q Q' i H1 H2.
  unfold hoare_triple in *.
  intros s HWF [HP HP'].
  specialize (H1 s HWF HP).
  specialize (H2 s HWF HP').
  destruct H1 as [HWF1 HQ].
  destruct H2 as [HWF2 HQ'].
  split; auto.
Qed.

Lemma hoare_disj : forall P1 P2 Q1 Q2 i,
  {{ P1 }} i {{ Q1 }} ->
  {{ P2 }} i {{ Q2 }} ->
  {{ fun s => P1 s \/ P2 s }} i {{ fun s => Q1 s \/ Q2 s }}.
Proof.
  intros P1 P2 Q1 Q2 i H1 H2.
  unfold hoare_triple in *.
  intros s HWF [HP1 | HP2].
  - specialize (H1 s HWF HP1).
    destruct H1 as [HWF' HQ1].
    split; auto.
  - specialize (H2 s HWF HP2).
    destruct H2 as [HWF' HQ2].
    split; auto.
Qed.

Lemma hoare_exists : forall A (P Q : A -> Intel4004State -> Prop) i,
  (forall x, {{ P x }} i {{ Q x }}) ->
  {{ fun s => exists x, P x s }} i {{ fun s => exists x, Q x s }}.
Proof.
  intros A P Q i H.
  unfold hoare_triple in *.
  intros s HWF [x HP].
  specialize (H x s HWF HP).
  destruct H as [HWF' HQ].
  split; auto.
  exists x. exact HQ.
Qed.

Lemma hoare_frame_regs : forall P Q i R,
  {{ P }} i {{ Q }} ->
  writes_regs i = false ->
  (forall s1 s2, regs s1 = regs s2 -> R s1 -> R s2) ->
  {{ fun s => P s /\ R s }} i {{ fun s => Q s /\ R s }}.
Proof.
  intros P Q i R Htriple Hwrites Hindep.
  unfold hoare_triple in *.
  intros s HWF [HP HR].
  specialize (Htriple s HWF HP).
  destruct Htriple as [HWF' HQ].
  split; auto.
  split; auto.
  apply (Hindep s (execute s i)).
  - symmetry. apply execute_regs_frame. exact Hwrites.
  - exact HR.
Qed.

Lemma hoare_frame_ram : forall P Q i R,
  {{ P }} i {{ Q }} ->
  writes_ram i = false ->
  (forall s1 s2, ram_sys s1 = ram_sys s2 -> R s1 -> R s2) ->
  {{ fun s => P s /\ R s }} i {{ fun s => Q s /\ R s }}.
Proof.
  intros P Q i R Htriple Hwrites Hindep.
  unfold hoare_triple in *.
  intros s HWF [HP HR].
  specialize (Htriple s HWF HP).
  destruct Htriple as [HWF' HQ].
  split; auto.
  split; auto.
  apply (Hindep s (execute s i)).
  - symmetry. apply execute_ram_frame. exact Hwrites.
  - exact HR.
Qed.

Lemma hoare_frame_acc : forall P Q i R,
  {{ P }} i {{ Q }} ->
  writes_acc i = false ->
  (forall s1 s2, acc s1 = acc s2 -> R s1 -> R s2) ->
  {{ fun s => P s /\ R s }} i {{ fun s => Q s /\ R s }}.
Proof.
  intros P Q i R Htriple Hwrites Hindep.
  unfold hoare_triple in *.
  intros s HWF [HP HR].
  specialize (Htriple s HWF HP).
  destruct Htriple as [HWF' HQ].
  split; auto.
  split; auto.
  apply (Hindep s (execute s i)).
  - symmetry. apply execute_acc_frame. exact Hwrites.
  - exact HR.
Qed.

(* ==================== Accumulator Instructions =================== *)

Lemma hoare_LDM : forall n,
  {{ fun _ => n < 16 }}
     LDM n
  {{ fun s => acc s = nibble_of_nat n }}.
Proof.
  intros n. unfold hoare_triple, execute. intros s HWF Hn.
  split.
  - apply execute_LDM_WF; auto; unfold instr_wf; exact Hn.
  - simpl; reflexivity.
Qed.

Lemma hoare_LDM_exact : forall n,
  n < 16 ->
  {{ fun _ => True }}
     LDM n
  {{ fun s => acc s = n }}.
Proof.
  intros n Hn. unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_LDM_WF; auto.
  - unfold execute. simpl. unfold nibble_of_nat.
    rewrite Nat.mod_small by exact Hn. reflexivity.
Qed.

Lemma hoare_LDM_frame : forall n r v,
  n < 16 ->
  {{ fun s => get_reg s r = v }}
     LDM n
  {{ fun s => acc s = n /\ get_reg s r = v }}.
Proof.
  intros n r v Hn. unfold hoare_triple. intros s HWF Hreg.
  split.
  - apply execute_LDM_WF; auto.
  - unfold execute. simpl. split.
    + unfold nibble_of_nat. rewrite Nat.mod_small by exact Hn. reflexivity.
    + exact Hreg.
Qed.

Lemma hoare_LD : forall r old_r,
  {{ fun s => get_reg s r = old_r /\ r < 16 }}
     LD r
  {{ fun s => acc s = old_r }}.
Proof.
  intros r old_r. unfold hoare_triple. intros s HWF [Hold Hr].
  split.
  - apply execute_LD_WF. exact HWF. unfold instr_wf. exact Hr.
  - unfold execute. simpl. exact Hold.
Qed.

Lemma hoare_LD_load : forall r v,
  {{ fun s => get_reg s r = v /\ r < 16 }}
     LD r
  {{ fun s => acc s = v }}.
Proof.
  intros r v. unfold hoare_triple. intros s HWF [Hreg Hr].
  split.
  - apply execute_LD_WF; auto.
  - unfold execute. simpl. exact Hreg.
Qed.

Lemma hoare_LD_frame : forall r1 r2 v1 v2,
  r1 <> r2 ->
  {{ fun s => get_reg s r1 = v1 /\ get_reg s r2 = v2 /\ r1 < 16 }}
     LD r1
  {{ fun s => acc s = v1 /\ get_reg s r1 = v1 /\ get_reg s r2 = v2 }}.
Proof.
  intros r1 r2 v1 v2 Hneq. unfold hoare_triple. intros s HWF [Hr1 [Hr2 Hbound]].
  split.
  - apply execute_LD_WF; auto.
  - unfold execute. simpl. split; [exact Hr1 | split; [exact Hr1 | exact Hr2]].
Qed.

Lemma hoare_CLB :
  {{ fun _ => True }}
     CLB
  {{ fun s => acc s = 0 /\ carry s = false }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_CLB_WF. exact HWF.
  - unfold execute. simpl. split; reflexivity.
Qed.

Lemma hoare_CLC : forall old_acc,
  {{ fun s => acc s = old_acc }}
     CLC
  {{ fun s => acc s = old_acc /\ carry s = false }}.
Proof.
  intros old_acc. unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_CLC_WF. exact HWF.
  - unfold execute. simpl. split; [exact Hacc | reflexivity].
Qed.


Lemma hoare_STC : forall old_acc,
  {{ fun s => acc s = old_acc }}
     STC
  {{ fun s => acc s = old_acc /\ carry s = true }}.
Proof.
  intros old_acc. unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_STC_WF. exact HWF.
  - unfold execute. simpl. split; [exact Hacc | reflexivity].
Qed.

Lemma hoare_CMC : forall old_acc old_carry,
  {{ fun s => acc s = old_acc /\ carry s = old_carry }}
     CMC
  {{ fun s => acc s = old_acc /\ carry s = negb old_carry }}.
Proof.
  intros old_acc old_carry. unfold hoare_triple. intros s HWF [Hacc Hcarry].
  split.
  - apply execute_CMC_WF. exact HWF.
  - unfold execute. simpl. split; [exact Hacc | rewrite Hcarry; reflexivity].
Qed.

Lemma hoare_CMA :
  {{ fun s => acc s < 16 }}
     CMA
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_CMA_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_CMA_involution : forall a,
  {{ fun s => acc s = a /\ a < 16 }}
     CMA
  {{ fun s => acc s = 15 - a }}.
Proof.
  intros a. unfold hoare_triple. intros s HWF [Hacc Ha].
  split.
  - apply execute_CMA_WF. exact HWF.
  - unfold execute. simpl. rewrite Hacc.
    do 16 (destruct a; simpl; [reflexivity|]); lia.
Qed.

Lemma hoare_CMA_double_involution : forall a r v,
  {{ fun s => acc s = a /\ a < 16 /\ get_reg s r = v }}
     CMA
  {{ fun s => acc s = 15 - a /\ get_reg s r = v }}.
Proof.
  intros a r v. unfold hoare_triple. intros s HWF [Hacc [Ha Hreg]].
  split.
  - apply execute_CMA_WF. exact HWF.
  - unfold execute. simpl. split.
    + rewrite Hacc. do 16 (destruct a; simpl; [reflexivity|]); lia.
    + exact Hreg.
Qed.

Lemma hoare_CMA_involution_proof : forall a,
  a < 16 ->
  15 - (15 - a) = a.
Proof.
  intros a Ha.
  do 16 (destruct a; simpl; [reflexivity|]); lia.
Qed.

Lemma hoare_IAC :
  {{ fun s => acc s < 16 }}
     IAC
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_IAC_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_DAC :
  {{ fun s => acc s < 16 }}
     DAC
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_DAC_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_RAL :
  {{ fun s => acc s < 16 }}
     RAL
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_RAL_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_RAR :
  {{ fun s => acc s < 16 }}
     RAR
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_RAR_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_TCC :
  {{ fun _ => True }}
     TCC
  {{ fun s => acc s < 16 /\ carry s = false }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_TCC_WF. exact HWF.
  - unfold execute. simpl. split; [destruct (carry s); lia | reflexivity].
Qed.

Lemma hoare_TCS :
  {{ fun _ => True }}
     TCS
  {{ fun s => acc s < 16 /\ carry s = false }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_TCS_WF. exact HWF.
  - unfold execute. simpl. split; [destruct (carry s); lia | reflexivity].
Qed.

Lemma hoare_DAA :
  {{ fun s => acc s < 16 }}
     DAA
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_DAA_WF. exact HWF.
  - unfold execute. simpl. apply nibble_lt16.
Qed.

Lemma hoare_KBP :
  {{ fun s => acc s < 16 }}
     KBP
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_KBP_WF. exact HWF.
  - unfold execute. simpl.
    destruct (acc s) as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]]]; lia.
Qed.

(* ==================== Register Instructions ====================== *)

Lemma hoare_INC : forall r,
  {{ fun s => r < length (regs s) }}
     INC r
  {{ fun s => get_reg s r < 16 }}.
Proof.
  intros r. unfold hoare_triple, execute. intros s HWF Hr.
  split.
  - apply execute_INC_WF; auto. unfold instr_wf.
    destruct HWF as [HlenR _]. lia.
  - unfold get_reg, set_reg. simpl.
    rewrite nth_update_nth_eq by assumption.
    apply nibble_lt16.
Qed.

Lemma hoare_INC_from_zero : forall r,
  {{ fun s => get_reg s r = 0 /\ r < 16 }}
     INC r
  {{ fun s => get_reg s r = 1 }}.
Proof.
  intros r. unfold hoare_triple. intros s HWF [Hreg Hr].
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR _].
  split.
  - apply execute_INC_WF; auto.
  - unfold execute. simpl. unfold get_reg, set_reg. simpl.
    rewrite nth_update_nth_eq by (rewrite HlenR; exact Hr).
    unfold nibble_of_nat. unfold get_reg in Hreg. rewrite Hreg. simpl. reflexivity.
Qed.

Lemma hoare_INC_from_zero_frame : forall r r2 v2 acc_val,
  r <> r2 ->
  {{ fun s => get_reg s r = 0 /\ r < 16 /\ get_reg s r2 = v2 /\ acc s = acc_val }}
     INC r
  {{ fun s => get_reg s r = 1 /\ get_reg s r2 = v2 /\ acc s = acc_val }}.
Proof.
  intros r r2 v2 acc_val Hneq. unfold hoare_triple. intros s HWF [Hreg [Hr [Hr2 Hacc]]].
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR _].
  split.
  - apply execute_INC_WF; auto.
  - unfold execute. simpl. unfold get_reg, set_reg in *. simpl.
    split; [|split].
    + rewrite nth_update_nth_eq by (rewrite HlenR; exact Hr).
      unfold nibble_of_nat. rewrite Hreg. simpl. reflexivity.
    + rewrite nth_update_nth_neq by lia. exact Hr2.
    + exact Hacc.
Qed.

Lemma hoare_INC_preserves_other_regs : forall r1 r2 v,
  r1 <> r2 ->
  {{ fun s => get_reg s r2 = v /\ r1 < 16 }}
     INC r1
  {{ fun s => get_reg s r2 = v }}.
Proof.
  intros r1 r2 v Hneq. unfold hoare_triple. intros s HWF [Hreg Hr1].
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR _].
  split.
  - apply execute_INC_WF; auto.
  - unfold execute. simpl. unfold get_reg, set_reg in *. simpl.
    rewrite nth_update_nth_neq by lia. exact Hreg.
Qed.

Lemma hoare_INC_full_frame : forall r1 r2 v1 v2,
  r1 <> r2 ->
  {{ fun s => get_reg s r1 = v1 /\ get_reg s r2 = v2 /\ r1 < 16 /\ v1 < 16 }}
     INC r1
  {{ fun s => get_reg s r1 < 16 /\ get_reg s r2 = v2 }}.
Proof.
  intros r1 r2 v1 v2 Hneq. unfold hoare_triple. intros s HWF [Hr1 [Hr2 [Hbound Hv1]]].
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR _].
  split.
  - apply execute_INC_WF; auto.
  - unfold execute. simpl. unfold get_reg, set_reg in *. simpl.
    split.
    + rewrite nth_update_nth_eq by (rewrite HlenR; exact Hbound).
      apply nibble_lt16.
    + rewrite nth_update_nth_neq by lia. exact Hr2.
Qed.

Lemma hoare_ADD : forall r,
  {{ fun s => r < length (regs s) /\ acc s < 16 /\ get_reg s r < 16 }}
     ADD r
  {{ fun s => acc s < 16 }}.
Proof.
  intros r. unfold hoare_triple, execute. intros s HWF [Hr [Hacc Hreg]].
  split.
  - apply execute_ADD_WF; auto. unfold instr_wf.
    destruct HWF as [HlenR _]. lia.
  - apply nibble_lt16.
Qed.

Lemma hoare_ADD_zero : forall r v,
  {{ fun s => acc s = v /\ get_reg s r = 0 /\ carry s = false /\ r < 16 /\ v < 16 }}
     ADD r
  {{ fun s => acc s = v }}.
Proof.
  intros r v. unfold hoare_triple. intros s HWF [Hacc [Hreg [Hcarry [Hr Hv]]]].
  split.
  - apply execute_ADD_WF; auto.
  - unfold execute, get_reg in *. simpl. rewrite Hacc, Hreg, Hcarry. simpl.
    unfold nibble_of_nat. rewrite Nat.add_0_r.
    rewrite Nat.mod_small by lia. lia.
Qed.

Lemma hoare_ADD_zero_preserves_carry : forall r v,
  {{ fun s => acc s = v /\ get_reg s r = 0 /\ carry s = false /\ r < 16 /\ v < 16 }}
     ADD r
  {{ fun s => acc s = v /\ carry s = false }}.
Proof.
  intros r v. unfold hoare_triple. intros s HWF [Hacc [Hr [Hcarry [Hbound Hv]]]].
  split.
  - apply execute_ADD_WF; auto.
  - unfold execute, get_reg in *. simpl.
    rewrite Hacc, Hr, Hcarry. simpl.
    split.
    + unfold nibble_of_nat. rewrite Nat.add_0_r.
      rewrite Nat.mod_small by lia. lia.
    + do 16 (destruct v; simpl; [reflexivity|]); lia.
Qed.

Lemma hoare_SUB : forall r,
  {{ fun s => r < length (regs s) /\ acc s < 16 /\ get_reg s r < 16 }}
     SUB r
  {{ fun s => acc s < 16 }}.
Proof.
  intros r. unfold hoare_triple, execute. intros s HWF [Hr [Hacc Hreg]].
  split.
  - apply execute_SUB_WF; auto. unfold instr_wf.
    destruct HWF as [HlenR _]. lia.
  - apply nibble_lt16.
Qed.

Lemma hoare_XCH : forall r,
  {{ fun s => r < length (regs s) }}
     XCH r
  {{ fun s => acc s < 16 /\ get_reg s r < 16 }}.
Proof.
  intros r. unfold hoare_triple. intros s HWF Hr.
  assert (HWF': WF s) by assumption.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  assert (Hwfi: instr_wf (XCH r)) by (unfold instr_wf; lia).
  split; [apply execute_XCH_WF; auto|].
  unfold execute. simpl.
  assert (Hreg_bound: get_reg s r < 16).
  { unfold get_reg. apply (nth_Forall_lt _ 0 r 16 HforR). lia. }
  split; [exact Hreg_bound|].
  unfold get_reg, set_reg. simpl. rewrite nth_update_nth_eq by assumption.
  unfold nibble_of_nat. rewrite Nat.mod_small by assumption. exact Hacc.
Qed.

Lemma hoare_XCH_preserves_sum : forall r n,
  {{ fun s => acc s + get_reg s r = n /\ r < 16 }}
     XCH r
  {{ fun s => acc s + get_reg s r = n }}.
Proof.
  intros r n. unfold hoare_triple. intros s HWF [Hsum Hr].
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR [HforR [Hacc_bound _]]].
  split.
  - apply execute_XCH_WF; auto.
  - unfold execute. simpl. unfold get_reg, set_reg in *. simpl.
    assert (Hlen_r: r < length (regs s)) by (rewrite HlenR; exact Hr).
    rewrite nth_update_nth_eq by exact Hlen_r.
    unfold nibble_of_nat.
    rewrite Nat.mod_small by exact Hacc_bound.
    lia.
Qed.

Lemma hoare_XCH_swaps_values : forall r a_val r_val,
  {{ fun s => acc s = a_val /\ get_reg s r = r_val /\ r < 16 /\ a_val < 16 /\ r_val < 16 }}
     XCH r
  {{ fun s => acc s = r_val /\ get_reg s r = a_val }}.
Proof.
  intros r a_val r_val. unfold hoare_triple. intros s HWF [Hacc [Hreg [Hr [Ha Hb]]]].
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR [HforR [Hacc_bound _]]].
  split.
  - apply execute_XCH_WF; auto.
  - unfold execute. simpl. unfold get_reg, set_reg in *. simpl.
    assert (Hlen_r: r < length (regs s)) by (rewrite HlenR; exact Hr).
    split.
    + rewrite Hreg. reflexivity.
    + rewrite nth_update_nth_eq by exact Hlen_r.
      unfold nibble_of_nat. rewrite Hacc.
      rewrite Nat.mod_small by exact Ha. reflexivity.
Qed.

Lemma hoare_FIM : forall r data,
  {{ fun s => r < 16 /\ r mod 2 = 0 /\ data < 256 }}
     FIM r data
  {{ fun s => get_reg_pair s r = data }}.
Proof.
Admitted.

Lemma hoare_FIM_frame : forall r data acc_val c_val,
  {{ fun s => r < 16 /\ r mod 2 = 0 /\ data < 256 /\ acc s = acc_val /\ carry s = c_val }}
     FIM r data
  {{ fun s => get_reg_pair s r = data /\ acc s = acc_val /\ carry s = c_val }}.
Proof.
Admitted.

Lemma hoare_SRC : forall r old_pair,
  {{ fun s => r < 16 /\ r mod 2 = 1 /\ get_reg_pair s r = old_pair }}
     SRC r
  {{ fun s => sel_rom s = old_pair / 16 /\
              sel_chip (sel_ram s) = old_pair / 16 / 4 /\
              sel_reg (sel_ram s) = (old_pair / 16) mod 4 /\
              sel_char (sel_ram s) = old_pair mod 16 }}.
Proof.
  intros r old_pair. unfold hoare_triple. intros s HWF [Hr [Hodd Hpair]].
  split.
  - apply execute_SRC_WF; auto. unfold instr_wf. split; assumption.
  - unfold execute. simpl.
    rewrite Hpair.
    split; [|split; [|split]]; reflexivity.
Qed.

Lemma hoare_SRC_sets_ram_address : forall r chip_val reg_val char_val,
  {{ fun s => r < 16 /\ r mod 2 = 1 /\
              get_reg_pair s r = chip_val * 64 + reg_val * 16 + char_val /\
              chip_val < 4 /\ reg_val < 4 /\ char_val < 16 }}
     SRC r
  {{ fun s => sel_chip (sel_ram s) = chip_val /\
              sel_reg (sel_ram s) = reg_val /\
              sel_char (sel_ram s) = char_val }}.
Proof.
Admitted.

(* Need: ISZ, the only loop primitive on the 4004 - without this, we can't verify loops! Also need JCN - Conditional branches - needed for any control flow verification! *)


(* ==================== Control Flow =============================== *)

Lemma hoare_NOP :
  {{ fun _ => True }}
     NOP
  {{ fun _ => True }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split.
  - apply execute_NOP_WF. exact HWF.
  - exact I.
Qed.

Lemma hoare_NOP_preserves_acc : forall v,
  {{ fun s => acc s = v }}
     NOP
  {{ fun s => acc s = v }}.
Proof.
  intros v. unfold hoare_triple. intros s HWF Hacc.
  split.
  - apply execute_NOP_WF. exact HWF.
  - unfold execute. simpl. exact Hacc.
Qed.

Lemma hoare_NOP_preserves_state : forall a r1 r2 v1 v2 c,
  {{ fun s => acc s = a /\ get_reg s r1 = v1 /\ get_reg s r2 = v2 /\ carry s = c }}
     NOP
  {{ fun s => acc s = a /\ get_reg s r1 = v1 /\ get_reg s r2 = v2 /\ carry s = c }}.
Proof.
  intros a r1 r2 v1 v2 c. unfold hoare_triple. intros s HWF [Hacc [Hr1 [Hr2 Hcarry]]].
  split.
  - apply execute_NOP_WF. exact HWF.
  - unfold execute. simpl. split; [|split; [|split]]; assumption.
Qed.

Lemma hoare_NOP_preserves_regs : forall r v,
  {{ fun s => get_reg s r = v }}
     NOP
  {{ fun s => get_reg s r = v }}.
Proof.
  intros r v. unfold hoare_triple. intros s HWF Hreg.
  split.
  - apply execute_NOP_WF. exact HWF.
  - unfold execute. simpl. exact Hreg.
Qed.

Lemma hoare_NOP_preserves_all_regs : forall r1 r2 r3 v1 v2 v3,
  r1 <> r2 -> r2 <> r3 -> r1 <> r3 ->
  {{ fun s => get_reg s r1 = v1 /\ get_reg s r2 = v2 /\ get_reg s r3 = v3 }}
     NOP
  {{ fun s => get_reg s r1 = v1 /\ get_reg s r2 = v2 /\ get_reg s r3 = v3 }}.
Proof.
  intros r1 r2 r3 v1 v2 v3 H12 H23 H13. unfold hoare_triple. intros s HWF [Hr1 [Hr2 Hr3]].
  split.
  - apply execute_NOP_WF. exact HWF.
  - unfold execute. simpl. split; [|split]; assumption.
Qed.

Lemma hoare_JUN : forall addr,
  {{ fun s => addr < 4096 }}
     JUN addr
  {{ fun s => pc s = addr }}.
Proof.
  intros addr. unfold hoare_triple. intros s HWF Haddr.
  split; [apply execute_JUN_WF; auto; unfold instr_wf; exact Haddr|apply pc_shape_jun].
Qed.

Lemma hoare_JMS : forall addr,
  {{ fun s => addr < 4096 /\ length (stack s) <= 3 }}
     JMS addr
  {{ fun s => pc s = addr /\ length (stack s) <= 3 }}.
Proof.
  intros addr. unfold hoare_triple. intros s HWF [Haddr Hstack].
  split; [apply execute_JMS_WF; auto; unfold instr_wf; exact Haddr|].
  unfold execute. simpl. split; [apply (pc_shape_jms s addr)|apply push_stack_len_le3].
Qed.

Lemma hoare_BBL : forall d,
  {{ fun s => d < 16 }}
     BBL d
  {{ fun s => acc s = nibble_of_nat d /\ length (stack s) <= 3 }}.
Proof.
  intros d. unfold hoare_triple. intros s HWF Hd.
  assert (HWF': WF s) by assumption.
  destruct HWF as [HlenR [HforR [Hacc [Hpc [Hstklen [HstkFor
    [HsysLen [HsysFor [Hbank [Hsel [HrpLen [HrpFor [Hselrom [HromFor [HromLen [Hpaddr Hpdata]]]]]]]]]]]]]]]].
  split; [apply execute_BBL_WF; auto; unfold instr_wf; exact Hd|].
  unfold execute. destruct (pop_stack s) as [[addr|] s'] eqn:Epop; simpl; (split; [reflexivity|eapply pop_stack_len_le3; eauto; lia]).
Qed.

(* ==================== RAM/ROM Operations ========================= *)

Lemma hoare_RDM :
  {{ fun _ => True }}
     RDM
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split; [apply execute_RDM_WF; auto|].
  unfold execute. simpl. apply ram_read_main_bound. exact HWF.
Qed.

Lemma hoare_WRM :
  {{ fun s => acc s < 16 }}
     WRM
  {{ fun _ => True }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split; [apply execute_WRM_WF; auto|auto].
Qed.

Lemma hoare_ADM :
  {{ fun s => acc s < 16 }}
     ADM
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split; [apply execute_ADM_WF; auto|].
  assert (HWF' := execute_ADM_WF s HWF).
  destruct HWF' as [_ [_ [Hacc' _]]].
  exact Hacc'.
Qed.

Lemma hoare_SBM :
  {{ fun s => acc s < 16 }}
     SBM
  {{ fun s => acc s < 16 }}.
Proof.
  unfold hoare_triple. intros s HWF Hacc.
  split; [apply execute_SBM_WF; auto|].
  assert (HWF' := execute_SBM_WF s HWF).
  destruct HWF' as [_ [_ [Hacc' _]]].
  exact Hacc'.
Qed.

Lemma hoare_DCL :
  {{ fun _ => True }}
     DCL
  {{ fun s => cur_bank s < NBANKS }}.
Proof.
  unfold hoare_triple. intros s HWF _.
  split; [apply execute_DCL_WF; auto|].
  assert (HWF' := execute_DCL_WF s HWF).
  destruct HWF' as [_ [_ [_ [_ [_ [_ [_ [_ [Hbank _]]]]]]]]].
  exact Hbank.
Qed.

(* ==================== Program-Level Hoare Logic ================== *)

Fixpoint exec_program (prog : list Instruction) (s : Intel4004State) : Intel4004State :=
  match prog with
  | [] => s
  | i :: rest => exec_program rest (execute s i)
  end.

Definition hoare_prog (P Q : Intel4004State -> Prop) (prog : list Instruction) : Prop :=
  forall s, WF s -> P s ->
    let s' := exec_program prog s in
    WF s' /\ Q s'.

Notation "{{| P |}} prog {{| Q |}}" := (hoare_prog P Q prog) (at level 90).

Lemma hoare_single : forall P Q i,
  {{ P }} i {{ Q }} ->
  {{| P |}} [i] {{| Q |}}.
Proof.
  intros P Q i H.
  unfold hoare_prog, hoare_triple in *.
  intros s HWF HP. simpl. apply H; auto.
Qed.

Lemma exec_program_app : forall prog1 prog2 s,
  exec_program (prog1 ++ prog2) s = exec_program prog2 (exec_program prog1 s).
Proof.
  induction prog1; intros prog2 s.
  - simpl. reflexivity.
  - simpl. rewrite IHprog1. reflexivity.
Qed.

Lemma hoare_prog_seq : forall P Q R prog1 prog2,
  {{| P |}} prog1 {{| Q |}} ->
  {{| Q |}} prog2 {{| R |}} ->
  {{| P |}} prog1 ++ prog2 {{| R |}}.
Proof.
  intros P Q R prog1 prog2 H1 H2.
  unfold hoare_prog in *.
  intros s HWF HP.
  rewrite exec_program_app.
  assert (Hmid := H1 s HWF HP).
  destruct Hmid as [HWF' HQ].
  apply H2; auto.
Qed.

Lemma hoare_prog_consequence : forall P P' Q Q' prog,
  (forall s, P' s -> P s) ->
  {{| P |}} prog {{| Q |}} ->
  (forall s, Q s -> Q' s) ->
  {{| P' |}} prog {{| Q' |}}.
Proof.
  intros P P' Q Q' prog Hpre Hprog Hpost.
  unfold hoare_prog in *.
  intros s HWF HP'.
  specialize (Hprog s HWF (Hpre s HP')).
  destruct Hprog as [HWF' HQ].
  split; auto.
Qed.

Fixpoint wp (prog : list Instruction) (Q : Intel4004State -> Prop) : Intel4004State -> Prop :=
  match prog with
  | [] => Q
  | i :: rest => fun s =>
      WF s ->
      let s' := execute s i in
      WF s' /\ wp rest Q s'
  end.

Theorem wp_soundness : forall prog Q,
  {{| wp prog Q |}} prog {{| Q |}}.
Proof.
  induction prog; intros Q.
  - unfold hoare_prog, wp. intros s HWF HQ. simpl. split; auto.
  - unfold hoare_prog, wp. intros s HWF Hwp.
    specialize (Hwp HWF).
    destruct Hwp as [HWF' Hwp'].
    simpl. fold exec_program.
    apply IHprog; auto.
Qed.

(* ==================== Example Verifications ====================== *)

Example ex_load_5 :
  {{| fun _ => True |}}
      [LDM 5]
  {{| fun s => acc s = 5 |}}.
Proof.
  apply hoare_single.
  apply hoare_consequence with (P := fun _ => 5 < 16) (Q := fun s => acc s = nibble_of_nat 5).
  - intros s _. lia.
  - apply hoare_LDM.
  - intros s H. unfold nibble_of_nat in H. rewrite Nat.mod_small in H by lia. exact H.
Qed.

Example ex_clear :
  {{| fun _ => True |}}
      [CLB]
  {{| fun s => acc s = 0 /\ carry s = false |}}.
Proof.
  apply hoare_single. apply hoare_CLB.
Qed.

Example ex_ldm_iac :
  {{| fun _ => True |}}
      [LDM 5; IAC]
  {{| fun s => acc s = 6 |}}.
Proof.
  unfold hoare_prog. intros s HWF _.
  simpl exec_program.
  assert (HWF1: WF (execute s (LDM 5))).
  { apply execute_LDM_WF; auto. unfold instr_wf. lia. }
  assert (HWF2: WF (execute (execute s (LDM 5)) IAC)).
  { apply execute_IAC_WF; auto. }
  split; [exact HWF2|].
  simpl. reflexivity.
Qed.

Lemma hoare_XCH_swap : forall r old_acc old_reg,
  {{ fun s => acc s = old_acc /\ get_reg s r = old_reg /\ r < 16 }}
     XCH r
  {{ fun s => acc s = old_reg /\ get_reg s r = old_acc }}.
Proof.
  intros r old_acc old_reg.
  unfold hoare_triple. intros s HWF [Hacc [Hreg Hr]].
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR [HforR [Hacc_bound _]]].
  split.
  - apply execute_XCH_WF; [exact HWF | unfold instr_wf; exact Hr].
  - unfold execute. simpl.
    split.
    + rewrite Hreg. reflexivity.
    + unfold get_reg, set_reg. simpl.
      rewrite nth_update_nth_eq by (rewrite HlenR; exact Hr).
      unfold nibble_of_nat.
      rewrite Hacc.
      rewrite Nat.mod_small by (rewrite <- Hacc; exact Hacc_bound).
      reflexivity.
Qed.

Example ex_CMA_involution : forall a,
  {{| fun s => acc s = a /\ a < 16 |}}
      [CMA; CMA]
  {{| fun s => acc s = a |}}.
Proof.
  intro a.
  unfold hoare_prog. intros s HWF [Hacc Ha].
  simpl exec_program.
  assert (HWF1: WF (execute s CMA)).
  { apply execute_CMA_WF. exact HWF. }
  assert (HWF2: WF (execute (execute s CMA) CMA)).
  { apply execute_CMA_WF. exact HWF1. }
  split. exact HWF2.
  unfold execute. simpl.
  rewrite Hacc.
  do 16 (destruct a; simpl; [reflexivity|]); lia.
Qed.

Example ex_CMA_involution_frame : forall a r v,
  {{| fun s => acc s = a /\ a < 16 /\ get_reg s r = v |}}
      [CMA; CMA]
  {{| fun s => acc s = a /\ get_reg s r = v |}}.
Proof.
  intros a r v.
  unfold hoare_prog. intros s HWF [Hacc [Ha Hreg]].
  simpl exec_program.
  assert (HWF1: WF (execute s CMA)).
  { apply execute_CMA_WF. exact HWF. }
  assert (HWF2: WF (execute (execute s CMA) CMA)).
  { apply execute_CMA_WF. exact HWF1. }
  split. exact HWF2.
  split.
  - unfold execute. simpl. rewrite Hacc.
    do 16 (destruct a; simpl; [reflexivity|]); lia.
  - unfold execute. simpl. exact Hreg.
Qed.

Lemma hoare_ADD_carry : forall r a b c,
  {{ fun s => acc s = a /\ get_reg s r = b /\ carry s = c /\ r < 16 /\ a < 16 /\ b < 16 }}
     ADD r
  {{ fun s => carry s = (16 <=? (a + b + (if c then 1 else 0))) }}.
Proof.
  intros r a b c.
  unfold hoare_triple. intros s HWF [Hacc [Hreg [Hcarry [Hr [Ha Hb]]]]].
  split.
  - apply execute_ADD_WF; [exact HWF | unfold instr_wf; exact Hr].
  - unfold execute. simpl.
    rewrite Hacc, Hreg, Hcarry. reflexivity.
Qed.

Example ex_copy_nibble : forall x,
  {{| fun s => get_reg s 5 = x /\ x < 16 |}}
      [LD 5; XCH 7]
  {{| fun s => get_reg s 5 = x /\ get_reg s 7 = x |}}.
Proof.
  intro x.
  unfold hoare_prog. intros s HWF [Hr5 Hx].
  simpl exec_program.
  assert (HWF1: WF (execute s (LD 5))).
  { apply execute_LD_WF; [exact HWF | unfold instr_wf; lia]. }
  assert (HWF2: WF (execute (execute s (LD 5)) (XCH 7))).
  { apply execute_XCH_WF; [exact HWF1 | unfold instr_wf; lia]. }
  split. exact HWF2.
  unfold execute, get_reg, set_reg in *. simpl.
  destruct HWF as [HlenR _].
  assert (Hlen7: 7 < length (regs s)) by (rewrite HlenR; lia).
  split.
  - rewrite nth_update_nth_neq by lia. exact Hr5.
  - rewrite nth_update_nth_eq by exact Hlen7.
    unfold nibble_of_nat.
    rewrite Hr5.
    rewrite Nat.mod_small by assumption.
    reflexivity.
Qed.

Example ex_accumulator_pipeline :
  {{| fun s => carry s = false |}}
      [LDM 3; XCH 2; LDM 7; ADD 2]
  {{| fun s => acc s = 10 /\ get_reg s 2 = 3 |}}.
Proof.
  unfold hoare_prog. intros s HWF Hcarry.
  simpl exec_program.
  assert (HWF1: WF (execute s (LDM 3))).
  { apply execute_LDM_WF; [exact HWF | unfold instr_wf; lia]. }
  assert (HWF2: WF (execute (execute s (LDM 3)) (XCH 2))).
  { apply execute_XCH_WF; [exact HWF1 | unfold instr_wf; lia]. }
  assert (HWF3: WF (execute (execute (execute s (LDM 3)) (XCH 2)) (LDM 7))).
  { apply execute_LDM_WF; [exact HWF2 | unfold instr_wf; lia]. }
  assert (HWF4: WF (execute (execute (execute (execute s (LDM 3)) (XCH 2)) (LDM 7)) (ADD 2))).
  { apply execute_ADD_WF; [exact HWF3 | unfold instr_wf; lia]. }
  split. exact HWF4.
  unfold execute. simpl.
  destruct HWF as [HlenR _].
  assert (Hlen2: 2 < length (regs s)) by (rewrite HlenR; lia).
  unfold get_reg, set_reg. simpl.
  rewrite nth_update_nth_eq by exact Hlen2.
  unfold nibble_of_nat. simpl.
  rewrite Hcarry. simpl. split; reflexivity.
Qed.

Example ex_jms_bbl_roundtrip : forall addr data old_pc,
  {{| fun s => pc s = old_pc /\ addr < 4096 /\ data < 16 /\ length (stack s) <= 2 |}}
      [JMS addr; BBL data]
  {{| fun s => pc s = addr12_of_nat (old_pc + 2) /\ acc s = data /\ length (stack s) <= 2 |}}.
Proof.
  intros addr data old_pc.
  unfold hoare_prog. intros s HWF [Hpc [Haddr [Hdata Hstack]]].
  simpl exec_program.
  assert (HWF1: WF (execute s (JMS addr))).
  { apply execute_JMS_WF; [exact HWF | unfold instr_wf; exact Haddr]. }
  assert (HWF2: WF (execute (execute s (JMS addr)) (BBL data))).
  { apply execute_BBL_WF; [exact HWF1 | unfold instr_wf; exact Hdata]. }
  split. exact HWF2.
  unfold execute. simpl.
  unfold push_stack, pop_stack. simpl.
  rewrite Hpc.
  destruct (stack s) as [|h1 [|h2 [|h3 rest]]]; simpl.
  - unfold nibble_of_nat. rewrite Nat.mod_small by exact Hdata.
    split. reflexivity. split. reflexivity. lia.
  - unfold nibble_of_nat. rewrite Nat.mod_small by exact Hdata.
    split. reflexivity. split. reflexivity. lia.
  - unfold nibble_of_nat. rewrite Nat.mod_small by exact Hdata.
    split. reflexivity. split. reflexivity. lia.
  - simpl in Hstack. lia.
Qed.

Example ex_stack_discipline : forall addr1 addr2 d1 d2 old_pc,
  {{| fun s => pc s = old_pc /\ length (stack s) = 0 /\
               addr1 < 4096 /\ addr2 < 4096 /\ d1 < 16 /\ d2 < 16 /\
               old_pc < 4096 /\ old_pc + 4 < 4096 |}}
      [JMS addr1; BBL d1; JMS addr2; BBL d2]
  {{| fun s => length (stack s) = 0 /\ pc s = addr12_of_nat (old_pc + 4) |}}.
Proof.
  intros addr1 addr2 d1 d2 old_pc.
  unfold hoare_prog. intros s HWF [Hpc [Hlen [Ha1 [Ha2 [Hd1 [Hd2 [Hpc_bound Hpc4_bound]]]]]]].
  simpl exec_program.
  assert (HWF1: WF (execute s (JMS addr1))).
  { apply execute_JMS_WF; [exact HWF | unfold instr_wf; exact Ha1]. }
  assert (HWF2: WF (execute (execute s (JMS addr1)) (BBL d1))).
  { apply execute_BBL_WF; [exact HWF1 | unfold instr_wf; exact Hd1]. }
  assert (HWF3: WF (execute (execute (execute s (JMS addr1)) (BBL d1)) (JMS addr2))).
  { apply execute_JMS_WF; [exact HWF2 | unfold instr_wf; exact Ha2]. }
  assert (HWF4: WF (execute (execute (execute (execute s (JMS addr1)) (BBL d1)) (JMS addr2)) (BBL d2))).
  { apply execute_BBL_WF; [exact HWF3 | unfold instr_wf; exact Hd2]. }
  split. exact HWF4.
  unfold execute. simpl.
  unfold push_stack, pop_stack.
  assert (Hstack_nil: stack s = []) by (destruct (stack s); [reflexivity | simpl in Hlen; lia]).
  rewrite Hstack_nil. simpl.
  rewrite Hpc.
  split.
  - reflexivity.
  - replace (old_pc + 4) with (old_pc + 2 + 2) by lia.
    rewrite <- (addr12_of_nat_add (old_pc + 2) 2); lia.
Qed.

(* ==================== Derived Lemmas: Common Patterns =================== *)

Lemma copy_reg : forall src dst val,
  src <> dst ->
  src < 16 ->
  dst < 16 ->
  {{| fun s => get_reg s src = val /\ val < 16 |}}
      [LD src; XCH dst]
  {{| fun s => get_reg s src = val /\ get_reg s dst = val |}}.
Proof.
  intros src dst val Hneq Hsrc Hdst.
  unfold hoare_prog. intros s HWF [Hreg Hval].
  simpl exec_program.
  assert (HWF1: WF (execute s (LD src))).
  { apply execute_LD_WF; [exact HWF | unfold instr_wf; exact Hsrc]. }
  assert (HWF2: WF (execute (execute s (LD src)) (XCH dst))).
  { apply execute_XCH_WF; [exact HWF1 | unfold instr_wf; exact Hdst]. }
  split. exact HWF2.
  unfold execute, get_reg, set_reg in *. simpl.
  destruct HWF as [HlenR _].
  assert (Hlen_src: src < length (regs s)) by (rewrite HlenR; exact Hsrc).
  assert (Hlen_dst: dst < length (regs s)) by (rewrite HlenR; exact Hdst).
  split.
  - rewrite nth_update_nth_neq by lia. exact Hreg.
  - rewrite nth_update_nth_eq by exact Hlen_dst.
    unfold nibble_of_nat.
    rewrite Hreg.
    rewrite Nat.mod_small by assumption.
    reflexivity.
Qed.

Lemma zero_reg : forall r,
  r < 16 ->
  {{| fun _ => True |}}
      [CLB; XCH r]
  {{| fun s => get_reg s r = 0 |}}.
Proof.
  intros r Hr.
  unfold hoare_prog. intros s HWF _.
  simpl exec_program.
  assert (HWF1: WF (execute s CLB)).
  { apply execute_CLB_WF. exact HWF. }
  assert (HWF2: WF (execute (execute s CLB) (XCH r))).
  { apply execute_XCH_WF; [exact HWF1 | unfold instr_wf; exact Hr]. }
  split. exact HWF2.
  unfold execute, get_reg, set_reg. simpl.
  destruct HWF as [HlenR _].
  assert (Hlen_r: r < length (regs s)) by (rewrite HlenR; exact Hr).
  rewrite nth_update_nth_eq by exact Hlen_r.
  unfold nibble_of_nat.
  simpl. reflexivity.
Qed.

Lemma nibble_of_nat_idempotent : forall n,
  nibble_of_nat (nibble_of_nat n) = nibble_of_nat n.
Proof.
  intros n.
  unfold nibble_of_nat.
  assert (n mod 16 < 16) by (apply Nat.mod_upper_bound; lia).
  rewrite Nat.mod_small by exact H.
  reflexivity.
Qed.

Lemma get_reg_after_INC : forall s r,
  length (regs s) = 16 ->
  r < 16 ->
  get_reg (execute s (INC r)) r = nibble_of_nat (get_reg s r + 1).
Proof.
  intros s r Hlen Hr.
  unfold execute, get_reg, set_reg. simpl.
  rewrite nth_update_nth_eq by (rewrite Hlen; exact Hr).
  apply nibble_of_nat_idempotent.
Qed.

Lemma inc_reg : forall r old,
  r < 16 ->
  {{| fun s => get_reg s r = old /\ old < 16 |}}
      [INC r]
  {{| fun s => get_reg s r = (old + 1) mod 16 |}}.
Proof.
  intros r old Hr.
  unfold hoare_prog. intros s HWF [Hreg Hold].
  simpl exec_program.
  assert (HWF1: WF (execute s (INC r))).
  { apply execute_INC_WF; [exact HWF | unfold instr_wf; exact Hr]. }
  split. exact HWF1.
  unfold execute, get_reg, set_reg. simpl.
  destruct HWF as [HlenR _].
  assert (Hlen_r: r < length (regs s)) by (rewrite HlenR; exact Hr).
  rewrite nth_update_nth_eq by exact Hlen_r.
  unfold nibble_of_nat.
  rewrite Nat.Div0.mod_mod by lia.
  f_equal. unfold get_reg in Hreg. rewrite Hreg. reflexivity.
Qed.

(* ==================== Integration Theorem =================== *)

Theorem load_and_frame : forall n r1 r2 v1 v2,
  n < 16 ->
  {{| fun s => get_reg s r1 = v1 /\ get_reg s r2 = v2 |}}
      [LDM n]
  {{| fun s => acc s = n /\ get_reg s r1 = v1 /\ get_reg s r2 = v2 |}}.
Proof.
  intros n r1 r2 v1 v2 Hn.
  unfold hoare_prog. intros s HWF [Hr1 Hr2].
  simpl exec_program.

  assert (HWF1: WF (execute s (LDM n))).
  { apply execute_LDM_WF; auto. }

  split. exact HWF1.

  unfold execute, get_reg in *. simpl.
  split; [|split].
  - unfold nibble_of_nat. rewrite Nat.mod_small by exact Hn. reflexivity.
  - exact Hr1.
  - exact Hr2.
Qed.

Theorem swap_preserves_registers : forall r a_val r_val r2 v2,
  r <> r2 ->
  r < 16 ->
  a_val < 16 ->
  r_val < 16 ->
  {{| fun s => acc s = a_val /\ get_reg s r = r_val /\ get_reg s r2 = v2 |}}
      [XCH r]
  {{| fun s => acc s = r_val /\ get_reg s r = a_val /\ get_reg s r2 = v2 |}}.
Proof.
  intros r a_val r_val r2 v2 Hneq Hr Ha Hb.
  unfold hoare_prog. intros s HWF [Hacc [Hreg Hr2]].
  simpl exec_program.

  assert (HWF1: WF (execute s (XCH r))).
  { apply execute_XCH_WF; auto. }

  split. exact HWF1.

  unfold execute, get_reg, set_reg in *. simpl.
  assert (HWF_copy := HWF).
  destruct HWF_copy as [HlenR [HforR [Hacc_bound _]]].
  assert (Hlen: r < length (regs s)) by (rewrite HlenR; exact Hr).

  split; [|split].
  - rewrite Hreg. reflexivity.
  - rewrite nth_update_nth_eq by exact Hlen.
    unfold nibble_of_nat. rewrite Hacc.
    rewrite Nat.mod_small by exact Ha. reflexivity.
  - rewrite nth_update_nth_neq by lia. exact Hr2.
Qed.

Theorem identity_with_frame : forall a r1 r2 v1 v2,
  a < 16 ->
  {{| fun s => acc s = a /\ get_reg s r1 = v1 /\ get_reg s r2 = v2 |}}
      [NOP; CMA; CMA; NOP]
  {{| fun s => acc s = a /\ get_reg s r1 = v1 /\ get_reg s r2 = v2 |}}.
Proof.
  intros a r1 r2 v1 v2 Ha.
  unfold hoare_prog. intros s HWF [Hacc [Hr1 Hr2]].
  simpl exec_program.

  assert (HWF1: WF (execute s NOP)).
  { apply execute_NOP_WF; auto. }

  assert (HWF2: WF (execute (execute s NOP) CMA)).
  { apply execute_CMA_WF; auto. }

  assert (HWF3: WF (execute (execute (execute s NOP) CMA) CMA)).
  { apply execute_CMA_WF; auto. }

  assert (HWF4: WF (execute (execute (execute (execute s NOP) CMA) CMA) NOP)).
  { apply execute_NOP_WF; auto. }

  split. exact HWF4.

  unfold execute. simpl.
  rewrite Hacc.
  split; [|split].
  - do 16 (destruct a; simpl; [reflexivity|]); lia.
  - exact Hr1.
  - exact Hr2.
Qed.

(* ==================== Automation Tactics =================== *)

Ltac hoare_auto :=
  match goal with
  | |- {{ _ }} NOP {{ _ }} => apply hoare_NOP
  | |- {{ _ }} CLB {{ _ }} => apply hoare_CLB
  | |- {{ _ }} CLC {{ _ }} => apply hoare_CLC
  | |- {{ _ }} STC {{ _ }} => apply hoare_STC
  | |- {{ _ }} CMC {{ _ }} => apply hoare_CMC
  | |- {{ _ }} CMA {{ _ }} => apply hoare_CMA
  | |- {{ _ }} IAC {{ _ }} => apply hoare_IAC
  | |- {{ _ }} DAC {{ _ }} => apply hoare_DAC
  | |- {{ _ }} RAL {{ _ }} => apply hoare_RAL
  | |- {{ _ }} RAR {{ _ }} => apply hoare_RAR
  | |- {{ _ }} TCC {{ _ }} => apply hoare_TCC
  | |- {{ _ }} TCS {{ _ }} => apply hoare_TCS
  | |- {{ _ }} DAA {{ _ }} => apply hoare_DAA
  | |- {{ _ }} KBP {{ _ }} => apply hoare_KBP
  | |- {{ _ }} LDM _ {{ _ }} => apply hoare_LDM
  | |- {{ _ }} LD _ {{ _ }} => apply hoare_LD
  | |- {{ _ }} INC _ {{ _ }} => apply hoare_INC
  | |- {{ _ }} ADD _ {{ _ }} => apply hoare_ADD
  | |- {{ _ }} SUB _ {{ _ }} => apply hoare_SUB
  | |- {{ _ }} XCH _ {{ _ }} => apply hoare_XCH
  | |- {{ _ }} RDM {{ _ }} => apply hoare_RDM
  | |- {{ _ }} WRM {{ _ }} => apply hoare_WRM
  | |- {{ _ }} ADM {{ _ }} => apply hoare_ADM
  | |- {{ _ }} SBM {{ _ }} => apply hoare_SBM
  | |- {{ _ }} DCL {{ _ }} => apply hoare_DCL
  | |- {{ _ }} JUN _ {{ _ }} => apply hoare_JUN
  | |- {{ _ }} JMS _ {{ _ }} => apply hoare_JMS
  | |- {{ _ }} BBL _ {{ _ }} => apply hoare_BBL
  | _ => fail "No matching Hoare rule"
  end.

Example hoare_auto_test :
  {{ fun _ => True }}
     CLB
  {{ fun s => acc s = 0 }}.
Proof.
  apply hoare_consequence with (P := fun _ => True) (Q := fun s => acc s = 0 /\ carry s = false).
  - intros; auto.
  - apply hoare_CLB.
  - intros s [H _]. exact H.
Qed.

(* ==================== Verified Subroutines =================== *)

Example ram_write_read_roundtrip : forall r val,
  val < 16 ->
  r < 16 ->
  r mod 2 = 1 ->
  {{| fun s => acc s = val |}}
      [SRC r; WRM; RDM]
  {{| fun s => acc s = val |}}.
Proof.
  intros r val Hval Hr Hodd.
  unfold hoare_prog. intros s HWF Hacc.
  simpl exec_program.
  assert (HWF1: WF (execute s (SRC r))).
  { apply execute_SRC_WF; [exact HWF | unfold instr_wf; split; [exact Hr | exact Hodd]]. }
  assert (HWF2: WF (execute (execute s (SRC r)) WRM)).
  { apply execute_WRM_WF. exact HWF1. }
  assert (HWF3: WF (execute (execute (execute s (SRC r)) WRM) RDM)).
  { apply execute_RDM_WF. exact HWF2. }
  split. exact HWF3.
  pose proof (wrm_then_rdm_reads_back s r HWF) as H.
  rewrite Hacc in H. exact H.
Qed.

Example double_accumulator : forall v,
  {{| fun s => acc s = v /\ carry s = false /\ v < 8 |}}
      [RAL]
  {{| fun s => acc s = 2 * v /\ carry s = false |}}.
Proof.
  intro v.
  unfold hoare_prog. intros s HWF [Hacc [Hcarry Hv]].
  simpl exec_program.
  assert (HWF1: WF (execute s RAL)).
  { apply execute_RAL_WF. exact HWF. }
  split. exact HWF1.
  unfold execute. simpl.
  rewrite Hacc, Hcarry. simpl.
  do 8 (destruct v; simpl; [split; [reflexivity | reflexivity] | ]); lia.
Qed.

Example halve_accumulator : forall v,
  {{| fun s => acc s = v /\ carry s = false /\ v < 16 |}}
      [RAR]
  {{| fun s => acc s = v / 2 |}}.
Proof.
  intro v.
  unfold hoare_prog. intros s HWF [Hacc [Hcarry Hv]].
  simpl exec_program.
  assert (HWF1: WF (execute s RAR)).
  { apply execute_RAR_WF. exact HWF. }
  split. exact HWF1.
  unfold execute. simpl.
  rewrite Hacc, Hcarry. simpl.
  do 16 (destruct v; simpl; [reflexivity | ]); lia.
Qed.

Example test_bit_zero : forall v,
  {{| fun s => acc s = v /\ v < 16 |}}
      [RAR; TCC]
  {{| fun s => acc s = (if v mod 2 =? 1 then 1 else 0) /\ carry s = false |}}.
Proof.
  intro v.
  unfold hoare_prog. intros s HWF [Hacc Hv].
  simpl exec_program.
  assert (HWF1: WF (execute s RAR)).
  { apply execute_RAR_WF. exact HWF. }
  assert (HWF2: WF (execute (execute s RAR) TCC)).
  { apply execute_TCC_WF. exact HWF1. }
  split. exact HWF2.
  unfold execute. simpl.
  rewrite Hacc. simpl.
  destruct (v mod 2) eqn:Emod.
  - simpl. split; reflexivity.
  - destruct n.
    + simpl. split; reflexivity.
    + assert (v mod 2 < 2) by (apply Nat.mod_upper_bound; lia).
      lia.
Qed.

Lemma max_nibbles : forall a b : nat,
  a < 16 -> b < 16 -> Nat.max a b < 16.
Proof.
  intros a b Ha Hb.
  destruct (Nat.max_spec a b) as [[_ ->]|[_ ->]]; assumption.
Qed.

Example max_of_two_concrete :
  {{| fun s => (get_reg s 0 = 7 /\ get_reg s 1 = 3 /\ carry s = false) |}}
      [LD 0; SUB 1]
  {{| fun s => (carry s = true) |}}.
Proof.
  unfold hoare_prog. intros s HWF [Hr0 [Hr1 Hcarry]].
  simpl exec_program.
  assert (HWF1: WF (execute s (LD 0))).
  { apply execute_LD_WF; [exact HWF | unfold instr_wf; lia]. }
  assert (HWF2: WF (execute (execute s (LD 0)) (SUB 1))).
  { apply execute_SUB_WF; [exact HWF1 | unfold instr_wf; lia]. }
  split. exact HWF2.
  unfold execute. simpl. unfold get_reg in *. simpl in *.
  rewrite Hr0, Hr1, Hcarry. simpl. reflexivity.
Qed.

Example add_two_nibbles :
  {{| fun s => (get_reg s 0 = 5 /\ get_reg s 1 = 7 /\ carry s = false) |}}
      [LD 0; ADD 1]
  {{| fun s => (acc s = 12) |}}.
Proof.
  unfold hoare_prog. intros s HWF [Hr0 [Hr1 Hcarry]].
  simpl exec_program.
  assert (HWF1: WF (execute s (LD 0))).
  { apply execute_LD_WF; [exact HWF | unfold instr_wf; lia]. }
  assert (HWF2: WF (execute (execute s (LD 0)) (ADD 1))).
  { apply execute_ADD_WF; [exact HWF1 | unfold instr_wf; lia]. }
  split. exact HWF2.
  unfold execute. simpl. unfold get_reg in *. simpl in *.
  rewrite Hr0, Hr1, Hcarry. simpl. reflexivity.
Qed.
