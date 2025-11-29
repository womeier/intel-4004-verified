(* ===================================================================== *)
(*  Intel 4004 Microprocessor + MCS-4 RAM/ROM I/O Formalization in Coq   *)
(* ===================================================================== *)

Require Export Intel4004.utils.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.NArith.NArith.
Require Import Lia.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* ======================== 4002 RAM structure ======================== *)

(** 4002 RAM register: 16 main characters + 4 status characters. No bounds enforced. *)
Record RAMReg := mkRAMReg {
  reg_main   : list nibble;  (* 16 main characters *)
  reg_status : list nibble   (* 4 status characters S0..S3 *)
}.

(** 4002 RAM chip: 4 registers + 4-bit output port. No bounds enforced. *)
Record RAMChip := mkRAMChip {
  chip_regs  : list RAMReg;  (* 4 registers *)
  chip_port  : nibble        (* 4-bit output port *)
}.

(** 4002 RAM bank: 4 chips. No bounds enforced. *)
Record RAMBank := mkRAMBank {
  bank_chips : list RAMChip  (* 4 chips per bank *)
}.

(** RAM address selection state. Chip/reg latched by SRC; bank by DCL. No bounds enforced. *)
Record RAMSel := mkRAMSel {
  sel_chip : nat;   (* 0..3 *)
  sel_reg  : nat;   (* 0..3 *)
  sel_char : nat    (* 0..15 *)
}.

(* ============================ State ================================= *)

(** Complete Intel 4004 + MCS-4 system state. 17 fields. No bounds enforced by types. *)
Record Intel4004State := mkState {
  acc       : nibble;           (* 4-bit accumulator *)
  regs      : list nibble;      (* 16 4-bit registers R0..R15 *)
  carry     : bool;             (* carry/link flag *)
  pc        : addr12;           (* 12-bit program counter *)
  stack     : list addr12;      (* 3-level return stack *)
  ram_sys   : list RAMBank;     (* 4 banks × 4 chips × 4 regs × (16 main + 4 status) *)
  cur_bank  : nat;              (* 0..3, selected by DCL *)
  sel_ram   : RAMSel;           (* last RAM address sent by SRC (chip,reg,char) *)
  rom_ports : list nibble;      (* 16 ROM ports (4-bit), selected by last SRC *)
  sel_rom   : nat;              (* 0..15, last ROM port selected by SRC *)
  rom       : list byte;        (* program ROM (bytes) - writable via WPM *)
  test_pin  : bool;             (* TEST input (active low in JCN condition) *)
  prom_addr : addr12;           (* PROM programming address (set via ROM ports) *)
  prom_data : byte;             (* PROM programming data (set via ROM ports) *)
  prom_enable : bool            (* PROM write enable (set via ROM port control) *)
}.

(* =========================== Registers ============================== *)

(** Reads register r. Returns 0 if r >= length of register file. *)
Definition get_reg (s : Intel4004State) (r : nat) : nibble :=
  nth r (regs s) 0.

(** Sets register r to normalized value v. Preserves all other state fields. *)
Definition set_reg (s : Intel4004State) (r : nat) (v : nibble) : Intel4004State :=
  let new_regs := update_nth r (nibble_of_nat v) (regs s) in
  mkState (acc s) new_regs (carry s) (pc s) (stack s)
          (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
          (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s).

(** Reads register pair starting at r (rounds down to even). Returns high*16 + low. *)
Definition get_reg_pair (s : Intel4004State) (r : nat) : byte :=
  let r_even := r - (r mod 2) in
  let high := get_reg s r_even in
  let low  := get_reg s (r_even + 1) in
  (high * 16) + low.

(** Sets register pair starting at r (rounds down to even) to v split into high/low nibbles. *)
Definition set_reg_pair (s : Intel4004State) (r : nat) (v : byte) : Intel4004State :=
  let r_even := r - (r mod 2) in
  let high := v / 16 in
  let low  := v mod 16 in
  let s1 := set_reg s r_even high in
  set_reg s1 (r_even + 1) low.

(** Proves set_reg preserves register file length. *)
Lemma set_reg_preserves_length : forall s r v,
  length (regs (set_reg s r v)) = length (regs s).
Proof. intros. simpl. apply update_nth_length. Qed.

(** Proves set_reg_pair preserves register file length. *)
Lemma set_reg_pair_preserves_length : forall s r v,
  length (regs (set_reg_pair s r v)) = length (regs s).
Proof.
  intros. unfold set_reg_pair.
  rewrite set_reg_preserves_length.
  rewrite set_reg_preserves_length.
  reflexivity.
Qed.

(** Proves set_reg preserves Forall (< 16) bound on registers. *)
Lemma set_reg_preserves_Forall16 : forall s r v,
  Forall (fun x => x < 16) (regs s) ->
  Forall (fun x => x < 16) (regs (set_reg s r v)).
Proof.
  intros. simpl. eapply Forall_update_nth; eauto. apply nibble_lt16.
Qed.

(** Proves set_reg_pair preserves Forall (< 16) bound on registers. *)
Lemma set_reg_pair_preserves_Forall16 : forall s r v,
  Forall (fun x => x < 16) (regs s) ->
  Forall (fun x => x < 16) (regs (set_reg_pair s r v)).
Proof.
  intros. unfold set_reg_pair.
  apply set_reg_preserves_Forall16.
  apply set_reg_preserves_Forall16.
  assumption.
Qed.

(** Proves nth of bounded register file with default 0 is also bounded. *)
Lemma nth_reg0_lt16 : forall s n,
  Forall (fun x => x < 16) (regs s) ->
  nth n (regs s) 0 < 16.
Proof. intros. eapply nth_Forall_lt with (k:=16); eauto; lia. Qed.

(* ============================= Stack ================================ *)

(** Pushes addr onto 3-level stack. Discards bottom level if full. *)
Definition push_stack (s : Intel4004State) (addr : addr12) : Intel4004State :=
  let new_stack :=
    match stack s with
    | [] => [addr]
    | [a] => [addr; a]
    | [a; b] => [addr; a; b]
    | a :: b :: c :: _ => [addr; a; b] (* Max 3 levels *)
    end in
  mkState (acc s) (regs s) (carry s) (pc s) new_stack
          (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
          (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s).

(** Pops top address from stack. Returns None if stack empty. *)
Definition pop_stack (s : Intel4004State) : (option addr12 * Intel4004State) :=
  match stack s with
  | [] => (None, s)
  | a :: rest =>
      (Some a, mkState (acc s) (regs s) (carry s) (pc s) rest
                       (ram_sys s) (cur_bank s) (sel_ram s) (rom_ports s) (sel_rom s)
                       (rom s) (test_pin s) (prom_addr s) (prom_data s) (prom_enable s))
  end.

(** Proves push_stack always produces stack of length <= 3. *)
Lemma push_stack_len_le3 : forall s a,
  length (stack (push_stack s a)) <= 3.
Proof. intros s a. unfold push_stack. destruct (stack s) as [|x [|x0 [|x1 l]]]; simpl; lia. Qed.

(** Proves pop_stack preserves stack length bound <= 3 when input <= 4. *)
Lemma pop_stack_len_le3 : forall s x s',
  length (stack s) <= 4 ->
  pop_stack s = (x, s') -> length (stack s') <= 3.
Proof.
  intros s x s' Hlen H. unfold pop_stack in H.
  destruct (stack s) as [|h l] eqn:Es; simpl in H.
  - inversion H; subst. rewrite Es. simpl. auto.
  - inversion H; subst; clear H; simpl.
    destruct l as [|h1 l']; simpl.
    + lia.
    + destruct l' as [|h2 l'']; simpl.
      * lia.
      * destruct l'' as [|h3 l''']; simpl.
        ** lia.
        ** destruct l''' as [|h4 l4].
           --- auto with arith.
           --- exfalso.
               subst. simpl in Hlen. lia.
Qed.

(** Proves pop_stack preserves Forall (< 4096) on stack addresses. *)
Lemma pop_stack_Forall_addr12 : forall s a s',
  Forall (fun x => x < 4096) (stack s) ->
  pop_stack s = (a, s') ->
  Forall (fun x => x < 4096) (stack s').
Proof.
  intros s a s' H Hp. unfold pop_stack in Hp.
  destruct (stack s) as [|h t] eqn:Es.
  - inversion Hp; subst. simpl. rewrite Es. auto.
  - inversion Hp; subst; simpl. inversion H; subst; auto.
Qed.

(* ============================ ROM =================================== *)

(** Fetches byte from ROM at addr. Returns 0 if addr >= ROM length. *)
Definition fetch_byte (s : Intel4004State) (addr : addr12) : byte :=
  nth addr (rom s) 0.

(** Increments PC by 1, normalized to 12-bit address space. *)
Definition pc_inc1 (s : Intel4004State) : addr12 := addr12_of_nat (pc s + 1).

(** Increments PC by 2, normalized to 12-bit address space. *)
Definition pc_inc2 (s : Intel4004State) : addr12 := addr12_of_nat (pc s + 2).

(** Extracts page number (upper 4 bits) from 12-bit address. *)
Definition page_of (p:addr12) := p / 256.

(** Computes base address of page containing p. *)
Definition page_base (p:addr12) := (page_of p) * 256.

(* ========================= RAM navigation =========================== *)

(** RAM system dimension constants. *)
Definition NBANKS := 4.
Definition NCHIPS := 4.
Definition NREGS  := 4.
Definition NMAIN  := 16.
Definition NSTAT  := 4.

(** Retrieves bank b from state. Returns empty default if b >= NBANKS. *)
Definition get_bank (s:Intel4004State) (b:nat) : RAMBank :=
  nth b (ram_sys s) (mkRAMBank (repeat (mkRAMChip (repeat (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)) NREGS) 0) NCHIPS)).

(** Retrieves chip c from bank. Returns empty default if c >= NCHIPS. *)
Definition get_chip (bk:RAMBank) (c:nat) : RAMChip :=
  nth c (bank_chips bk) (mkRAMChip (repeat (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)) NREGS) 0).

(** Retrieves register r from chip. Returns empty default if r >= NREGS. *)
Definition get_regRAM (ch:RAMChip) (r:nat) : RAMReg :=
  nth r (chip_regs ch) (mkRAMReg (repeat 0 NMAIN) (repeat 0 NSTAT)).

(** Retrieves main character i from register. Returns 0 if i >= NMAIN. *)
Definition get_main (rg:RAMReg) (i:nat) : nibble := nth i (reg_main rg) 0.

(** Retrieves status character i from register. Returns 0 if i >= NSTAT. *)
Definition get_stat (rg:RAMReg) (i:nat) : nibble := nth i (reg_status rg) 0.

(** Updates main character i in register to normalized v. *)
Definition upd_main_in_reg (rg:RAMReg) (i:nat) (v:nibble) : RAMReg :=
  mkRAMReg (update_nth i (nibble_of_nat v) (reg_main rg)) (reg_status rg).

(** Updates status character i in register to normalized v. *)
Definition upd_stat_in_reg (rg:RAMReg) (i:nat) (v:nibble) : RAMReg :=
  mkRAMReg (reg_main rg) (update_nth i (nibble_of_nat v) (reg_status rg)).

(** Updates register r in chip with new register value. *)
Definition upd_reg_in_chip (ch:RAMChip) (r:nat) (rg:RAMReg) : RAMChip :=
  mkRAMChip (update_nth r rg (chip_regs ch)) (chip_port ch).

(** Updates output port in chip to normalized v. *)
Definition upd_port_in_chip (ch:RAMChip) (v:nibble) : RAMChip :=
  mkRAMChip (chip_regs ch) (nibble_of_nat v).

(** Updates chip c in bank with new chip value. *)
Definition upd_chip_in_bank (bk:RAMBank) (c:nat) (ch:RAMChip) : RAMBank :=
  mkRAMBank (update_nth c ch (bank_chips bk)).

(** Updates bank b in system with new bank value. Returns updated bank list. *)
Definition upd_bank_in_sys (s:Intel4004State) (b:nat) (bk:RAMBank) : list RAMBank :=
  update_nth b bk (ram_sys s).

(** Reads main character from RAM using current bank and latched selection. *)
Definition ram_read_main (s:Intel4004State) : nibble :=
  let bk := get_bank s (cur_bank s) in
  let ch := get_chip bk (sel_chip (sel_ram s)) in
  let rg := get_regRAM ch (sel_reg (sel_ram s)) in
  get_main rg (sel_char (sel_ram s)).

(** Writes main character to RAM using current bank and latched selection. Returns updated bank list. *)
Definition ram_write_main_sys (s:Intel4004State) (v:nibble) : list RAMBank :=
  let b := cur_bank s in
  let c := sel_chip (sel_ram s) in
  let r := sel_reg  (sel_ram s) in
  let i := sel_char (sel_ram s) in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let rg := get_regRAM ch r in
  let rg' := upd_main_in_reg rg i v in
  let ch' := upd_reg_in_chip ch r rg' in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

(** Writes status character idx to RAM using current bank and latched selection. Returns updated bank list. *)
Definition ram_write_status_sys (s:Intel4004State) (idx:nat) (v:nibble) : list RAMBank :=
  let b := cur_bank s in
  let c := sel_chip (sel_ram s) in
  let r := sel_reg  (sel_ram s) in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let rg := get_regRAM ch r in
  let rg' := upd_stat_in_reg rg idx v in
  let ch' := upd_reg_in_chip ch r rg' in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.

(** Writes to RAM chip output port using current bank and latched chip selection. Returns updated bank list. *)
Definition ram_write_port_sys (s:Intel4004State) (v:nibble) : list RAMBank :=
  let b := cur_bank s in
  let c := sel_chip (sel_ram s) in
  let bk := get_bank s b in
  let ch := get_chip bk c in
  let ch' := upd_port_in_chip ch v in
  let bk' := upd_chip_in_bank bk c ch' in
  upd_bank_in_sys s b bk'.
