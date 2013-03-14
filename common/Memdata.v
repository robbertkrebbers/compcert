(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** In-memory representation of values. *)

Require Import Coqlib.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.

(** * Properties of memory chunks *)

(** Memory reads and writes are performed by quantities called memory chunks,
  encoding the type, size and signedness of the chunk being addressed.
  The following functions extract the size information from a chunk. *)

Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 8
  end.

Lemma size_chunk_pos:
  forall chunk, size_chunk chunk > 0.
Proof.
  intros. destruct chunk; simpl; omega.
Qed.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  nat_of_Z(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z_of_nat (size_chunk_nat chunk).
Proof.
  intros. destruct chunk; reflexivity.
Qed.

Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros. 
  generalize (size_chunk_pos chunk). rewrite size_chunk_conv. 
  destruct (size_chunk_nat chunk).
  simpl; intros; omegaContradiction.
  intros; exists n; auto.
Qed.

(** Memory reads and writes must respect alignment constraints:
  the byte offset of the location being addressed should be an exact
  multiple of the natural alignment for the chunk being addressed.
  This natural alignment is defined by the following 
  [align_chunk] function.  Some target architectures
  (e.g. PowerPC and x86) have no alignment constraints, which we could
  reflect by taking [align_chunk chunk = 1].  However, other architectures
  have stronger alignment requirements.  The following definition is
  appropriate for PowerPC, ARM and x86. *)

Definition align_chunk (chunk: memory_chunk) : Z := 
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 4
  end.

Lemma align_chunk_pos:
  forall chunk, align_chunk chunk > 0.
Proof.
  intro. destruct chunk; simpl; omega.
Qed.

Lemma align_size_chunk_divides:
  forall chunk, (align_chunk chunk | size_chunk chunk).
Proof.
  intros. destruct chunk; simpl; try apply Zdivide_refl; exists 2; auto. 
Qed.

Lemma align_le_divides:
  forall chunk1 chunk2,
  align_chunk chunk1 <= align_chunk chunk2 -> (align_chunk chunk1 | align_chunk chunk2).
Proof.
  intros. destruct chunk1; destruct chunk2; simpl in *;
  solve [ omegaContradiction
        | apply Zdivide_refl
        | exists 2; reflexivity
        | exists 4; reflexivity
        | exists 8; reflexivity ].
Qed.

(** * Memory values *)

(** A ``memory value'' is a byte-sized quantity that describes the current
  content of a memory cell.  It can be either:
- a concrete 8-bit integer;
- a byte-sized fragment of an opaque pointer;
- a special construct [PointerPad] that represents the padding belonging
  to a single pointer fragment written as an integer.
- the special constant [Undef] that represents uninitialized memory.
*)

(** Values stored in memory cells. *)

Inductive memval: Type :=
  | Undef: memval
  | Byte: byte -> memval
  | Pointer: block -> int -> nat -> memval
  | PointerPad : memval.

(** * Encoding and decoding integers *)

(** We define functions to convert between integers and lists of bytes
  of a given length *)

Fixpoint bytes_of_int (n: nat) (x: Z) {struct n}: list byte :=
  match n with
  | O => nil
  | S m => Byte.repr x :: bytes_of_int m (x / 256)
  end.

Fixpoint int_of_bytes (l: list byte): Z :=
  match l with
  | nil => 0
  | b :: l' => Byte.unsigned b + int_of_bytes l' * 256
  end.

(** Length properties *)

Lemma length_bytes_of_int:
  forall n x, length (bytes_of_int n x) = n.
Proof.
  induction n; simpl; intros. auto. decEq. auto.
Qed.

Lemma bytes_of_int_length:
  forall sz x, length (bytes_of_int sz x) = sz.
Proof.
  intros. apply length_bytes_of_int.
Qed.

(** Decoding after encoding *)

Lemma int_of_bytes_of_int:
  forall n x,
  int_of_bytes (bytes_of_int n x) = x mod (two_p (Z_of_nat n * 8)).
Proof.
  induction n; intros.
  simpl. rewrite Zmod_1_r. auto.
  rewrite inj_S. simpl.
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  rewrite Zmod_recombine. rewrite IHn. rewrite Zplus_comm. 
  change (Byte.unsigned (Byte.repr x)) with (Byte.Z_mod_modulus x). 
  rewrite Byte.Z_mod_modulus_eq. reflexivity. 
  apply two_p_gt_ZERO. omega. apply two_p_gt_ZERO. omega.
Qed.

Lemma int_of_bytes_of_int_1:
  forall x, Int.repr (int_of_bytes (bytes_of_int 1 (Int.unsigned x))) = Int.zero_ext 8 x.
Proof.
  intros. rewrite int_of_bytes_of_int. 
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute. intuition congruence. 
Qed.

Lemma int_of_bytes_of_int_2:
  forall x, Int.repr (int_of_bytes (bytes_of_int 2 (Int.unsigned x))) = Int.zero_ext 16 x.
Proof.
  intros. rewrite int_of_bytes_of_int. 
  rewrite <- (Int.repr_unsigned (Int.zero_ext 16 x)).
  decEq. symmetry. apply Int.zero_ext_mod. compute. intuition congruence. 
Qed.

Lemma int_of_bytes_of_int_4:
  forall x, Int.repr (int_of_bytes (bytes_of_int 4 (Int.unsigned x))) = x.
Proof.
  intros. rewrite int_of_bytes_of_int. transitivity (Int.repr (Int.unsigned x)).
  decEq. apply Zmod_small. apply Int.unsigned_range. apply Int.repr_unsigned.
Qed.

Lemma int_of_bytes_of_int_8:
  forall x, Int64.repr (int_of_bytes (bytes_of_int 8 (Int64.unsigned x))) = x.
Proof.
  intros. rewrite int_of_bytes_of_int. transitivity (Int64.repr (Int64.unsigned x)).
  decEq. apply Zmod_small. apply Int64.unsigned_range. apply Int64.repr_unsigned.
Qed.

Lemma int_of_bytes_append:
  forall l2 l1, 
  int_of_bytes (l1 ++ l2) = int_of_bytes l1 + int_of_bytes l2 * two_p (Z_of_nat (length l1) * 8).
Proof.
  induction l1; simpl int_of_bytes; intros.
  simpl. ring.
  simpl length. rewrite inj_S. 
  replace (Z.succ (Z.of_nat (length l1)) * 8) with (Z_of_nat (length l1) * 8 + 8) by omega.
  rewrite two_p_is_exp. change (two_p 8) with 256. rewrite IHl1. ring.
  omega. omega.
Qed.

Lemma int_of_bytes_range:
  forall l, 0 <= int_of_bytes l < two_p (Z_of_nat (length l) * 8).
Proof.
  induction l; intros. 
  simpl. omega.
  simpl length. rewrite inj_S. 
  replace (Z.succ (Z.of_nat (length l)) * 8) with (Z.of_nat (length l) * 8 + 8) by omega.
  rewrite two_p_is_exp. change (two_p 8) with 256. 
  simpl int_of_bytes. generalize (Byte.unsigned_range a). 
  change Byte.modulus with 256. omega. 
  omega. omega. 
Qed.

Lemma bytes_of_int_append:
  forall n2 x2 n1 x1,
  0 <= x1 < two_p (Z_of_nat n1 * 8) ->
  bytes_of_int (n1 + n2) (x1 + x2 * two_p (Z_of_nat n1 * 8)) =
  bytes_of_int n1 x1 ++ bytes_of_int n2 x2.
Proof.
  induction n1; intros.
- simpl in *. f_equal. omega. 
- assert (E: two_p (Z.of_nat (S n1) * 8) = two_p (Z.of_nat n1 * 8) * 256).
  {
    rewrite inj_S. change 256 with (two_p 8). rewrite <- two_p_is_exp. 
    f_equal. omega. omega. omega. 
  }
  rewrite E in *. simpl. f_equal.
  apply Byte.eqm_samerepr. exists (x2 * two_p (Z.of_nat n1 * 8)). 
  change Byte.modulus with 256. ring.
  rewrite Zmult_assoc. rewrite Z_div_plus. apply IHn1.
  apply Zdiv_interval_1. omega. apply two_p_gt_ZERO; omega. omega. 
  assumption. omega.
Qed.

(** A length-[n] encoding depends only on the low [8*n] bits of the integer. *)

Lemma bytes_of_int_mod:
  forall n x y,
  Int.eqmod (two_p (Z_of_nat n * 8)) x y ->
  bytes_of_int n x = bytes_of_int n y.
Proof.
  induction n.
  intros; simpl; auto.
  intros until y.
  rewrite inj_S. 
  replace (Zsucc (Z_of_nat n) * 8) with (Z_of_nat n * 8 + 8) by omega.
  rewrite two_p_is_exp; try omega. 
  intro EQM.
  simpl; decEq. 
  apply Byte.eqm_samerepr. red. 
  eapply Int.eqmod_divides; eauto. apply Zdivide_factor_l.
  apply IHn.
  destruct EQM as [k EQ]. exists k. rewrite EQ. 
  rewrite <- Z_div_plus_full_l. decEq. change (two_p 8) with 256. ring. omega.
Qed.

Lemma bytes_of_int_8_mod:
  forall x y,
  Int.eqmod (two_p 8) x y ->
  bytes_of_int 1 x = bytes_of_int 1 y.
Proof. apply (bytes_of_int_mod 1). Qed.

Lemma bytes_of_int_16_mod:
  forall x y,
  Int.eqmod (two_p 16) x y ->
  bytes_of_int 2 x = bytes_of_int 2 y.
Proof. apply (bytes_of_int_mod 2). Qed.

(** * Encoding and decoding values *)

Definition inj_bytes (bl: list byte) : list memval :=
  List.map Byte bl.

Fixpoint proj_bytes (vl: list memval) : option (list byte) :=
  match vl with
  | nil => Some nil
  | Byte b :: vl' =>
      match proj_bytes vl' with None => None | Some bl => Some(b :: bl) end
  | _ => None
  end.

Remark length_inj_bytes:
  forall bl, length (inj_bytes bl) = length bl.
Proof.
  intros. apply List.map_length. 
Qed.

Remark proj_inj_bytes:
  forall bl, proj_bytes (inj_bytes bl) = Some bl.
Proof.
  induction bl; simpl. auto. rewrite IHbl. auto.
Qed.

Lemma inj_proj_bytes:
  forall cl bl, proj_bytes cl = Some bl -> cl = inj_bytes bl.
Proof.
  induction cl; simpl; intros. 
  inv H; auto.
  destruct a; try congruence. destruct (proj_bytes cl); inv H.
  simpl. decEq. auto.
Qed.

Fixpoint inj_pointer (n: nat) (b: block) (ofs: int) {struct n}: list memval :=
  match n with
  | O => nil
  | S m => Pointer b ofs m :: inj_pointer m b ofs
  end.

Definition inj_pointer_seg (n : nat) (b: block) (ofs: int) (i : nat) : list memval :=
  match n with
  | O => nil
  | S m => Pointer b ofs i :: list_repeat m PointerPad
  end.

Fixpoint check_pointer (n: nat) (b: block) (ofs: int) (vl: list memval) 
                       {struct n} : bool :=
  match n, vl with
  | O, nil => true
  | S m, Pointer b' ofs' m' :: vl' =>
      eq_block b b' && Int.eq_dec ofs ofs' && beq_nat m m' && check_pointer m b ofs vl'
  | _, _ => false
  end.

Definition proj_pointer (vl: list memval) : option (block * int) :=
  match vl with
  | Pointer b ofs n :: vl' =>
     if check_pointer 4 b ofs vl then Some (b, ofs) else None
  | _ => None
  end.

Fixpoint check_pointer_pad (n: nat) (vl: list memval) : bool :=
  match n, vl with
  | O, nil => true
  | S m, PointerPad :: vl' => check_pointer_pad m vl'
  | _, _ => false
  end.
Definition proj_pointer_seg (n : nat) (vl: list memval) : option (block * int * nat) :=
  match n, vl with
  | S m, Pointer b ofs i :: vl' =>
     if check_pointer_pad m vl' then Some (b, ofs, i) else None
  | _, _ => None
  end.

Lemma check_inj_pointer:
  forall b ofs n, check_pointer n b ofs (inj_pointer n b ofs) = true.
Proof.
  induction n; simpl. auto. 
  unfold proj_sumbool. rewrite dec_eq_true. rewrite dec_eq_true.  
  rewrite <- beq_nat_refl. simpl; auto.
Qed.
Lemma check_repeat_pointer_pad:
  forall n, check_pointer_pad n (list_repeat n PointerPad) = true.
Proof.
  induction n; simpl; auto. 
Qed.

Lemma proj_inj_pointer:
  forall b ofs, proj_pointer (inj_pointer 4 b ofs) = Some (b, ofs).
Proof.
  intros. change (proj_pointer (inj_pointer 4 b ofs)) with
    (if check_pointer 4 b ofs (inj_pointer 4 b ofs) then Some (b, ofs) else None).
  now rewrite check_inj_pointer.
Qed.

Lemma proj_inj_pointer_seg:
  forall n b ofs i,
  (0 < n)%nat ->
  proj_pointer_seg n (inj_pointer_seg n b ofs i) = Some (b, ofs, i).
Proof.
  intros. destruct n as [|n]; [omega|].
  unfold inj_pointer_seg. unfold proj_pointer_seg.
  now rewrite check_repeat_pointer_pad.
Qed.

Lemma proj_inj_pointer_seg_None:
  forall n b ofs i, proj_pointer (inj_pointer_seg n b ofs i) = None.
Proof.
  intros. destruct n as [|[|?]]; simpl; rewrite ?andb_false_r; auto.
Qed.

Lemma check_pointer_inv:
  forall b ofs n mv,
  check_pointer n b ofs mv = true -> mv = inj_pointer n b ofs.
Proof.
  induction n; destruct mv; simpl; auto; try discriminate.
  destruct m; try discriminate. intro.
  rewrite !andb_true_iff in H. destruct H as [[[??]?]?].
  apply beq_nat_true in H1. apply proj_sumbool_true in H.
  apply proj_sumbool_true in H0. subst. now rewrite (IHn mv).
Qed.

Lemma proj_pointer_inv:
  forall b ofs mv,
  proj_pointer mv = Some (b,ofs) -> mv = inj_pointer 4 b ofs.
Proof.
  intros. apply (check_pointer_inv b ofs 4 mv).
  destruct mv as [|[]]; try discriminate. unfold proj_pointer in *.
  destruct (check_pointer _ b0 _ _) eqn:?; congruence.
Qed.

Lemma check_pointer_pad_inv:
  forall n mv,
  check_pointer_pad n mv = true -> mv = list_repeat n PointerPad.
Proof.
  induction n; destruct mv; simpl; auto; try discriminate.
  destruct m; try discriminate. intros; f_equal; auto.
Qed.

Lemma proj_pointer_seg_inv:
  forall n b ofs i mv,
  proj_pointer_seg n mv = Some (b,ofs,i) -> mv = inj_pointer_seg n b ofs i.
Proof.
  intros [|n] b ofs i [|[]] ?; simpl in *; try discriminate.
  destruct (check_pointer_pad _ _) eqn:?; inv H.
  now erewrite <-check_pointer_pad_inv by eauto.
Qed.

Lemma length_proj_bytes:
  forall l b, proj_bytes l = Some b -> length b = length l.
Proof.
  induction l; simpl; intros. 
  inv H; auto.
  destruct a; try discriminate. 
  destruct (proj_bytes l) eqn:E; inv H. 
  simpl. f_equal. auto.
Qed.

Lemma proj_bytes_append:
  forall l2 l1,
  proj_bytes (l1 ++ l2) =
  match proj_bytes l1, proj_bytes l2 with
  | Some b1, Some b2 => Some (b1 ++ b2)
  | _, _ => None
  end.
Proof.
  induction l1; simpl.
  destruct (proj_bytes l2); auto.
  destruct a; auto. rewrite IHl1. 
  destruct (proj_bytes l1); auto. destruct (proj_bytes l2); auto. 
Qed.

Arguments bytes_of_int _ _ : simpl never.
Arguments int_of_bytes _ : simpl never.
Arguments proj_bytes _ : simpl never.
Arguments inj_bytes _ : simpl never.
Arguments check_pointer _ _ _ _ : simpl never.
Arguments check_pointer_pad _ _ : simpl never.
Arguments inj_pointer _ _ _ : simpl never.
Arguments inj_pointer_seg _ _ _ _ : simpl never.
Arguments proj_pointer _ : simpl never.
Arguments proj_pointer_seg _ _ : simpl never.


Definition rev_if_be {A} (l: list A) : list A :=
  if Archi.big_endian then List.rev_append l nil else l.

Lemma rev_if_be_length:
  forall (A: Type) (l : list A), length (rev_if_be l) = length l.
Proof.
  intros. unfold rev_if_be. destruct Archi.big_endian; auto.
  now rewrite rev_append_rev, app_nil_r, List.rev_length.
Qed.
Lemma rev_if_be_involutive:
  forall (A: Type) (l : list A), rev_if_be (rev_if_be l) = l.
Proof.
  intros. unfold rev_if_be. destruct Archi.big_endian; auto.
  now rewrite !rev_append_rev, !app_nil_r, List.rev_involutive. 
Qed.
Lemma rev_if_be_repeat:
  forall (A : Type) n (x : A), rev_if_be (list_repeat n x) = list_repeat n x.
Proof.
  intros. unfold rev_if_be. destruct Archi.big_endian; auto.
  rewrite rev_append_rev, app_nil_r.
  induction n; intros; simpl; auto.
  change (x :: nil) with (list_repeat 1 x).
  now rewrite IHn, <-list_repeat_plus, plus_comm.
Qed.
Lemma in_rev_if_be:
  forall (A : Type) (x : A) (l : list A), In x (rev_if_be l) <-> In x l.
Proof.
  intros. unfold rev_if_be. now destruct Archi.big_endian;
    rewrite ?rev_append_rev, ?app_nil_r, <-?in_rev.
Qed.
Lemma rev_if_be_forall2:
  forall (A B : Type) (P : A -> B -> Prop) l1 l2,
  list_forall2 P l1 l2 -> list_forall2 P (rev_if_be l1) (rev_if_be l2).
Proof.
  intros until 0. unfold rev_if_be. destruct Archi.big_endian; auto.
  rewrite !rev_append_rev, !app_nil_r.
  induction 1; simpl.
  * constructor.
  * apply list_forall2_app; repeat constructor; auto.
Qed.
Lemma rev_if_be_app:
  forall (A : Type) (l1 l2 : list A), rev_if_be (l1 ++ l2) =
    rev_if_be (if Archi.big_endian then l2 else l1) ++
    rev_if_be (if Archi.big_endian then l1 else l2).
Proof.
  intros. unfold rev_if_be. destruct Archi.big_endian; auto.
  now rewrite !rev_append_rev, !app_nil_r, rev_app_distr.
Qed.

Definition encode_val (chunk: memory_chunk) (v: val) : list memval :=
  rev_if_be
  match v, chunk with
  | Vint n, (Mint8signed | Mint8unsigned) => inj_bytes (bytes_of_int 1 (Int.unsigned n))
  | Vint n, (Mint16signed | Mint16unsigned) => inj_bytes (bytes_of_int 2 (Int.unsigned n))
  | Vint n, Mint32 => inj_bytes (bytes_of_int 4 (Int.unsigned n))
  | Vptrseg b ofs i, (Mint8signed | Mint8unsigned) => inj_pointer_seg 1 b ofs i
  | Vptrseg b ofs i, Mint32 => inj_pointer_seg 4 b ofs i
  | Vptr b ofs, Mint32 => inj_pointer 4 b ofs
  | Vlong n, Mint64 => inj_bytes (bytes_of_int 8 (Int64.unsigned n))
  | Vfloat n, Mfloat32 => inj_bytes (bytes_of_int 4 (Int.unsigned (Float.bits_of_single n)))
  | Vfloat n, Mfloat64 => inj_bytes (bytes_of_int 8 (Int64.unsigned (Float.bits_of_double n)))
  | _, _ => list_repeat (size_chunk_nat chunk) Undef
  end.

Definition decode_val (chunk: memory_chunk) (vl: list memval) : val :=
  let vl := rev_if_be vl in
  match proj_bytes vl with
  | Some bl =>
      match chunk with
      | Mint8signed => Vint (Int.sign_ext 8 (Int.repr (int_of_bytes bl)))
      | Mint8unsigned => Vint (Int.zero_ext 8 (Int.repr (int_of_bytes bl)))
      | Mint16signed => Vint (Int.sign_ext 16 (Int.repr (int_of_bytes bl)))
      | Mint16unsigned => Vint (Int.zero_ext 16 (Int.repr (int_of_bytes bl)))
      | Mint32 => Vint (Int.repr (int_of_bytes bl))
      | Mint64 => Vlong (Int64.repr (int_of_bytes bl))
      | Mfloat32 => Vfloat (Float.single_of_bits (Int.repr (int_of_bytes bl)))
      | Mfloat64 => Vfloat(Float.double_of_bits (Int64.repr (int_of_bytes bl)))
      end
  | None =>
      match chunk with
      | Mint32 =>
          match proj_pointer vl with
          | Some (b,ofs) => Vptr b ofs
          | None =>
              match proj_pointer_seg 4 vl with
              | Some (b,ofs,i) => Vptrseg b ofs i
              | None => Vundef
              end
          end
      | Mint8signed | Mint8unsigned =>
          match proj_pointer_seg 1 vl with
          | Some (b,ofs,i) => Vptrseg b ofs i
          | None => Vundef
          end
      | _ => Vundef
      end
  end.

Definition decode_encode_val (v1: val) (chunk1 chunk2: memory_chunk) (v2: val) : Prop :=
  match v1, chunk1, chunk2 with
  | Vundef, _, _ => v2 = Vundef
  | Vint n, Mint8signed, Mint8signed => v2 = Vint(Int.sign_ext 8 n)
  | Vint n, Mint8unsigned, Mint8signed => v2 = Vint(Int.sign_ext 8 n)
  | Vint n, Mint8signed, Mint8unsigned => v2 = Vint(Int.zero_ext 8 n)
  | Vint n, Mint8unsigned, Mint8unsigned => v2 = Vint(Int.zero_ext 8 n)
  | Vint n, Mint16signed, Mint16signed => v2 = Vint(Int.sign_ext 16 n)
  | Vint n, Mint16unsigned, Mint16signed => v2 = Vint(Int.sign_ext 16 n)
  | Vint n, Mint16signed, Mint16unsigned => v2 = Vint(Int.zero_ext 16 n)
  | Vint n, Mint16unsigned, Mint16unsigned => v2 = Vint(Int.zero_ext 16 n)
  | Vint n, Mint32, Mint32 => v2 = Vint n
  | Vint n, Mint32, Mfloat32 => v2 = Vfloat(Float.single_of_bits n)
  | Vint n, (Mint64 | Mfloat32 | Mfloat64), _ => v2 = Vundef
  | Vint n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vptr b ofs, Mint32, Mint32 => v2 = Vptr b ofs
  | Vptr b ofs, _, _ => v2 = Vundef
  | Vlong n, Mint64, Mint64 => v2 = Vlong n
  | Vlong n, Mint64, Mfloat64 => v2 = Vfloat(Float.double_of_bits n)
  | Vlong n, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mfloat32|Mfloat64), _ => v2 = Vundef
  | Vlong n, _, _ => True (**r nothing meaningful to say about v2 *)
  | Vptrseg b ofs i, (Mint8signed | Mint8unsigned), (Mint8signed | Mint8unsigned) => v2 = Vptrseg b ofs i
  | Vptrseg b ofs i, Mint32, Mint32 => v2 = Vptrseg b ofs i
  | Vptrseg b ofs i, _, _ => v2 = Vundef
  | Vfloat f, Mfloat32, Mfloat32 => v2 = Vfloat(Float.singleoffloat f)
  | Vfloat f, Mfloat32, Mint32 => v2 = Vint(Float.bits_of_single f)
  | Vfloat f, Mfloat64, Mfloat64 => v2 = Vfloat f
  | Vfloat f, (Mint8signed|Mint8unsigned|Mint16signed|Mint16unsigned|Mint32|Mint64), _ => v2 = Vundef
  | Vfloat f, Mfloat64, Mint64 => v2 = Vlong(Float.bits_of_double f)
  | Vfloat f, _, _ => True   (* nothing interesting to say about v2 *)
  end.

Lemma encode_val_length:
  forall chunk v, length (encode_val chunk v) = size_chunk_nat chunk.
Proof.
  intros. unfold encode_val. rewrite rev_if_be_length.
  now destruct v, chunk; rewrite ?length_list_repeat,
    ?length_inj_bytes, ?length_bytes_of_int.
Qed.

Lemma decode_val_repeat_undef:
  forall chunk n, (0 < n)%nat -> decode_val chunk (list_repeat n Undef) = Vundef.
Proof.
  intros. unfold decode_val. rewrite rev_if_be_repeat.
  destruct n. omega. destruct chunk; reflexivity.
Qed.

Lemma decode_encode_val_general:
  forall v chunk1 chunk2,
  decode_encode_val v chunk1 chunk2 (decode_val chunk2 (encode_val chunk1 v)).
Proof.
  intros. unfold decode_val, encode_val. rewrite rev_if_be_involutive.
  destruct v, chunk1, chunk2; auto;
    unfold decode_encode_val; rewrite
    ?proj_inj_bytes, ?int_of_bytes_of_int_1, ?int_of_bytes_of_int_2,
    ?int_of_bytes_of_int_4, ?int_of_bytes_of_int_8,
    ?Int.sign_ext_zero_ext, ?Int.zero_ext_idem,
    ?Float.single_of_bits_of_single, ?Float.double_of_bits_of_double by omega; auto.
  * now rewrite proj_inj_pointer.
  * now rewrite proj_inj_pointer_seg_None.
  * now rewrite proj_inj_pointer_seg_None.
  * now rewrite proj_inj_pointer_seg_None.
Qed.

Lemma decode_encode_val_similar:
  forall v1 chunk1 chunk2 v2,
  type_of_chunk chunk1 = type_of_chunk chunk2 ->
  size_chunk chunk1 = size_chunk chunk2 ->
  decode_encode_val v1 chunk1 chunk2 v2 ->
  v2 = Val.load_result chunk2 v1.
Proof.
  intros until v2; intros TY SZ DE. 
  destruct chunk1; destruct chunk2; simpl in TY; try discriminate; simpl in SZ; try omegaContradiction;
  destruct v1; auto.
Qed.

Lemma decode_val_type:
  forall chunk cl,
  Val.has_type (decode_val chunk cl) (type_of_chunk chunk).
Proof.
  intros. unfold decode_val.
  destruct (proj_bytes _), chunk; simpl; auto.
  * apply Float.single_of_bits_is_single.
  * destruct (proj_pointer_seg 1 _) as [[[??]?]|]; simpl; auto.
  * destruct (proj_pointer_seg 1 _) as [[[??]?]|]; simpl; auto.
  * destruct (proj_pointer _) as [[??]|]; simpl; auto.
    destruct (proj_pointer_seg 4 _) as [[[??]?]|]; simpl; auto.
Qed.

Lemma encode_val_int8_signed_unsigned:
  forall v, encode_val Mint8signed v = encode_val Mint8unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.
Lemma encode_val_int16_signed_unsigned:
  forall v, encode_val Mint16signed v = encode_val Mint16unsigned v.
Proof.
  intros. destruct v; simpl; auto.
Qed.
Lemma encode_val_int8_zero_ext:
  forall n, encode_val Mint8unsigned (Vint (Int.zero_ext 8 n)) = encode_val Mint8unsigned (Vint n).
Proof.
  intros; unfold encode_val. rewrite (bytes_of_int_mod _ _ (Int.unsigned n)); auto.
  apply Int.eqmod_zero_ext. compute; intuition congruence.
Qed.
Lemma encode_val_int8_sign_ext:
  forall n, encode_val Mint8signed (Vint (Int.sign_ext 8 n)) = encode_val Mint8signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite (bytes_of_int_mod _ _ (Int.unsigned n)); auto.
  apply Int.eqmod_sign_ext'. compute; intuition congruence.
Qed.
Lemma encode_val_int16_zero_ext:
  forall n, encode_val Mint16unsigned (Vint (Int.zero_ext 16 n)) = encode_val Mint16unsigned (Vint n).
Proof.
  intros; unfold encode_val. rewrite (bytes_of_int_mod _ _ (Int.unsigned n)); auto.
  apply Int.eqmod_zero_ext. compute; intuition congruence.
Qed.
Lemma encode_val_int16_sign_ext:
  forall n, encode_val Mint16signed (Vint (Int.sign_ext 16 n)) = encode_val Mint16signed (Vint n).
Proof.
  intros; unfold encode_val. rewrite (bytes_of_int_mod _ _ (Int.unsigned n)); auto.
  apply Int.eqmod_sign_ext'. compute; intuition congruence.
Qed.

Lemma decode_val_cast:
  forall chunk l,
  let v := decode_val chunk l in
  match chunk with
  | Mint8signed => ~is_ptrseg v -> v = Val.sign_ext 8 v
  | Mint8unsigned => ~is_ptrseg v -> v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | Mfloat32 => v = Val.singleoffloat v
  | _ => True
  end.
Proof.
  unfold decode_val; intros; destruct chunk; auto; destruct (proj_bytes _); auto.
  * unfold Val.sign_ext. rewrite Int.sign_ext_idem; auto. omega.
  * destruct (proj_pointer_seg _ _) as [[[??]?]|]; simpl; auto. now intros [].
  * unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega.
  * destruct (proj_pointer_seg _ _) as [[[??]?]|]; simpl; auto. now intros [].
  * unfold Val.sign_ext. rewrite Int.sign_ext_idem; auto. omega.
  * unfold Val.zero_ext. rewrite Int.zero_ext_idem; auto. omega.
  * simpl. rewrite Float.singleoffloat_of_bits. auto.
Qed.
Lemma decode_val_int8_signed_unsigned:
  forall l,
  ~is_ptrseg (decode_val Mint8signed l) ->
  decode_val Mint8signed l = Val.sign_ext 8 (decode_val Mint8unsigned l).
Proof.
  intros. rewrite (decode_val_cast Mint8signed) by auto.
  unfold decode_val. destruct (proj_bytes _); [|reflexivity].
  simpl. now rewrite Int.sign_ext_zero_ext, Int.sign_ext_idem by omega.
Qed.
Lemma decode_val_int8_signed_unsigned_ptrseg:
  forall l,
  is_ptrseg (decode_val Mint8signed l) <-> is_ptrseg (decode_val Mint8unsigned l).
Proof.
  intros. unfold decode_val. destruct (proj_bytes _).
  * split; inversion 1.
  * reflexivity.
Qed.
Lemma decode_val_int8_signed_unsigned_alt:
  forall l,
  decode_val Mint8signed l = Val.sign_ext_8_alt (decode_val Mint8unsigned l).
Proof.
  intros. unfold decode_val. destruct (proj_bytes _).
  * simpl. now rewrite Int.sign_ext_zero_ext.
  * now destruct (proj_pointer_seg _ _) as [[[??]?]|].
Qed.

Lemma decode_val_int16_signed_unsigned:
  forall l,
  decode_val Mint16signed l = Val.sign_ext 16 (decode_val Mint16unsigned l).
Proof.
  intros. rewrite (decode_val_cast Mint16signed).
  unfold decode_val. destruct (proj_bytes _); [|reflexivity].
  simpl. now rewrite Int.sign_ext_zero_ext, Int.sign_ext_idem by omega.
Qed.

Lemma decode_val_pointer_inv:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ mvl = rev_if_be (inj_pointer 4 b ofs).
Proof.
  unfold decode_val. intros.
  destruct (proj_bytes _), chunk; try congruence.
  * destruct (proj_pointer_seg _ _) as [[[??]?]|]; discriminate.
  * destruct (proj_pointer_seg _ _) as [[[??]?]|]; discriminate.
  * destruct (proj_pointer _) as [[??]|] eqn:?.
    { inv H. now rewrite <-(proj_pointer_inv _ _ (rev_if_be mvl)),
        rev_if_be_involutive. }
    destruct (proj_pointer_seg _ _) as [[[??]?]|]; discriminate.
Qed.

Lemma in_inj_bytes:
  forall mv bl, In mv (inj_bytes bl) -> exists b, mv = Byte b /\ In b bl.
Proof.
  induction bl; simpl; firstorder eauto.
Qed.
Lemma in_inj_pointer:
  forall mv n b ofs, In mv (inj_pointer n b ofs) -> exists i, mv = Pointer b ofs i.
Proof.
  induction n; simpl; intuition eauto.
Qed.
Lemma in_inj_pointer_seg:
  forall mv n b ofs i, In mv (inj_pointer_seg n b ofs i) ->
  mv = Pointer b ofs i \/ (mv = PointerPad /\ n <> 1%nat).
Proof.
  intros mv [|n] b ofs i; [intros []|intros [?|?]; auto].
  right. split. eauto using in_list_repeat. destruct n; intuition.
Qed.

Local Ltac simplify_in_inj :=
  repeat match goal with
    | _ => discriminate
    | H : In _ (list_repeat _ _) |- _ =>
      apply in_list_repeat in H; subst
    | H : In _ (inj_pointer _ _ _) |- _ =>
      apply in_inj_pointer in H; destruct H; subst
    | H : In _ (inj_bytes _) |- _ =>
      apply in_inj_bytes in H; destruct H as (?&?&?); subst
    | H : In _ (inj_pointer_seg _ _ _ _) |- _ =>
      apply in_inj_pointer_seg in H; destruct H as [?|[??]]; subst
    | H : Pointer _ _ _ = Pointer _ _ _ |- _ =>
      injection H; clear H; intros; subst
    end.

Lemma inj_pointer_encode_val_overlap:
  forall chunk n v mv b ofs,
  In mv (inj_pointer n b ofs) -> In mv (encode_val chunk v) ->
  chunk <> Mint32 ->
  exists i, (chunk = Mint8signed \/ chunk = Mint8unsigned) /\ v = Vptrseg b ofs i.
Proof.
  intros chunk n v mv b ofs INJ ENC CNK.
  unfold encode_val in ENC; rewrite in_rev_if_be in ENC.
  destruct chunk, v; simplify_in_inj; intuition eauto.
Qed.

Lemma decode_val_pointer_seg_inv:
  forall chunk mvl b ofs i,
  decode_val chunk mvl = Vptrseg b ofs i ->
  (chunk = Mint8signed \/ chunk = Mint8unsigned \/ chunk = Mint32) /\
  mvl = rev_if_be (inj_pointer_seg (size_chunk_nat chunk) b ofs i).
Proof.
  unfold decode_val. intros.
  destruct (proj_bytes _), chunk; try congruence.
  * destruct (proj_pointer_seg _ _) as [[[??]?]|] eqn:?; inv H.
    erewrite <-proj_pointer_seg_inv, rev_if_be_involutive by eauto; auto.
  * destruct (proj_pointer_seg _ _) as [[[??]?]|] eqn:?; inv H.
    erewrite <-proj_pointer_seg_inv, rev_if_be_involutive by eauto; auto.
  * destruct (proj_pointer _) as [[??]|] eqn:?; inv H.
    destruct (proj_pointer_seg _ _) as [[[??]?]|] eqn:?; inv H1.
    erewrite <-(proj_pointer_seg_inv 4), rev_if_be_involutive by eauto; auto.
Qed.

Lemma inj_pointer_seg_encode_val_overlap:
  forall chunk n v mv b ofs i,
  In mv (inj_pointer_seg n b ofs i) -> In mv (encode_val chunk v) ->
  chunk <> Mint32 ->
  (chunk = Mint8signed \/ chunk = Mint8unsigned) /\ v = Vptrseg b ofs i.
Proof.
  intros chunk n v mv b ofs i INJ ENC CNK.
  unfold encode_val in ENC; rewrite in_rev_if_be in ENC.
  destruct chunk, v; simplify_in_inj; intuition eauto.
Qed.

Lemma inj_pointer_seg_1_encode_val_overlap:
  forall chunk v mv b ofs i,
  In mv (inj_pointer_seg 1 b ofs i) -> In mv (encode_val chunk v) ->
  (chunk = Mint32 /\ v = Vptr b ofs)
  \/ (chunk = Mint8signed \/ chunk = Mint8unsigned \/ chunk = Mint32) /\ v = Vptrseg b ofs i.
Proof.
  intros chunk v mv b ofs i INJ ENC.
  unfold encode_val in ENC; rewrite in_rev_if_be in ENC.
  destruct chunk, v; simplify_in_inj; intuition eauto.
Qed.

(** * Breaking 64-bit memory accesses into two 32-bit accesses *)
Lemma decode_val_int64:
  forall l1 l2,
  length l1 = 4%nat -> length l2 = 4%nat ->
  decode_val Mint64 (l1 ++ l2) =
  Val.longofwords (decode_val Mint32 (if Archi.big_endian then l1 else l2))
                  (decode_val Mint32 (if Archi.big_endian then l2 else l1)).
Proof.
  intros. unfold decode_val. rewrite !rev_if_be_app, proj_bytes_append.
  destruct (proj_bytes (rev_if_be (if Archi.big_endian then l2 else l1))) as [b1|] eqn:?,
    (proj_bytes (rev_if_be (if Archi.big_endian then l1 else l2))) as [b2|] eqn:?;
    repeat match goal with
    | |- context [ proj_pointer ?l ] => destruct (proj_pointer l) as [[??]|]
    | |- context [ proj_pointer_seg ?n ?l ] => destruct (proj_pointer_seg n l) as [[[??]?]|]
    end; try reflexivity.
  assert (UR: forall b,
    length b = 4%nat -> Int.unsigned (Int.repr (int_of_bytes b)) = int_of_bytes b).
  { intros b Hb. apply Int.unsigned_repr.
    generalize (int_of_bytes_range b). rewrite Hb.
    change (two_p (Z.of_nat 4 * 8)) with (Int.max_unsigned + 1). omega. }
  assert (length b1 = 4%nat) as Hb1.
  { erewrite length_proj_bytes, rev_if_be_length by eauto. now destruct Archi.big_endian. }
  assert (length b2 = 4%nat) as Hb2.
  { erewrite length_proj_bytes, rev_if_be_length by eauto. now destruct Archi.big_endian. }
  rewrite int_of_bytes_append; simpl. rewrite Int64.ofwords_add, !UR, Hb1 by easy.
  now rewrite Z.add_comm.
Qed.

Lemma bytes_of_int64:
  forall i,
  bytes_of_int 8 (Int64.unsigned i) =
  bytes_of_int 4 (Int.unsigned (Int64.loword i)) ++ bytes_of_int 4 (Int.unsigned (Int64.hiword i)).
Proof.
  intros. transitivity (bytes_of_int (4 + 4) (Int64.unsigned (Int64.ofwords (Int64.hiword i) (Int64.loword i)))).
  f_equal. f_equal. rewrite Int64.ofwords_recompose. auto.
  rewrite Int64.ofwords_add'.
  change 32 with (Z_of_nat 4 * 8). 
  rewrite Zplus_comm. apply bytes_of_int_append. apply Int.unsigned_range. 
Qed.

Lemma encode_val_int64:
  forall v,
  encode_val Mint64 v =
     encode_val Mint32 (if Archi.big_endian then Val.hiword v else Val.loword v)
  ++ encode_val Mint32 (if Archi.big_endian then Val.loword v else Val.hiword v).
Proof.
  intros. destruct v; unfold encode_val, rev_if_be; destruct Archi.big_endian eqn:BI; try reflexivity.
  * unfold Val.loword, Val.hiword, encode_val, inj_bytes.
    now rewrite !rev_append_rev, !app_nil_r, <-rev_app_distr, <-map_app, bytes_of_int64.
  * unfold Val.loword, Val.hiword, encode_val, inj_bytes.
    now rewrite <-map_app, bytes_of_int64.
Qed.

(** Pointers cannot be forged. *)

Inductive pointer_bytes_valid (b : block) (ofs : int) :
    nat -> list memval -> Prop :=
  | pointer_bytes_valid_nil : pointer_bytes_valid b ofs 0 nil
  | pointer_bytes_valid_cons n mws :
     pointer_bytes_valid b ofs n mws ->
     pointer_bytes_valid b ofs (S n) (Pointer b ofs n :: mws).

(*
Definition memval_valid_first (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n = 3%nat
  | _ => True
  end.

Definition memval_valid_cont (mv: memval) : Prop :=
  match mv with
  | Pointer b ofs n => n <> 3%nat
  | _ => True
  end.

Inductive encoding_shape: list memval -> Prop :=
  | encoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 ->
      (forall mv, In mv mvl -> memval_valid_cont mv) ->
      encoding_shape (mv1 :: mvl).

Lemma encode_val_shape:
  forall chunk v, encoding_shape (encode_val chunk v).
Proof.
  intros. 
  destruct (size_chunk_nat_pos chunk) as [sz1 EQ].
  assert (A: encoding_shape (list_repeat (size_chunk_nat chunk) Undef)).
    rewrite EQ; simpl; constructor. exact I. 
    intros. replace mv with Undef. exact I. symmetry; eapply in_list_repeat; eauto.
  assert (B: forall bl, length bl = size_chunk_nat chunk ->
          encoding_shape (inj_bytes bl)).
    intros. destruct bl; simpl in *. congruence. 
    constructor. exact I. unfold inj_bytes. intros.
    exploit list_in_map_inv; eauto. intros [x [C D]]. subst mv. exact I.
  destruct v; auto; destruct chunk; simpl; auto; try (apply B; apply encode_int_length).
  constructor. red. auto.
  simpl; intros. intuition; subst mv; red; simpl; congruence.
Qed.

Lemma check_pointer_inv:
  forall b ofs n mv,
  check_pointer n b ofs mv = true -> mv = inj_pointer n b ofs.
Proof.
  induction n; destruct mv; simpl. 
  auto.
  congruence.
  congruence.
  destruct m; try congruence. intro. 
  destruct (andb_prop _ _ H). destruct (andb_prop _ _ H0). 
  destruct (andb_prop _ _ H2).
  decEq. decEq. symmetry; eapply proj_sumbool_true; eauto.
  symmetry; eapply proj_sumbool_true; eauto.
  symmetry; apply beq_nat_true; auto.
  auto.
Qed.

Inductive decoding_shape: list memval -> Prop :=
  | decoding_shape_intro: forall mv1 mvl,
      memval_valid_first mv1 -> mv1 <> Undef ->
      (forall mv, In mv mvl -> memval_valid_cont mv /\ mv <> Undef) ->
      decoding_shape (mv1 :: mvl).

Lemma decode_val_shape:
  forall chunk mvl,
  List.length mvl = size_chunk_nat chunk ->
  decode_val chunk mvl = Vundef \/ decoding_shape mvl.
Proof.
  intros. destruct (size_chunk_nat_pos chunk) as [sz EQ]. 
  unfold decode_val. 
  caseEq (proj_bytes mvl).
  intros bl PROJ. right. exploit inj_proj_bytes; eauto. intros. subst mvl.
  destruct bl; simpl in H. congruence. simpl. constructor. 
  red; auto. congruence.
  unfold inj_bytes; intros. exploit list_in_map_inv; eauto. intros [b [A B]]. 
  subst mv. split. red; auto. congruence.
  intros. destruct chunk; auto. unfold proj_pointer.
  destruct mvl; auto. destruct m; auto. 
  caseEq (check_pointer 4%nat b i (Pointer b i n :: mvl)); auto.
  intros. right. exploit check_pointer_inv; eauto. simpl; intros; inv H2.
  constructor. red. auto. congruence. 
  simpl; intros. intuition; subst mv; simpl; congruence.
Qed.

Lemma encode_val_pointer_inv:
  forall chunk v b ofs n mvl,
  encode_val chunk v = Pointer b ofs n :: mvl ->
  chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer 3%nat b ofs.
Proof.
  intros until mvl.
  assert (A: list_repeat (size_chunk_nat chunk) Undef = Pointer b ofs n :: mvl ->
            chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer 3 b ofs).
    intros. destruct (size_chunk_nat_pos chunk) as [sz SZ]. rewrite SZ in H. simpl in H. discriminate.
  assert (B: forall bl, length bl <> 0%nat -> inj_bytes bl = Pointer b ofs n :: mvl ->
            chunk = Mint32 /\ v = Vptr b ofs /\ mvl = inj_pointer 3 b ofs).
    intros. destruct bl; simpl in *; congruence.
  unfold encode_val; destruct v; destruct chunk;
  (apply A; assumption) ||
  (apply B; rewrite encode_int_length; congruence) || idtac.
  simpl. intros EQ; inv EQ; auto. 
Qed.

Lemma decode_val_pointer_inv:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ mvl = inj_pointer 4%nat b ofs.
Proof.
  intros until ofs; unfold decode_val.
  destruct (proj_bytes mvl). 
  destruct chunk; congruence.
  destruct chunk; try congruence.
  unfold proj_pointer. destruct mvl. congruence. destruct m; try congruence.
  case_eq (check_pointer 4%nat b0 i (Pointer b0 i n :: mvl)); intros.
  inv H0. split; auto. apply check_pointer_inv; auto. 
  congruence.
Qed.

Inductive pointer_encoding_shape: list memval -> Prop :=
  | pointer_encoding_shape_intro: forall mv1 mvl,
      ~memval_valid_cont mv1 ->
      (forall mv, In mv mvl -> ~memval_valid_first mv) ->
      pointer_encoding_shape (mv1 :: mvl).

Lemma encode_pointer_shape:
  forall b ofs, pointer_encoding_shape (encode_val Mint32 (Vptr b ofs)).
Proof.
  intros. simpl. constructor.
  unfold memval_valid_cont. red; intro. elim H. auto. 
  unfold memval_valid_first. simpl; intros; intuition; subst mv; congruence.
Qed.

Lemma decode_pointer_shape:
  forall chunk mvl b ofs,
  decode_val chunk mvl = Vptr b ofs ->
  chunk = Mint32 /\ pointer_encoding_shape mvl.
Proof.
  intros. exploit decode_val_pointer_inv; eauto. intros [A B].
  split; auto. subst mvl. apply encode_pointer_shape. 
Qed.
*)

(** * Compatibility with memory injections *)

(** Relating two memory values according to a memory injection. *)

Inductive memval_inject (f: meminj): memval -> memval -> Prop :=
  | memval_inject_byte:
      forall n, memval_inject f (Byte n) (Byte n)
  | memval_inject_ptr:
      forall b1 ofs1 b2 ofs2 delta n,
      f b1 = Some (b2, delta) ->
      ofs2 = Int.add ofs1 (Int.repr delta) ->
      memval_inject f (Pointer b1 ofs1 n) (Pointer b2 ofs2 n)
  | memval_inject_ptr_pad:
      memval_inject f PointerPad PointerPad
  | memval_inject_undef:
      forall mv, memval_inject f Undef mv.

Lemma memval_inject_incr:
  forall f f' v1 v2, memval_inject f v1 v2 -> inject_incr f f' -> memval_inject f' v1 v2.
Proof.
  intros. inv H; econstructor. rewrite (H0 _ _ _ H1). reflexivity. auto.
Qed.

(** [decode_val], applied to lists of memory values that are pairwise
  related by [memval_inject], returns values that are related by [val_inject]. *)

Lemma proj_bytes_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall bl,
  proj_bytes vl = Some bl ->
  proj_bytes vl' = Some bl.
Proof.
  intros. apply inj_proj_bytes in H0.
  cut (vl' = inj_bytes bl).
  { intros. subst. apply proj_inj_bytes. }
  subst. revert vl' H.
  induction bl; inversion_clear 1; auto.
  inv H0. unfold inj_bytes; fold inj_bytes; simpl; decEq; auto.
Qed.
Lemma proj_bytes_not_inject:
  forall f vl vl' bs,
  list_forall2 (memval_inject f) vl vl' ->
  proj_bytes vl = None -> proj_bytes vl' = Some bs -> In Undef vl.
Proof.
  intros until 1. revert bs.
  induction H; simpl; unfold proj_bytes; fold proj_bytes; intros; [discriminate |].
  inv H; try intuition congruence.
  destruct (proj_bytes al); try discriminate.
  destruct (proj_bytes bl); try discriminate.
  eauto.
Qed.

Lemma check_pointer_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n b ofs b' delta,
  check_pointer n b ofs vl = true ->
  f b = Some(b', delta) ->
  check_pointer n b' (Int.add ofs (Int.repr delta)) vl' = true.
Proof.
  intros. apply check_pointer_inv in H0. subst.
  cut (vl' = inj_pointer n b' (Int.add ofs (Int.repr delta))).
  { intros. subst. apply check_inj_pointer. }
  revert vl' H. induction n; unfold inj_pointer; fold inj_pointer;
    inversion_clear 1; auto.
  f_equal. inv H0. congruence. auto.
Qed.
Lemma proj_pointer_inject:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall b ofs,
  proj_pointer vl1 = Some (b,ofs) ->
  exists b' delta,
  f b = Some (b', delta) /\
  proj_pointer vl2 = Some (b', Int.add ofs (Int.repr delta)).
Proof.
  destruct 1; try discriminate.
  unfold proj_pointer. intros. destruct H; try discriminate.
  destruct (check_pointer 4 b1 _ _) eqn:?; inv H1.
  exists b2, delta. erewrite check_pointer_inject; eauto.
  constructor. econstructor; eauto. auto.
Qed.

Lemma check_pointer_pad_inject:
  forall f vl vl',
  list_forall2 (memval_inject f) vl vl' ->
  forall n,
  check_pointer_pad n vl = true ->
  check_pointer_pad n vl' = true.
Proof.
  induction 1; intros [|?];
    unfold check_pointer_pad; fold check_pointer_pad; auto.
  destruct H; try discriminate; auto.
Qed.
Lemma proj_pointer_seg_inject:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall n b ofs i,
  proj_pointer_seg n vl1 = Some (b,ofs,i) ->
  exists b' delta,
  f b = Some (b', delta) /\
  proj_pointer_seg n vl2 = Some (b', Int.add ofs (Int.repr delta), i).
Proof.
  destruct 1; intros [|?]; try discriminate.
  unfold proj_pointer_seg. intros. destruct H; try discriminate.
  destruct (check_pointer_pad n al) eqn:?; inv H1.
  exists b2, delta. erewrite check_pointer_pad_inject; eauto.
Qed.

Lemma check_pointer_undef:
  forall n b ofs vl,
  In Undef vl -> check_pointer n b ofs vl = false.
Proof.
  induction n; intros ?? [|??]; simpl; intuition auto; subst.
  * reflexivity.
  * unfold check_pointer; fold check_pointer.
    now destruct m; rewrite ?IHn, ?andb_false_r by auto.
Qed.
Lemma proj_pointer_undef:
  forall vl, In Undef vl -> proj_pointer vl = None.
Proof.
  intros; unfold proj_pointer.
  destruct vl as [|[]?]; auto. now rewrite check_pointer_undef.
Qed.

Lemma check_pointer_pad_undef:
  forall n vl,
  In Undef vl -> check_pointer_pad n vl = false.
Proof.
  induction n; intros [|??]; simpl; intuition auto; subst.
  * reflexivity.
  * unfold check_pointer_pad; fold check_pointer_pad.
    destruct m; auto.
Qed.
Lemma proj_pointer_seg_undef:
  forall n vl, In Undef vl -> proj_pointer_seg n vl = None.
Proof.
  intros; unfold proj_pointer_seg.
  destruct n; auto.
  destruct vl as [|[]?]; auto.
  destruct H; try discriminate.
  now rewrite check_pointer_pad_undef.
Qed.

Lemma proj_pointer_seg_not_pointer:
  forall f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall b ofs i,
  proj_pointer_seg 4 vl1 = Some (b, ofs, i) ->
  proj_pointer vl2 = None.
Proof.
  destruct 1; try discriminate. inv H; try discriminate.
  unfold proj_pointer, proj_pointer_seg. intros.
  destruct H0; try discriminate. inv H0; try discriminate.
  unfold check_pointer. simpl. now rewrite !andb_false_r.
Qed.

Theorem decode_val_inject:
  forall f vl1 vl2 chunk,
  list_forall2 (memval_inject f) vl1 vl2 ->
  val_inject f (decode_val chunk vl1) (decode_val chunk vl2).
Proof.
  intros. unfold decode_val.
  destruct (proj_bytes (rev_if_be vl1)) eqn:?.
  { exploit (proj_bytes_inject f (rev_if_be vl1) (rev_if_be vl2));
      eauto using rev_if_be_forall2.
    intros. rewrite H0. destruct chunk; constructor. }
  destruct chunk; auto.
  * destruct (proj_bytes (rev_if_be vl2)) eqn:?.
    { rewrite proj_pointer_seg_undef;
        eauto using proj_bytes_not_inject, rev_if_be_forall2. }
    destruct (proj_pointer_seg 1 (rev_if_be vl1)) as [[[??]?]|] eqn:?; [|constructor].
    exploit (proj_pointer_seg_inject f (rev_if_be vl1) (rev_if_be vl2));
      eauto using rev_if_be_forall2.
    intros (?&?&?&E). rewrite E. econstructor; eauto.
  * destruct (proj_bytes (rev_if_be vl2)) eqn:?.
    { rewrite proj_pointer_seg_undef;
        eauto using proj_bytes_not_inject, rev_if_be_forall2. }
    destruct (proj_pointer_seg 1 (rev_if_be vl1)) as [[[??]?]|] eqn:?; [|constructor].
    exploit (proj_pointer_seg_inject f (rev_if_be vl1) (rev_if_be vl2));
      eauto using rev_if_be_forall2.
    intros (?&?&?&E). rewrite E. econstructor; eauto.
  * destruct (proj_bytes (rev_if_be vl2)) eqn:?.
    { rewrite proj_pointer_undef, proj_pointer_seg_undef;
        eauto using proj_bytes_not_inject, rev_if_be_forall2. }
    destruct (proj_pointer (rev_if_be vl1)) as [[??]|] eqn:?.
    { exploit (proj_pointer_inject f (rev_if_be vl1) (rev_if_be vl2));
        eauto using rev_if_be_forall2.
      intros (?&?&?&E). rewrite E. econstructor; eauto. }
    destruct (proj_pointer_seg 4 (rev_if_be vl1)) as [[[??]?]|] eqn:?; [|constructor].
    erewrite proj_pointer_seg_not_pointer by eauto using rev_if_be_forall2.
    exploit (proj_pointer_seg_inject f (rev_if_be vl1) (rev_if_be vl2));
      eauto using rev_if_be_forall2.
    intros (?&?&?&E). rewrite E. econstructor; eauto.
Qed.

(** Symmetrically, [encode_val], applied to values related by [val_inject],
  returns lists of memory values that are pairwise
  related by [memval_inject]. *)

Lemma inj_bytes_inject:
  forall f bl, list_forall2 (memval_inject f) (inj_bytes bl) (inj_bytes bl).
Proof.
  induction bl; constructor; auto. constructor.
Qed.

Lemma repeat_Undef_inject_any:
  forall f n vl,
  n = length vl ->
  list_forall2 (memval_inject f) (list_repeat n Undef) vl.
Proof.
  intros. subst.
  induction vl; simpl; constructor; auto. constructor. 
Qed.

Lemma repeat_Undef_inject_self:
  forall f n,
  list_forall2 (memval_inject f) (list_repeat n Undef) (list_repeat n Undef).
Proof.
  induction n; simpl; constructor; auto. constructor.
Qed.

Theorem encode_val_inject:
  forall f v1 v2 chunk,
  val_inject f v1 v2 ->
  list_forall2 (memval_inject f) (encode_val chunk v1) (encode_val chunk v2).
Proof.
  intros. unfold encode_val. apply rev_if_be_forall2. inv H.
  * destruct chunk; apply inj_bytes_inject || apply repeat_Undef_inject_self.
  * destruct chunk; apply inj_bytes_inject || apply repeat_Undef_inject_self.
  * destruct chunk; try (apply repeat_Undef_inject_self); repeat econstructor; eauto.
  * destruct chunk; try (apply repeat_Undef_inject_self); repeat econstructor; eauto.
  * destruct chunk; try (apply repeat_Undef_inject_self); repeat econstructor; eauto.
  * apply repeat_Undef_inject_any.
    now destruct v2, chunk; rewrite ?length_list_repeat,
      ?length_inj_bytes, ?length_bytes_of_int.
Qed.

Definition memval_lessdef: memval -> memval -> Prop := memval_inject inject_id.

Lemma memval_lessdef_refl:
  forall mv, memval_lessdef mv mv.
Proof.
  red. destruct mv; econstructor.
  unfold inject_id; reflexivity. rewrite Int.add_zero; auto. 
Qed.

(** [memval_inject] and identity and compositions *)

Lemma memval_inject_id:
  forall v, memval_inject inject_id v v.
Proof.
  apply memval_lessdef_refl.
Qed.

Lemma memval_inject_compose:
  forall f f' v1 v2 v3,
  memval_inject f v1 v2 -> memval_inject f' v2 v3 ->
  memval_inject (compose_meminj f f') v1 v3.
Proof.
  intros. inv H.
  * inv H0. constructor.
  * inv H0. econstructor.
    unfold compose_meminj; rewrite H1; rewrite H5; eauto.
    rewrite Int.add_assoc. decEq. unfold Int.add. apply Int.eqm_samerepr. auto with ints.
  * inv H0. constructor.
  * constructor.
Qed. 
