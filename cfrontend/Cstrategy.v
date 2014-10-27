(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** A deterministic evaluation strategy for C. *)

Require Import Axioms.
Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import AST.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Ctypes.
Require Import Cop.
Require Import Csyntax.
Require Import Csem.

Section STRATEGY.

Variable ge: genv.

(** * Definition of the strategy *)

(** We now formalize a particular strategy for reducing expressions which
  is the one implemented by the CompCert compiler.  It evaluates effectful
  subexpressions first, in leftmost-innermost order, then finishes 
  with the evaluation of the remaining simple expression. *)

(** Simple expressions are defined as follows. *)

Fixpoint simple (a: expr) : bool :=
  match a with
  | Eloc _ _ _ => true
  | Evar _ _ => true
  | Ederef r _ => simple r
  | Efield r _ _ => simple r
  | Eval _ _ => true
  | Evalof l _ => simple l && negb(type_is_volatile (typeof l))
  | Eaddrof l _ => simple l
  | Eunop _ r1 _ => simple r1
  | Ebinop _ r1 r2 _ => simple r1 && simple r2
  | Ecast r1 _ => simple r1
  | Eseqand _ _ _ => false
  | Eseqor _ _ _ => false
  | Econdition _ _ _ _ => false
  | Esizeof _ _ => true
  | Ealignof _ _ => true
  | Eassign _ _ _ => false
  | Eassignop _ _ _ _ _ => false
  | Epostincr _ _ _ => false
  | Ecomma _ _ _ => false
  | Ecall _ _ _ => false
  | Ebuiltin _ _ _ _ => false
  | Eparen _ _ _ => false
  end.

Fixpoint simplelist (rl: exprlist) : bool :=
  match rl with Enil => true | Econs r rl' => simple r && simplelist rl' end.

(** Simple expressions have interesting properties: their evaluations always
  terminate, are deterministic, and preserve the memory state.
  We seize this opportunity to define a big-step semantics for simple
  expressions. *)

Section SIMPLE_EXPRS.

Variable e: env.
Variable m: mem.

Inductive eval_simple_lvalue: expr -> block -> int -> Prop :=
  | esl_loc: forall b ofs ty,
      eval_simple_lvalue (Eloc b ofs ty) b ofs
  | esl_var_local: forall x ty b,
      e!x = Some(b, ty) ->
      eval_simple_lvalue (Evar x ty) b Int.zero
  | esl_var_global: forall x ty b,
      e!x = None ->
      Genv.find_symbol ge x = Some b ->
      eval_simple_lvalue (Evar x ty) b Int.zero
  | esl_deref: forall r ty b ofs,
      eval_simple_rvalue r (Vptr b ofs) ->
      eval_simple_lvalue (Ederef r ty) b ofs
  | esl_field_struct: forall r f ty b ofs id fList a delta,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tstruct id fList a -> field_offset f fList = OK delta ->
      eval_simple_lvalue (Efield r f ty) b (Int.add ofs (Int.repr delta))
  | esl_field_union: forall r f ty b ofs id fList a,
      eval_simple_rvalue r (Vptr b ofs) ->
      typeof r = Tunion id fList a ->
      eval_simple_lvalue (Efield r f ty) b ofs

with eval_simple_rvalue: expr -> val -> Prop :=
  | esr_val: forall v ty,
      eval_simple_rvalue (Eval v ty) v
  | esr_rvalof: forall b ofs l ty v,
      eval_simple_lvalue l b ofs ->
      ty = typeof l -> type_is_volatile ty = false ->
      deref_loc ge ty m b ofs E0 v ->
      eval_simple_rvalue (Evalof l ty) v
  | esr_addrof: forall b ofs l ty,
      eval_simple_lvalue l b ofs ->
      eval_simple_rvalue (Eaddrof l ty) (Vptr b ofs)
  | esr_unop: forall op r1 ty v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_unary_operation op v1 (typeof r1) = Some v ->
      eval_simple_rvalue (Eunop op r1 ty) v
  | esr_binop: forall op r1 r2 ty v1 v2 v,
      eval_simple_rvalue r1 v1 -> eval_simple_rvalue r2 v2 ->
      sem_binary_operation op v1 (typeof r1) v2 (typeof r2) m = Some v ->
      eval_simple_rvalue (Ebinop op r1 r2 ty) v
  | esr_cast: forall ty r1 v1 v,
      eval_simple_rvalue r1 v1 ->
      sem_cast v1 (typeof r1) ty = Some v ->
      eval_simple_rvalue (Ecast r1 ty) v
  | esr_sizeof: forall ty1 ty,
      eval_simple_rvalue (Esizeof ty1 ty) (Vint (Int.repr (sizeof ty1)))
  | esr_alignof: forall ty1 ty,
      eval_simple_rvalue (Ealignof ty1 ty) (Vint (Int.repr (alignof ty1))).

Inductive eval_simple_list: exprlist -> typelist -> list val -> Prop :=
  | esrl_nil:
      eval_simple_list Enil Tnil nil
  | esrl_cons: forall r rl ty tyl v vl v',
      eval_simple_rvalue r v' -> sem_cast v' (typeof r) ty = Some v ->
      eval_simple_list rl tyl vl ->
      eval_simple_list (Econs r rl) (Tcons ty tyl) (v :: vl).

Scheme eval_simple_rvalue_ind2 := Minimality for eval_simple_rvalue Sort Prop
  with eval_simple_lvalue_ind2 := Minimality for eval_simple_lvalue Sort Prop.
Combined Scheme eval_simple_rvalue_lvalue_ind from eval_simple_rvalue_ind2, eval_simple_lvalue_ind2.

End SIMPLE_EXPRS.

(** Left reduction contexts. These contexts allow reducing to the right
  of a binary operator only if the left subexpression is simple. *)

Inductive leftcontext: kind -> kind -> (expr -> expr) -> Prop :=
  | lctx_top: forall k,
      leftcontext k k (fun x => x)
  | lctx_deref: forall k C ty,
      leftcontext k RV C -> leftcontext k LV (fun x => Ederef (C x) ty)
  | lctx_field: forall k C f ty,
      leftcontext k RV C -> leftcontext k LV (fun x => Efield (C x) f ty)
  | lctx_rvalof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Evalof (C x) ty)
  | lctx_addrof: forall k C ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eaddrof (C x) ty)
  | lctx_unop: forall k C op ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eunop op (C x) ty)
  | lctx_binop_left: forall k C op e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ebinop op (C x) e2 ty)
  | lctx_binop_right: forall k C op e1 ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Ebinop op e1 (C x) ty)
  | lctx_cast: forall k C ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecast (C x) ty)
  | lctx_seqand: forall k C r2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eseqand (C x) r2 ty)
  | lctx_seqor: forall k C r2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eseqor (C x) r2 ty)
  | lctx_condition: forall k C r2 r3 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Econdition (C x) r2 r3 ty)
  | lctx_assign_left: forall k C e2 ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassign (C x) e2 ty)
  | lctx_assign_right: forall k C e1 ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassign e1 (C x) ty)
  | lctx_assignop_left: forall k C op e2 tyres ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Eassignop op (C x) e2 tyres ty)
  | lctx_assignop_right: forall k C op e1 tyres ty,
      simple e1 = true -> leftcontext k RV C ->
      leftcontext k RV (fun x => Eassignop op e1 (C x) tyres ty)
  | lctx_postincr: forall k C id ty,
      leftcontext k LV C -> leftcontext k RV (fun x => Epostincr id (C x) ty)
  | lctx_call_left: forall k C el ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecall (C x) el ty)
  | lctx_call_right: forall k C e1 ty,
      simple e1 = true -> leftcontextlist k C ->
      leftcontext k RV (fun x => Ecall e1 (C x) ty)
  | lctx_builtin: forall k C ef tyargs ty,
      leftcontextlist k C ->
      leftcontext k RV (fun x => Ebuiltin ef tyargs (C x) ty)
  | lctx_comma: forall k C e2 ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Ecomma (C x) e2 ty)
  | lctx_paren: forall k C tycast ty,
      leftcontext k RV C -> leftcontext k RV (fun x => Eparen (C x) tycast ty)

with leftcontextlist: kind -> (expr -> exprlist) -> Prop :=
  | lctx_list_head: forall k C el,
      leftcontext k RV C -> leftcontextlist k (fun x => Econs (C x) el)
  | lctx_list_tail: forall k C e1,
      simple e1 = true -> leftcontextlist k C ->
      leftcontextlist k (fun x => Econs e1 (C x)).

Lemma leftcontext_context:
  forall k1 k2 C, leftcontext k1 k2 C -> context k1 k2 C
with leftcontextlist_contextlist:
  forall k C, leftcontextlist k C -> contextlist k C.
Proof.
  induction 1; constructor; auto.
  induction 1; constructor; auto.
Qed.

Hint Resolve leftcontext_context.

(** Strategy for reducing expressions. We reduce the leftmost innermost
  non-simple subexpression, evaluating its arguments (which are necessarily
  simple expressions) with the big-step semantics.
  If there are none, the whole expression is simple and is evaluated in
  one big step. *)

Inductive estep: state -> trace -> state -> Prop :=

  | step_expr: forall f r k e m v ty,
      eval_simple_rvalue e m r v ->
      match r with Eval _ _ => False | _ => True end ->
      ty = typeof r ->
      estep (ExprState f r k e m)
         E0 (ExprState f (Eval v ty) k e m)

  | step_rvalof_volatile: forall f C l ty k e m b ofs t v,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc ge ty m b ofs t v ->
      ty = typeof l -> type_is_volatile ty = true ->
      estep (ExprState f (C (Evalof l ty)) k e m)
          t (ExprState f (C (Eval v ty)) k e m)

  | step_seqand_true: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) = Some true ->
      estep (ExprState f (C (Eseqand r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eparen r2 type_bool ty)) k e m)
  | step_seqand_false: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) = Some false ->
      estep (ExprState f (C (Eseqand r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eval (Vint Int.zero) ty)) k e m)

  | step_seqor_true: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) = Some true ->
      estep (ExprState f (C (Eseqor r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eval (Vint Int.one) ty)) k e m)
  | step_seqor_false: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) = Some false ->
      estep (ExprState f (C (Eseqor r1 r2 ty)) k e m)
         E0 (ExprState f (C (Eparen r2 type_bool ty)) k e m)

  | step_condition: forall f C r1 r2 r3 ty k e m v b,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      bool_val v (typeof r1) = Some b ->
      estep (ExprState f (C (Econdition r1 r2 r3 ty)) k e m)
         E0 (ExprState f (C (Eparen (if b then r2 else r3) ty ty)) k e m)

  | step_assign: forall f C l r ty k e m b ofs v v' t m',
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      eval_simple_rvalue e m r v ->
      sem_cast v (typeof r) (typeof l) = Some v' ->
      assign_loc ge (typeof l) m b ofs v' t m' ->
      ty = typeof l ->
      estep (ExprState f (C (Eassign l r ty)) k e m)
          t (ExprState f (C (Eval v' ty)) k e m')

  | step_assignop: forall f C op l r tyres ty k e m b ofs v1 v2 v3 v4 t1 t2 m' t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc ge (typeof l) m b ofs t1 v1 ->
      eval_simple_rvalue e m r v2 ->
      sem_binary_operation op v1 (typeof l) v2 (typeof r) m = Some v3 ->
      sem_cast v3 tyres (typeof l) = Some v4 ->
      assign_loc ge (typeof l) m b ofs v4 t2 m' ->
      ty = typeof l ->
      t = t1 ** t2 ->
      estep (ExprState f (C (Eassignop op l r tyres ty)) k e m)
          t (ExprState f (C (Eval v4 ty)) k e m')

  | step_assignop_stuck: forall f C op l r tyres ty k e m b ofs v1 v2 t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc ge (typeof l) m b ofs t v1 ->
      eval_simple_rvalue e m r v2 ->
      match sem_binary_operation op v1 (typeof l) v2 (typeof r) m with
      | None => True
      | Some v3 =>
          match sem_cast v3 tyres (typeof l) with
          | None => True
          | Some v4 => forall t2 m', ~(assign_loc ge (typeof l) m b ofs v4 t2 m')
          end
      end ->
      ty = typeof l ->
      estep (ExprState f (C (Eassignop op l r tyres ty)) k e m)
          t Stuckstate

  | step_postincr: forall f C id l ty k e m b ofs v1 v2 v3 t1 t2 m' t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc ge ty m b ofs t1 v1 ->
      sem_incrdecr id v1 ty = Some v2 ->
      sem_cast v2 (incrdecr_type ty) ty = Some v3 ->
      assign_loc ge ty m b ofs v3 t2 m' ->
      ty = typeof l ->
      t = t1 ** t2 ->
      estep (ExprState f (C (Epostincr id l ty)) k e m)
          t (ExprState f (C (Eval v1 ty)) k e m')

  | step_postincr_stuck: forall f C id l ty k e m b ofs v1 t,
      leftcontext RV RV C ->
      eval_simple_lvalue e m l b ofs ->
      deref_loc ge ty m b ofs t v1 ->
      match sem_incrdecr id v1 ty with
      | None => True
      | Some v2 =>
          match sem_cast v2 (incrdecr_type ty) ty with
          | None => True
          | Some v3 => forall t2 m', ~(assign_loc ge (typeof l) m b ofs v3 t2 m')
          end
      end ->
      ty = typeof l ->
      estep (ExprState f (C (Epostincr id l ty)) k e m)
          t Stuckstate

  | step_comma: forall f C r1 r2 ty k e m v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r1 v ->
      ty = typeof r2 ->
      estep (ExprState f (C (Ecomma r1 r2 ty)) k e m)
         E0 (ExprState f (C r2) k e m)

  | step_paren: forall f C r tycast ty k e m v1 v,
      leftcontext RV RV C ->
      eval_simple_rvalue e m r v1 ->
      sem_cast v1 (typeof r) tycast = Some v ->
      estep (ExprState f (C (Eparen r tycast ty)) k e m)
         E0 (ExprState f (C (Eval v ty)) k e m)

  | step_call: forall f C rf rargs ty k e m targs tres cconv vf vargs fd,
      leftcontext RV RV C ->
      classify_fun (typeof rf) = fun_case_f targs tres cconv ->
      eval_simple_rvalue e m rf vf ->
      eval_simple_list e m rargs targs vargs ->
      Genv.find_funct ge vf = Some fd ->
      type_of_fundef fd = Tfunction targs tres cconv ->
      estep (ExprState f (C (Ecall rf rargs ty)) k e m)
         E0 (Callstate fd vargs (Kcall f e C ty k) m)

  | step_builtin: forall f C ef tyargs rargs ty k e m vargs t vres m',
      leftcontext RV RV C ->
      eval_simple_list e m rargs tyargs vargs ->
      builtin_call ef ge vargs m t vres m' ->
      estep (ExprState f (C (Ebuiltin ef tyargs rargs ty)) k e m)
          t (ExprState f (C (Eval vres ty)) k e m').

Definition step (S: state) (t: trace) (S': state) : Prop :=
  estep S t S' \/ sstep ge S t S'.

(** Properties of contexts *)

Lemma context_compose:
  forall k2 k3 C2, context k2 k3 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  context k1 k3 (fun x => C2(C1 x))
with contextlist_compose:
  forall k2 C2, contextlist k2 C2 ->
  forall k1 C1, context k1 k2 C1 ->
  contextlist k1 (fun x => C2(C1 x)).
Proof.
  induction 1; intros; try (constructor; eauto).
  replace (fun x => C1 x) with C1. auto. apply extensionality; auto.
  induction 1; intros; constructor; eauto.
Qed.

Hint Constructors context contextlist.
Hint Resolve context_compose contextlist_compose.

(** * Safe executions. *)

(** A state is safe according to the nondeterministic semantics 
  if it cannot get stuck by doing silent transitions only. *)

Definition safe (s: Csem.state) : Prop :=
  forall s', star (Csem.step ge) s E0 s' ->
  (exists r, final_state s' r) \/ (exists t, exists s'', Csem.step ge s' t s'').

Lemma safe_steps:
  forall s s',
  safe s -> star (Csem.step ge) s E0 s' -> safe s'.
Proof.
  intros; red; intros. 
  eapply H. eapply star_trans; eauto. 
Qed.

Lemma star_safe:
  forall s1 s2 t s3,
  safe s1 -> star (Csem.step ge) s1 E0 s2 -> (safe s2 -> star (Csem.step ge) s2 t s3) ->
  star (Csem.step ge) s1 t s3.
Proof.
  intros. eapply star_trans; eauto. apply H1. eapply safe_steps; eauto. auto.
Qed.

Lemma plus_safe:
  forall s1 s2 t s3,
  safe s1 -> star (Csem.step ge) s1 E0 s2 -> (safe s2 -> plus (Csem.step ge) s2 t s3) ->
  plus (Csem.step ge) s1 t s3.
Proof.
  intros. eapply star_plus_trans; eauto. apply H1. eapply safe_steps; eauto. auto.
Qed.

Require Import Classical. 

Lemma safe_imm_safe:
  forall f C a k e m K,
  safe (ExprState f (C a) k e m) ->
  context K RV C ->
  imm_safe ge e K a m.
Proof.
  intros. destruct (classic (imm_safe ge e K a m)); auto.
  destruct (H Stuckstate). 
  apply star_one. left. econstructor; eauto.
  destruct H2 as [r F]. inv F. 
  destruct H2 as [t [s' S]]. inv S. inv H2. inv H2. 
Qed.

(** Safe expressions are well-formed with respect to l-values and r-values. *)

Definition expr_kind (a: expr) : kind :=
  match a with
  | Eloc _ _ _ => LV
  | Evar _ _ => LV
  | Ederef _ _ => LV
  | Efield _ _ _ => LV
  | _ => RV
  end.

Lemma lred_kind:
  forall e a m a' m', lred ge e a m a' m' -> expr_kind a = LV.
Proof.
  induction 1; auto.
Qed.

Lemma rred_kind:
  forall a m t a' m', rred ge a m t a' m' -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma callred_kind:
  forall a fd args ty, callred ge a fd args ty -> expr_kind a = RV.
Proof.
  induction 1; auto.
Qed.

Lemma context_kind:
  forall a from to C, context from to C -> expr_kind a = from -> expr_kind (C a) = to.
Proof.
  induction 1; intros; simpl; auto.
Qed.

Lemma imm_safe_kind:
  forall e k a m, imm_safe ge e k a m -> expr_kind a = k.
Proof.
  induction 1.
  auto.
  auto.
  eapply context_kind; eauto. eapply lred_kind; eauto.
  eapply context_kind; eauto. eapply rred_kind; eauto.
  eapply context_kind; eauto. eapply callred_kind; eauto.
Qed.

Lemma safe_expr_kind:
  forall from C f a k e m,
  context from RV C ->
  safe (ExprState f (C a) k e m) ->
  expr_kind a = from.
Proof.
  intros. eapply imm_safe_kind. eapply safe_imm_safe; eauto.
Qed.

(** Painful inversion lemmas on particular states that are safe. *)

Section INVERSION_LEMMAS.

Variable e: env.

Fixpoint exprlist_all_values (rl: exprlist) : Prop :=
  match rl with
  | Enil => True
  | Econs (Eval v ty) rl' => exprlist_all_values rl'
  | Econs _ _ => False
  end.

Definition invert_expr_prop (a: expr) (m: mem) : Prop :=
  match a with
  | Eloc b ofs ty => False
  | Evar x ty =>
      exists b,
      e!x = Some(b, ty)
      \/ (e!x = None /\ Genv.find_symbol ge x = Some b)
  | Ederef (Eval v ty1) ty =>
      exists b, exists ofs, v = Vptr b ofs
  | Efield (Eval v ty1) f ty =>
      exists b, exists ofs, v = Vptr b ofs /\
      match ty1 with
      | Tstruct _ fList _ => exists delta, field_offset f fList = Errors.OK delta
      | Tunion _ _ _ => True
      | _ => False
      end
  | Eval v ty => False
  | Evalof (Eloc b ofs ty') ty =>
      ty' = ty /\ exists t, exists v, deref_loc ge ty m b ofs t v
  | Eunop op (Eval v1 ty1) ty =>
      exists v, sem_unary_operation op v1 ty1 = Some v
  | Ebinop op (Eval v1 ty1) (Eval v2 ty2) ty =>
      exists v, sem_binary_operation op v1 ty1 v2 ty2 m = Some v
  | Ecast (Eval v1 ty1) ty =>
      exists v, sem_cast v1 ty1 ty = Some v
  | Eseqand (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 = Some b
  | Eseqor (Eval v1 ty1) r2 ty =>
      exists b, bool_val v1 ty1 = Some b
  | Econdition (Eval v1 ty1) r1 r2 ty =>
      exists b, bool_val v1 ty1 = Some b
  | Eassign (Eloc b ofs ty1) (Eval v2 ty2) ty =>
      exists v, exists m', exists t,
      ty = ty1 /\ sem_cast v2 ty2 ty1 = Some v /\ assign_loc ge ty1 m b ofs v t m'
  | Eassignop op (Eloc b ofs ty1) (Eval v2 ty2) tyres ty =>
      exists t, exists v1,
      ty = ty1
      /\ deref_loc ge ty1 m b ofs t v1
  | Epostincr id (Eloc b ofs ty1) ty =>
      exists t, exists v1,
      ty = ty1
      /\ deref_loc ge ty m b ofs t v1
  | Ecomma (Eval v ty1) r2 ty =>
      typeof r2 = ty
  | Eparen (Eval v1 ty1) ty2 ty =>
      exists v, sem_cast v1 ty1 ty2 = Some v
  | Ecall (Eval vf tyf) rargs ty =>
      exprlist_all_values rargs ->
      exists tyargs tyres cconv fd vl,
         classify_fun tyf = fun_case_f tyargs tyres cconv
      /\ Genv.find_funct ge vf = Some fd
      /\ cast_arguments rargs tyargs vl
      /\ type_of_fundef fd = Tfunction tyargs tyres cconv
  | Ebuiltin ef tyargs rargs ty =>
      exprlist_all_values rargs ->
      exists vargs, exists t, exists vres, exists m',
         cast_arguments rargs tyargs vargs
      /\ builtin_call ef ge vargs m t vres m'
  | _ => True
  end.

Lemma lred_invert:
  forall l m l' m', lred ge e l m l' m' -> invert_expr_prop l m.
Proof.
  induction 1; red; auto.
  exists b; auto.
  exists b; auto.
  exists b; exists ofs; auto.
  exists b; exists ofs; split; auto. exists delta; auto.
  exists b; exists ofs; auto.
Qed.

Lemma rred_invert:
  forall r m t r' m', rred ge r m t r' m' -> invert_expr_prop r m.
Proof.
  induction 1; red; auto.
  split; auto; exists t; exists v; auto.
  exists v; auto.
  exists v; auto.
  exists v; auto.
  exists true; auto. exists false; auto.
  exists true; auto. exists false; auto.
  exists b; auto.
  exists v; exists m'; exists t; auto.
  exists t; exists v1; auto.
  exists t; exists v1; auto.
  exists v; auto.
  intros. exists vargs; exists t; exists vres; exists m'; auto.
Qed.

Lemma callred_invert:
  forall r fd args ty m,
  callred ge r fd args ty ->
  invert_expr_prop r m.
Proof.
  intros. inv H. simpl.
  intros. exists tyargs, tyres, cconv, fd, args; auto.
Qed.

Scheme context_ind2 := Minimality for context Sort Prop
  with contextlist_ind2 := Minimality for contextlist Sort Prop.
Combined Scheme context_contextlist_ind from context_ind2, contextlist_ind2.

Lemma invert_expr_context:
  (forall from to C, context from to C ->
   forall a m,
   invert_expr_prop a m ->
   invert_expr_prop (C a) m)
/\(forall from C, contextlist from C ->
  forall a m,
  invert_expr_prop a m ->
  ~exprlist_all_values (C a)).
Proof.
  apply context_contextlist_ind; intros; try (exploit H0; [eauto|intros]); simpl.
  auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  auto.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto; destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  destruct e1; auto. intros. elim (H0 a m); auto.
  intros. elim (H0 a m); auto. 
  destruct (C a); auto; contradiction.
  destruct (C a); auto; contradiction.
  red; intros. destruct (C a); auto. 
  red; intros. destruct e1; auto. elim (H0 a m); auto. 
Qed.

Lemma imm_safe_inv:
  forall k a m,
  imm_safe ge e k a m ->
  match a with
  | Eloc _ _ _ => True
  | Eval _ _ => True
  | _ => invert_expr_prop a m
  end.
Proof.
  destruct invert_expr_context as [A B].
  intros. inv H. 
  auto.
  auto.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply lred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply rred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
  assert (invert_expr_prop (C e0) m).
    eapply A; eauto. eapply callred_invert; eauto.
  red in H. destruct (C e0); auto; contradiction.
Qed.

Lemma safe_inv:
  forall k C f a K m,
  safe (ExprState f (C a) K e m) ->
  context k RV C ->
  match a with
  | Eloc _ _ _ => True
  | Eval _ _ => True
  | _ => invert_expr_prop a m
  end.
Proof.
  intros. eapply imm_safe_inv; eauto. eapply safe_imm_safe; eauto.
Qed.

End INVERSION_LEMMAS.

(** * Correctness of the strategy. *)

Section SIMPLE_EVAL.

Variable f: function.
Variable k: cont.
Variable e: env.
Variable m: mem.

Lemma eval_simple_steps:
   (forall a v, eval_simple_rvalue e m a v ->
    forall C, context RV RV C ->
    star (Csem.step ge) (ExprState f (C a) k e m)
                     E0 (ExprState f (C (Eval v (typeof a))) k e m))
/\ (forall a b ofs, eval_simple_lvalue e m a b ofs ->
    forall C, context LV RV C ->
    star (Csem.step ge) (ExprState f (C a) k e m)
                     E0 (ExprState f (C (Eloc b ofs (typeof a))) k e m)).
Proof.

Ltac Steps REC C' := eapply star_trans; [apply (REC C'); eauto | idtac | simpl; reflexivity].
Ltac FinishR := apply star_one; left; apply step_rred; eauto; simpl; try (econstructor; eauto; fail).
Ltac FinishL := apply star_one; left; apply step_lred; eauto; simpl; try (econstructor; eauto; fail).

  apply eval_simple_rvalue_lvalue_ind; intros.
(* val *)
  apply star_refl.
(* valof *)
  Steps H0 (fun x => C(Evalof x ty)). rewrite <- H1 in *. FinishR.
(* addrof *)
  Steps H0 (fun x => C(Eaddrof x ty)). FinishR.
(* unop *)
  Steps H0 (fun x => C(Eunop op x ty)). FinishR.
(* binop *)
  Steps H0 (fun x => C(Ebinop op x r2 ty)).
  Steps H2 (fun x => C(Ebinop op (Eval v1 (typeof r1)) x ty)).
  FinishR.
(* cast *)
  Steps H0 (fun x => C(Ecast x ty)). FinishR. 
(* sizeof *)
  FinishR.
(* alignof *)
  FinishR.
(* loc *)
  apply star_refl.
(* var local *)
  FinishL. 
(* var global *)
  FinishL. apply red_var_global; auto.
(* deref *)
  Steps H0 (fun x => C(Ederef x ty)). FinishL. 
(* field struct *)
  Steps H0 (fun x => C(Efield x f0 ty)). rewrite H1 in *. FinishL.
(* field union *)
  Steps H0 (fun x => C(Efield x f0 ty)). rewrite H1 in *. FinishL.
Qed.

Lemma eval_simple_rvalue_steps:
  forall a v, eval_simple_rvalue e m a v ->
  forall C, context RV RV C ->
  star (Csem.step ge) (ExprState f (C a) k e m)
                   E0 (ExprState f (C (Eval v (typeof a))) k e m).
Proof (proj1 eval_simple_steps).

Lemma eval_simple_lvalue_steps:
  forall a b ofs, eval_simple_lvalue e m a b ofs ->
  forall C, context LV RV C ->
  star (Csem.step ge) (ExprState f (C a) k e m)
                   E0 (ExprState f (C (Eloc b ofs (typeof a))) k e m).
Proof (proj2 eval_simple_steps).

Corollary eval_simple_rvalue_safe:
  forall C a v,
  eval_simple_rvalue e m a v ->
  context RV RV C -> safe (ExprState f (C a) k e m) ->
  safe (ExprState f (C (Eval v (typeof a))) k e m).
Proof.
  intros. eapply safe_steps; eauto. eapply eval_simple_rvalue_steps; eauto.
Qed.

Corollary eval_simple_lvalue_safe:
  forall C a b ofs,
  eval_simple_lvalue e m a b ofs ->
  context LV RV C -> safe (ExprState f (C a) k e m) ->
  safe (ExprState f (C (Eloc b ofs (typeof a))) k e m).
Proof.
  intros. eapply safe_steps; eauto. eapply eval_simple_lvalue_steps; eauto.
Qed.

Lemma simple_can_eval:
  forall a from C,
  simple a = true -> context from RV C -> safe (ExprState f (C a) k e m) ->
  match from with
  | LV => exists b, exists ofs, eval_simple_lvalue e m a b ofs
  | RV => exists v, eval_simple_rvalue e m a v
  end.
Proof.
Ltac StepL REC C' a :=
  let b := fresh "b" in let ofs := fresh "ofs" in
  let E := fresh "E" in let S := fresh "SAFE" in
  exploit (REC LV C'); eauto; intros [b [ofs E]];
  assert (S: safe (ExprState f (C' (Eloc b ofs (typeof a))) k e m)) by 
    (eapply (eval_simple_lvalue_safe C'); eauto);
  simpl in S.
Ltac StepR REC C' a :=
  let v := fresh "v" in let E := fresh "E" in let S := fresh "SAFE" in
  exploit (REC RV C'); eauto; intros [v E];
  assert (S: safe (ExprState f (C' (Eval v (typeof a))) k e m)) by 
    (eapply (eval_simple_rvalue_safe C'); eauto);
  simpl in S.

  induction a; intros from C S CTX SAFE;
  generalize (safe_expr_kind _ _ _ _ _ _ _ CTX SAFE); intro K; subst;
  simpl in S; try discriminate; simpl.
(* val *)
  exists v; constructor.
(* var *)
  exploit safe_inv; eauto; simpl. intros [b A].
  exists b; exists Int.zero.
  intuition. apply esl_var_local; auto. apply esl_var_global; auto.
(* field *)
  StepR IHa (fun x => C(Efield x f0 ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl.
  intros [b [ofs [EQ TY]]]. subst v. destruct (typeof a) eqn:?; try contradiction.
  destruct TY as [delta OFS]. exists b; exists (Int.add ofs (Int.repr delta)); econstructor; eauto.
  exists b; exists ofs; econstructor; eauto.
(* valof *)
  destruct (andb_prop _ _ S) as [S1 S2]. clear S. rewrite negb_true_iff in S2.
  StepL IHa (fun x => C(Evalof x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [TY [t [v LOAD]]].
  assert (t = E0). inv LOAD; auto. congruence. subst t.
  exists v; econstructor; eauto. congruence.
(* deref *)
  StepR IHa (fun x => C(Ederef x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [b [ofs EQ]].
  subst v. exists b; exists ofs; econstructor; eauto.
(* addrof *)
  StepL IHa (fun x => C(Eaddrof x ty)) a.
  exists (Vptr b ofs); econstructor; eauto.
(* unop *)
  StepR IHa (fun x => C(Eunop op x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [v' EQ].
  exists v'; econstructor; eauto.
(* binop *)
  destruct (andb_prop _ _ S) as [S1 S2]; clear S.
  StepR IHa1 (fun x => C(Ebinop op x a2 ty)) a1.
  StepR IHa2 (fun x => C(Ebinop op (Eval v (typeof a1)) x ty)) a2.
  exploit safe_inv. eexact SAFE1. eauto. simpl. intros [v' EQ].
  exists v'; econstructor; eauto.
(* cast *)
  StepR IHa (fun x => C(Ecast x ty)) a.
  exploit safe_inv. eexact SAFE0. eauto. simpl. intros [v' CAST].
  exists v'; econstructor; eauto.
(* sizeof *)
  econstructor; econstructor.
(* alignof *)
  econstructor; econstructor.
(* loc *)
  exists b; exists ofs; constructor.
Qed.

Lemma simple_can_eval_rval:
  forall r C, 
  simple r = true -> context RV RV C -> safe (ExprState f (C r) k e m) ->
  exists v, eval_simple_rvalue e m r v
        /\ safe (ExprState f (C (Eval v (typeof r))) k e m).
Proof.
  intros. exploit (simple_can_eval r RV); eauto. intros [v A]. 
  exists v; split; auto. eapply eval_simple_rvalue_safe; eauto.
Qed.

Lemma simple_can_eval_lval:
  forall l C, 
  simple l = true -> context LV RV C -> safe (ExprState f (C l) k e m) ->
  exists b, exists ofs, eval_simple_lvalue e m l b ofs
         /\ safe (ExprState f (C (Eloc b ofs (typeof l))) k e m).
Proof.
  intros. exploit (simple_can_eval l LV); eauto. intros [b [ofs A]]. 
  exists b; exists ofs; split; auto. eapply eval_simple_lvalue_safe; eauto.
Qed.

Fixpoint rval_list (vl: list val) (rl: exprlist) : exprlist :=
  match vl, rl with
  | v1 :: vl', Econs r1 rl' => Econs (Eval v1 (typeof r1)) (rval_list vl' rl')
  | _, _ => Enil
  end.

Inductive eval_simple_list': exprlist -> list val -> Prop :=
  | esrl'_nil:
      eval_simple_list' Enil nil
  | esrl'_cons: forall r rl v vl,
      eval_simple_rvalue e m r v ->
      eval_simple_list' rl vl ->
      eval_simple_list' (Econs r rl) (v :: vl).

Lemma eval_simple_list_implies:
  forall rl tyl vl,
  eval_simple_list e m rl tyl vl -> 
  exists vl', cast_arguments (rval_list vl' rl) tyl vl /\ eval_simple_list' rl vl'.
Proof.
  induction 1.
  exists (@nil val); split. constructor. constructor.
  destruct IHeval_simple_list as [vl' [A B]].
  exists (v' :: vl'); split. constructor; auto. constructor; auto.
Qed.

Lemma can_eval_simple_list:
  forall rl vl,
  eval_simple_list' rl vl ->
  forall tyl vl',
  cast_arguments (rval_list vl rl) tyl vl' ->
  eval_simple_list e m rl tyl vl'.
Proof.
  induction 1; simpl; intros. 
  inv H. constructor.
  inv H1. econstructor; eauto. 
Qed.

Fixpoint exprlist_app (rl1 rl2: exprlist) : exprlist :=
  match rl1 with
  | Enil => rl2
  | Econs r1 rl1' => Econs r1 (exprlist_app rl1' rl2)
  end.

Lemma exprlist_app_assoc:
  forall rl2 rl3 rl1,
  exprlist_app (exprlist_app rl1 rl2) rl3 =
  exprlist_app rl1 (exprlist_app rl2 rl3).
Proof.
  induction rl1; auto. simpl. congruence. 
Qed.

Inductive contextlist' : (exprlist -> expr) -> Prop :=
  | contextlist'_call: forall r1 rl0 ty C,
      context RV RV C ->
      contextlist' (fun rl => C (Ecall r1 (exprlist_app rl0 rl) ty))
  | contextlist'_builtin: forall ef tyargs rl0 ty C,
      context RV RV C ->
      contextlist' (fun rl => C (Ebuiltin ef tyargs (exprlist_app rl0 rl) ty)).

Lemma exprlist_app_context:
  forall rl1 rl2,
  contextlist RV (fun x => exprlist_app rl1 (Econs x rl2)).
Proof.
  induction rl1; simpl; intros. 
  apply ctx_list_head. constructor.
  apply ctx_list_tail. auto. 
Qed.

Lemma contextlist'_head:
  forall rl C,
  contextlist' C ->
  context RV RV (fun x => C (Econs x rl)).
Proof.
  intros. inv H. 
  set (C' := fun x => Ecall r1 (exprlist_app rl0 (Econs x rl)) ty).
  assert (context RV RV C'). constructor. apply exprlist_app_context.
  change (context RV RV (fun x => C0 (C' x))). 
  eapply context_compose; eauto.
  set (C' := fun x => Ebuiltin ef tyargs (exprlist_app rl0 (Econs x rl)) ty).
  assert (context RV RV C'). constructor. apply exprlist_app_context.
  change (context RV RV (fun x => C0 (C' x))). 
  eapply context_compose; eauto.
Qed.

Lemma contextlist'_tail:
  forall r1 C,
  contextlist' C ->
  contextlist' (fun x => C (Econs r1 x)).
Proof.
  intros. inv H. 
  replace (fun x => C0 (Ecall r0 (exprlist_app rl0 (Econs r1 x)) ty))
     with (fun x => C0 (Ecall r0 (exprlist_app (exprlist_app rl0 (Econs r1 Enil)) x) ty)).
  constructor. auto. 
  apply extensionality; intros. f_equal. f_equal. apply exprlist_app_assoc.
  replace (fun x => C0 (Ebuiltin ef tyargs (exprlist_app rl0 (Econs r1 x)) ty))
     with (fun x => C0 (Ebuiltin ef tyargs (exprlist_app (exprlist_app rl0 (Econs r1 Enil)) x) ty)).
  constructor. auto. 
  apply extensionality; intros. f_equal. f_equal. apply exprlist_app_assoc.
Qed.

Hint Resolve contextlist'_head contextlist'_tail.

Lemma eval_simple_list_steps:
  forall rl vl, eval_simple_list' rl vl ->
  forall C, contextlist' C ->
  star (Csem.step ge) (ExprState f (C rl) k e m)
                   E0 (ExprState f (C (rval_list vl rl)) k e m).
Proof.
  induction 1; intros. 
(* nil *)
  apply star_refl.
(* cons *)
  eapply star_trans.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Econs x rl)); eauto.
  apply IHeval_simple_list' with (C := fun x => C(Econs (Eval v (typeof r)) x)); auto.
  auto.
Qed.

Lemma simple_list_can_eval:
  forall rl C,
  simplelist rl = true ->
  contextlist' C ->
  safe (ExprState f (C rl) k e m) ->
  exists vl, eval_simple_list' rl vl.
Proof.
  induction rl; intros.
  econstructor; constructor.
  simpl in H. destruct (andb_prop _ _ H). 
  exploit (simple_can_eval r1 RV (fun x => C(Econs x rl))); eauto.
  intros [v1 EV1].
  exploit (IHrl (fun x => C(Econs (Eval v1 (typeof r1)) x))); eauto.
  apply (eval_simple_rvalue_safe (fun x => C(Econs x rl))); eauto.
  intros [vl EVl].
  exists (v1 :: vl); constructor; auto.
Qed.

Lemma rval_list_all_values:
  forall vl rl, exprlist_all_values (rval_list vl rl).
Proof.
  induction vl; simpl; intros. auto. 
  destruct rl; simpl; auto.
Qed.

End SIMPLE_EVAL.

(** Decomposition *)

Section DECOMPOSITION.

Variable f: function.
Variable k: cont.
Variable e: env.
Variable m: mem.

Definition simple_side_effect (r: expr) : Prop :=
  match r with
  | Evalof l _ => simple l = true /\ type_is_volatile (typeof l) = true
  | Eseqand r1 r2 _ => simple r1 = true
  | Eseqor r1 r2 _ => simple r1 = true
  | Econdition r1 r2 r3 _ => simple r1 = true
  | Eassign l1 r2 _ => simple l1 = true /\ simple r2 = true
  | Eassignop _ l1 r2 _ _ => simple l1 = true /\ simple r2 = true
  | Epostincr _ l1 _ => simple l1 = true
  | Ecomma r1 r2 _ => simple r1 = true
  | Ecall r1 rl _ => simple r1 = true /\ simplelist rl = true
  | Ebuiltin ef tyargs rl _ => simplelist rl = true
  | Eparen r1 _ _ => simple r1 = true
  | _ => False
  end.

Scheme expr_ind2 := Induction for expr Sort Prop
  with exprlist_ind2 := Induction for exprlist Sort Prop.
Combined Scheme expr_expr_list_ind from expr_ind2, exprlist_ind2.

Hint Constructors leftcontext leftcontextlist.

Lemma decompose_expr:
  (forall a from C,
   context from RV C -> safe (ExprState f (C a) k e m) ->
       simple a = true
    \/ exists C', exists a', a = C' a' /\ simple_side_effect a' /\ leftcontext RV from C')
/\(forall rl C,
   contextlist' C -> safe (ExprState f (C rl) k e m) ->
       simplelist rl = true
    \/ exists C', exists a', rl = C' a' /\ simple_side_effect a' /\ leftcontextlist RV C').
Proof.
  apply expr_expr_list_ind; intros; simpl; auto.

Ltac Kind :=
  exploit safe_expr_kind; eauto; simpl; intros X; rewrite <- X in *; clear X.
Ltac Rec HR kind C C' :=
  destruct (HR kind (fun x => C(C' x))) as [? | [C'' [a' [D [A B]]]]];
  [eauto | eauto | auto |
   right; exists (fun x => C'(C'' x)); exists a'; rewrite D; auto].
Ltac Base :=
  right; exists (fun x => x); econstructor; split; [eauto | simpl; auto].

(* field *)
  Kind. Rec H RV C (fun x => Efield x f0 ty).
(* rvalof *)
  Kind. Rec H LV C (fun x => Evalof x ty).
  destruct (type_is_volatile (typeof l)) eqn:?.
  Base. rewrite H2; auto.
(* deref *)
  Kind. Rec H RV C (fun x => Ederef x ty).
(* addrof *)
  Kind. Rec H LV C (fun x => Eaddrof x ty).
(* unop *)
  Kind. Rec H RV C (fun x => Eunop op x ty).
(* binop *)
  Kind. Rec H RV C (fun x => Ebinop op x r2 ty). rewrite H3.
  Rec H0 RV C (fun x => Ebinop op r1 x ty).
(* cast *)
  Kind. Rec H RV C (fun x => Ecast x ty).
(* seqand *)
  Kind. Rec H RV C (fun x => Eseqand x r2 ty). Base.
(* seqor *)
  Kind. Rec H RV C (fun x => Eseqor x r2 ty). Base.
(* condition *)
  Kind. Rec H RV C (fun x => Econdition x r2 r3 ty). Base.
(* assign *)
  Kind. Rec H LV C (fun x => Eassign x r ty). Rec H0 RV C (fun x => Eassign l x ty). Base.
(* assignop *)
  Kind. Rec H LV C (fun x => Eassignop op x r tyres ty). Rec H0 RV C (fun x => Eassignop op l x tyres ty). Base.
(* postincr *)
  Kind. Rec H LV C (fun x => Epostincr id x ty). Base.
(* comma *)
  Kind. Rec H RV C (fun x => Ecomma x r2 ty). Base.
(* call *)
  Kind. Rec H RV C (fun x => Ecall x rargs ty). 
  destruct (H0 (fun x => C (Ecall r1 x ty))) as [A | [C' [a' [D [A B]]]]].
    eapply contextlist'_call with (C := C) (rl0 := Enil). auto. auto.
  Base.
  right; exists (fun x => Ecall r1 (C' x) ty); exists a'. rewrite D; simpl; auto.
(* builtin *)
  Kind. 
  destruct (H (fun x => C (Ebuiltin ef tyargs x ty))) as [A | [C' [a' [D [A B]]]]].
    eapply contextlist'_builtin with (C := C) (rl0 := Enil). auto. auto.
  Base.
  right; exists (fun x => Ebuiltin ef tyargs (C' x) ty); exists a'. rewrite D; simpl; auto.
(* rparen *)
  Kind. Rec H RV C (fun x => (Eparen x tycast ty)). Base.
(* cons *)
  destruct (H RV (fun x => C (Econs x rl))) as [A | [C' [a' [A [B D]]]]].
    eapply contextlist'_head; eauto. auto.
  destruct (H0 (fun x => C (Econs r1 x))) as [A' | [C' [a' [A' [B D]]]]].
    eapply contextlist'_tail; eauto. auto.
  rewrite A; rewrite A'; auto. 
  right; exists (fun x => Econs r1 (C' x)); exists a'. rewrite A'; eauto.
  right; exists (fun x => Econs (C' x) rl); exists a'. rewrite A; eauto.
Qed.

Lemma decompose_topexpr:
  forall a,
  safe (ExprState f a k e m) ->
       simple a = true
    \/ exists C, exists a', a = C a' /\ simple_side_effect a' /\ leftcontext RV RV C.
Proof.
  intros. eapply (proj1 decompose_expr). apply ctx_top. auto.
Qed.

End DECOMPOSITION.

(** Simulation for expressions. *)

Lemma estep_simulation:
  forall S t S',
  estep S t S' -> plus (Csem.step ge) S t S'.
Proof.
  intros. inv H. 
(* simple *)
  exploit eval_simple_rvalue_steps; eauto. simpl; intros STEPS.
  exploit star_inv; eauto. intros [[EQ1 EQ2] | A]; eauto. 
  inversion EQ1. rewrite <- H2 in H1; contradiction.
(* valof volatile *)
  eapply plus_right. 
  eapply eval_simple_lvalue_steps with (C := fun x => C(Evalof x (typeof l))); eauto.
  left. apply step_rred; eauto. econstructor; eauto. auto.
(* seqand true *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqand x r2 ty)); eauto. 
  left. apply step_rred; eauto. apply red_seqand_true; auto. traceEq.
(* seqand false *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqand x r2 ty)); eauto. 
  left. apply step_rred; eauto. apply red_seqand_false; auto. traceEq.
(* seqor true *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqor x r2 ty)); eauto. 
  left. apply step_rred; eauto. apply red_seqor_true; auto. traceEq.
(* seqor false *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eseqor x r2 ty)); eauto. 
  left. apply step_rred; eauto. apply red_seqor_false; auto. traceEq.
(* condition *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Econdition x r2 r3 ty)); eauto.
  left; apply step_rred; eauto. constructor; auto. auto. 
(* assign *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Eassign x r (typeof l))); eauto.
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eassign (Eloc b ofs (typeof l)) x (typeof l))); eauto.
  left; apply step_rred; eauto. econstructor; eauto.
  reflexivity. auto. 
(* assignop *) 
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Eassignop op x r tyres (typeof l))); eauto.
  eapply star_plus_trans.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eassignop op (Eloc b ofs (typeof l)) x tyres (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  eapply star_left.
  left; apply step_rred with (C := fun x => C(Eassign (Eloc b ofs (typeof l)) x (typeof l))); eauto. econstructor; eauto.  
  apply star_one. 
  left; apply step_rred; auto. econstructor; eauto. 
  reflexivity. reflexivity. reflexivity. traceEq.
(* assignop stuck *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Eassignop op x r tyres (typeof l))); eauto.
  eapply star_plus_trans.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eassignop op (Eloc b ofs (typeof l)) x tyres (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  destruct (sem_binary_operation op v1 (typeof l) v2 (typeof r) m) as [v3|] eqn:?.
  eapply star_left.
  left; apply step_rred with (C := fun x => C(Eassign (Eloc b ofs (typeof l)) x (typeof l))); eauto. econstructor; eauto.  
  apply star_one. 
  left; eapply step_stuck; eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v4' [m' [t' [A [B D]]]]].
  rewrite B in H4. eelim H4; eauto.
  reflexivity.
  apply star_one.
  left; eapply step_stuck with (C := fun x => C(Eassign (Eloc b ofs (typeof l)) x (typeof l))); eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v3 A]. congruence.
  reflexivity.
  reflexivity. traceEq.
(* postincr *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Epostincr id x (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  eapply star_left.
  left; apply step_rred with (C := fun x => C (Ecomma (Eassign (Eloc b ofs (typeof l)) x (typeof l)) (Eval v1 (typeof l)) (typeof l))); eauto.
  econstructor. instantiate (1 := v2). destruct id; assumption. 
  eapply star_left.
  left; apply step_rred with (C := fun x => C (Ecomma x (Eval v1 (typeof l)) (typeof l))); eauto.
  econstructor; eauto.
  apply star_one.
  left; apply step_rred; auto. econstructor; eauto. 
  reflexivity. reflexivity. reflexivity. traceEq.
(* postincr stuck *)
  eapply star_plus_trans.
  eapply eval_simple_lvalue_steps with (C := fun x => C(Epostincr id x (typeof l))); eauto.
  eapply plus_left.
  left; apply step_rred; auto. econstructor; eauto.
  set (op := match id with Incr => Oadd | Decr => Osub end).
  assert (SEM: sem_binary_operation op v1 (typeof l) (Vint Int.one) type_int32s m =
              sem_incrdecr id v1 (typeof l)).
    destruct id; auto.
  destruct (sem_incrdecr id v1 (typeof l)) as [v2|].
  eapply star_left.
  left; apply step_rred with (C := fun x => C (Ecomma (Eassign (Eloc b ofs (typeof l)) x (typeof l)) (Eval v1 (typeof l)) (typeof l))); eauto.
  econstructor; eauto.
  apply star_one.
  left; eapply step_stuck with (C := fun x => C (Ecomma x (Eval v1 (typeof l)) (typeof l))); eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v3 [m' [t' [A [B D]]]]].
  rewrite B in H3. eelim H3; eauto.
  reflexivity.
  apply star_one.
  left; eapply step_stuck with (C := fun x => C (Ecomma (Eassign (Eloc b ofs (typeof l)) x (typeof l)) (Eval v1 (typeof l)) (typeof l))); eauto.
  red; intros. exploit imm_safe_inv; eauto. simpl. intros [v2 A]. congruence.
  reflexivity. 
  traceEq.
(* comma *)
  eapply plus_right.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Ecomma x r2 (typeof r2))); eauto.
  left; apply step_rred; eauto. econstructor; eauto. auto.
(* paren *)
  eapply plus_right; eauto.
  eapply eval_simple_rvalue_steps with (C := fun x => C(Eparen x tycast ty)); eauto.
  left; apply step_rred; eauto. econstructor; eauto. auto.
(* call *)
  exploit eval_simple_list_implies; eauto. intros [vl' [A B]].
  eapply star_plus_trans. 
  eapply eval_simple_rvalue_steps with (C := fun x => C(Ecall x rargs ty)); eauto.
  eapply plus_right.
  eapply eval_simple_list_steps with (C := fun x => C(Ecall (Eval vf (typeof rf)) x ty)); eauto.
  eapply contextlist'_call with (rl0 := Enil); auto.
  left; apply Csem.step_call; eauto. econstructor; eauto.
  traceEq. auto.
(* builtin *)
  exploit eval_simple_list_implies; eauto. intros [vl' [A B]].
  eapply plus_right.
  eapply eval_simple_list_steps with (C := fun x => C(Ebuiltin ef tyargs x ty)); eauto.
  eapply contextlist'_builtin with (rl0 := Enil); auto.
  left; apply Csem.step_rred; eauto. econstructor; eauto.
  traceEq. 
Qed.

Lemma can_estep:
  forall f a k e m,
  safe (ExprState f a k e m) ->
  match a with Eval _ _ => False | _ => True end ->
  exists t, exists S, estep (ExprState f a k e m) t S.
Proof.
  intros. destruct (decompose_topexpr f k e m a H) as [A | [C [b [P [Q R]]]]].
(* simple expr *)
  exploit (simple_can_eval f k e m a RV (fun x => x)); auto. intros [v P].
  econstructor; econstructor; eapply step_expr; eauto. 
(* side effect *)
  clear H0. subst a. red in Q. destruct b; try contradiction. 
(* valof volatile *)
  destruct Q.
  exploit (simple_can_eval_lval f k e m b (fun x => C(Evalof x ty))); eauto.
  intros [b1 [ofs [E1 S1]]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [A [t [v B]]].
  econstructor; econstructor; eapply step_rvalof_volatile; eauto. congruence. 
(* seqand *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Eseqand x b2 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [b BV].
  destruct b.
  econstructor; econstructor; eapply step_seqand_true; eauto. 
  econstructor; econstructor; eapply step_seqand_false; eauto. 
(* seqor *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Eseqor x b2 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [b BV].
  destruct b.
  econstructor; econstructor; eapply step_seqor_true; eauto. 
  econstructor; econstructor; eapply step_seqor_false; eauto. 
(* condition *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Econdition x b2 b3 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [b BV].
  econstructor; econstructor. eapply step_condition; eauto. 
(* assign *)
  destruct Q.
  exploit (simple_can_eval_lval f k e m b1 (fun x => C(Eassign x b2 ty))); eauto.
  intros [b [ofs [E1 S1]]].
  exploit (simple_can_eval_rval f k e m b2 (fun x => C(Eassign (Eloc b ofs (typeof b1)) x ty))); eauto.
  intros [v [E2 S2]].
  exploit safe_inv. eexact S2. eauto. simpl. intros [v' [m' [t [A [B D]]]]].
  econstructor; econstructor; eapply step_assign; eauto. 
(* assignop *)
  destruct Q.
  exploit (simple_can_eval_lval f k e m b1 (fun x => C(Eassignop op x b2 tyres ty))); eauto.
  intros [b [ofs [E1 S1]]].
  exploit (simple_can_eval_rval f k e m b2 (fun x => C(Eassignop op (Eloc b ofs (typeof b1)) x tyres ty))); eauto.
  intros [v [E2 S2]].
  exploit safe_inv. eexact S2. eauto. simpl. intros [t1 [v1 [A B]]].
  destruct (sem_binary_operation op v1 (typeof b1) v (typeof b2) m) as [v3|] eqn:?.
  destruct (sem_cast v3 tyres (typeof b1)) as [v4|] eqn:?.
  destruct (classic (exists t2, exists m', assign_loc ge (typeof b1) m b ofs v4 t2 m')).
  destruct H2 as [t2 [m' D]].
  econstructor; econstructor; eapply step_assignop; eauto.
  econstructor; econstructor; eapply step_assignop_stuck; eauto. 
  rewrite Heqo. rewrite Heqo0. intros; red; intros. elim H2. exists t2; exists m'; auto.
  econstructor; econstructor; eapply step_assignop_stuck; eauto. 
  rewrite Heqo. rewrite Heqo0. auto.
  econstructor; econstructor; eapply step_assignop_stuck; eauto. 
  rewrite Heqo. auto.
(* postincr *)
  exploit (simple_can_eval_lval f k e m b (fun x => C(Epostincr id x ty))); eauto.
  intros [b1 [ofs [E1 S1]]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [t [v1 [A B]]].
  destruct (sem_incrdecr id v1 ty) as [v2|] eqn:?.
  destruct (sem_cast v2 (incrdecr_type ty) ty) as [v3|] eqn:?.
  destruct (classic (exists t2, exists m', assign_loc ge ty m b1 ofs v3 t2 m')).
  destruct H0 as [t2 [m' D]].
  econstructor; econstructor; eapply step_postincr; eauto.
  econstructor; econstructor; eapply step_postincr_stuck; eauto. 
  rewrite Heqo. rewrite Heqo0. intros; red; intros. elim H0. exists t2; exists m'; congruence.
  econstructor; econstructor; eapply step_postincr_stuck; eauto. 
  rewrite Heqo. rewrite Heqo0. auto.
  econstructor; econstructor; eapply step_postincr_stuck; eauto. 
  rewrite Heqo. auto.
(* comma *)
  exploit (simple_can_eval_rval f k e m b1 (fun x => C(Ecomma x b2 ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros EQ.
  econstructor; econstructor; eapply step_comma; eauto.
(* call *)
  destruct Q.
  exploit (simple_can_eval_rval f k e m b (fun x => C(Ecall x rargs ty))); eauto.
  intros [vf [E1 S1]].
  pose (C' := fun x => C(Ecall (Eval vf (typeof b)) x ty)).
  assert (contextlist' C'). unfold C'; eapply contextlist'_call with (rl0 := Enil); auto.
  exploit (simple_list_can_eval f k e m rargs C'); eauto.
  intros [vl E2].
  exploit safe_inv. 2: eapply leftcontext_context; eexact R.
  eapply safe_steps. eexact S1.
  apply (eval_simple_list_steps f k e m rargs vl E2 C'); auto.
  simpl. intros X. exploit X. eapply rval_list_all_values. 
  intros [tyargs [tyres [cconv [fd [vargs [P [Q [U V]]]]]]]].
  econstructor; econstructor; eapply step_call; eauto. eapply can_eval_simple_list; eauto. 
(* builtin *)
  pose (C' := fun x => C(Ebuiltin ef tyargs x ty)).
  assert (contextlist' C'). unfold C'; eapply contextlist'_builtin with (rl0 := Enil); auto.
  exploit (simple_list_can_eval f k e m rargs C'); eauto.
  intros [vl E].
  exploit safe_inv. 2: eapply leftcontext_context; eexact R.
  eapply safe_steps. eexact H.
  apply (eval_simple_list_steps f k e m rargs vl E C'); auto.
  simpl. intros X. exploit X. eapply rval_list_all_values.
  intros [vargs [t [vres [m' [U V]]]]].
  econstructor; econstructor; eapply step_builtin; eauto.
  eapply can_eval_simple_list; eauto. 
(* paren *)
  exploit (simple_can_eval_rval f k e m b (fun x => C(Eparen x tycast ty))); eauto.
  intros [v1 [E1 S1]].
  exploit safe_inv. eexact S1. eauto. simpl. intros [v CAST].
  econstructor; econstructor; eapply step_paren; eauto.
Qed.

(** Simulation for all states *)

Theorem step_simulation:
  forall S1 t S2,
  step S1 t S2 -> plus (Csem.step ge) S1 t S2.
Proof.
  intros. inv H.
  apply estep_simulation; auto.
  apply plus_one. right. auto.
Qed.

Theorem progress:
  forall S,
  safe S -> (exists r, final_state S r) \/ (exists t, exists S', step S t S').
Proof.
  intros. exploit H. apply star_refl. intros [FIN | [t [S' STEP]]].
  (* 1. Finished. *)
  auto.
  right. destruct STEP.
  (* 2. Expression step. *)
  assert (exists t, exists S', estep S t S').
    inv H0.
    (* lred *)
    eapply can_estep; eauto. inv H2; auto. 
    (* rred *)
    eapply can_estep; eauto. inv H2; auto. inv H1; auto. 
    (* callred *)
    eapply can_estep; eauto. inv H2; auto. inv H1; auto.
    (* stuck *)
    exploit (H Stuckstate). apply star_one. left. econstructor; eauto.
    intros [[r F] | [t [S' R]]]. inv F. inv R. inv H0. inv H0.
  destruct H1 as [t' [S'' ESTEP]].
  exists t'; exists S''; left; auto.
  (* 3. Other step. *)
  exists t; exists S'; right; auto.
Qed.

End STRATEGY.

(** The semantics that follows the strategy. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

Remark deref_loc_trace:
  forall F V (ge: Genv.t F V) ty m b ofs t v,
  deref_loc ge ty m b ofs t v ->
  match t with nil => True | ev :: nil => True | _ => False end.
Proof.
  intros. inv H; simpl; auto. inv H2; simpl; auto. 
Qed.

Remark deref_loc_receptive:
  forall F V (ge: Genv.t F V) ty m b ofs ev1 t1 v ev2,
  deref_loc ge ty m b ofs (ev1 :: t1) v ->
  match_traces ge (ev1 :: nil) (ev2 :: nil) ->
  t1 = nil /\ exists v', deref_loc ge ty m b ofs (ev2 :: nil) v'.
Proof.
  intros.
  assert (t1 = nil). exploit deref_loc_trace; eauto. destruct t1; simpl; tauto.
  inv H. exploit volatile_load_receptive; eauto. intros [v' A]. 
  split; auto; exists v'; econstructor; eauto.
Qed.

Remark assign_loc_trace:
  forall F V (ge: Genv.t F V) ty m b ofs t v m',
  assign_loc ge ty m b ofs v t m' ->
  match t with nil => True | ev :: nil => output_event ev | _ => False end.
Proof.
  intros. inv H; simpl; auto. inv H2; simpl; auto. 
Qed.

Remark assign_loc_receptive:
  forall F V (ge: Genv.t F V) ty m b ofs ev1 t1 v m' ev2,
  assign_loc ge ty m b ofs v (ev1 :: t1) m' ->
  match_traces ge (ev1 :: nil) (ev2 :: nil) ->
  ev1 :: t1 = ev2 :: nil.
Proof.
  intros.
  assert (t1 = nil). exploit assign_loc_trace; eauto. destruct t1; simpl; tauto.
  inv H. eapply volatile_store_receptive; eauto. 
Qed.

Lemma semantics_strongly_receptive: 
  forall p, strongly_receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  inversion H; subst.
  inv H1.
  (* valof volatile *)
  exploit deref_loc_receptive; eauto. intros [A [v' B]]. 
  econstructor; econstructor. left; eapply step_rvalof_volatile; eauto. 
  (* assign *)
  exploit assign_loc_receptive; eauto. intro EQ; rewrite EQ in H.
  econstructor; econstructor; eauto.
  (* assignop *)
  destruct t0 as [ | ev0 t0]; simpl in H10. 
  subst t2. exploit assign_loc_receptive; eauto. intros EQ; rewrite EQ in H.
  econstructor; econstructor; eauto.
  inv H10. exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t0.
  destruct (sem_binary_operation op v1' (typeof l) v2 (typeof r) m) as [v3'|] eqn:?.
  destruct (sem_cast v3' tyres (typeof l)) as [v4'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc (Genv.globalenv p) (typeof l) m b ofs v4' t2' m'')).
  destruct H1 as [t2' [m'' P]]. 
  econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity. 
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; auto.
  (* assignop stuck *)
  exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
  destruct (sem_binary_operation op v1' (typeof l) v2 (typeof r) m) as [v3'|] eqn:?.
  destruct (sem_cast v3' tyres (typeof l)) as [v4'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc (Genv.globalenv p) (typeof l) m b ofs v4' t2' m'')).
  destruct H1 as [t2' [m'' P]]. 
  econstructor; econstructor. left; eapply step_assignop with (v1 := v1'); eauto. simpl; reflexivity. 
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_assignop_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; auto.
  (* postincr *)
  destruct t0 as [ | ev0 t0]; simpl in H9. 
  subst t2. exploit assign_loc_receptive; eauto. intros EQ; rewrite EQ in H.
  econstructor; econstructor; eauto.
  inv H9. exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t0.
  destruct (sem_incrdecr id v1' (typeof l)) as [v2'|] eqn:?.
  destruct (sem_cast v2' (incrdecr_type (typeof l)) (typeof l)) as [v3'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc (Genv.globalenv p) (typeof l) m b ofs v3' t2' m'')).
  destruct H1 as [t2' [m'' P]]. 
  econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity. 
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t0; exists m'0; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; auto.
  (* postincr stuck *)
  exploit deref_loc_receptive; eauto. intros [EQ [v1' A]]. subst t1.
  destruct (sem_incrdecr id v1' (typeof l)) as [v2'|] eqn:?.
  destruct (sem_cast v2' (incrdecr_type (typeof l)) (typeof l)) as [v3'|] eqn:?.
  destruct (classic (exists t2', exists m'', assign_loc (Genv.globalenv p) (typeof l) m b ofs v3' t2' m'')).
  destruct H1 as [t2' [m'' P]]. 
  econstructor; econstructor. left; eapply step_postincr with (v1 := v1'); eauto. simpl; reflexivity. 
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0. intros; red; intros; elim H1. exists t2; exists m'; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; rewrite Heqo0; auto.
  econstructor; econstructor. left; eapply step_postincr_stuck with (v1 := v1'); eauto. 
  rewrite Heqo; auto.
  (* builtin *)
  exploit builtin_call_trace_length; eauto. destruct t1; simpl; intros. 
  exploit builtin_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  econstructor; econstructor. left; eapply step_builtin; eauto.
  omegaContradiction.
  (* external calls *)
  inv H1.
  exploit external_call_trace_length; eauto. destruct t1; simpl; intros. 
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (Returnstate vres2 k m2); exists E0; right; econstructor; eauto.
  omegaContradiction.
(* well-behaved traces *)
  red; intros. inv H; inv H0; simpl; auto.
  (* valof volatile *)
  exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
  (* assign *)
  exploit assign_loc_trace; eauto. destruct t; auto. destruct t; simpl; tauto.
  (* assignop *)
  exploit deref_loc_trace; eauto. exploit assign_loc_trace; eauto.
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto. 
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto. 
  tauto.
  (* assignop stuck *)
  exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
  (* postincr *)
  exploit deref_loc_trace; eauto. exploit assign_loc_trace; eauto.
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto. 
  destruct t1. destruct t2. simpl; auto. destruct t2; simpl; tauto. 
  tauto.
  (* postincr stuck *)
  exploit deref_loc_trace; eauto. destruct t; auto. destruct t; tauto.
  (* builtins *)
  exploit builtin_call_trace_length; eauto.
  destruct t; simpl; auto. destruct t; simpl; auto. intros; omegaContradiction.
  (* external calls *)
  exploit external_call_trace_length; eauto.
  destruct t; simpl; auto. destruct t; simpl; auto. intros; omegaContradiction.
Qed.

(** The main simulation result. *)

Theorem strategy_simulation:
  forall p, backward_simulation (Csem.semantics p) (semantics p).
Proof.
  intros.
  apply backward_simulation_plus with (match_states := fun (S1 S2: state) => S1 = S2); simpl.
(* symbols *)
  auto.
(* initial states exist *)
  intros. exists s1; auto.
(* initial states match *)
  intros. exists s2; auto.
(* final states match *)
  intros. subst s2. auto. 
(* progress *)
  intros. subst s2. apply progress. auto. 
(* simulation *)
  intros. subst s1. exists s2'; split; auto. apply step_simulation; auto.
Qed.
