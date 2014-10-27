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

(** Abstract syntax and semantics for the Cminor language. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Events.
Require Import Values.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Switch.

(** * Abstract syntax *)

(** Cminor is a low-level imperative language structured in expressions,
  statements, functions and programs.  We first define the constants
  and operators that occur within expressions. *)

Inductive constant : Type :=
  | Ointconst: int -> constant     (**r integer constant *)
  | Ofloatconst: float -> constant (**r double-precision floating-point constant *)
  | Osingleconst: float32 -> constant (**r single-precision floating-point constant *)
  | Olongconst: int64 -> constant  (**r long integer constant *)
  | Oaddrsymbol: ident -> int -> constant (**r address of the symbol plus the offset *)
  | Oaddrstack: int -> constant.   (**r stack pointer plus the given offset *)

Inductive unary_operation : Type :=
  | Ocast8unsigned: unary_operation        (**r 8-bit zero extension  *)
  | Ocast8signed: unary_operation          (**r 8-bit sign extension  *)
  | Ocast16unsigned: unary_operation       (**r 16-bit zero extension  *)
  | Ocast16signed: unary_operation         (**r 16-bit sign extension *)
  | Onegint: unary_operation               (**r integer opposite *)
  | Onotint: unary_operation               (**r bitwise complement  *)
  | Onegf: unary_operation                 (**r float64 opposite *)
  | Oabsf: unary_operation                 (**r float64 absolute value *)
  | Onegfs: unary_operation                (**r float32 opposite *)
  | Oabsfs: unary_operation                (**r float32 absolute value *)
  | Osingleoffloat: unary_operation        (**r float truncation to float32 *)
  | Ofloatofsingle: unary_operation        (**r float extension to float64 *)
  | Ointoffloat: unary_operation           (**r signed integer to float64 *)
  | Ointuoffloat: unary_operation          (**r unsigned integer to float64 *)
  | Ofloatofint: unary_operation           (**r float64 to signed integer *)
  | Ofloatofintu: unary_operation          (**r float64 to unsigned integer *)
  | Ointofsingle: unary_operation          (**r signed integer to float32 *)
  | Ointuofsingle: unary_operation         (**r unsigned integer to float32 *)
  | Osingleofint: unary_operation          (**r float32 to signed integer *)
  | Osingleofintu: unary_operation        (**r float32 to unsigned integer *)
  | Onegl: unary_operation                 (**r long integer opposite *)
  | Onotl: unary_operation                 (**r long bitwise complement *)
  | Ointoflong: unary_operation            (**r long to int *)
  | Olongofint: unary_operation            (**r signed int to long *)
  | Olongofintu: unary_operation           (**r unsigned int to long *)
  | Olongoffloat: unary_operation          (**r float64 to signed long *)
  | Olonguoffloat: unary_operation         (**r float64 to unsigned long *)
  | Ofloatoflong: unary_operation          (**r signed long to float64 *)
  | Ofloatoflongu: unary_operation         (**r unsigned long to float64 *)
  | Olongofsingle: unary_operation         (**r float32 to signed long *)
  | Olonguofsingle: unary_operation        (**r float32 to unsigned long *)
  | Osingleoflong: unary_operation         (**r signed long to float32 *)
  | Osingleoflongu: unary_operation.       (**r unsigned long to float32 *)

Inductive binary_operation : Type :=
  | Oadd: binary_operation                 (**r integer addition *)
  | Osub: binary_operation                 (**r integer subtraction *)
  | Omul: binary_operation                 (**r integer multiplication *)
  | Odiv: binary_operation                 (**r integer signed division *)
  | Odivu: binary_operation                (**r integer unsigned division *)
  | Omod: binary_operation                 (**r integer signed modulus *)
  | Omodu: binary_operation                (**r integer unsigned modulus *)
  | Oand: binary_operation                 (**r integer bitwise ``and'' *)
  | Oor: binary_operation                  (**r integer bitwise ``or'' *)
  | Oxor: binary_operation                 (**r integer bitwise ``xor'' *)
  | Oshl: binary_operation                 (**r integer left shift *)
  | Oshr: binary_operation                 (**r integer right signed shift *)
  | Oshru: binary_operation                (**r integer right unsigned shift *)
  | Oaddf: binary_operation                (**r float64 addition *)
  | Osubf: binary_operation                (**r float64 subtraction *)
  | Omulf: binary_operation                (**r float64 multiplication *)
  | Odivf: binary_operation                (**r float64 division *)
  | Oaddfs: binary_operation               (**r float32 addition *)
  | Osubfs: binary_operation               (**r float32 subtraction *)
  | Omulfs: binary_operation               (**r float32 multiplication *)
  | Odivfs: binary_operation               (**r float32 division *)
  | Oaddl: binary_operation                (**r long addition *)
  | Osubl: binary_operation                (**r long subtraction *)
  | Omull: binary_operation                (**r long multiplication *)
  | Odivl: binary_operation                (**r long signed division *)
  | Odivlu: binary_operation               (**r long unsigned division *)
  | Omodl: binary_operation                (**r long signed modulus *)
  | Omodlu: binary_operation               (**r long unsigned modulus *)
  | Oandl: binary_operation                (**r long bitwise ``and'' *)
  | Oorl: binary_operation                 (**r long bitwise ``or'' *)
  | Oxorl: binary_operation                (**r long bitwise ``xor'' *)
  | Oshll: binary_operation                (**r long left shift *)
  | Oshrl: binary_operation                (**r long right signed shift *)
  | Oshrlu: binary_operation               (**r long right unsigned shift *)
  | Ocmp: comparison -> binary_operation   (**r integer signed comparison *)
  | Ocmpu: comparison -> binary_operation  (**r integer unsigned comparison *)
  | Ocmpf: comparison -> binary_operation  (**r float64 comparison *)
  | Ocmpfs: comparison -> binary_operation (**r float32 comparison *)
  | Ocmpl: comparison -> binary_operation  (**r long signed comparison *)
  | Ocmplu: comparison -> binary_operation. (**r long unsigned comparison *)

(** Expressions include reading local variables, constants,
  arithmetic operations, and memory loads. *)

Inductive expr : Type :=
  | Evar : ident -> expr
  | Econst : constant -> expr
  | Eunop : unary_operation -> expr -> expr
  | Ebinop : binary_operation -> expr -> expr -> expr
  | Eload : memory_chunk -> expr -> expr.

(** Statements include expression evaluation, assignment to local variables,
  memory stores, function calls, an if/then/else conditional, infinite
  loops, blocks and early block exits, and early function returns.
  [Sexit n] terminates prematurely the execution of the [n+1]
  enclosing [Sblock] statements. *)

Definition label := ident.

Inductive stmt : Type :=
  | Sskip: stmt
  | Sassign : ident -> expr -> stmt
  | Sstore : memory_chunk -> expr -> expr -> stmt
  | Scall : option ident -> signature -> expr -> list expr -> stmt
  | Stailcall: signature -> expr -> list expr -> stmt
  | Sbuiltin : option ident -> builtin -> list expr -> stmt
  | Sseq: stmt -> stmt -> stmt
  | Sifthenelse: expr -> stmt -> stmt -> stmt
  | Sloop: stmt -> stmt
  | Sblock: stmt -> stmt
  | Sexit: nat -> stmt
  | Sswitch: bool -> expr -> list (Z * nat) -> nat -> stmt
  | Sreturn: option expr -> stmt
  | Slabel: label -> stmt -> stmt
  | Sgoto: label -> stmt.

(** Functions are composed of a signature, a list of parameter names,
  a list of local variables, and a  statement representing
  the function body.  Each function can allocate a memory block of
  size [fn_stackspace] on entrance.  This block will be deallocated
  automatically before the function returns.  Pointers into this block
  can be taken with the [Oaddrstack] operator. *)

Record function : Type := mkfunction {
  fn_sig: signature;
  fn_params: list ident;
  fn_vars: list ident;
  fn_stackspace: Z;
  fn_body: stmt
}.

Definition fundef := AST.fundef function.
Definition program := AST.program fundef unit.

Definition funsig (fd: fundef) :=
  match fd with
  | Internal f => fn_sig f
  | External ef => ef_sig ef
  end.

(** * Operational semantics (small-step) *)

(** Two kinds of evaluation environments are involved:
- [genv]: global environments, define symbols and functions;
- [env]: local environments, map local variables to values.
*)

Definition genv := Genv.t fundef unit.
Definition env := PTree.t val.

(** The following functions build the initial local environment at
  function entry, binding parameters to the provided arguments and
  initializing local variables to [Vundef]. *)

Fixpoint set_params (vl: list val) (il: list ident) {struct il} : env :=
  match il, vl with
  | i1 :: is, v1 :: vs => PTree.set i1 v1 (set_params vs is)
  | i1 :: is, nil => PTree.set i1 Vundef (set_params nil is)
  | _, _ => PTree.empty val
  end.

Fixpoint set_locals (il: list ident) (e: env) {struct il} : env :=
  match il with
  | nil => e
  | i1 :: is => PTree.set i1 Vundef (set_locals is e)
  end.

Definition set_optvar (optid: option ident) (v: val) (e: env) : env :=
  match optid with
  | None => e
  | Some id => PTree.set id v e
  end.

(** Continuations *)

Inductive cont: Type :=
  | Kstop: cont                         (**r stop program execution *)
  | Kseq: stmt -> cont -> cont          (**r execute stmt, then cont *)
  | Kblock: cont -> cont                (**r exit a block, then do cont *)
  | Kcall: option ident -> function -> val -> env -> cont -> cont.
                                        (**r return to caller *)

(** States *)

Inductive state: Type :=
  | State:                      (**r Execution within a function *)
      forall (f: function)              (**r currently executing function  *)
             (s: stmt)                  (**r statement under consideration *)
             (k: cont)                  (**r its continuation -- what to do next *)
             (sp: val)                  (**r current stack pointer *)
             (e: env),                  (**r current local environment *)
      state
  | Callstate:                  (**r Invocation of a function *)
      forall (f: fundef)                (**r function to invoke *)
             (args: list val)           (**r arguments provided by caller *)
             (k: cont),                 (**r what to do next  *)
      state
  | Returnstate:                (**r Return from a function *)
      forall (v: val)                   (**r Return value *)
             (k: cont),                 (**r what to do next *)
      state.
             
Section RELSEM.

Variable ge: genv.

(** Evaluation of constants and operator applications.
    [None] is returned when the computation is undefined, e.g.
    if arguments are of the wrong types, or in case of an integer division
    by zero. *)

Definition eval_constant (sp: val) (cst: constant) : option val :=
  match cst with
  | Ointconst n => Some (Vint n)
  | Ofloatconst n => Some (Vfloat n)
  | Osingleconst n => Some (Vsingle n)
  | Olongconst n => Some (Vlong n)
  | Oaddrsymbol s ofs =>
      Some(match Genv.find_symbol ge s with
           | None => Vundef
           | Some b => Vptr b ofs end)
  | Oaddrstack ofs => Some (Val.add sp (Vint ofs))
  end.

Definition eval_unop (op: unary_operation) (arg: val) : option val :=
  match op with
  | Ocast8unsigned => Some (Val.zero_ext 8 arg)
  | Ocast8signed => Some (Val.sign_ext 8 arg)
  | Ocast16unsigned => Some (Val.zero_ext 16 arg)
  | Ocast16signed => Some (Val.sign_ext 16 arg)
  | Onegint => Some (Val.negint arg)
  | Onotint => Some (Val.notint arg)
  | Onegf => Some (Val.negf arg)
  | Oabsf => Some (Val.absf arg)
  | Onegfs => Some (Val.negfs arg)
  | Oabsfs => Some (Val.absfs arg)
  | Osingleoffloat => Some (Val.singleoffloat arg)
  | Ofloatofsingle => Some (Val.floatofsingle arg)
  | Ointoffloat => Val.intoffloat arg
  | Ointuoffloat => Val.intuoffloat arg
  | Ofloatofint => Val.floatofint arg
  | Ofloatofintu => Val.floatofintu arg
  | Ointofsingle => Val.intofsingle arg
  | Ointuofsingle => Val.intuofsingle arg
  | Osingleofint => Val.singleofint arg
  | Osingleofintu => Val.singleofintu arg
  | Onegl => Some (Val.negl arg)
  | Onotl => Some (Val.notl arg)
  | Ointoflong => Some (Val.loword arg)
  | Olongofint => Some (Val.longofint arg)
  | Olongofintu => Some (Val.longofintu arg)
  | Olongoffloat => Val.longoffloat arg
  | Olonguoffloat => Val.longuoffloat arg
  | Ofloatoflong => Val.floatoflong arg
  | Ofloatoflongu => Val.floatoflongu arg
  | Olongofsingle => Val.longofsingle arg
  | Olonguofsingle => Val.longuofsingle arg
  | Osingleoflong => Val.singleoflong arg
  | Osingleoflongu => Val.singleoflongu arg
  end.

Definition eval_binop
            (op: binary_operation) (arg1 arg2: val) (m: mem): option val :=
  match op with
  | Oadd => Some (Val.add arg1 arg2)
  | Osub => Some (Val.sub arg1 arg2)
  | Omul => Some (Val.mul arg1 arg2)
  | Odiv => Val.divs arg1 arg2
  | Odivu => Val.divu arg1 arg2
  | Omod => Val.mods arg1 arg2
  | Omodu => Val.modu arg1 arg2
  | Oand => Some (Val.and arg1 arg2)
  | Oor => Some (Val.or arg1 arg2)
  | Oxor => Some (Val.xor arg1 arg2)
  | Oshl => Some (Val.shl arg1 arg2)
  | Oshr => Some (Val.shr arg1 arg2)
  | Oshru => Some (Val.shru arg1 arg2)
  | Oaddf => Some (Val.addf arg1 arg2)
  | Osubf => Some (Val.subf arg1 arg2)
  | Omulf => Some (Val.mulf arg1 arg2)
  | Odivf => Some (Val.divf arg1 arg2)
  | Oaddfs => Some (Val.addfs arg1 arg2)
  | Osubfs => Some (Val.subfs arg1 arg2)
  | Omulfs => Some (Val.mulfs arg1 arg2)
  | Odivfs => Some (Val.divfs arg1 arg2)
  | Oaddl => Some (Val.addl arg1 arg2)
  | Osubl => Some (Val.subl arg1 arg2)
  | Omull => Some (Val.mull arg1 arg2)
  | Odivl => Val.divls arg1 arg2
  | Odivlu => Val.divlu arg1 arg2
  | Omodl => Val.modls arg1 arg2
  | Omodlu => Val.modlu arg1 arg2
  | Oandl => Some (Val.andl arg1 arg2)
  | Oorl => Some (Val.orl arg1 arg2)
  | Oxorl => Some (Val.xorl arg1 arg2)
  | Oshll => Some (Val.shll arg1 arg2)
  | Oshrl => Some (Val.shrl arg1 arg2)
  | Oshrlu => Some (Val.shrlu arg1 arg2)
  | Ocmp c => Some (Val.cmp c arg1 arg2)
  | Ocmpu c => Some (Val.cmpu (Mem.valid_pointer m) c arg1 arg2)
  | Ocmpf c => Some (Val.cmpf c arg1 arg2)
  | Ocmpfs c => Some (Val.cmpfs c arg1 arg2)
  | Ocmpl c => Val.cmpl c arg1 arg2
  | Ocmplu c => Val.cmplu c arg1 arg2
  end.

(** Evaluation of an expression: [eval_expr ge sp e m a v]
  states that expression [a] evaluates to value [v].
  [ge] is the global environment, [e] the local environment,
  and [m] the current memory state.  They are unchanged during evaluation.
  [sp] is the pointer to the memory block allocated for this function
  (stack frame).
*)

Section EVAL_EXPR.

Variable sp: val.
Variable e: env.
Variable m: mem.

Inductive eval_expr: expr -> val -> Prop :=
  | eval_Evar: forall id v,
      PTree.get id e = Some v ->
      eval_expr (Evar id) v
  | eval_Econst: forall cst v,
      eval_constant sp cst = Some v ->
      eval_expr (Econst cst) v
  | eval_Eunop: forall op a1 v1 v,
      eval_expr a1 v1 ->
      eval_unop op v1 = Some v ->
      eval_expr (Eunop op a1) v
  | eval_Ebinop: forall op a1 a2 v1 v2 v,
      eval_expr a1 v1 ->
      eval_expr a2 v2 ->
      eval_binop op v1 v2 m = Some v ->
      eval_expr (Ebinop op a1 a2) v
  | eval_Eload: forall chunk addr vaddr v,
      eval_expr addr vaddr ->
      Mem.loadv chunk m vaddr = Some v ->     
      eval_expr (Eload chunk addr) v.

Inductive eval_exprlist: list expr -> list val -> Prop :=
  | eval_Enil:
      eval_exprlist nil nil
  | eval_Econs: forall a1 al v1 vl,
      eval_expr a1 v1 -> eval_exprlist al vl ->
      eval_exprlist (a1 :: al) (v1 :: vl).

End EVAL_EXPR.

(** Pop continuation until a call or stop *)

Fixpoint call_cont (k: cont) : cont :=
  match k with
  | Kseq s k => call_cont k
  | Kblock k => call_cont k
  | _ => k
  end.

Definition is_call_cont (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kcall _ _ _ _ _ => True
  | _ => False
  end.

(** Find the statement and manufacture the continuation 
  corresponding to a label *)

Fixpoint find_label (lbl: label) (s: stmt) (k: cont) 
                    {struct s}: option (stmt * cont) :=
  match s with
  | Sseq s1 s2 =>
      match find_label lbl s1 (Kseq s2 k) with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sifthenelse a s1 s2 =>
      match find_label lbl s1 k with
      | Some sk => Some sk
      | None => find_label lbl s2 k
      end
  | Sloop s1 =>
      find_label lbl s1 (Kseq (Sloop s1) k)
  | Sblock s1 =>
      find_label lbl s1 (Kblock k)
  | Slabel lbl' s' =>
      if ident_eq lbl lbl' then Some(s', k) else find_label lbl s' k
  | _ => None
  end.

(** One step of execution *)

Inductive step: state * mem -> trace -> state * mem -> Prop :=

  | step_skip_seq: forall f s k sp e m,
      step (State f Sskip (Kseq s k) sp e, m)
        E0 (State f s k sp e, m)
  | step_skip_block: forall f k sp e m,
      step (State f Sskip (Kblock k) sp e, m)
        E0 (State f Sskip k sp e, m)
  | step_skip_call: forall f k sp e m m',
      is_call_cont k ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f Sskip k (Vptr sp Int.zero) e, m)
        E0 (Returnstate Vundef k, m')

  | step_assign: forall f id a k sp e m v,
      eval_expr sp e m a v ->
      step (State f (Sassign id a) k sp e, m)
        E0 (State f Sskip k sp (PTree.set id v e), m)

  | step_store: forall f chunk addr a k sp e m vaddr v m',
      eval_expr sp e m addr vaddr ->
      eval_expr sp e m a v ->
      Mem.storev chunk m vaddr v = Some m' ->
      step (State f (Sstore chunk addr a) k sp e, m)
        E0 (State f Sskip k sp e, m')

  | step_call: forall f optid sig a bl k sp e m vf vargs fd,
      eval_expr sp e m a vf ->
      eval_exprlist sp e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      step (State f (Scall optid sig a bl) k sp e, m)
        E0 (Callstate fd vargs (Kcall optid f sp e k), m)

  | step_tailcall: forall f sig a bl k sp e m vf vargs fd m',
      eval_expr (Vptr sp Int.zero) e m a vf ->
      eval_exprlist (Vptr sp Int.zero) e m bl vargs ->
      Genv.find_funct ge vf = Some fd ->
      funsig fd = sig ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Stailcall sig a bl) k (Vptr sp Int.zero) e, m)
        E0 (Callstate fd vargs (call_cont k), m')

  | step_builtin: forall f optid ef bl k sp e m vargs t vres m',
      eval_exprlist sp e m bl vargs ->
      builtin_call ef ge vargs m t vres m' ->
      step (State f (Sbuiltin optid ef bl) k sp e, m)
         t (State f Sskip k sp (set_optvar optid vres e), m')

  | step_seq: forall f s1 s2 k sp e m,
      step (State f (Sseq s1 s2) k sp e, m)
        E0 (State f s1 (Kseq s2 k) sp e, m)

  | step_ifthenelse: forall f a s1 s2 k sp e m v b,
      eval_expr sp e m a v ->
      Val.bool_of_val v b ->
      step (State f (Sifthenelse a s1 s2) k sp e, m)
        E0 (State f (if b then s1 else s2) k sp e, m)

  | step_loop: forall f s k sp e m,
      step (State f (Sloop s) k sp e, m)
        E0 (State f s (Kseq (Sloop s) k) sp e, m)

  | step_block: forall f s k sp e m,
      step (State f (Sblock s) k sp e, m)
        E0 (State f s (Kblock k) sp e, m)

  | step_exit_seq: forall f n s k sp e m,
      step (State f (Sexit n) (Kseq s k) sp e, m)
        E0 (State f (Sexit n) k sp e, m)
  | step_exit_block_0: forall f k sp e m,
      step (State f (Sexit O) (Kblock k) sp e, m)
        E0 (State f Sskip k sp e, m)
  | step_exit_block_S: forall f n k sp e m,
      step (State f (Sexit (S n)) (Kblock k) sp e, m)
        E0 (State f (Sexit n) k sp e, m)

  | step_switch: forall f islong a cases default k sp e m v n,
      eval_expr sp e m a v ->
      switch_argument islong v n ->
      step (State f (Sswitch islong a cases default) k sp e, m)
        E0 (State f (Sexit (switch_target n default cases)) k sp e, m)

  | step_return_0: forall f k sp e m m',
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn None) k (Vptr sp Int.zero) e, m)
        E0 (Returnstate Vundef (call_cont k), m')
  | step_return_1: forall f a k sp e m v m',
      eval_expr (Vptr sp Int.zero) e m a v ->
      Mem.free m sp 0 f.(fn_stackspace) = Some m' ->
      step (State f (Sreturn (Some a)) k (Vptr sp Int.zero) e, m)
        E0 (Returnstate v (call_cont k), m')

  | step_label: forall f lbl s k sp e m,
      step (State f (Slabel lbl s) k sp e, m)
        E0 (State f s k sp e, m)

  | step_goto: forall f lbl k sp e m s' k',
      find_label lbl f.(fn_body) (call_cont k) = Some(s', k') ->
      step (State f (Sgoto lbl) k sp e, m)
        E0 (State f s' k' sp e, m)

  | step_internal_function: forall f vargs k m m' sp e,
      Mem.alloc m 0 f.(fn_stackspace) = (m', sp) ->
      set_locals f.(fn_vars) (set_params vargs f.(fn_params)) = e ->
      step (Callstate (Internal f) vargs k, m)
        E0 (State f f.(fn_body) k (Vptr sp Int.zero) e, m')
  | step_external_function: forall ef vargs k m t vres m',
      external_call ef ge vargs m t vres m' ->
      step (Callstate (External ef) vargs k, m)
         t (Returnstate vres k, m')        

  | step_return: forall v optid f sp e k m,
      step (Returnstate v (Kcall optid f sp e k), m)
        E0 (State f Sskip k sp (set_optvar optid v e), m).

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  An initial state is a [Callstate]
  corresponding to the invocation of the ``main'' function of the program
  without arguments and with an empty continuation. *)

Inductive initial_state (p: program): state * mem -> Prop :=
  | initial_state_intro: forall b f m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      Genv.find_symbol ge p.(prog_main) = Some b ->
      Genv.find_funct_ptr ge b = Some f ->
      funsig f = signature_main ->
      initial_state p (Callstate f nil Kstop, m0).

(** A final state is a [Returnstate] with an empty continuation. *)

Inductive final_state: state * mem -> int -> Prop :=
  | final_state_intro: forall r m,
      final_state (Returnstate (Vint r) Kstop, m) r.

(** The corresponding small-step semantics. *)

Lemma semantics_forward:
  forall ge s1 m1 t s2 m2,
  step ge (s1,m1) t (s2,m2) -> Mem.forward m1 m2.
Proof.
  intros; inv H; eauto using Mem.forward_refl, Mem.storev_forward,
    Mem.free_forward, Mem.alloc_forward, external_call_forward, builtin_call_forward.
Qed.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p) semantics_forward.

(** This semantics is receptive to changes in events. *)

Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
  intros. constructor; simpl; intros.
(* receptiveness *)
  assert (t1 = E0 -> exists s2, step (Genv.globalenv p) s t2 s2).
    intros. subst. inv H0. exists s1; auto.
  inversion H; subst; auto.
  exploit builtin_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (State f Sskip k sp (set_optvar optid vres2 e), m2). econstructor; eauto. 
  exploit external_call_receptive; eauto. intros [vres2 [m2 EC2]]. 
  exists (Returnstate vres2 k, m2). econstructor; eauto.
(* trace length *)
  red; intros; inv H; simpl; try omega;
    eauto using builtin_call_trace_length, external_call_trace_length.
Qed.
