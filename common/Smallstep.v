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

(** Tools for small-step operational semantics *)

(** This module defines generic operations and theorems over
  the one-step transition relations that are used to specify
  operational semantics in small-step style. *)

Require Import Relations.
Require Import Wellfounded.
Require Import Coqlib.
Require Import Events.
Require Import Globalenvs.
Require Import Integers.
Require Import Memory.

Set Implicit Arguments.

(** * Closures of transitions relations *)

Section CLOSURES.

Variable state: Type.

(** A one-step transition relation has the following signature.
  It is parameterized by a global environment, which does not
  change during the transition.  It relates the initial state
  of the transition with its final state.  The [trace] parameter
  captures the observable events possibly generated during the
  transition. *)

Variable step: state -> trace -> state -> Prop.

(** No transitions: stuck state *)

Definition nostep (s: state) : Prop :=
  forall t s', ~(step s t s').

(** Zero, one or several transitions.  Also known as Kleene closure,
    or reflexive transitive closure. *)

Inductive star : state -> trace -> state -> Prop :=
  | star_refl: forall s,
      star s E0 s
  | star_step: forall s1 t1 s2 t2 s3 t,
      step s1 t1 s2 -> star s2 t2 s3 -> t = t1 ** t2 ->
      star s1 t s3.

Lemma star_one:
  forall s1 t s2, step s1 t s2 -> star s1 t s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl. traceEq. 
Qed.

Lemma star_two:
  forall s1 t1 s2 t2 s3 t,
  step s1 t1 s2 -> step s2 t2 s3 -> t = t1 ** t2 ->
  star s1 t s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto.  
Qed.

Lemma star_three:
  forall s1 t1 s2 t2 s3 t3 s4 t,
  step s1 t1 s2 -> step s2 t2 s3 -> step s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  star s1 t s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto. 
Qed.

Lemma star_four:
  forall s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step s1 t1 s2 -> step s2 t2 s3 ->
  step s3 t3 s4 -> step s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  star s1 t s5.
Proof.
  intros. eapply star_step; eauto. eapply star_three; eauto. 
Qed.

Lemma star_trans:
  forall s1 t1 s2, star s1 t1 s2 ->
  forall t2 s3 t, star s2 t2 s3 -> t = t1 ** t2 -> star s1 t s3.
Proof.
  induction 1; intros.
  rewrite H0. simpl. auto.
  eapply star_step; eauto. traceEq.
Qed.

Lemma star_left:
  forall s1 t1 s2 t2 s3 t,
  step s1 t1 s2 -> star s2 t2 s3 -> t = t1 ** t2 ->
  star s1 t s3.
Proof star_step.

Lemma star_right:
  forall s1 t1 s2 t2 s3 t,
  star s1 t1 s2 -> step s2 t2 s3 -> t = t1 ** t2 ->
  star s1 t s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto. auto.
Qed.

Lemma star_E0_ind:
  forall (P: state -> state -> Prop),
  (forall s, P s s) ->
  (forall s1 s2 s3, step s1 E0 s2 -> P s2 s3 -> P s1 s3) ->
  forall s1 s2, star s1 E0 s2 -> P s1 s2.
Proof.
  intros P BASE REC. 
  assert (forall s1 t s2, star s1 t s2 -> t = E0 -> P s1 s2).
    induction 1; intros; subst.
    auto.
    destruct (Eapp_E0_inv _ _ H2). subst. eauto.
  eauto.
Qed. 

(** One or several transitions.  Also known as the transitive closure. *)

Inductive plus : state -> trace -> state -> Prop :=
  | plus_left: forall s1 t1 s2 t2 s3 t,
      step s1 t1 s2 -> star s2 t2 s3 -> t = t1 ** t2 ->
      plus s1 t s3.

Lemma plus_one:
  forall s1 t s2,
  step s1 t s2 -> plus s1 t s2.
Proof.
  intros. econstructor; eauto. apply star_refl. traceEq.
Qed.

Lemma plus_two:
  forall s1 t1 s2 t2 s3 t,
  step s1 t1 s2 -> step s2 t2 s3 -> t = t1 ** t2 ->
  plus s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply star_one; auto.  
Qed.

Lemma plus_three:
  forall s1 t1 s2 t2 s3 t3 s4 t,
  step s1 t1 s2 -> step s2 t2 s3 -> step s3 t3 s4 -> t = t1 ** t2 ** t3 ->
  plus s1 t s4.
Proof.
  intros. eapply plus_left; eauto. eapply star_two; eauto. 
Qed.

Lemma plus_four:
  forall s1 t1 s2 t2 s3 t3 s4 t4 s5 t,
  step s1 t1 s2 -> step s2 t2 s3 ->
  step s3 t3 s4 -> step s4 t4 s5 -> t = t1 ** t2 ** t3 ** t4 ->
  plus s1 t s5.
Proof.
  intros. eapply plus_left; eauto. eapply star_three; eauto. 
Qed.

Lemma plus_star:
  forall s1 t s2, plus s1 t s2 -> star s1 t s2.
Proof.
  intros. inversion H; subst.
  eapply star_step; eauto. 
Qed.

Lemma plus_right:
  forall s1 t1 s2 t2 s3 t,
  star s1 t1 s2 -> step s2 t2 s3 -> t = t1 ** t2 ->
  plus s1 t s3.
Proof.
  intros. inversion H; subst. simpl. apply plus_one. auto.
  rewrite Eapp_assoc. eapply plus_left; eauto.
  eapply star_right; eauto. 
Qed.

Lemma plus_left':
  forall s1 t1 s2 t2 s3 t,
  step s1 t1 s2 -> plus s2 t2 s3 -> t = t1 ** t2 ->
  plus s1 t s3.
Proof.
  intros. eapply plus_left; eauto. apply plus_star; auto.
Qed.

Lemma plus_right':
  forall s1 t1 s2 t2 s3 t,
  plus s1 t1 s2 -> step s2 t2 s3 -> t = t1 ** t2 ->
  plus s1 t s3.
Proof.
  intros. eapply plus_right; eauto. apply plus_star; auto.
Qed.

Lemma plus_star_trans:
  forall s1 t1 s2 t2 s3 t,
  plus s1 t1 s2 -> star s2 t2 s3 -> t = t1 ** t2 -> plus s1 t s3.
Proof.
  intros. inversion H; subst. 
  econstructor; eauto. eapply star_trans; eauto.
  traceEq.
Qed.

Lemma star_plus_trans:
  forall s1 t1 s2 t2 s3 t,
  star s1 t1 s2 -> plus s2 t2 s3 -> t = t1 ** t2 -> plus s1 t s3.
Proof.
  intros. inversion H; subst.
  simpl; auto.
  rewrite Eapp_assoc. 
  econstructor. eauto. eapply star_trans. eauto. 
  apply plus_star. eauto. eauto. auto.
Qed.

Lemma plus_trans:
  forall s1 t1 s2 t2 s3 t,
  plus s1 t1 s2 -> plus s2 t2 s3 -> t = t1 ** t2 -> plus s1 t s3.
Proof.
  intros. eapply plus_star_trans. eauto. apply plus_star. eauto. auto.
Qed.

Lemma plus_inv:
  forall s1 t s2, 
  plus s1 t s2 ->
  step s1 t s2 \/ exists s', exists t1, exists t2, step s1 t1 s' /\ plus s' t2 s2 /\ t = t1 ** t2.
Proof.
  intros. inversion H; subst. inversion H1; subst.
  left. rewrite E0_right. auto.
  right. exists s3; exists t1; exists (t0 ** t3); split. auto.
  split. econstructor; eauto. auto.
Qed.

Lemma star_inv:
  forall s1 t s2,
  star s1 t s2 ->
  (s2 = s1 /\ t = E0) \/ plus s1 t s2.
Proof.
  intros. inv H. left; auto. right; econstructor; eauto.
Qed.

Lemma plus_ind2:
  forall (P: state -> trace -> state -> Prop),
  (forall s1 t s2, step s1 t s2 -> P s1 t s2) ->
  (forall s1 t1 s2 t2 s3 t, 
   step s1 t1 s2 -> plus s2 t2 s3 -> P s2 t2 s3 -> t = t1 ** t2 ->
   P s1 t s3) ->
  forall s1 t s2, plus s1 t s2 -> P s1 t s2.
Proof.
  intros P BASE IND.
  assert (forall s1 t s2, star s1 t s2 ->
         forall s0 t0, step s0 t0 s1 ->
         P s0 (t0 ** t) s2).
  induction 1; intros.
  rewrite E0_right. apply BASE; auto.
  eapply IND. eauto. econstructor; eauto. subst t. eapply IHstar; eauto. auto.

  intros. inv H0. eauto. 
Qed.

Lemma plus_E0_ind:
  forall (P: state -> state -> Prop),
  (forall s1 s2 s3, step s1 E0 s2 -> star s2 E0 s3 -> P s1 s3) ->
  forall s1 s2, plus s1 E0 s2 -> P s1 s2.
Proof.
  intros. inv H0. exploit Eapp_E0_inv; eauto. intros [A B]; subst. eauto.
Qed.
End CLOSURES.

(** * Transition semantics *)

(** The general form of a transition semantics. *)

Record semantics : Type := Semantics {
  state: Type;
  funtype: Type;
  vartype: Type;
  step : Genv.t funtype vartype -> (state * mem) -> trace -> (state * mem) -> Prop;
  initial_state: (state * mem) -> Prop;
  final_state: (state * mem) -> int -> Prop;
  globalenv: Genv.t funtype vartype;
  step_forward :
    forall ge s1 m1 t s2 m2,
    step ge (s1,m1) t (s2,m2) -> Mem.forward m1 m2
}.

(** Handy notations. *)

Notation " 'Step' L " := (step L (globalenv L)) (at level 1) : smallstep_scope.
Notation " 'Star' L " := (star (step L (globalenv L))) (at level 1) : smallstep_scope.
Notation " 'Plus' L " := (plus (step L (globalenv L))) (at level 1) : smallstep_scope.
Notation " 'Nostep' L " := (nostep (step L (globalenv L))) (at level 1) : smallstep_scope.

Open Scope smallstep_scope.

(** * Forward simulations between two transition semantics. *)

(** The general form of a forward simulation. *)

Record forward_simulation (L1 L2: semantics) : Type :=
  Forward_simulation {
    fsim_index: Type;
    fsim_order: fsim_index -> fsim_index -> Prop;
    fsim_order_wf: well_founded fsim_order;
    fsim_match_states :> fsim_index -> (state L1 * mem) -> (state L2 * mem) -> Prop;
    fsim_match_initial_states:
      forall s1, initial_state L1 s1 ->
      exists i, exists s2, initial_state L2 s2 /\ fsim_match_states i s1 s2;
    fsim_match_final_states:
      forall i s1 s2 r, 
      fsim_match_states i s1 s2 -> final_state L1 s1 r -> final_state L2 s2 r;
    fsim_simulation:
      forall s1 t s1', Step L1 s1 t s1' ->
      forall i s2, fsim_match_states i s1 s2 ->
      exists i', exists s2',
         (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ fsim_order i' i))
      /\ fsim_match_states i' s1' s2';
    fsim_symbols_preserved:
      forall id, Genv.find_symbol (globalenv L2) id = Genv.find_symbol (globalenv L1) id
  }.

Implicit Arguments forward_simulation [].

(** An alternate form of the simulation diagram *)

Lemma fsim_simulation':
  forall L1 L2 (S: forward_simulation L1 L2),
  forall i s1 t s1', Step L1 s1 t s1' ->
  forall s2, S i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ S i' s1' s2')
  \/ (exists i', fsim_order S i' i /\ t = E0 /\ S i' s1' s2).
Proof.
  intros. exploit fsim_simulation; eauto. 
  intros [i' [s2' [A B]]]. intuition. 
  left; exists i'; exists s2'; auto.
  inv H2. 
  right; exists i'; auto.
  left; exists i'; exists s2'; split; auto. econstructor; eauto. 
Qed.

(** ** Forward simulation diagrams. *)

(** Various simulation diagrams that imply forward simulation *)

Section FORWARD_SIMU_DIAGRAMS.

Variable L1: semantics.
Variable L2: semantics.

Hypothesis symbols_preserved:
  forall id, Genv.find_symbol (globalenv L2) id = Genv.find_symbol (globalenv L1) id.

Variable match_states: (state L1 * mem) -> (state L2 * mem) -> Prop.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists s2, initial_state L2 s2 /\ match_states s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r,
  match_states s1 s2 ->
  final_state L1 s1 r ->
  final_state L2 s2 r.

(** Simulation when one transition in the first program
    corresponds to zero, one or several transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_STAR_WF.

(** [order] is a well-founded ordering associated with states
  of the first semantics.  Stuttering steps must correspond
  to states that decrease w.r.t. [order]. *)

Variable order: (state L1 * mem) -> (state L1 * mem) -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2',
  (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order s1' s1))
  /\ match_states s1' s2'.

Lemma forward_simulation_star_wf: forward_simulation L1 L2.
Proof.
  apply Forward_simulation with
    (fsim_order := order)
    (fsim_match_states := fun idx s1 s2 => idx = s1 /\ match_states s1 s2);
  auto.
  intros. exploit match_initial_states; eauto. intros [s2 [A B]].
    exists s1; exists s2; auto.
  intros. destruct H. eapply match_final_states; eauto.
  intros. destruct H0. subst i. exploit simulation; eauto. intros [s2' [A B]].
  exists s1'; exists s2'; intuition.
Qed.

End SIMULATION_STAR_WF.

Section SIMULATION_STAR.

(** We now consider the case where we have a nonnegative integer measure
  associated with states of the first semantics.  It must decrease when we take 
  a stuttering step. *)

Variable measure: (state L1 * mem) -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Plus L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star_wf with (ltof _ measure).
  apply well_founded_ltof.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  exists s2'; auto.
  exists s2; split. right; split. rewrite B. apply star_refl. auto. auto.
Qed.

End SIMULATION_STAR.

(** Simulation when one transition in the first program corresponds
    to one or several transitions in the second program. *)

Section SIMULATION_PLUS.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Plus L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_plus: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with (measure := fun _ => O).
  intros. exploit simulation; eauto.
Qed.

End SIMULATION_PLUS.

(** Lock-step simulation: each transition in the first semantics
    corresponds to exactly one transition in the second semantics. *)

Section SIMULATION_STEP.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  exists s2', Step L2 s2 t s2' /\ match_states s1' s2'.

Lemma forward_simulation_step: forward_simulation L1 L2.
Proof.
  apply forward_simulation_plus. 
  intros. exploit simulation; eauto. intros [s2' [A B]].
  exists s2'; split; auto. apply plus_one; auto.
Qed.

End SIMULATION_STEP.

(** Simulation when one transition in the first program
    corresponds to zero or one transitions in the second program.
    However, there is no stuttering: infinitely many transitions
    in the source program must correspond to infinitely many
    transitions in the second program. *)

Section SIMULATION_OPT.

Variable measure: (state L1 * mem) -> nat.

Hypothesis simulation:
  forall s1 t s1', Step L1 s1 t s1' ->
  forall s2, match_states s1 s2 ->
  (exists s2', Step L2 s2 t s2' /\ match_states s1' s2')
  \/ (measure s1' < measure s1 /\ t = E0 /\ match_states s1' s2)%nat.

Lemma forward_simulation_opt: forward_simulation L1 L2.
Proof.
  apply forward_simulation_star with measure.
  intros. exploit simulation; eauto. intros [[s2' [A B]] | [A [B C]]].
  left; exists s2'; split; auto. apply plus_one; auto.
  right; auto.
Qed.

End SIMULATION_OPT.

End FORWARD_SIMU_DIAGRAMS.

(** ** Forward simulation of transition sequences *)

Section SIMULATION_SEQUENCES.

Variable L1: semantics.
Variable L2: semantics.
Variable S: forward_simulation L1 L2.

Lemma simulation_star:
  forall s1 t s1', Star L1 s1 t s1' ->
  forall i s2, S i s1 s2 ->
  exists i', exists s2', Star L2 s2 t s2' /\ S i' s1' s2'.
Proof.
  induction 1; intros.
  exists i; exists s2; split; auto. apply star_refl.
  exploit fsim_simulation; eauto. intros [i' [s2' [A B]]].
  exploit IHstar; eauto. intros [i'' [s2'' [C D]]].
  exists i''; exists s2''; split; auto. eapply star_trans; eauto.
  intuition. apply plus_star; auto. 
Qed.

Lemma simulation_plus:
  forall s1 t s1', Plus L1 s1 t s1' ->
  forall i s2, S i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 t s2' /\ S i' s1' s2')
  \/ (exists i', clos_trans _ (fsim_order S) i' i /\ t = E0 /\ S i' s1' s2).
Proof.
  induction 1 using plus_ind2; intros.
(* base case *)
  exploit fsim_simulation'; eauto. intros [A | [i' A]].
  left; auto.
  right; exists i'; intuition. 
(* inductive case *)
  exploit fsim_simulation'; eauto. intros [[i' [s2' [A B]]] | [i' [A [B C]]]].
  exploit simulation_star. apply plus_star; eauto. eauto. 
  intros [i'' [s2'' [P Q]]].
  left; exists i''; exists s2''; split; auto. eapply plus_star_trans; eauto.
  exploit IHplus; eauto. intros [[i'' [s2'' [P Q]]] | [i'' [P [Q R]]]].
  subst. simpl. left; exists i''; exists s2''; auto.
  subst. simpl. right; exists i''; intuition.
  eapply t_trans; eauto. eapply t_step; eauto.
Qed.
End SIMULATION_SEQUENCES.

(** ** Composing two forward simulations *)

Section COMPOSE_SIMULATIONS.

Variable L1: semantics.
Variable L2: semantics.
Variable L3: semantics.
Variable S12: forward_simulation L1 L2.
Variable S23: forward_simulation L2 L3.

Let ff_index : Type := (fsim_index S23 * fsim_index S12)%type.

Let ff_order : ff_index -> ff_index -> Prop :=
  lex_ord (clos_trans _ (fsim_order S23)) (fsim_order S12).

Let ff_match_states (i: ff_index) (s1: state L1 * mem) (s3: state L3 * mem) : Prop :=
  exists s2, S12 (snd i) s1 s2 /\ S23 (fst i) s2 s3.

Lemma compose_forward_simulation: forward_simulation L1 L3.
Proof.
  apply Forward_simulation with (fsim_order := ff_order) (fsim_match_states := ff_match_states).
(* well founded *)
  unfold ff_order. apply wf_lex_ord. apply wf_clos_trans. apply fsim_order_wf. apply fsim_order_wf.
(* initial states *)
  intros. exploit (fsim_match_initial_states S12); eauto. intros [i [s2 [A B]]].
  exploit (fsim_match_initial_states S23); eauto. intros [i' [s3 [C D]]].
  exists (i', i); exists s3; split; auto. exists s2; auto. 
(* final states *)
  intros. destruct H as [s3 [A B]].
  eapply (fsim_match_final_states S23); eauto.
  eapply (fsim_match_final_states S12); eauto.
(* simulation *)
  intros. destruct H0 as [s3 [A B]]. destruct i as [i2 i1]; simpl in *.
  exploit (fsim_simulation' S12); eauto. intros [[i1' [s3' [C D]]] | [i1' [C [D E]]]].
  (* L2 makes one or several steps. *)
  exploit simulation_plus; eauto. intros [[i2' [s2' [P Q]]] | [i2' [P [Q R]]]].
  (* L3 makes one or several steps *)
  exists (i2', i1'); exists s2'; split. auto. exists s3'; auto.
  (* L3 makes no step *)
  exists (i2', i1'); exists s2; split. 
  right; split. subst t; apply star_refl. red. left. auto.
  exists s3'; auto. 
  (* L2 makes no step *)
  exists (i2, i1'); exists s2; split.
  right; split. subst t; apply star_refl. red. right. auto. 
  exists s3; auto.
(* symbols *)
  intros. transitivity (Genv.find_symbol (globalenv L2) id); apply fsim_symbols_preserved; auto.
Qed.

End COMPOSE_SIMULATIONS.

(** * Receptiveness and determinacy *)

Definition single_events (L: semantics) : Prop :=
  forall s t s', Step L s t s' -> (length t <= 1)%nat.

Record receptive (L: semantics) : Prop :=
  Receptive {
    sr_receptive: forall s t1 s1 t2,
      Step L s t1 s1 -> match_traces (globalenv L) t1 t2 -> exists s2, Step L s t2 s2;
    sr_traces:
      single_events L
  }.

Record determinate (L: semantics) : Prop :=
  Determinate {
    sd_determ: forall s t1 s1 t2 s2,
      Step L s t1 s1 -> Step L s t2 s2 ->
      match_traces (globalenv L) t1 t2 /\ (t1 = t2 -> s1 = s2);
    sd_traces:
      single_events L;
    sd_initial_determ: forall s1 s2,
      initial_state L s1 -> initial_state L s2 -> s1 = s2;
    sd_final_nostep: forall s r,
      final_state L s r -> Nostep L s;
    sd_final_determ: forall s r1 r2,
      final_state L s r1 -> final_state L s r2 -> r1 = r2
  }.

Section DETERMINACY.

Variable L: semantics.
Hypothesis DET: determinate L.

Lemma sd_determ_1:
  forall s t1 s1 t2 s2,
  Step L s t1 s1 -> Step L s t2 s2 -> match_traces (globalenv L) t1 t2.
Proof.
  intros. eapply sd_determ; eauto.
Qed. 

Lemma sd_determ_2:
  forall s t s1 s2,
  Step L s t s1 -> Step L s t s2 -> s1 = s2.
Proof.
  intros. eapply sd_determ; eauto.
Qed.

Lemma star_determinacy:
  forall s t s', Star L s t s' ->
  forall s'', Star L s t s'' -> Star L s' E0 s'' \/ Star L s'' E0 s'.
Proof.
  induction 1; intros. 
  auto.
  inv H2.
  right. eapply star_step; eauto.
  exploit sd_determ_1. eexact H. eexact H3. intros MT.
  exploit (sd_traces DET). eexact H. intros L1.
  exploit (sd_traces DET). eexact H3. intros L2.
  assert (t1 = t0 /\ t2 = t3).
    destruct t1. inv MT. auto. 
    destruct t1; simpl in L1; try omegaContradiction. 
    destruct t0. inv MT. destruct t0; simpl in L2; try omegaContradiction.
    simpl in H5. split. congruence. congruence.
  destruct H1; subst.
  assert (s2 = s4) by (eapply sd_determ_2; eauto). subst s4. 
  auto.
Qed.

End DETERMINACY.
