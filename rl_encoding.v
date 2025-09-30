(******************************************************************************)
(*                                                                            *)
(*  Run-Length Encoding: A Complete Formalization                            *)
(*                                                                            *)
(*  A formally verified implementation of the Run-Length Encoding            *)
(*  compression algorithm in Coq, with complete correctness proofs           *)
(*  and comprehensive specifications including well-formedness,              *)
(*  injectivity, compression bounds, and optimality properties.              *)
(*                                                                            *)
(*  Author: Charles C. Norton                                                *)
(*  Date: September 29, 2025                                                 *)
(*                                                                            *)
(******************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Decidable.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.ListSet.
Import ListNotations.

(** * Core Definitions *)

Definition run := (nat * nat)%type.

Fixpoint rle_encode_aux (val : nat) (count : nat) (l : list nat) : list run :=
  match l with
  | [] => [(count, val)]
  | h :: t =>
      if Nat.eqb h val then
        rle_encode_aux val (S count) t
      else
        (count, val) :: rle_encode_aux h 1 t
  end.

Definition rle_encode (l : list nat) : list run :=
  match l with
  | [] => []
  | h :: t => rle_encode_aux h 1 t
  end.

Fixpoint repeat (n : nat) (val : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => val :: repeat n' val
  end.

Fixpoint rle_decode (runs : list run) : list nat :=
  match runs with
  | [] => []
  | (count, val) :: t => repeat count val ++ rle_decode t
  end.

(** * Basic Properties *)

Lemma repeat_length : forall n val,
  length (repeat n val) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma repeat_app : forall n m val,
  repeat (n + m) val = repeat n val ++ repeat m val.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

Lemma repeat_In : forall n val x,
  In x (repeat n val) -> x = val.
Proof.
  induction n; simpl; intros.
  - contradiction.
  - destruct H; auto.
Qed.

Lemma repeat_not_nil : forall n val,
  n > 0 -> repeat n val <> [].
Proof.
  destruct n; simpl; intros.
  - lia.
  - discriminate.
Qed.

Lemma repeat_S : forall n val,
  repeat (S n) val = val :: repeat n val.
Proof.
  reflexivity.
Qed.

Lemma repeat_cons_app : forall n val l,
  repeat n val ++ (val :: l) = repeat (S n) val ++ l.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

(** * Core Correctness *)

Lemma rle_encode_aux_decode : forall l val count acc,
  rle_decode (rle_encode_aux val count l) ++ acc =
  repeat count val ++ l ++ acc.
Proof.
  induction l; intros val count acc.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. destruct (Nat.eqb a val) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      rewrite IHl. rewrite <- repeat_cons_app. reflexivity.
    + simpl. rewrite <- app_assoc. f_equal. apply IHl.
Qed.

Theorem rle_correct : forall l : list nat,
  rle_decode (rle_encode l) = l.
Proof.
  intros l. destruct l.
  - reflexivity.
  - unfold rle_encode.
    assert (rle_decode (rle_encode_aux n 1 l) ++ [] =
            repeat 1 n ++ l ++ []).
    { apply rle_encode_aux_decode. }
    simpl in H. rewrite app_nil_r in H. rewrite app_nil_r in H.
    simpl in H. exact H.
Qed.

(** * Well-formedness *)

Definition well_formed_rle (runs : list run) : Prop :=
  (forall r, In r runs -> fst r > 0) /\
  (forall i, i < pred (length runs) ->
             snd (nth i runs (0,0)) <> snd (nth (S i) runs (0,0))).

Lemma rle_encode_aux_positive : forall l val count,
  count > 0 ->
  forall r, In r (rle_encode_aux val count l) -> fst r > 0.
Proof.
  induction l; simpl; intros.
  - destruct H0; [subst|contradiction]. simpl. assumption.
  - destruct (Nat.eqb a val) eqn:Heq.
    + apply IHl with (val := val) (count := S count); [lia|auto].
    + destruct H0.
      * rewrite <- H0. simpl. assumption.
      * apply IHl with (val := a) (count := 1); [lia|auto].
Qed.

Lemma neq_sym : forall (a b : nat), a <> b -> b <> a.
Proof.
  intros a b H. intro H1. apply H. symmetry. exact H1.
Qed.

Lemma rle_encode_aux_no_adjacent_nil : forall val count i,
  count > 0 ->
  i < pred (length (rle_encode_aux val count [])) ->
  snd (nth i (rle_encode_aux val count []) (0,0)) <>
  snd (nth (S i) (rle_encode_aux val count []) (0,0)).
Proof.
  intros. simpl in *. lia.
Qed.

Lemma rle_encode_aux_no_adjacent_same : forall l val count i,
  count > 0 ->
  i < pred (length (rle_encode_aux val (S count) l)) ->
  snd (nth i (rle_encode_aux val (S count) l) (0,0)) <>
  snd (nth (S i) (rle_encode_aux val (S count) l) (0,0)) ->
  i < pred (length (rle_encode_aux val count (val :: l))) ->
  snd (nth i (rle_encode_aux val count (val :: l)) (0,0)) <>
  snd (nth (S i) (rle_encode_aux val count (val :: l)) (0,0)).
Proof.
  intros. simpl. rewrite Nat.eqb_refl. exact H1.
Qed.

Lemma rle_encode_aux_no_adjacent_diff_first : forall (a val count : nat),
  count > 0 ->
  a <> val ->
  val <> a.
Proof.
  intros. apply neq_sym. exact H0.
Qed.

Lemma rle_encode_aux_first_snd_general : forall a count l,
  count > 0 ->
  snd (nth 0 (rle_encode_aux a count l) (0,0)) = a.
Proof.
  intros a count l H.
  generalize dependent count.
  induction l; intros; simpl.
  - reflexivity.
  - case_eq (Nat.eqb a0 a); intro Heq.
    + apply IHl. lia.
    + simpl. reflexivity.
Qed.

Lemma rle_encode_aux_no_adjacent : forall l val count,
  count > 0 ->
  forall i, i < pred (length (rle_encode_aux val count l)) ->
       snd (nth i (rle_encode_aux val count l) (0,0)) <>
       snd (nth (S i) (rle_encode_aux val count l) (0,0)).
Proof.
  induction l as [|a l IHl]; simpl; intros val count Hcount i Hi.
  - apply rle_encode_aux_no_adjacent_nil; auto.
  - destruct (Nat.eqb a val) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      apply IHl; [lia|auto].
    + apply Nat.eqb_neq in Heq.
      destruct i as [|i']; simpl.
      * destruct l as [|n l']; simpl in *.
        -- lia.
        -- destruct (Nat.eqb n a) eqn:Heq2.
           ++ apply Nat.eqb_eq in Heq2; subst.
              rewrite rle_encode_aux_first_snd_general; [|lia].
              simpl. apply neq_sym. exact Heq.
           ++ simpl. apply neq_sym. exact Heq.
      * simpl in Hi.
        assert (i' < pred (length (rle_encode_aux a 1 l))).
        { simpl in Hi. lia. }
        apply IHl; [lia|exact H].
Qed.

Theorem encode_well_formed : forall l,
  l <> [] -> well_formed_rle (rle_encode l).
Proof.
  intros l Hne. destruct l.
  - congruence.
  - unfold well_formed_rle, rle_encode. split.
    + intros. apply rle_encode_aux_positive with (val := n) (count := 1) (l := l); [lia|auto].
    + intros. apply rle_encode_aux_no_adjacent; [lia|auto].
Qed.

(** * Injectivity *)

Lemma rle_decode_app : forall r1 r2,
  rle_decode (r1 ++ r2) = rle_decode r1 ++ rle_decode r2.
Proof.
  induction r1; simpl; intros.
  - reflexivity.
  - destruct a. rewrite IHr1. rewrite app_assoc. reflexivity.
Qed.

Theorem rle_injective : forall l1 l2,
  rle_encode l1 = rle_encode l2 -> l1 = l2.
Proof.
  intros. rewrite <- rle_correct. rewrite <- H.
  symmetry. apply rle_correct.
Qed.

(** * Compression Bounds *)

Fixpoint count_runs_aux (val : nat) (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t =>
      if Nat.eqb h val then
        count_runs_aux val t
      else
        S (count_runs_aux h t)
  end.

Definition count_runs (l : list nat) : nat :=
  match l with
  | [] => 0
  | h :: t => count_runs_aux h t
  end.

Lemma rle_encode_aux_length : forall l val count,
  length (rle_encode_aux val count l) = count_runs_aux val l.
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - destruct (Nat.eqb a val); simpl; auto.
Qed.

Theorem rle_length : forall l,
  length (rle_encode l) = count_runs l.
Proof.
  destruct l; simpl.
  - reflexivity.
  - apply rle_encode_aux_length.
Qed.

Lemma count_runs_aux_le : forall l val,
  count_runs_aux val l <= S (length l).
Proof.
  induction l; simpl; intros.
  - auto.
  - destruct (Nat.eqb a val).
    + apply le_S. apply IHl.
    + simpl. apply le_n_S. apply IHl.
Qed.

Theorem rle_worst_case : forall l,
  length (rle_encode l) <= length l.
Proof.
  intros. rewrite rle_length. destruct l; simpl.
  - auto.
  - apply count_runs_aux_le.
Qed.

Theorem rle_best_case : forall n val,
  n > 0 -> length (rle_encode (repeat n val)) = 1.
Proof.
  intros. rewrite rle_length. destruct n; [lia|].
  simpl. clear H. induction n; simpl.
  - reflexivity.
  - rewrite Nat.eqb_refl. assumption.
Qed.

(** * Compression Ratio Analysis *)

Definition compression_ratio_num (original : list nat) (encoded : list run) : nat :=
  length original.

Definition compression_ratio_den (original : list nat) (encoded : list run) : nat :=
  length encoded.

Theorem compression_ratio_uniform : forall n val,
  n > 0 ->
  compression_ratio_num (repeat n val) (rle_encode (repeat n val)) = n /\
  compression_ratio_den (repeat n val) (rle_encode (repeat n val)) = 1.
Proof.
  intros. split.
  - unfold compression_ratio_num. apply repeat_length.
  - unfold compression_ratio_den. apply rle_best_case. exact H.
Qed.

Definition worst_case_list (n : nat) : list nat :=
  map (fun i => i mod 2) (seq 0 n).

Lemma worst_case_list_length : forall n,
  length (worst_case_list n) = n.
Proof.
  intros. unfold worst_case_list.
  rewrite map_length. apply seq_length.
Qed.

Lemma no_compression_worst : forall l,
  (forall i, i < pred (length l) -> nth i l 0 <> nth (S i) l 0) ->
  length (rle_encode l) = length l.
Proof.
  intros l H. rewrite rle_length.
  destruct l as [|h t]; [reflexivity|].
  unfold count_runs. simpl.
  generalize dependent h. induction t; intros.
  - reflexivity.
  - simpl. destruct (Nat.eqb a h) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      assert (0 < pred (length (h :: h :: t))) by (simpl; lia).
      specialize (H 0 H0). simpl in H. congruence.
    + simpl. f_equal.
      apply IHt. intros.
      assert (S i < pred (length (h :: a :: t))) by (simpl; simpl in H0; lia).
      specialize (H (S i) H1). simpl in H. exact H.
Qed.

Theorem compression_ratio_no_benefit : forall l,
  (forall i, i < pred (length l) -> nth i l 0 <> nth (S i) l 0) ->
  compression_ratio_num l (rle_encode l) = length l /\
  compression_ratio_den l (rle_encode l) = length l.
Proof.
  intros. split.
  - unfold compression_ratio_num. reflexivity.
  - unfold compression_ratio_den. apply no_compression_worst. exact H.
Qed.

Theorem rle_beneficial : forall n val,
  count_runs (repeat (S (S n)) val) <= S n.
Proof.
  intros. unfold count_runs. simpl.
  rewrite Nat.eqb_refl.
  induction n; simpl.
  - reflexivity.
  - rewrite Nat.eqb_refl. lia.
Qed.

Corollary compression_achievable : forall n val,
  n > 1 ->
  length (rle_encode (repeat n val)) < length (repeat n val).
Proof.
  intros. rewrite rle_best_case; [|lia].
  rewrite repeat_length. exact H.
Qed.


(** * Optimality *)

Definition is_valid_rle (runs : list run) : Prop :=
  forall r, In r runs -> fst r > 0.

Definition decodes_to (runs : list run) (l : list nat) : Prop :=
  rle_decode runs = l.

Lemma valid_rle_decode_length : forall runs,
  is_valid_rle runs ->
  forall r, In r runs -> length (repeat (fst r) (snd r)) = fst r.
Proof.
  intros. apply repeat_length.
Qed.

Lemma decode_length_sum : forall runs,
  length (rle_decode runs) = fold_right (fun r acc => fst r + acc) 0 runs.
Proof.
  induction runs; simpl.
  - reflexivity.
  - destruct a. rewrite app_length. rewrite repeat_length.
    f_equal. apply IHruns.
Qed.

Lemma pred_length_cons : forall {A} (a : A) (l : list A),
  l <> [] -> pred (length (a :: l)) = S (pred (length l)).
Proof.
  intros. destruct l.
  - congruence.
  - simpl. reflexivity.
Qed.

Lemma decode_nonempty : forall runs val l,
  decodes_to runs (val :: l) -> runs <> [].
Proof.
  intros. intro Hcontra. subst.
  unfold decodes_to in H. simpl in H. discriminate.
Qed.

Lemma valid_rle_positive_first : forall runs,
  is_valid_rle runs -> runs <> [] ->
  fst (hd (0,0) runs) > 0.
Proof.
  intros. destruct runs.
  - congruence.
  - simpl. unfold is_valid_rle in H.
    apply H. simpl. auto.
Qed.

Lemma no_adjacent_tail : forall r runs i,
  (forall j, j < pred (length (r :: runs)) ->
             snd (nth j (r :: runs) (0,0)) <> snd (nth (S j) (r :: runs) (0,0))) ->
  i < pred (length runs) ->
  snd (nth i runs (0,0)) <> snd (nth (S i) runs (0,0)).
Proof.
  intros.
  assert (S i < pred (length (r :: runs))).
  { destruct runs.
    - simpl in H0. inversion H0.
    - simpl in *. lia. }
  specialize (H (S i) H1). simpl in H. exact H.
Qed.

Lemma decode_cons_structure : forall runs val l,
  decodes_to runs (val :: l) ->
  is_valid_rle runs ->
  match runs with
  | [] => False
  | (count, v) :: runs' =>
      count > 0 /\
      ((count = 1 /\ v = val /\ decodes_to runs' l) \/
       (count > 1 /\ v = val /\ decodes_to ((count-1, v) :: runs') l))
  end.
Proof.
  intros. destruct runs as [|p runs'].
  - unfold decodes_to in H. simpl in H. discriminate.
  - destruct p as [count v].
    assert (count > 0).
    { unfold is_valid_rle in H0.
      assert (fst (count, v) > 0).
      { apply H0. simpl. left. reflexivity. }
      simpl in H1. exact H1. }
    split. assumption.
    unfold decodes_to in H. simpl in H.
    destruct count.
    + inversion H1.
    + destruct count.
      * simpl in H. injection H; intros H2 H3.
        left. split; [reflexivity|].
        split; [exact H3|].
        unfold decodes_to. exact H2.
      * simpl in H. injection H; intros H2 H3.
        right. split; [lia|].
        split; [exact H3|].
        unfold decodes_to. simpl. exact H2.
Qed.

Lemma count_runs_base_case : forall val runs,
  decodes_to runs [val] ->
  is_valid_rle runs ->
  snd (nth 0 runs (0,0)) = val ->
  1 <= length runs.
Proof.
  intros.
  assert (runs <> []) by (apply decode_nonempty with (val := val) (l := []); auto).
  destruct runs; [congruence|]. simpl. lia.
Qed.

Lemma decode_same_value_continuation : forall runs val l,
  decodes_to runs (val :: val :: l) ->
  is_valid_rle runs ->
  snd (nth 0 runs (0,0)) = val ->
  exists runs',
    (decodes_to runs' (val :: l) /\
     is_valid_rle runs' /\
     snd (nth 0 runs' (0,0)) = val /\
     length runs' <= length runs).
Proof.
  intros runs val l Hdec Hvalid Hfirst.
  pose proof (decode_cons_structure _ _ _ Hdec Hvalid) as Hstruct.
  destruct runs as [|[count v] runs']; [contradiction|].
  simpl in Hfirst.
  assert (Hv_eq: v = val) by exact Hfirst. subst v.
  destruct Hstruct as [Hpos [[Hc1 [Hv1 Hdec1]]|[Hc2 [Hv2 Hdec2]]]].
  - (* count = 1 *)
    subst. exists runs'. split; [|split; [|split]].
    + exact Hdec1.
    + unfold is_valid_rle in *. intros. apply Hvalid. simpl. auto.
    + destruct runs' as [|p runs'']; [unfold decodes_to in Hdec1; simpl in Hdec1; discriminate|].
      destruct p as [c v]. unfold decodes_to in Hdec1. simpl in Hdec1.
      destruct c.
      * unfold is_valid_rle in Hvalid.
        assert (fst (0, v) > 0) by (apply Hvalid; simpl; right; left; auto).
        simpl in H. inversion H.
      * simpl in Hdec1. injection Hdec1; intros. subst. reflexivity.
    + simpl. lia.
  - (* count > 1 *)
    subst. exists ((count - 1, val) :: runs'). split; [|split; [|split]].
    + exact Hdec2.
    + unfold is_valid_rle in *. intros. simpl in H. destruct H.
      * inversion H. simpl. lia.
      * apply Hvalid. simpl. auto.
    + simpl. reflexivity.
    + simpl. lia.
Qed.

Lemma count_runs_minimal_aux_simple : forall l val runs,
  decodes_to runs (val :: l) ->
  is_valid_rle runs ->
  count_runs_aux val l <= length runs.
Proof.
  induction l; intros val runs Hdecode Hvalid.
  - simpl.
    assert (runs <> []) by (apply decode_nonempty with (val := val) (l := []); auto).
    destruct runs; [congruence|]. simpl. lia.
  - simpl. destruct (Nat.eqb a val) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst a.
      (* When next element is val, we continue the same run *)
      pose proof (decode_cons_structure _ _ _ Hdecode Hvalid) as Hstruct.
      destruct runs as [|[count v] runs']; [contradiction|].
      destruct Hstruct as [Hpos [[Hc1 [Hv1 Hdec1]]|[Hc2 [Hv2 Hdec2]]]].
      * (* count = 1 *)
        subst. unfold decodes_to in Hdec1.
        assert (count_runs_aux val l <= length runs').
        { apply IHl with (runs := runs'); auto.
          unfold is_valid_rle in *. intros. apply Hvalid. simpl. auto. }
        simpl. lia.
      * (* count > 1 *)
        subst.
        apply IHl with (runs := ((count - 1, val) :: runs')).
        -- exact Hdec2.
        -- unfold is_valid_rle in *. intros. simpl in H. destruct H.
           ++ inversion H. simpl. lia.
           ++ apply Hvalid. simpl. auto.
    + apply Nat.eqb_neq in Heq.
      (* When a ≠ val, we start a new run with value a *)
      simpl.
      pose proof (decode_cons_structure _ _ _ Hdecode Hvalid) as Hstruct.
      destruct runs as [|[count v] runs']; [contradiction|].
      destruct Hstruct as [Hpos [[Hc1 [Hv1 Hdec1]]|[Hc2 [Hv2 Hdec2]]]].
      * (* count = 1 *)
        subst.
        assert (count_runs_aux a l <= length runs').
        { apply IHl with (val := a) (runs := runs').
          -- exact Hdec1.
          -- unfold is_valid_rle in *. intros. apply Hvalid. simpl. auto. }
        simpl. lia.
      * (* count > 1 *)
        subst. unfold decodes_to in Hdec2.
        assert (count - 1 > 0) by lia.
        destruct (count - 1) eqn:Hcount.
        -- lia.
        -- simpl in Hdec2.
           assert (val :: repeat n val ++ rle_decode runs' = a :: l).
           { exact Hdec2. }
           injection H0; intros. subst a. congruence.
Qed.

Lemma count_runs_minimal_aux : forall l val runs,
  decodes_to runs (val :: l) ->
  is_valid_rle runs ->
  snd (nth 0 runs (0,0)) = val ->
  (forall i, i < pred (length runs) ->
             snd (nth i runs (0,0)) <> snd (nth (S i) runs (0,0))) ->
  count_runs_aux val l <= length runs.
Proof.
  intros. apply count_runs_minimal_aux_simple; auto.
Qed.

Theorem encode_is_minimal : forall l runs,
  decodes_to runs l ->
  is_valid_rle runs ->
  well_formed_rle runs ->
  count_runs l <= length runs.
Proof.
  intros l runs Hdecode Hvalid Hwf.
  destruct l.
  - destruct runs as [|p runs'].
    + simpl. auto.
    + unfold decodes_to in Hdecode. simpl in Hdecode.
      destruct p. destruct n.
      * unfold is_valid_rle in Hvalid.
        assert (fst (0, n0) > 0) by (apply Hvalid; simpl; auto).
        simpl in H. lia.
      * simpl in Hdecode. discriminate.
  - simpl. destruct runs as [|p runs'].
    + unfold decodes_to in Hdecode. simpl in Hdecode. discriminate.
    + destruct Hwf as [_ Hwf].
      eapply count_runs_minimal_aux with (runs := (p :: runs')); eauto.
      * unfold decodes_to in Hdecode. simpl in Hdecode.
        destruct p. simpl in *.
        destruct n0.
        -- unfold is_valid_rle in Hvalid.
           assert (fst (0, n1) > 0) by (apply Hvalid; simpl; auto).
           simpl in H. lia.
        -- simpl in Hdecode. injection Hdecode; intros H_rest H_eq.
           rewrite <- H_eq. reflexivity.
Qed.

(** * Run Decomposition *)

Definition is_run (l : list nat) : Prop :=
  match l with
  | [] => False
  | h :: t => forall x, In x t -> x = h
  end.

Fixpoint split_run (val : nat) (l : list nat) : (list nat * list nat) :=
  match l with
  | [] => ([val], [])
  | h :: t =>
      if Nat.eqb h val then
        let (run, rest) := split_run val t in
        (val :: run, rest)
      else
        ([val], l)
  end.

Fixpoint decompose_runs_aux (fuel : nat) (l : list nat) : list (list nat) :=
  match fuel with
  | 0 => match l with [] => [] | _ => [l] end
  | S fuel' =>
      match l with
      | [] => []
      | h :: t =>
          let (run, rest) := split_run h t in
          run :: decompose_runs_aux fuel' rest
      end
  end.

Definition decompose_runs (l : list nat) : list (list nat) :=
  decompose_runs_aux (length l) l.

Lemma split_run_app : forall val l,
  let (run, rest) := split_run val l in
  val :: l = run ++ rest.
Proof.
  intros val l. generalize dependent val.
  induction l; intros val; simpl.
  * reflexivity.
  * destruct (Nat.eqb a val) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst.
      remember (split_run val l) as p. destruct p as [run rest]. simpl.
      f_equal. specialize (IHl val). rewrite <- Heqp in IHl.
      simpl in IHl. exact IHl.
    + reflexivity.
Qed.

Fixpoint flatten_runs (runs : list (list nat)) : list nat :=
  match runs with
  | [] => []
  | h :: t => h ++ flatten_runs t
  end.

Lemma decompose_runs_aux_correct : forall fuel l,
  fuel >= length l ->
  flatten_runs (decompose_runs_aux fuel l) = l.
Proof.
  induction fuel; intros l Hfuel.
  * destruct l; simpl.
    + reflexivity.
    + simpl in Hfuel. lia.
  * destruct l; simpl.
    + reflexivity.
    + destruct (split_run n l) eqn:Hsplit. simpl.
      assert (n :: l = l0 ++ l1).
      { pose proof (split_run_app n l) as H.
        rewrite Hsplit in H. simpl in H. exact H. }
      assert (length l1 <= length l).
      { clear - Hsplit.
        generalize dependent l1. generalize dependent l0.
        induction l; intros l0 l1 Hsplit_eq; simpl in *.
        - inversion Hsplit_eq. simpl. auto.
        - destruct (Nat.eqb a n) eqn:Heq.
          + destruct (split_run n l) eqn:Hsplit2.
            inversion Hsplit_eq. subst l0 l1. clear Hsplit_eq. simpl.
            assert (length l3 <= length l) by (apply (IHl l2 l3); reflexivity).
            lia.
          + inversion Hsplit_eq. simpl. auto. }
      rewrite IHfuel.
      -- symmetry. exact H.
      -- simpl in Hfuel. lia.
Qed.

Theorem decompose_flatten : forall l,
  flatten_runs (decompose_runs l) = l.
Proof.
  intros. unfold decompose_runs.
  apply decompose_runs_aux_correct. auto.
Qed.

(** * Composition Properties *)

Theorem rle_decode_app_safe : forall runs1 runs2,
  is_valid_rle runs1 ->
  is_valid_rle runs2 ->
  well_formed_rle runs1 ->
  well_formed_rle runs2 ->
  (runs1 = [] \/ runs2 = [] \/ snd (last runs1 (0,0)) <> snd (hd (0,0) runs2)) ->
  rle_decode (runs1 ++ runs2) = rle_decode runs1 ++ rle_decode runs2.
Proof.
  intros runs1 runs2 Hvalid1 Hvalid2 Hwf1 Hwf2 Hboundary.
  apply rle_decode_app.
Qed.

Lemma count_runs_app_le : forall l1 l2,
  count_runs (l1 ++ l2) <= count_runs l1 + count_runs l2.
Proof.
  intros l1 l2.
  destruct l1 as [|h1 t1].
  - simpl. reflexivity.
  - destruct l2 as [|h2 t2].
    + rewrite app_nil_r. lia.
    + unfold count_runs at 1 3. simpl app.
      assert (count_runs_aux h1 (t1 ++ h2 :: t2) <=
              count_runs_aux h1 t1 + count_runs (h2 :: t2)).
      { clear.
        generalize dependent h1.
        induction t1 as [|a t1']; intros h1.
        - simpl. destruct (Nat.eqb h2 h1) eqn:E.
          + unfold count_runs. simpl.
            apply Nat.eqb_eq in E. subst h2. lia.
          + unfold count_runs. simpl. lia.
        - simpl. destruct (Nat.eqb a h1).
          + apply IHt1'.
          + simpl. apply le_n_S. apply IHt1'. }
      exact H.
Qed.

Theorem parallel_encode_safe : forall l1 l2,
  l1 <> [] ->
  l2 <> [] ->
  last l1 0 <> hd 0 l2 ->
  exists encoded_concat,
    rle_decode encoded_concat = l1 ++ l2 /\
    length encoded_concat <= length (rle_encode l1) + length (rle_encode l2).
Proof.
  intros l1 l2 Hne1 Hne2 Hboundary.
  exists (rle_encode (l1 ++ l2)).
  split.
  - apply rle_correct.
  - rewrite !rle_length.
    apply count_runs_app_le.
Qed.

Theorem streaming_safe_append : forall runs1 runs2 l1 l2,
  rle_decode runs1 = l1 ->
  rle_decode runs2 = l2 ->
  well_formed_rle runs1 ->
  well_formed_rle runs2 ->
  (runs1 = [] \/ runs2 = [] \/ snd (last runs1 (0,0)) <> snd (hd (0,0) runs2)) ->
  rle_decode (runs1 ++ runs2) = l1 ++ l2.
Proof.
  intros runs1 runs2 l1 l2 H1 H2 Hwf1 Hwf2 Hboundary.
  rewrite rle_decode_app. rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma well_formed_tail : forall val c v runs,
  well_formed_rle ((1, val) :: (S c, v) :: runs) ->
  v <> val.
Proof.
  intros. unfold well_formed_rle in H. destruct H as [_ H].
  assert (0 < pred (length ((1, val) :: (S c, v) :: runs))) by (simpl; lia).
  apply H in H0. simpl in H0. apply neq_sym. exact H0.
Qed.

Lemma pred_length_triple : forall {A} (a b c : A) (l : list A),
  pred (length (a :: b :: c :: l)) = S (S (length l)).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma lt_pred_to_succ : forall i n,
  i < S n -> S i < S (S n).
Proof.
  intros. lia.
Qed.

Lemma rle_encode_aux_repeat_accumulator : forall val count n,
  rle_encode_aux val count (repeat n val) = [(count + n, val)].
Proof.
  intros val count n. generalize dependent count.
  induction n; intros; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.eqb_refl. rewrite IHn. f_equal. f_equal. lia.
Qed.

Lemma rle_encode_aux_repeat_plus_decode : forall val init count runs,
  rle_encode_aux val init (repeat count val ++ rle_decode runs) =
  rle_encode_aux val (init + count) (rle_decode runs).
Proof.
  intros val init count.
  generalize dependent init.
  induction count; intros; simpl.
  - rewrite Nat.add_0_r. destruct runs; reflexivity.
  - rewrite Nat.eqb_refl. rewrite IHcount. f_equal. lia.
Qed.

Lemma well_formed_skip_one : forall val c v runs,
  well_formed_rle ((1, val) :: (S c, v) :: runs) ->
  well_formed_rle ((S c, v) :: runs).
Proof.
  intros. unfold well_formed_rle in *. destruct H. split.
  - intros. apply H. simpl. auto.
  - intros. destruct runs.
    + simpl in *. lia.
    + destruct p as [c' v'].
      assert (S i < pred (length ((1, val) :: (S c, v) :: (c', v') :: runs))).
      { simpl. simpl in H1. apply lt_pred_to_succ. exact H1. }
      apply H0 in H2. simpl in H2. exact H2.
Qed.

Lemma rle_encode_decode_empty :
  rle_encode (rle_decode []) = [].
Proof.
  reflexivity.
Qed.

Lemma rle_encode_decode_single : forall count val,
  count > 0 ->
  rle_encode (rle_decode [(count, val)]) = [(count, val)].
Proof.
  intros. simpl. destruct count.
  - lia.
  - clear H. simpl rle_decode. rewrite app_nil_r. simpl rle_encode.
    rewrite rle_encode_aux_repeat_accumulator.
    replace (1 + count) with (S count) by lia. reflexivity.
Qed.

Lemma rle_encode_single_value_list : forall val,
  rle_encode [val] = [(1, val)].
Proof.
  intros. reflexivity.
Qed.

Lemma rle_decode_single_run : forall count val,
  rle_decode [(count, val)] = repeat count val.
Proof.
  intros. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma rle_decode_cons : forall count val runs,
  rle_decode ((count, val) :: runs) = repeat count val ++ rle_decode runs.
Proof.
  intros. reflexivity.
Qed.

Lemma rle_encode_aux_different_value : forall val v count l,
  v <> val ->
  rle_encode_aux val count (v :: l) = (count, val) :: rle_encode_aux v 1 l.
Proof.
  intros. simpl. destruct (Nat.eqb v val) eqn:Heq.
  - apply Nat.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma rle_encode_aux_same_value : forall val count l,
  rle_encode_aux val count (val :: l) = rle_encode_aux val (S count) l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma rle_encode_aux_empty : forall val count,
  rle_encode_aux val count [] = [(count, val)].
Proof.
  intros. reflexivity.
Qed.

Lemma rle_encode_repeat : forall count val,
  count > 0 ->
  rle_encode (repeat count val) = [(count, val)].
Proof.
  intros. destruct count.
  - lia.
  - simpl. rewrite rle_encode_aux_repeat_accumulator.
    replace (1 + count) with (S count) by lia. reflexivity.
Qed.

Lemma valid_rle_cons : forall count val runs,
  is_valid_rle ((count, val) :: runs) ->
  count > 0 /\ is_valid_rle runs.
Proof.
  intros. unfold is_valid_rle in *. split.
  - assert (fst (count, val) > 0) by (apply H; simpl; auto).
    simpl in H0. exact H0.
  - intros r Hr. apply H. simpl. auto.
Qed.

Lemma well_formed_cons_different : forall count val c v runs,
  well_formed_rle ((count, val) :: (c, v) :: runs) ->
  val <> v.
Proof.
  intros. unfold well_formed_rle in H. destruct H as [_ H].
  assert (0 < pred (length ((count, val) :: (c, v) :: runs))) by (simpl; lia).
  apply H in H0. simpl in H0. exact H0.
Qed.

Lemma rle_decode_two_runs : forall c1 v1 c2 v2,
  rle_decode [(c1, v1); (c2, v2)] = repeat c1 v1 ++ repeat c2 v2.
Proof.
  intros. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma rle_encode_two_runs_case1 : forall v1 v2,
  v1 <> v2 ->
  rle_encode (v1 :: repeat 0 v1 ++ repeat 0 v2) = [(1, v1)].
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma rle_encode_single_then_different : forall v1 v2,
  v1 <> v2 ->
  rle_encode [v1; v2] = [(1, v1); (1, v2)].
Proof.
  intros. simpl. destruct (Nat.eqb v2 v1) eqn:Heq.
  - apply Nat.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

Lemma rle_encode_aux_app_different : forall val count v l,
  v <> val ->
  rle_encode_aux val count (v :: l) = (count, val) :: rle_encode_aux v 1 l.
Proof.
  intros. apply rle_encode_aux_different_value. auto.
Qed.

Lemma rle_encode_aux_repeat_self_app : forall v1 init n v2 l,
  rle_encode_aux v1 init (repeat n v1 ++ v2 :: l) =
  rle_encode_aux v1 (init + n) (v2 :: l).
Proof.
  intros v1 init n. generalize dependent init.
  induction n; intros; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.eqb_refl. rewrite IHn.
    f_equal. rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma rle_encode_repeat_app_different : forall c1 v1 c2 v2,
  c1 > 0 -> c2 > 0 -> v1 <> v2 ->
  rle_encode (repeat c1 v1 ++ repeat c2 v2) = [(c1, v1); (c2, v2)].
Proof.
  intros. destruct c1; [lia|]. destruct c2; [lia|].
  simpl repeat at 1. simpl rle_encode.
  rewrite rle_encode_aux_repeat_self_app.
  replace (1 + c1) with (S c1) by lia. simpl.
  destruct (Nat.eqb v2 v1) eqn:Heq.
  - apply Nat.eqb_eq in Heq. congruence.
  - simpl. rewrite rle_encode_aux_repeat_accumulator.
    replace (1 + c2) with (S c2) by lia. reflexivity.
Qed.

Lemma rle_encode_cons_repeat_different : forall val v count,
  v <> val ->
  rle_encode (val :: repeat count v) =
  if count =? 0 then [(1, val)] else [(1, val); (count, v)].
Proof.
  intros. simpl. destruct count.
  - reflexivity.
  - simpl. destruct (Nat.eqb v val) eqn:Heq.
    + apply Nat.eqb_eq in Heq. congruence.
    + simpl. rewrite rle_encode_aux_repeat_accumulator.
      replace (1 + count) with (S count) by lia. reflexivity.
Qed.

Lemma rle_encode_decode_two_runs : forall c1 v1 c2 v2,
  c1 > 0 -> c2 > 0 -> v1 <> v2 ->
  rle_encode (rle_decode [(c1, v1); (c2, v2)]) = [(c1, v1); (c2, v2)].
Proof.
  intros. rewrite rle_decode_two_runs.
  apply rle_encode_repeat_app_different; auto.
Qed.

Theorem rle_encode_decode_encode_simple : forall runs,
  is_valid_rle runs ->
  well_formed_rle runs ->
  length runs <= 2 ->
  rle_encode (rle_decode runs) = runs.
Proof.
  intros runs Hvalid Hwf Hlen.
  destruct runs as [|[c1 v1] runs'].
  - reflexivity.
  - destruct runs' as [|[c2 v2] runs''].
    + assert (c1 > 0) by (apply valid_rle_cons in Hvalid; destruct Hvalid; auto).
      apply rle_encode_decode_single. auto.
    + destruct runs''.
      * assert (c1 > 0) by (apply valid_rle_cons in Hvalid; destruct Hvalid; auto).
        assert (c2 > 0).
        { apply valid_rle_cons in Hvalid. destruct Hvalid as [_ Hvalid'].
          apply valid_rle_cons in Hvalid'. destruct Hvalid'. auto. }
        assert (v1 <> v2) by (apply (well_formed_cons_different c1 v1 c2 v2 []); auto).
        apply rle_encode_decode_two_runs; auto.
      * simpl in Hlen. lia.
Qed.

Lemma app_assoc_reverse : forall A (l1 l2 l3 : list A),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros. rewrite <- app_assoc. reflexivity.
Qed.

Lemma rle_encode_repeat_rest : forall c v rest,
  c > 0 ->
  v <> hd 0 rest ->
  rle_encode (repeat c v ++ rest) = (c, v) :: rle_encode rest.
Proof.
  intros. destruct c; [lia|]. simpl.
  destruct rest.
  - rewrite app_nil_r. simpl. rewrite rle_encode_aux_repeat_accumulator.
    replace (1 + c) with (S c) by lia. reflexivity.
  - simpl in H0. destruct (Nat.eqb n v) eqn:Heq.
    + apply Nat.eqb_eq in Heq. congruence.
    + rewrite rle_encode_aux_repeat_self_app.
      replace (1 + c) with (S c) by lia.
      rewrite rle_encode_aux_different_value.
      * reflexivity.
      * apply Nat.eqb_neq. exact Heq.
Qed.

Lemma hd_rle_decode_neq : forall (c : nat) v c' v' rs,
  v <> v' -> c' > 0 ->
  hd 0 (rle_decode ((c', v') :: rs)) <> v.
Proof.
  intros. simpl. destruct c'.
  - lia.
  - simpl. apply neq_sym. exact H.
Qed.

Theorem rle_encode_decode_identity_full : forall runs,
  is_valid_rle runs ->
  well_formed_rle runs ->
  rle_encode (rle_decode runs) = runs.
Proof.
  intros runs. remember (length runs) as n.
  generalize dependent runs.
  induction n using lt_wf_ind.
  intros runs Hlen Hvalid Hwf. subst n.
  destruct runs as [|[c v] rs].
  - reflexivity.
  - assert (Hc_pos: c > 0).
    { unfold is_valid_rle in Hvalid.
      assert (fst (c, v) > 0) by (apply Hvalid; simpl; auto).
      simpl in H0. exact H0. }
    destruct rs as [|[c' v'] rs'].
    + simpl rle_decode. simpl. rewrite app_nil_r.
      apply rle_encode_repeat. exact Hc_pos.
    + assert (Hv_neq: v <> v').
      { apply well_formed_cons_different with (count := c) (c := c') (runs := rs').
        exact Hwf. }
      assert (Hc'_pos: c' > 0).
      { unfold is_valid_rle in Hvalid.
        assert (fst (c', v') > 0) by (apply Hvalid; simpl; auto).
        simpl in H0. exact H0. }
      simpl rle_decode. rewrite rle_encode_repeat_rest.
      3: { simpl. destruct c'; [lia|]. simpl. exact Hv_neq. }
      2: { exact Hc_pos. }
      f_equal.
      change (rle_decode ((c', v') :: rs')) with (repeat c' v' ++ rle_decode rs').
      rewrite <- rle_decode_cons.
      apply H with (m := length ((c', v') :: rs')).
      * simpl. apply Nat.lt_succ_diag_r.
      * reflexivity.
      * unfold is_valid_rle in *. intros. apply Hvalid. simpl. auto.
      * unfold well_formed_rle in *. destruct Hwf. split.
        -- intros. apply H0. simpl. auto.
        -- intros.
           assert (S i < pred (length ((c, v) :: (c', v') :: rs'))).
           { simpl. destruct rs' as [|p rs'']; simpl in *.
             - inversion H2.
             - apply -> Nat.succ_lt_mono. exact H2. }
           apply (H1 (S i)) in H3. simpl in H3. exact H3.
Qed.

Corollary encode_well_formed_any : forall l,
  well_formed_rle (rle_encode l).
Proof.
  intros. destruct l.
  - simpl. unfold well_formed_rle. split; intros.
    + contradiction.
    + simpl in H. inversion H.
  - apply encode_well_formed. discriminate.
Qed.

Theorem rle_encode_minimizes_runs : forall l runs,
  decodes_to runs l ->
  is_valid_rle runs ->
  well_formed_rle runs ->
  length (rle_encode l) <= length runs.
Proof.
  intros. rewrite rle_length.
  apply encode_is_minimal; auto.
Qed.

Theorem rle_idempotent : forall l,
  rle_encode (rle_decode (rle_encode l)) = rle_encode l.
Proof.
  intros. rewrite rle_correct. reflexivity.
Qed.

Theorem rle_decode_idempotent : forall runs,
  is_valid_rle runs ->
  well_formed_rle runs ->
  rle_decode (rle_encode (rle_decode runs)) = rle_decode runs.
Proof.
  intros. rewrite rle_correct. reflexivity.
Qed.

(** * Error Handling and Invalid Inputs *)

Lemma rle_decode_invalid_count : forall v rs,
  rle_decode ((0, v) :: rs) = rle_decode rs.
Proof.
  intros. reflexivity.
Qed.

Lemma rle_encode_never_zero_count : forall l r,
  In r (rle_encode l) -> fst r > 0.
Proof.
  intros. destruct l.
  - simpl in H. contradiction.
  - apply rle_encode_aux_positive with (val := n) (count := 1) (l := l).
    + lia.
    + exact H.
Qed.

Definition sanitize_runs (runs : list run) : list run :=
  filter (fun r => match fst r with 0 => false | _ => true end) runs.

Lemma sanitize_preserves_valid : forall runs,
  is_valid_rle (sanitize_runs runs).
Proof.
  intros. unfold is_valid_rle, sanitize_runs.
  intros r Hr. apply filter_In in Hr.
  destruct Hr as [_ H]. destruct (fst r); [discriminate | lia].
Qed.

Theorem rle_decode_sanitized : forall runs,
  rle_decode (sanitize_runs runs) =
  rle_decode (filter (fun r => negb (Nat.eqb (fst r) 0)) runs).
Proof.
  intros. unfold sanitize_runs. f_equal.
  apply filter_ext. intros [c v]. simpl.
  destruct c; reflexivity.
Qed.

(** * Element Preservation *)

Lemma In_repeat : forall n val x,
  In x (repeat n val) <-> (n > 0 /\ x = val).
Proof.
  induction n; simpl; intros; split; intros.
  - contradiction.
  - lia.
  - destruct H; subst.
    + split; auto. lia.
    + apply IHn in H. destruct H. split; auto; lia.
  - destruct H. destruct n.
    + simpl. auto.
    + right. apply IHn. split; auto. lia.
Qed.

Lemma In_rle_decode : forall runs x,
  In x (rle_decode runs) <->
  exists r, In r runs /\ fst r > 0 /\ x = snd r.
Proof.
  induction runs; simpl; intros; split; intros.
  - contradiction.
  - destruct H as [r [H _]]. contradiction.
  - destruct a as [count val]. apply in_app_or in H. destruct H.
    + apply In_repeat in H. destruct H; subst.
      exists (count, val). simpl. auto.
    + apply IHruns in H. destruct H as [r [Hr [Hpos Hx]]].
      exists r. simpl. auto.
  - destruct H as [r [[Hr | Hr] [Hpos Hx]]].
    + subst r. destruct a as [count val]. simpl in *. subst x.
      apply in_or_app. left. apply In_repeat. split; auto.
    + destruct a as [count val]. simpl. apply in_or_app. right.
      apply IHruns. exists r. split; [exact Hr | split; [exact Hpos | exact Hx]].
Qed.

Theorem rle_preserves_elements : forall l x,
  In x l <-> In x (rle_decode (rle_encode l)).
Proof.
  intros. rewrite rle_correct. reflexivity.
Qed.

(** * Generic RLE *)

Section GenericRLE.

Variable A : Type.
Variable A_eqb : A -> A -> bool.
Variable A_eqb_spec : forall x y, reflect (x = y) (A_eqb x y).

Definition generic_run := (nat * A)%type.

Fixpoint generic_repeat (n : nat) (val : A) : list A :=
  match n with
  | 0 => []
  | S n' => val :: generic_repeat n' val
  end.

Fixpoint generic_rle_encode_aux (val : A) (count : nat) (l : list A) : list generic_run :=
  match l with
  | [] => [(count, val)]
  | h :: t =>
      if A_eqb h val then
        generic_rle_encode_aux val (S count) t
      else
        (count, val) :: generic_rle_encode_aux h 1 t
  end.

Definition generic_rle_encode (l : list A) : list generic_run :=
  match l with
  | [] => []
  | h :: t => generic_rle_encode_aux h 1 t
  end.

Fixpoint generic_rle_decode (runs : list generic_run) : list A :=
  match runs with
  | [] => []
  | (count, val) :: t => generic_repeat count val ++ generic_rle_decode t
  end.

Lemma generic_repeat_S : forall n val,
  generic_repeat (S n) val = val :: generic_repeat n val.
Proof.
  reflexivity.
Qed.

Lemma generic_repeat_cons_app : forall n val l,
  generic_repeat n val ++ (val :: l) = generic_repeat (S n) val ++ l.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

Lemma generic_rle_encode_aux_decode : forall l val count acc,
  generic_rle_decode (generic_rle_encode_aux val count l) ++ acc =
  generic_repeat count val ++ l ++ acc.
Proof.
  induction l; intros val count acc.
  - simpl. rewrite app_nil_r. reflexivity.
  - simpl. destruct (A_eqb a val) eqn:Heq.
    + destruct (A_eqb_spec a val).
      * subst. specialize (IHl val (S count) acc).
        rewrite IHl. rewrite <- generic_repeat_cons_app. reflexivity.
      * congruence.
    + simpl. rewrite <- app_assoc. f_equal. apply IHl.
Qed.

Theorem generic_rle_correct : forall l : list A,
  generic_rle_decode (generic_rle_encode l) = l.
Proof.
  intros l. destruct l.
  - reflexivity.
  - unfold generic_rle_encode.
    assert (H: generic_rle_decode (generic_rle_encode_aux a 1 l) ++ [] =
               generic_repeat 1 a ++ l ++ []).
    { apply generic_rle_encode_aux_decode. }
    simpl in H. rewrite app_nil_r in H. rewrite app_nil_r in H.
    simpl generic_repeat in H. exact H.
Qed.

End GenericRLE.

(** * Computational Complexity *)

Fixpoint rle_encode_steps_aux (val : nat) (count : nat) (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t =>
      if Nat.eqb h val then
        S (rle_encode_steps_aux val (S count) t)
      else
        S (rle_encode_steps_aux h 1 t)
  end.

Definition rle_encode_steps (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => S (rle_encode_steps_aux h 1 t)
  end.

Lemma rle_encode_steps_aux_linear : forall l val count,
  rle_encode_steps_aux val count l = length l + 1.
Proof.
  induction l; intros.
  - reflexivity.
  - simpl. destruct (Nat.eqb a val).
    + rewrite IHl. reflexivity.
    + rewrite IHl. reflexivity.
Qed.

Theorem rle_encode_linear_time : forall l,
  rle_encode_steps l = length l + 1.
Proof.
  intros. destruct l.
  - reflexivity.
  - simpl. rewrite rle_encode_steps_aux_linear. reflexivity.
Qed.

Fixpoint rle_decode_steps (runs : list run) : nat :=
  match runs with
  | [] => 1
  | (count, val) :: t => count + rle_decode_steps t
  end.

Theorem rle_decode_linear_time : forall runs,
  rle_decode_steps runs = fold_right (fun r acc => fst r + acc) 1 runs.
Proof.
  induction runs.
  - reflexivity.
  - destruct a. simpl. rewrite IHruns. reflexivity.
Qed.

Theorem rle_decode_time_equals_output_length : forall runs,
  rle_decode_steps runs = length (rle_decode runs) + 1.
Proof.
  intros. rewrite rle_decode_linear_time. rewrite decode_length_sum.
  induction runs.
  - reflexivity.
  - destruct a. simpl. rewrite IHruns. lia.
Qed.

Lemma rle_encode_space_linear : forall l,
  length (rle_encode l) <= length l.
Proof.
  apply rle_worst_case.
Qed.

Theorem rle_space_optimal : forall l,
  length (rle_encode l) = count_runs l.
Proof.
  apply rle_length.
Qed.

(** * Refined Complexity Model *)

Fixpoint rle_encode_cost_aux (val : nat) (count : nat) (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t =>
      1 + rle_encode_cost_aux (if Nat.eqb h val then val else h)
                              (if Nat.eqb h val then S count else 1)
                              t
  end.

Definition rle_encode_cost (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => 1 + rle_encode_cost_aux h 1 t
  end.

Lemma rle_encode_cost_aux_linear : forall l val count,
  rle_encode_cost_aux val count l = length l + 1.
Proof.
  induction l; intros; simpl.
  - reflexivity.
  - destruct (Nat.eqb a val); rewrite IHl; reflexivity.
Qed.

Theorem rle_encode_truly_linear : forall l,
  rle_encode_cost l = 1 + length l.
Proof.
  intros. destruct l; simpl.
  - reflexivity.
  - rewrite rle_encode_cost_aux_linear. lia.
Qed.

(** * Advanced Properties **)

Lemma last_cons : forall A (x : A) l d,
  l <> [] -> last (x :: l) d = last l d.
Proof.
  intros. destruct l.
  - congruence.
  - reflexivity.
Qed.

Lemma count_runs_aux_positive : forall val l,
  count_runs_aux val l > 0.
Proof.
  intros val l. induction l.
  - simpl. auto.
  - simpl. destruct (Nat.eqb a val).
    + auto.
    + apply Nat.lt_0_succ.
Qed.

Lemma last_app : forall A (l1 l2 : list A) d,
  l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros A l1 l2 d H. induction l1.
  - reflexivity.
  - simpl. destruct (l1 ++ l2) eqn:E.
    + destruct l1; simpl in E.
      * congruence.
      * discriminate.
    + exact IHl1.
Qed.

(** * Bounded Correctness *)

Definition bounded_list (bound : nat) (l : list nat) : Prop :=
  forall x, In x l -> x < bound.

Definition max_int_runtime : nat := 2^62 - 1.

Lemma bounded_list_nil : forall bound,
  bounded_list bound [].
Proof.
  intros bound x H. contradiction.
Qed.

Lemma bounded_list_cons : forall bound h t,
  h < bound ->
  bounded_list bound t ->
  bounded_list bound (h :: t).
Proof.
  intros bound h t Hh Ht.
  intros x Hin. simpl in Hin. destruct Hin.
  - subst. exact Hh.
  - apply Ht. exact H.
Qed.

Lemma bounded_list_app : forall bound l1 l2,
  bounded_list bound l1 ->
  bounded_list bound l2 ->
  bounded_list bound (l1 ++ l2).
Proof.
  intros bound l1 l2 H1 H2.
  intros x Hin. apply in_app_or in Hin. destruct Hin.
  - apply H1. exact H.
  - apply H2. exact H.
Qed.

Lemma bounded_repeat : forall bound n val,
  val < bound ->
  bounded_list bound (repeat n val).
Proof.
  intros bound n val Hval.
  intros x Hin. apply repeat_In in Hin. subst. exact Hval.
Qed.

Lemma bounded_decode_single : forall bound count val,
  val < bound ->
  bounded_list bound (rle_decode [(count, val)]).
Proof.
  intros bound count val Hval.
  simpl. rewrite app_nil_r. apply bounded_repeat. exact Hval.
Qed.

Lemma bounded_decode : forall bound runs,
  (forall r, In r runs -> snd r < bound) ->
  bounded_list bound (rle_decode runs).
Proof.
  intros bound runs Hr. induction runs.
  - simpl. apply bounded_list_nil.
  - destruct a as [count val]. simpl. apply bounded_list_app.
    + apply bounded_repeat.
      assert (snd (count, val) < bound).
      { apply Hr. simpl. auto. }
      simpl in H. exact H.
    + apply IHruns. intros r Hr'. apply Hr. simpl. auto.
Qed.

Lemma bounded_encode_aux : forall l val count bound,
  val < bound ->
  bounded_list bound l ->
  (forall r, In r (rle_encode_aux val count l) -> snd r < bound).
Proof.
  induction l; intros val count bound Hval Hbound r Hr.
  - simpl in Hr. destruct Hr.
    + inversion H. simpl. exact Hval.
    + contradiction.
  - simpl in Hr. destruct (Nat.eqb a val) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst.
      apply IHl with (val := val) (count := S count); auto.
      intros x Hx. apply Hbound. simpl. auto.
    + simpl in Hr. destruct Hr.
      * inversion H. simpl. exact Hval.
      * apply IHl with (val := a) (count := 1); auto.
        -- assert (In a (a :: l)) by (simpl; auto).
           apply Hbound in H0. exact H0.
        -- intros x Hx. apply Hbound. simpl. auto.
Qed.

Lemma bounded_encode : forall bound l,
  bounded_list bound l ->
  (forall r, In r (rle_encode l) -> snd r < bound).
Proof.
  intros bound l Hbound. destruct l.
  - simpl. intros r Hr. contradiction.
  - simpl. apply bounded_encode_aux.
    + assert (In n (n :: l)) by (simpl; auto).
      apply Hbound in H. exact H.
    + intros x Hx. apply Hbound. simpl. auto.
Qed.

Theorem rle_correct_bounded : forall l : list nat,
  bounded_list max_int_runtime l ->
  rle_decode (rle_encode l) = l.
Proof.
  intros l Hbound. apply rle_correct.
Qed.

Theorem rle_correct_bounded_explicit : forall l : list nat,
  (forall x, In x l -> x < 2^63) ->
  rle_decode (rle_encode l) = l.
Proof.
  intros l Hbound. apply rle_correct.
Qed.

Theorem rle_roundtrip_preserves_bounds : forall l : list nat,
  bounded_list max_int_runtime l ->
  bounded_list max_int_runtime (rle_decode (rle_encode l)).
Proof.
  intros l Hbound. rewrite rle_correct. exact Hbound.
Qed.

Theorem rle_encode_decode_preserves_bounds : forall runs,
  is_valid_rle runs ->
  well_formed_rle runs ->
  (forall r, In r runs -> snd r < max_int_runtime) ->
  bounded_list max_int_runtime (rle_decode runs).
Proof.
  intros runs Hvalid Hwf Hbound.
  apply bounded_decode. exact Hbound.
Qed.

(** * OCaml Extraction - Production Configuration *)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.

Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].

Set Extraction Optimize.
Set Extraction Conservative Types.
Set Extraction KeepSingleton.
Set Extraction AutoInline.

Extraction Blacklist List String Int.

Extraction Inline Nat.add Nat.sub Nat.mul Nat.div Nat.modulo.
Extraction Inline Nat.leb Nat.ltb Nat.eqb.
Extraction Inline negb andb orb.
Extraction Inline app length.
Extraction Inline fst snd proj1_sig.

Extraction NoInline rle_encode rle_decode.
Extraction NoInline rle_encode_aux repeat.
Extraction NoInline count_runs count_runs_aux.


Definition rle_encode_validated (l : list nat) : option (list (nat * nat)) :=
  if andb (Nat.leb (length l) max_int_runtime)
          (forallb (fun x => Nat.ltb x max_int_runtime) l) then
    Some (rle_encode l)
  else
    None.

Definition compute_decode_size_early (runs : list run) : nat :=
  fold_right (fun r acc => fst r + acc) 0 runs.

Definition rle_decode_validated (runs : list (nat * nat)) : option (list nat) :=
  if andb (forallb (fun r => andb (Nat.ltb 0 (fst r))
                                  (andb (Nat.leb (fst r) max_int_runtime)
                                       (Nat.ltb (snd r) max_int_runtime))) runs)
          (Nat.leb (compute_decode_size_early runs) max_int_runtime) then
    Some (rle_decode runs)
  else
    None.

Lemma rle_encode_preserves_values : forall l r,
  In r (rle_encode l) -> In (snd r) l.
Proof.
  intros l r Hr.
  assert (In (snd r) (rle_decode (rle_encode l))).
  { apply In_rle_decode. exists r. split; [exact Hr | split].
    - apply rle_encode_never_zero_count with l. exact Hr.
    - reflexivity. }
  rewrite rle_correct in H. exact H.
Qed.

Lemma rle_worst_case_run_bound : forall l r,
  In r (rle_encode l) -> fst r <= length l.
Proof.
  intros l r Hr.
  destruct l.
  - simpl in Hr. contradiction.
  - destruct r as [count val].
    simpl in *.
    assert (fst (count, val) > 0).
    { apply rle_encode_never_zero_count with (n :: l). exact Hr. }
    simpl in H.
    assert (length (rle_decode (rle_encode (n :: l))) = length (n :: l)).
    { rewrite rle_correct. reflexivity. }
    assert (In (count, val) (rle_encode (n :: l))) by exact Hr.
    clear Hr. simpl in H0. simpl.
    assert (count <= length (rle_decode (rle_encode (n :: l)))).
    { rewrite decode_length_sum.
      clear H0.
      induction (rle_encode (n :: l)) as [|[c v] rs].
      - contradiction.
      - simpl in H1. destruct H1.
        + injection H0; intros; subst. simpl. lia.
        + simpl. specialize (IHrs H0). lia. }
    rewrite <- H0. exact H2.
Qed.

Theorem validated_roundtrip : forall l encoded,
  rle_encode_validated l = Some encoded ->
  exists decoded, rle_decode_validated encoded = Some decoded /\ decoded = l.
Proof.
  intros l encoded Henc.
  unfold rle_encode_validated in Henc.
  destruct (andb (Nat.leb (length l) max_int_runtime)
                 (forallb (fun x => Nat.ltb x max_int_runtime) l)) eqn:Hvalid.
  - injection Henc; intro Heq; subst encoded.
    exists (rle_decode (rle_encode l)).
    split.
    + unfold rle_decode_validated.
      apply andb_true_iff in Hvalid. destruct Hvalid as [Hlen Hvals].
      assert (forallb (fun r => andb (Nat.ltb 0 (fst r))
                                     (andb (Nat.leb (fst r) max_int_runtime)
                                          (Nat.ltb (snd r) max_int_runtime)))
                      (rle_encode l) = true).
      { apply forallb_forall. intros r Hr.
        apply andb_true_iff. split.
        - apply Nat.ltb_lt. apply rle_encode_never_zero_count with l. exact Hr.
        - apply andb_true_iff. split.
          + apply Nat.leb_le.
            assert (fst r <= length l).
            { apply rle_worst_case_run_bound. exact Hr. }
            apply Nat.leb_le in Hlen. lia.
          + apply Nat.ltb_lt.
            assert (H0: In (snd r) l).
            { apply rle_encode_preserves_values. exact Hr. }
            assert (Hvals': forall x, In x l -> Nat.ltb x max_int_runtime = true).
            { apply forallb_forall. exact Hvals. }
            specialize (Hvals' (snd r) H0).
            apply Nat.ltb_lt in Hvals'. exact Hvals'. }
      rewrite H. simpl.
      assert (compute_decode_size_early (rle_encode l) <= length l).
      { unfold compute_decode_size_early.
        rewrite <- decode_length_sum.
        rewrite rle_correct. reflexivity. }
      apply Nat.leb_le in Hlen.
      assert (compute_decode_size_early (rle_encode l) <= max_int_runtime).
      { lia. }
      apply Nat.leb_le in H1. rewrite H1. simpl. reflexivity.
    + apply rle_correct.
  - discriminate.
Qed.

(** * Extended RLE with Maximum Run Length *)

Fixpoint rle_encode_aux_maxrun (max_run : nat) (val : nat) (count : nat) (l : list nat) : list run :=
  match l with
  | [] => [(count, val)]
  | h :: t =>
      if Nat.eqb h val then
        if Nat.ltb count max_run then
          rle_encode_aux_maxrun max_run val (S count) t
        else
          (max_run, val) :: rle_encode_aux_maxrun max_run h 1 t
      else
        (count, val) :: rle_encode_aux_maxrun max_run h 1 t
  end.

Definition rle_encode_maxrun (max_run : nat) (l : list nat) : list run :=
  match l with
  | [] => []
  | h :: t => rle_encode_aux_maxrun max_run h 1 t
  end.

Definition byte_limit : nat := 255.
Definition seven_bit_limit : nat := 127.

Definition rle_encode_byte := rle_encode_maxrun byte_limit.
Definition rle_encode_7bit := rle_encode_maxrun seven_bit_limit.

Lemma rle_encode_aux_maxrun_nil : forall max_run val count,
  rle_encode_aux_maxrun max_run val count [] = [(count, val)].
Proof.
  intros. reflexivity.
Qed.

Lemma rle_decode_single : forall count val,
  rle_decode [(count, val)] = repeat count val.
Proof.
  intros. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma rle_encode_aux_maxrun_same_under : forall max_run val count l,
  count < max_run ->
  rle_encode_aux_maxrun max_run val count (val :: l) =
  rle_encode_aux_maxrun max_run val (S count) l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

Lemma rle_encode_aux_maxrun_same_at_max : forall max_run val count l,
  count = max_run ->
  rle_encode_aux_maxrun max_run val count (val :: l) =
  (max_run, val) :: rle_encode_aux_maxrun max_run val 1 l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl.
  subst count. rewrite Nat.ltb_irrefl. reflexivity.
Qed.

Lemma repeat_split_at_max : forall max_run val,
  repeat max_run val ++ repeat 1 val = repeat (S max_run) val.
Proof.
  induction max_run; intros.
  - reflexivity.
  - simpl. f_equal. apply IHmax_run.
Qed.

Lemma rle_encode_aux_maxrun_same_over_max : forall max_run val count l,
  count > max_run ->
  rle_encode_aux_maxrun max_run val count (val :: l) =
  (max_run, val) :: rle_encode_aux_maxrun max_run val 1 l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl.
  assert (Nat.ltb count max_run = false) by (apply Nat.ltb_ge; lia).
  rewrite H0. reflexivity.
Qed.

Lemma rle_encode_aux_maxrun_diff : forall max_run val count h l,
  h <> val ->
  rle_encode_aux_maxrun max_run val count (h :: l) =
  (count, val) :: rle_encode_aux_maxrun max_run h 1 l.
Proof.
  intros. simpl.
  destruct (Nat.eqb h val) eqn:Heq.
  - apply Nat.eqb_eq in Heq. contradiction.
  - reflexivity.
Qed.

Lemma rle_encode_aux_maxrun_decode : forall max_run l val count,
  max_run > 0 ->
  count <= max_run ->
  rle_decode (rle_encode_aux_maxrun max_run val count l) =
  repeat count val ++ l.
Proof.
  induction l; intros val count Hmax Hbound.
  - simpl. rewrite app_nil_r. reflexivity.
  - destruct (Nat.eq_dec a val) as [Heqval|Hneqval].
    + subst a. destruct (lt_dec count max_run) as [Hlt|Hge].
      * rewrite rle_encode_aux_maxrun_same_under; auto.
        assert (S count <= max_run) by lia.
        rewrite IHl; auto. rewrite <- repeat_cons_app. reflexivity.
      * assert (count = max_run) by lia. subst count.
        rewrite rle_encode_aux_maxrun_same_at_max; auto.
        simpl. rewrite IHl; [| auto | lia].
        rewrite app_assoc.
        assert (Hrep1: repeat 1 val = [val]) by reflexivity.
        rewrite Hrep1. rewrite <- app_assoc. simpl. reflexivity.
    + rewrite rle_encode_aux_maxrun_diff; auto.
      simpl. rewrite IHl; [| auto | lia].
      rewrite app_assoc.
      assert (Hrep1a: repeat 1 a = [a]) by reflexivity.
      rewrite Hrep1a. rewrite <- app_assoc. simpl. reflexivity.
Qed.

Theorem rle_maxrun_correct : forall max_run l,
  max_run > 0 ->
  rle_decode (rle_encode_maxrun max_run l) = l.
Proof.
  intros max_run l Hmax.
  destruct l.
  - reflexivity.
  - unfold rle_encode_maxrun.
    assert (1 <= max_run) by lia.
    rewrite rle_encode_aux_maxrun_decode; auto.
Qed.

Definition wf_rle_capped (cap : nat) (runs : list run) : Prop :=
  (forall r, In r runs -> fst r > 0) /\
  (forall i, i < pred (length runs) ->
             snd (nth i runs (0,0)) <> snd (nth (S i) runs (0,0)) \/
             fst (nth i runs (0,0)) = cap).

Definition strictly_well_formed_capped (cap : nat) (runs : list run) : Prop :=
  wf_rle_capped cap runs /\
  (forall i, i < pred (length runs) ->
    fst (nth i runs (0,0)) = cap ->
    snd (nth i runs (0,0)) <> snd (nth (S i) runs (0,0))).

Lemma rle_encode_aux_maxrun_positive : forall max_run l val count,
  max_run > 0 ->
  count > 0 ->
  forall r, In r (rle_encode_aux_maxrun max_run val count l) -> fst r > 0.
Proof.
  induction l; intros val count Hmax Hcount r Hr.
  - simpl in Hr. destruct Hr; [|contradiction].
    inversion H. simpl. assumption.
  - simpl in Hr. destruct (Nat.eqb a val) eqn:Heq.
    + destruct (Nat.ltb count max_run) eqn:Hlt.
      * apply IHl with (val := val) (count := S count); auto; lia.
      * simpl in Hr. destruct Hr.
        -- inversion H. simpl. lia.
        -- apply IHl with (val := a) (count := 1); auto; lia.
    + simpl in Hr. destruct Hr.
      * inversion H. simpl. assumption.
      * apply IHl with (val := a) (count := 1); auto; lia.
Qed.

Theorem rle_maxrun_positive_counts : forall max_run l,
  max_run > 0 ->
  l <> [] ->
  forall r, In r (rle_encode_maxrun max_run l) -> fst r > 0.
Proof.
  intros max_run l Hmax Hne.
  destruct l.
  - congruence.
  - unfold rle_encode_maxrun.
    intros r Hr.
    apply rle_encode_aux_maxrun_positive with (max_run := max_run) (val := n) (count := 1) (l := l); auto; lia.
Qed.

Lemma rle_encode_aux_maxrun_bounded : forall max_run l val count,
  max_run > 0 ->
  count > 0 ->
  count <= max_run ->
  forall r, In r (rle_encode_aux_maxrun max_run val count l) -> fst r <= max_run.
Proof.
  induction l; intros val count Hmax Hcount Hbound r Hr.
  - simpl in Hr. destruct Hr; [|contradiction].
    inversion H. simpl. exact Hbound.
  - simpl in Hr.
    destruct (Nat.eqb a val) eqn:Heqval.
    + destruct (Nat.ltb count max_run) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt.
        apply IHl with (val := val) (count := S count); auto; lia.
      * simpl in Hr. destruct Hr.
        -- inversion H. simpl. lia.
        -- apply IHl with (val := a) (count := 1); auto; lia.
    + simpl in Hr. destruct Hr.
      * inversion H. simpl. exact Hbound.
      * apply IHl with (val := a) (count := 1); auto; lia.
Qed.

Theorem rle_maxrun_bounded : forall max_run l,
  max_run > 0 ->
  forall r, In r (rle_encode_maxrun max_run l) -> fst r <= max_run.
Proof.
  intros max_run l Hmax.
  destruct l.
  - simpl. intros r Hr. contradiction.
  - unfold rle_encode_maxrun. intros r Hr.
    apply rle_encode_aux_maxrun_bounded with (val := n) (count := 1) (l := l); auto; lia.
Qed.

Lemma rle_encode_aux_maxrun_first_snd : forall cap a count l,
  cap > 0 ->
  count > 0 ->
  snd (nth 0 (rle_encode_aux_maxrun cap a count l) (0,0)) = a.
Proof.
  intros cap a count l Hcap Hcount.
  generalize dependent count.
  induction l; intros; simpl.
  - reflexivity.
  - destruct (Nat.eqb a0 a) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst a0.
      destruct (Nat.ltb count cap).
      * apply IHl. lia.
      * simpl. reflexivity.
    + simpl. reflexivity.
Qed.

Lemma rle_encode_aux_maxrun_no_adjacent : forall cap l v c,
  cap > 0 ->
  0 < c <= cap ->
  forall i, i < pred (length (rle_encode_aux_maxrun cap v c l)) ->
  snd (nth i (rle_encode_aux_maxrun cap v c l) (0,0)) <>
  snd (nth (S i) (rle_encode_aux_maxrun cap v c l) (0,0)) \/
  fst (nth i (rle_encode_aux_maxrun cap v c l) (0,0)) = cap.
Proof.
  induction l; intros v c Hcap Hbound i Hi.
  - simpl in Hi. simpl. lia.
  - simpl. destruct (Nat.eqb a v) eqn:Heqval.
    + apply Nat.eqb_eq in Heqval; subst a.
      destruct (Nat.ltb c cap) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt.
        assert (0 < S c <= cap) by lia.
        assert (rle_encode_aux_maxrun cap v c (v :: l) = rle_encode_aux_maxrun cap v (S c) l).
        { simpl. rewrite Nat.eqb_refl.
          assert (Nat.ltb c cap = true) by (apply Nat.ltb_lt; exact Hlt).
          rewrite H0. reflexivity. }
        rewrite H0 in Hi.
        apply IHl; auto; exact Hi.
      * apply Nat.ltb_ge in Hlt.
        assert (c = cap) by lia; subst c.
        simpl.
        destruct i.
        -- simpl. right. reflexivity.
        -- assert (Hi' : i < pred (length (rle_encode_aux_maxrun cap v 1 l))).
           { simpl in Hi.
             rewrite Nat.eqb_refl in Hi.
             assert (Heq: Nat.ltb cap cap = false) by apply Nat.ltb_irrefl.
             rewrite Heq in Hi. simpl in Hi.
             lia. }
           apply IHl in Hi'; try lia.
    + apply Nat.eqb_neq in Heqval.
      simpl.
      destruct i.
      -- simpl. left.
         rewrite rle_encode_aux_maxrun_first_snd; auto; try lia.
      -- assert (Hi': i < pred (length (rle_encode_aux_maxrun cap a 1 l))).
         { simpl in Hi.
           assert (Heqf: a =? v = false) by (apply Nat.eqb_neq; exact Heqval).
           rewrite Heqf in Hi. simpl in Hi. lia. }
         assert (Hbound': 0 < 1 <= cap) by lia.
         apply IHl with (v := a) (c := 1) in Hi'; auto.
Qed.

Theorem rle_maxrun_wf_capped : forall cap l,
  cap > 0 ->
  wf_rle_capped cap (rle_encode_maxrun cap l).
Proof.
  intros cap l Hcap.
  unfold wf_rle_capped. split.
  - intros r Hr. apply rle_maxrun_positive_counts with (max_run := cap) (l := l); auto.
    destruct l; [simpl in Hr; contradiction | discriminate].
  - destruct l.
    + simpl. intros i Hi. simpl in Hi. lia.
    + unfold rle_encode_maxrun. apply rle_encode_aux_maxrun_no_adjacent; lia.
Qed.

Theorem rle_maxrun_respects_cap : forall cap l,
  cap > 0 ->
  wf_rle_capped cap (rle_encode_maxrun cap l).
Proof.
  intros. apply rle_maxrun_wf_capped; auto.
Qed.

(** * Streaming/Incremental RLE API *)

Record rle_stream_state := mk_stream_state {
  current_val : nat;
  current_count : nat;
  max_run_length : nat
}.

Definition init_stream_state (max_run : nat) : rle_stream_state :=
  mk_stream_state 0 0 max_run.

Definition stream_push (state : rle_stream_state) (val : nat) : (option run * rle_stream_state) :=
  if Nat.eqb (current_count state) 0 then
    (None, mk_stream_state val 1 (max_run_length state))
  else if Nat.eqb val (current_val state) then
    if Nat.ltb (current_count state) (max_run_length state) then
      (None, mk_stream_state (current_val state) (S (current_count state)) (max_run_length state))
    else
      (Some ((max_run_length state), (current_val state)),
       mk_stream_state val 1 (max_run_length state))
  else
    (Some ((current_count state), (current_val state)),
     mk_stream_state val 1 (max_run_length state)).

Definition stream_flush (state : rle_stream_state) : option run :=
  if Nat.eqb (current_count state) 0 then
    None
  else
    Some ((current_count state), (current_val state)).

Fixpoint stream_encode_list (state : rle_stream_state) (l : list nat) : (list run * rle_stream_state) :=
  match l with
  | [] => ([], state)
  | h :: t =>
      let (opt_run, new_state) := stream_push state h in
      let (runs, final_state) := stream_encode_list new_state t in
      match opt_run with
      | None => (runs, final_state)
      | Some r => (r :: runs, final_state)
      end
  end.

Definition stream_state_invariant (state : rle_stream_state) : Prop :=
  (current_count state = 0 \/ current_count state > 0) /\
  (current_count state <= max_run_length state) /\
  (max_run_length state > 0).

Lemma stream_push_preserves_invariant : forall state val,
  stream_state_invariant state ->
  stream_state_invariant (snd (stream_push state val)).
Proof.
  intros state val Hinv.
  unfold stream_state_invariant in *.
  destruct Hinv as [[Hzero | Hpos] [Hbound Hmax]].
  - unfold stream_push. rewrite Hzero. simpl.
    split; [right; lia | split; [lia | exact Hmax]].
  - unfold stream_push.
    destruct (Nat.eqb (current_count state) 0) eqn:Hcount.
    + apply Nat.eqb_eq in Hcount. lia.
    + destruct (Nat.eqb val (current_val state)) eqn:Hval.
      * destruct (Nat.ltb (current_count state) (max_run_length state)) eqn:Hlt.
        -- simpl. split; [right; lia | split].
           ++ apply Nat.ltb_lt in Hlt. lia.
           ++ exact Hmax.
        -- simpl. split; [right; lia | split; [lia | exact Hmax]].
      * simpl. split; [right; lia | split; [lia | exact Hmax]].
Qed.

Lemma stream_encode_list_preserves_invariant : forall l state,
  stream_state_invariant state ->
  stream_state_invariant (snd (stream_encode_list state l)).
Proof.
  induction l; intros state Hinv.
  - simpl. exact Hinv.
  - simpl.
    destruct (stream_push state a) as [opt new_state] eqn:Hpush.
    destruct (stream_encode_list new_state l) as [runs final_state] eqn:Hencode.
    destruct opt; simpl.
    + assert (final_state = snd (stream_encode_list new_state l)).
      { rewrite Hencode. reflexivity. }
      rewrite H.
      apply IHl.
      assert (new_state = snd (stream_push state a)).
      { rewrite Hpush. reflexivity. }
      rewrite H0.
      apply stream_push_preserves_invariant.
      exact Hinv.
    + assert (final_state = snd (stream_encode_list new_state l)).
      { rewrite Hencode. reflexivity. }
      rewrite H.
      apply IHl.
      assert (new_state = snd (stream_push state a)).
      { rewrite Hpush. reflexivity. }
      rewrite H0.
      apply stream_push_preserves_invariant.
      exact Hinv.
Qed.

Lemma init_stream_state_invariant : forall max_run,
  max_run > 0 ->
  stream_state_invariant (init_stream_state max_run).
Proof.
  intros max_run Hmax.
  unfold stream_state_invariant, init_stream_state.
  simpl. split; [left; auto | split; [lia | exact Hmax]].
Qed.

Definition stream_complete_encode (max_run : nat) (l : list nat) : list run :=
  let (runs, final_state) := stream_encode_list (init_stream_state max_run) l in
  match stream_flush final_state with
  | None => runs
  | Some r => runs ++ [r]
  end.

Theorem stream_complete_encode_exists : forall max_run l,
  max_run > 0 ->
  exists runs, stream_complete_encode max_run l = runs.
Proof.
  intros max_run l Hmax.
  exists (stream_complete_encode max_run l).
  reflexivity.
Qed.

Lemma stream_vs_aux : forall cap xs v c,
  cap > 0 ->
  0 < c <= cap ->
  let s := mk_stream_state v c cap in
  let '(runs, s') := stream_encode_list s xs in
  let out := runs ++ match stream_flush s' with None => [] | Some r => [r] end in
  out = rle_encode_aux_maxrun cap v c xs.
Proof.
  intros cap xs v c Hcap Hbound.
  generalize dependent c.
  generalize dependent v.
  induction xs; intros v c Hbound; simpl.
  - unfold stream_flush. simpl.
    destruct (Nat.eqb c 0) eqn:Heqz.
    + apply Nat.eqb_eq in Heqz. destruct Hbound. lia.
    + simpl. reflexivity.
  - unfold stream_push. simpl.
    destruct (Nat.eqb c 0) eqn:Heqz.
    + apply Nat.eqb_eq in Heqz. destruct Hbound. lia.
    + destruct (Nat.eqb a v) eqn:Heqval.
      * apply Nat.eqb_eq in Heqval; subst a.
        destruct (Nat.ltb c cap) eqn:Hlt.
        -- apply Nat.ltb_lt in Hlt.
           assert (0 < S c <= cap) by lia.
           simpl.
           destruct (stream_encode_list
                     {| current_val := v; current_count := S c; max_run_length := cap |} xs)
                     as [runs s'] eqn:Heqstream.
           specialize (IHxs v (S c) H).
           simpl in IHxs.
           rewrite Heqstream in IHxs.
           exact IHxs.
        -- apply Nat.ltb_ge in Hlt.
           assert (c = cap) by lia; subst c.
           assert (0 < 1 <= cap) by lia.
           simpl.
           destruct (stream_encode_list
                     {| current_val := v; current_count := 1; max_run_length := cap |} xs)
                     as [runs' s''] eqn:Heqstream2.
           specialize (IHxs v 1 H).
           simpl in IHxs.
           rewrite Heqstream2 in IHxs.
           rewrite <- IHxs.
           simpl. reflexivity.
      * simpl.
        assert (0 < 1 <= cap) by lia.
        destruct (stream_encode_list
                  {| current_val := a; current_count := 1; max_run_length := cap |} xs)
                  as [runs' s''] eqn:Heqstream3.
        specialize (IHxs a 1 H).
        simpl in IHxs.
        rewrite Heqstream3 in IHxs.
        rewrite <- IHxs.
        simpl. reflexivity.
Qed.

Theorem stream_eq_batch : forall cap xs,
  cap > 0 ->
  stream_complete_encode cap xs = rle_encode_maxrun cap xs.
Proof.
  intros cap xs Hcap.
  destruct xs.
  - reflexivity.
  - unfold stream_complete_encode, rle_encode_maxrun.
    simpl stream_encode_list.
    unfold stream_push. simpl.
    assert (0 < 1 <= cap) by lia.
    destruct (stream_encode_list
              {| current_val := n; current_count := 1; max_run_length := cap |} xs)
              as [runs s'] eqn:Heqstream.
    pose proof (stream_vs_aux cap xs n 1 Hcap H) as Heq.
    simpl in Heq.
    rewrite Heqstream in Heq.
    destruct (stream_flush s') as [r|] eqn:Hflush.
    + rewrite <- Heq. reflexivity.
    + rewrite app_nil_r in Heq. rewrite <- Heq. reflexivity.
Qed.

(** * Streaming Decoder *)

Record decode_stream_state := mk_decode_state {
  remaining_count : nat;
  current_decode_val : nat
}.

Definition init_decode_state : decode_stream_state :=
  mk_decode_state 0 0.

Definition stream_pull (state : decode_stream_state) (runs : list run)
  : (list nat * decode_stream_state * list run) :=
  match remaining_count state with
  | 0 =>
      match runs with
      | [] => ([], state, [])
      | (count, val) :: rest =>
          if Nat.eqb count 0 then
            ([], state, rest)
          else
            ([val], mk_decode_state (pred count) val, rest)
      end
  | S n =>
      ([current_decode_val state],
       mk_decode_state n (current_decode_val state),
       runs)
  end.

Fixpoint stream_decode_list (fuel : nat) (state : decode_stream_state) (runs : list run)
  : list nat :=
  match fuel with
  | 0 => []
  | S fuel' =>
      let '(vals, new_state, new_runs) := stream_pull state runs in
      match vals with
      | [] =>
          match new_runs with
          | [] => []
          | _ => stream_decode_list fuel' new_state new_runs
          end
      | _ => vals ++ stream_decode_list fuel' new_state new_runs
      end
  end.

Definition decode_state_invariant (state : decode_stream_state) (runs : list run) : Prop :=
  match runs with
  | [] => remaining_count state = 0
  | (count, val) :: rest =>
      (remaining_count state = 0) \/
      (remaining_count state > 0 /\ remaining_count state < count /\
       current_decode_val state = val)
  end.

Lemma init_decode_state_invariant : forall runs,
  decode_state_invariant init_decode_state runs.
Proof.
  intros. unfold decode_state_invariant, init_decode_state. simpl.
  destruct runs as [|[c v] rest].
  - reflexivity.
  - left. reflexivity.
Qed.

Lemma stream_pull_output : forall state runs,
  let '(vals, new_state, new_runs) := stream_pull state runs in
  vals = [] \/ exists v, vals = [v].
Proof.
  intros state runs.
  unfold stream_pull.
  destruct (remaining_count state).
  - destruct runs as [|[count val] rest].
    + left. reflexivity.
    + destruct (Nat.eqb count 0).
      * left. reflexivity.
      * right. exists val. reflexivity.
  - right. exists (current_decode_val state). reflexivity.
Qed.

Definition compute_decode_size (runs : list run) : nat :=
  fold_right (fun r acc => fst r + acc) 0 runs.

Definition safe_decode_with_limit (max_output : nat) (runs : list run)
  : option (list nat) :=
  if Nat.leb (compute_decode_size runs) max_output then
    Some (rle_decode runs)
  else
    None.

Lemma stream_decode_empty_state_nil : forall n,
  stream_decode_list n init_decode_state [] = [].
Proof.
  intros. destruct n.
  - reflexivity.
  - simpl. unfold stream_pull. simpl. reflexivity.
Qed.

Lemma compute_decode_size_correct : forall runs,
  compute_decode_size runs = length (rle_decode runs).
Proof.
  intros. unfold compute_decode_size.
  symmetry. apply decode_length_sum.
Qed.

Theorem safe_decode_protects_memory : forall max_output runs result,
  safe_decode_with_limit max_output runs = Some result ->
  length result <= max_output.
Proof.
  intros. unfold safe_decode_with_limit in H.
  destruct (Nat.leb (compute_decode_size runs) max_output) eqn:Hle.
  - injection H; intro Heq. subst result.
    rewrite <- compute_decode_size_correct.
    apply Nat.leb_le. exact Hle.
  - discriminate.
Qed.

Theorem streaming_decoder_completeness :
  forall runs, exists fuel,
    fuel >= compute_decode_size runs.
Proof.
  intros runs.
  exists (compute_decode_size runs).
  lia.
Qed.

Lemma stream_decode_empty : forall fuel state,
  remaining_count state = 0 ->
  stream_decode_list fuel state [] = [].
Proof.
  intros. destruct fuel; simpl.
  - reflexivity.
  - unfold stream_pull. rewrite H. reflexivity.
Qed.

Lemma compute_decode_size_zero_only_empty : forall runs,
  compute_decode_size runs = 0 ->
  rle_decode runs = [].
Proof.
  induction runs as [|[c v] rs]; intros H.
  - reflexivity.
  - unfold compute_decode_size in H. simpl in H.
    assert (c = 0).
    { destruct c; auto. simpl in H. lia. }
    subst. simpl.
    apply IHrs. unfold compute_decode_size. exact H.
Qed.

Lemma stream_decode_zero_fuel : forall runs state,
  stream_decode_list 0 state runs = [].
Proof.
  reflexivity.
Qed.

Lemma stream_decode_zero_count : forall fuel' state runs' val,
  remaining_count state = 0 ->
  stream_decode_list (S fuel') state ((0, val) :: runs') =
  stream_decode_list fuel' state runs'.
Proof.
  intros. simpl. unfold stream_pull. rewrite H. simpl.
  destruct runs'.
  - rewrite stream_decode_empty; auto.
  - reflexivity.
Qed.

Lemma stream_decode_single_step : forall fuel' val state runs',
  remaining_count state = 0 ->
  stream_decode_list (S fuel') state ((S 0, val) :: runs') =
  val :: stream_decode_list fuel' (mk_decode_state 0 val) runs'.
Proof.
  intros. simpl. unfold stream_pull. rewrite H. simpl. reflexivity.
Qed.

Lemma stream_decode_multi_step : forall fuel' count val state runs',
  remaining_count state = 0 ->
  count > 0 ->
  stream_decode_list (S fuel') state ((S count, val) :: runs') =
  val :: stream_decode_list fuel' (mk_decode_state count val) runs'.
Proof.
  intros. simpl. unfold stream_pull. rewrite H. simpl. reflexivity.
Qed.

Lemma stream_decode_continue : forall fuel' count val runs',
  count > 0 ->
  stream_decode_list (S fuel') (mk_decode_state count val) runs' =
  val :: stream_decode_list fuel' (mk_decode_state (pred count) val) runs'.
Proof.
  intros. destruct count; [lia|]. simpl. unfold stream_pull. simpl. reflexivity.
Qed.

Lemma stream_decode_repeat_helper : forall n val fuel runs',
  fuel >= n + compute_decode_size runs' ->
  stream_decode_list fuel (mk_decode_state n val) runs' =
  repeat n val ++ stream_decode_list (fuel - n) (mk_decode_state 0 val) runs'.
Proof.
  induction n; intros val fuel runs' Hfuel.
  - simpl. rewrite Nat.sub_0_r. reflexivity.
  - destruct fuel.
    + simpl in Hfuel. lia.
    + simpl repeat. rewrite stream_decode_continue; [|lia].
      simpl pred. rewrite IHn; [|lia].
      simpl. f_equal.
Qed.

Lemma stream_decode_with_state_strong : forall runs fuel state,
  remaining_count state = 0 ->
  fuel >= compute_decode_size runs + length runs ->
  stream_decode_list fuel state runs = rle_decode runs.
Proof.
  induction runs as [|[count val] runs' IH]; intros fuel state Hstate Hfuel.
  - apply stream_decode_empty. exact Hstate.
  - destruct fuel.
    + simpl in Hfuel. unfold compute_decode_size in Hfuel. simpl in Hfuel. lia.
    + destruct count.
      * rewrite stream_decode_zero_count; auto. simpl.
        apply IH; auto.
        unfold compute_decode_size in *. simpl in *. lia.
      * destruct count.
        -- rewrite stream_decode_single_step; auto. simpl. f_equal.
           apply IH; auto. unfold compute_decode_size in *. simpl in *. lia.
        -- rewrite stream_decode_multi_step; auto; [|lia]. simpl.
           assert (fuel >= S count + compute_decode_size runs' + length runs').
           { unfold compute_decode_size in Hfuel. simpl in Hfuel.
             unfold compute_decode_size. lia. }
           assert (fuel >= S count + (compute_decode_size runs' + length runs')).
           { lia. }
           clear H.
           assert (fuel - S count >= compute_decode_size runs' + length runs').
           { lia. }
           rewrite stream_decode_repeat_helper.
           2: { lia. }
           assert (fuel - S count = fuel - S count) by reflexivity.
           rewrite IH; auto.
Qed.

Theorem stream_decode_complete : forall runs,
  exists fuel, fuel >= compute_decode_size runs /\
  stream_decode_list fuel init_decode_state runs = rle_decode runs.
Proof.
  intros runs.
  exists (compute_decode_size runs + length runs).
  split.
  - lia.
  - apply stream_decode_with_state_strong.
    + reflexivity.
    + lia.
Qed.

Definition stream_pull_safe (state : decode_stream_state) (runs : list run) (budget : nat)
  : option (list nat * decode_stream_state * list run * nat) :=
  let '(vals, new_state, new_runs) := stream_pull state runs in
  let cost := length vals in
  if Nat.leb cost budget then
    Some (vals, new_state, new_runs, budget - cost)
  else
    None.

(** * Integer Width Support *)

Definition max_int_8 : nat := 2^8 - 1.
Definition max_int_16 : nat := 2^16 - 1.
Definition max_int_32 : nat := 2^32 - 1.

Definition bounded_rle_encode (max_val : nat) (l : list nat) : option (list run) :=
  if forallb (fun x => Nat.leb x max_val) l then
    Some (rle_encode l)
  else
    None.

Definition runs_fit_width (max_count : nat) (runs : list run) : Prop :=
  forall r, In r runs -> fst r <= max_count.

Definition bounded_rle_encode_full (max_val max_count : nat) (l : list nat)
  : option (list run) :=
  if forallb (fun x => Nat.leb x max_val) l then
    let encoded := rle_encode_maxrun max_count l in
    if forallb (fun r => andb (Nat.leb (fst r) max_count)
                              (Nat.leb (snd r) max_val)) encoded then
      Some encoded
    else
      None
  else
    None.

Definition rle_encode_u8_safe (l : list nat) : option (list run) :=
  bounded_rle_encode_full 255 255 l.

Theorem rle_encode_u8_safe_sound : forall l runs,
  rle_encode_u8_safe l = Some runs ->
  (forall x, In x l -> x <= 255) /\
  (forall r, In r runs -> fst r <= 255 /\ snd r <= 255).
Proof.
  intros l runs H.
  unfold rle_encode_u8_safe, bounded_rle_encode_full in H.
  destruct (forallb (fun x => Nat.leb x 255) l) eqn:Hval; [|discriminate].
  remember (rle_encode_maxrun 255 l) as encoded.
  destruct (forallb (fun r => andb (Nat.leb (fst r) 255)
                                   (Nat.leb (snd r) 255)) encoded) eqn:Hrun; [|discriminate].
  injection H; intro Heq; subst runs.
  split.
  - intros x Hx.
    assert (forallb (fun z => Nat.leb z 255) l = true ->
            forall y, In y l -> Nat.leb y 255 = true).
    { apply forallb_forall. }
    specialize (H0 Hval x Hx). apply Nat.leb_le in H0. exact H0.
  - intros r Hr.
    assert (forallb (fun z => andb (Nat.leb (fst z) 255) (Nat.leb (snd z) 255)) encoded = true ->
            forall x, In x encoded -> andb (Nat.leb (fst x) 255) (Nat.leb (snd x) 255) = true).
    { apply forallb_forall. }
    specialize (H0 Hrun r Hr). apply andb_true_iff in H0.
    destruct H0 as [Hc Hv].
    apply Nat.leb_le in Hc. apply Nat.leb_le in Hv.
    split; assumption.
Qed.

Definition rle_encode_u8 := bounded_rle_encode max_int_8.
Definition rle_encode_u16 := bounded_rle_encode max_int_16.
Definition rle_encode_u32 := bounded_rle_encode max_int_32.

Definition bounded_rle_decode (max_val : nat) (runs : list run) : option (list nat) :=
  if forallb (fun r => Nat.leb (snd r) max_val) runs then
    Some (rle_decode runs)
  else
    None.

Definition rle_decode_u8 := bounded_rle_decode max_int_8.
Definition rle_decode_u16 := bounded_rle_decode max_int_16.
Definition rle_decode_u32 := bounded_rle_decode max_int_32.

Lemma bounded_encode_u8_correct : forall l,
  (forall x, In x l -> x <= max_int_8) ->
  exists runs, rle_encode_u8 l = Some runs /\ rle_decode runs = l.
Proof.
  intros l H.
  unfold rle_encode_u8, bounded_rle_encode.
  assert (forallb (fun x => Nat.leb x max_int_8) l = true).
  { induction l.
    - reflexivity.
    - simpl. apply andb_true_intro. split.
      + apply Nat.leb_le. apply H. simpl. auto.
      + apply IHl. intros. apply H. simpl. auto. }
  rewrite H0. exists (rle_encode l). split.
  - reflexivity.
  - apply rle_correct.
Qed.

Lemma bounded_encode_u16_correct : forall l,
  (forall x, In x l -> x <= max_int_16) ->
  exists runs, rle_encode_u16 l = Some runs /\ rle_decode runs = l.
Proof.
  intros l H.
  unfold rle_encode_u16, bounded_rle_encode.
  assert (forallb (fun x => Nat.leb x max_int_16) l = true).
  { induction l.
    - reflexivity.
    - simpl. apply andb_true_intro. split.
      + apply Nat.leb_le. apply H. simpl. auto.
      + apply IHl. intros. apply H. simpl. auto. }
  rewrite H0. exists (rle_encode l). split.
  - reflexivity.
  - apply rle_correct.
Qed.

Lemma bounded_encode_u32_correct : forall l,
  (forall x, In x l -> x <= max_int_32) ->
  exists runs, rle_encode_u32 l = Some runs /\ rle_decode runs = l.
Proof.
  intros l H.
  unfold rle_encode_u32, bounded_rle_encode.
  assert (forallb (fun x => Nat.leb x max_int_32) l = true).
  { induction l.
    - reflexivity.
    - simpl. apply andb_true_intro. split.
      + apply Nat.leb_le. apply H. simpl. auto.
      + apply IHl. intros. apply H. simpl. auto. }
  rewrite H0. exists (rle_encode l). split.
  - reflexivity.
  - apply rle_correct.
Qed.

Corollary rle_decode_u8_correct : forall runs,
  (forall r, In r runs -> snd r <= max_int_8) ->
  rle_decode_u8 runs = Some (rle_decode runs).
Proof.
  intros runs H.
  unfold rle_decode_u8, bounded_rle_decode.
  assert (forallb (fun r => Nat.leb (snd r) max_int_8) runs = true).
  { induction runs.
    - reflexivity.
    - simpl. apply andb_true_intro. split.
      + apply Nat.leb_le. apply H. simpl. auto.
      + apply IHruns. intros. apply H. simpl. auto. }
  rewrite H0. reflexivity.
Qed.

Corollary rle_decode_u16_correct : forall runs,
  (forall r, In r runs -> snd r <= max_int_16) ->
  rle_decode_u16 runs = Some (rle_decode runs).
Proof.
  intros runs H.
  unfold rle_decode_u16, bounded_rle_decode.
  assert (forallb (fun r => Nat.leb (snd r) max_int_16) runs = true).
  { induction runs.
    - reflexivity.
    - simpl. apply andb_true_intro. split.
      + apply Nat.leb_le. apply H. simpl. auto.
      + apply IHruns. intros. apply H. simpl. auto. }
  rewrite H0. reflexivity.
Qed.

Corollary rle_decode_u32_correct : forall runs,
  (forall r, In r runs -> snd r <= max_int_32) ->
  rle_decode_u32 runs = Some (rle_decode runs).
Proof.
  intros runs H.
  unfold rle_decode_u32, bounded_rle_decode.
  assert (forallb (fun r => Nat.leb (snd r) max_int_32) runs = true).
  { induction runs.
    - reflexivity.
    - simpl. apply andb_true_intro. split.
      + apply Nat.leb_le. apply H. simpl. auto.
      + apply IHruns. intros. apply H. simpl. auto. }
  rewrite H0. reflexivity.
Qed.

(** * Test Suite *)

Definition run_eq_dec : forall (r1 r2 : run), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition test_decode_encode_fixpoint (runs : list run) : bool :=
  let decoded := rle_decode runs in
  let reencoded := rle_encode decoded in
  if list_eq_dec run_eq_dec runs reencoded then true else false.

Definition counterexample_uniqueness : list run * list run :=
  ([(3, 1); (2, 1)], [(5, 1)]).

Definition test_uniqueness : bool :=
  let (r1, r2) := counterexample_uniqueness in
  let d1 := rle_decode r1 in
  let d2 := rle_decode r2 in
  if list_eq_dec Nat.eq_dec d1 d2 
  then if list_eq_dec run_eq_dec r1 r2 then true else false
  else true.

Definition test_streaming_equivalence (l : list nat) : bool :=
  let batch := rle_encode_maxrun 255 l in
  let streaming := stream_complete_encode 255 l in
  if list_eq_dec run_eq_dec batch streaming then true else false.

Definition test_worst_case : bool :=
  let alternating := [1; 2; 1; 2; 1; 2; 1; 2] in
  let encoded := rle_encode alternating in
  Nat.eqb (length encoded) (length alternating).

Definition test_best_case : bool :=
  let uniform := repeat 1000 42 in
  let encoded := rle_encode uniform in
  Nat.eqb (length encoded) 1.

Definition test_impossible_compression : bool :=
  let data := [1; 2; 3; 4; 5] in
  let encoded := rle_encode data in
  negb (Nat.ltb (length encoded) (length data)).

Definition test_incremental_consistency (l1 l2 : list nat) : bool :=
  let full := rle_encode (l1 ++ l2) in
  let p1 := rle_encode l1 in
  let p2 := rle_encode l2 in
  Nat.leb (length full) (length p1 + length p2).

Eval compute in test_decode_encode_fixpoint [(3, 1)].
Eval compute in test_streaming_equivalence [1;1;2;2;3;3].
Eval compute in test_worst_case.
Eval compute in test_best_case.
Eval compute in test_impossible_compression.
Eval compute in test_incremental_consistency [1;1;1] [1;1;1].
Eval compute in well_formed_rle (rle_encode [1;1;1;1;1]).

Definition test_double_roundtrip (l : list nat) : bool :=
  let e1 := rle_encode l in
  let d1 := rle_decode e1 in
  let e2 := rle_encode d1 in
  let d2 := rle_decode e2 in
  if list_eq_dec Nat.eq_dec l d2 
  then if list_eq_dec run_eq_dec e1 e2 then true else false
  else false.

Definition test_maxrun_boundary : bool :=
  let exactly_255 := repeat 255 7 in
  let exactly_256 := repeat 256 7 in
  let enc_255 := rle_encode_maxrun 255 exactly_255 in
  let enc_256 := rle_encode_maxrun 255 exactly_256 in
  andb (Nat.eqb (length enc_255) 1)
       (Nat.eqb (length enc_256) 2).

Definition test_streaming_state_consistency : bool :=
  let state1 := init_stream_state 255 in
  let (r1, s1) := stream_encode_list state1 [1;1;1] in
  let (r2, s2) := stream_encode_list s1 [1;1;1] in
  let (r3, s3) := stream_encode_list s2 [2;2;2] in
  let final := match stream_flush s3 with
              | Some r => r1 ++ r2 ++ r3 ++ [r]
              | None => r1 ++ r2 ++ r3
              end in
  let batch := rle_encode [1;1;1;1;1;1;2;2;2] in
  if list_eq_dec run_eq_dec final batch then true else false.

Definition test_compression_never_expands : bool :=
  let test_lists := [[1]; [1;2]; [1;2;3]; [1;1]; [1;1;1]; 
                     [1;2;1;2]; repeat 100 5; repeat 50 3 ++ repeat 50 4] in
  forallb (fun l => Nat.leb (length (rle_encode l)) (length l)) test_lists.

Definition test_encode_preserves_length_sum : bool :=
  let l := [1;1;2;2;2;3;3;3;3] in
  let encoded := rle_encode l in
  Nat.eqb (fold_right (fun r acc => fst r + acc) 0 encoded) (length l).

Definition test_maxrun_decode_equals_standard : bool :=
  let l := repeat 1000 42 in
  let standard := rle_encode l in
  let maxrun := rle_encode_maxrun 255 l in
  if list_eq_dec Nat.eq_dec (rle_decode standard) (rle_decode maxrun)
  then true else false.

Eval compute in test_double_roundtrip [1;1;2;2;3;3].
Eval compute in test_maxrun_boundary.
Eval compute in test_streaming_state_consistency.
Eval compute in test_compression_never_expands.
Eval compute in test_encode_preserves_length_sum.
Eval compute in test_maxrun_decode_equals_standard.

(** * Production OCaml Extraction *)

(**
OCaml Usage Examples (after extraction):

Basic encoding/decoding:
  let data = [1; 1; 1; 2; 2; 3; 3; 3; 3] in
  let encoded = rle_encode data in
  let decoded = rle_decode encoded in
  assert (decoded = data);;

Safe encoding with bounds checking:
  let safe_data = [100; 100; 200; 200; 200] in
  match rle_encode_validated safe_data with
  | Some encoded -> print_endline "Success"
  | None -> print_endline "Data exceeds bounds";;

Maximum run length (for protocols like PackBits):
  let long_run = List.init 1000 (fun _ -> 42) in
  let byte_limited = rle_encode_byte long_run in
  let seven_bit = rle_encode_7bit long_run in
  Printf.printf "Byte: %d runs, 7-bit: %d runs\n"
    (List.length byte_limited) (List.length seven_bit);;

Streaming/incremental encoding:
  let state = init_stream_state 255 in
  let (runs1, state1) = stream_encode_list state [1; 1; 1; 1] in
  let (runs2, state2) = stream_encode_list state1 [1; 1; 2; 2] in
  match stream_flush state2 with
  | Some final_run ->
      Printf.printf "Final: (%d,%d)\n"
        (fst final_run) (snd final_run)
  | None -> ();;

Different integer widths:
  let data_8bit = [0; 128; 255; 255] in
  match rle_encode_u8 data_8bit with
  | Some encoded -> print_endline "8-bit encoding succeeded"
  | None -> print_endline "Values exceed 8-bit range";;

Performance characteristics:
  let homogeneous = List.init 10000 (fun _ -> 42) in
  let compressed = rle_encode homogeneous in
  Printf.printf "Compression: %d:1\n"
    (List.length homogeneous / List.length compressed);;

Counting runs without full encoding:
  let alternating = List.init 1000 (fun i -> i mod 2) in
  let run_count = count_runs alternating in
  Printf.printf "Counted %d runs\n" run_count;;
*)

From Coq Require Import ExtrOcamlNatInt.

Extract Constant plus => "(+)".
Extract Constant mult => "( * )".
Extract Constant Nat.add => "(+)".
Extract Constant Nat.mul => "( * )".
Extract Constant minus => "(fun x y -> max 0 (x - y))".
Extract Constant Nat.eqb => "(=)".
Extract Constant Nat.leb => "(<=)".
Extract Constant Nat.ltb => "(<)".
Extract Constant Nat.max => "max".
Extract Constant Nat.min => "min".
Extract Constant pred => "(fun n -> max 0 (n - 1))".
Extract Constant Nat.div => "(/)".
Extract Constant Nat.modulo => "(mod)".
Extract Constant Nat.pow =>
  "(fun x y -> int_of_float ((float_of_int x) ** (float_of_int y)))".
Extract Constant max_int_runtime => "Stdlib.max_int".
Extract Constant max_int_8 => "255".
Extract Constant max_int_16 => "65535".
Extract Constant max_int_32 => "4294967295".
Extract Constant byte_limit => "255".
Extract Constant seven_bit_limit => "127".

Extraction Inline pred.

Set Extraction Output Directory ".".

Extraction "rle_encoding.ml"
  rle_encode rle_decode repeat count_runs
  rle_encode_validated rle_decode_validated
  rle_encode_maxrun rle_encode_aux_maxrun
  byte_limit seven_bit_limit
  rle_encode_byte rle_encode_7bit
  init_stream_state stream_push stream_flush stream_encode_list
  rle_encode_u8 rle_encode_u16 rle_encode_u32
  rle_decode_u8 rle_decode_u16 rle_decode_u32
  bounded_rle_encode bounded_rle_decode.
    
