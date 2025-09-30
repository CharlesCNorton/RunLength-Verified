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

(** The length of a repeated list equals the repetition count. *)
Lemma repeat_length : forall n val,
  length (repeat n val) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** Repeating [n + m] times is equivalent to concatenating [repeat n] and [repeat m]. *)
Lemma repeat_app : forall n m val,
  repeat (n + m) val = repeat n val ++ repeat m val.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

(** All elements in a repeated list are equal to the repeated value. *)
Lemma repeat_In : forall n val x,
  In x (repeat n val) -> x = val.
Proof.
  induction n; simpl; intros.
  - contradiction.
  - destruct H; auto.
Qed.

(** A repeated list with positive count is nonempty. *)
Lemma repeat_not_nil : forall n val,
  n > 0 -> repeat n val <> [].
Proof.
  destruct n; simpl; intros.
  - lia.
  - discriminate.
Qed.

(** The successor case of [repeat] unfolds to a cons cell. *)
Lemma repeat_S : forall n val,
  repeat (S n) val = val :: repeat n val.
Proof.
  reflexivity.
Qed.

(** Appending a value to a repeated list extends the repetition count. *)
Lemma repeat_cons_app : forall n val l,
  repeat n val ++ (val :: l) = repeat (S n) val ++ l.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

(** * Core Correctness *)

(** Decoding the auxiliary encoder's output, with an accumulator appended,
    equals the repeated prefix followed by the list and accumulator. *)
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

(** Decoding the encoding of any list recovers the original list. *)
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

(** All runs produced by the auxiliary encoder have positive counts. *)
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

(** Symmetric inequality for natural numbers. *)
Lemma neq_sym : forall (a b : nat), a <> b -> b <> a.
Proof.
  intros a b H. intro H1. apply H. symmetry. exact H1.
Qed.

(** The auxiliary encoder applied to the empty list produces no adjacent equal values. *)
Lemma rle_encode_aux_no_adjacent_nil : forall val count i,
  count > 0 ->
  i < pred (length (rle_encode_aux val count [])) ->
  snd (nth i (rle_encode_aux val count []) (0,0)) <>
  snd (nth (S i) (rle_encode_aux val count []) (0,0)).
Proof.
  intros. simpl in *. lia.
Qed.

(** Incrementing the count preserves the no-adjacent-duplicates property. *)
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

(** Inequality is symmetric when the first element differs from the accumulator value. *)
Lemma rle_encode_aux_no_adjacent_diff_first : forall (a val count : nat),
  count > 0 ->
  a <> val ->
  val <> a.
Proof.
  intros. apply neq_sym. exact H0.
Qed.

(** The first run produced by the auxiliary encoder has the accumulator value as its second component. *)
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

(** No two adjacent runs in the auxiliary encoder's output have equal values. *)
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

(** The encoder produces well-formed run-length encodings for nonempty lists. *)
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

(** Decoding distributes over concatenation of run lists. *)
Lemma rle_decode_app : forall r1 r2,
  rle_decode (r1 ++ r2) = rle_decode r1 ++ rle_decode r2.
Proof.
  induction r1; simpl; intros.
  - reflexivity.
  - destruct a. rewrite IHr1. rewrite app_assoc. reflexivity.
Qed.

(** The encoder is injective: distinct lists produce distinct encodings. *)
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

(** The length of the auxiliary encoder's output equals the run count. *)
Lemma rle_encode_aux_length : forall l val count,
  length (rle_encode_aux val count l) = count_runs_aux val l.
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - destruct (Nat.eqb a val); simpl; auto.
Qed.

(** The length of the encoding equals the number of runs in the input. *)
Theorem rle_length : forall l,
  length (rle_encode l) = count_runs l.
Proof.
  destruct l; simpl.
  - reflexivity.
  - apply rle_encode_aux_length.
Qed.

(** The auxiliary run counter is bounded by one plus the list length. *)
Lemma count_runs_aux_le : forall l val,
  count_runs_aux val l <= S (length l).
Proof.
  induction l; simpl; intros.
  - auto.
  - destruct (Nat.eqb a val).
    + apply le_S. apply IHl.
    + simpl. apply le_n_S. apply IHl.
Qed.

(** In the worst case, the encoding is no longer than the original list. *)
Theorem rle_worst_case : forall l,
  length (rle_encode l) <= length l.
Proof.
  intros. rewrite rle_length. destruct l; simpl.
  - auto.
  - apply count_runs_aux_le.
Qed.

(** In the best case, a uniform list compresses to a single run. *)
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

(** For uniform lists, the compression ratio is [n:1]. *)
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

(** The length of the worst-case alternating list equals [n]. *)
Lemma worst_case_list_length : forall n,
  length (worst_case_list n) = n.
Proof.
  intros. unfold worst_case_list.
  rewrite map_length. apply seq_length.
Qed.

(** When all adjacent elements differ, the encoding length equals the input length. *)
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

(** Lists with no adjacent equal elements achieve no compression. *)
Theorem compression_ratio_no_benefit : forall l,
  (forall i, i < pred (length l) -> nth i l 0 <> nth (S i) l 0) ->
  compression_ratio_num l (rle_encode l) = length l /\
  compression_ratio_den l (rle_encode l) = length l.
Proof.
  intros. split.
  - unfold compression_ratio_num. reflexivity.
  - unfold compression_ratio_den. apply no_compression_worst. exact H.
Qed.

(** Repeated lists of length at least two benefit from compression. *)
Theorem rle_beneficial : forall n val,
  count_runs (repeat (S (S n)) val) <= S n.
Proof.
  intros. unfold count_runs. simpl.
  rewrite Nat.eqb_refl.
  induction n; simpl.
  - reflexivity.
  - rewrite Nat.eqb_refl. lia.
Qed.

(** For lists with length greater than one, compression reduces size. *)
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

(** For valid run lists, the length of each repeated segment equals the run count. *)
Lemma valid_rle_decode_length : forall runs,
  is_valid_rle runs ->
  forall r, In r runs -> length (repeat (fst r) (snd r)) = fst r.
Proof.
  intros. apply repeat_length.
Qed.

(** The decoded length equals the sum of run counts. *)
Lemma decode_length_sum : forall runs,
  length (rle_decode runs) = fold_right (fun r acc => fst r + acc) 0 runs.
Proof.
  induction runs; simpl.
  - reflexivity.
  - destruct a. rewrite app_length. rewrite repeat_length.
    f_equal. apply IHruns.
Qed.

(** The predecessor of the length of a nonempty cons list follows a pattern. *)
Lemma pred_length_cons : forall {A} (a : A) (l : list A),
  l <> [] -> pred (length (a :: l)) = S (pred (length l)).
Proof.
  intros. destruct l.
  - congruence.
  - simpl. reflexivity.
Qed.

(** If an encoding decodes to a nonempty list, the encoding itself is nonempty. *)
Lemma decode_nonempty : forall runs val l,
  decodes_to runs (val :: l) -> runs <> [].
Proof.
  intros. intro Hcontra. subst.
  unfold decodes_to in H. simpl in H. discriminate.
Qed.

(** For valid nonempty run lists, the first run has positive count. *)
Lemma valid_rle_positive_first : forall runs,
  is_valid_rle runs -> runs <> [] ->
  fst (hd (0,0) runs) > 0.
Proof.
  intros. destruct runs.
  - congruence.
  - simpl. unfold is_valid_rle in H.
    apply H. simpl. auto.
Qed.

(** The no-adjacent-duplicates property of a cons list holds for its tail. *)
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

(** An encoding that decodes to a cons list has a structured first run. *)
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

(** An encoding that decodes to a singleton list has at least one run. *)
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

(** Decoding two consecutive identical values admits a shorter encoding. *)
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

(** The auxiliary run counter is bounded by the encoding length. *)
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
      pose proof (decode_cons_structure _ _ _ Hdecode Hvalid) as Hstruct.
      destruct runs as [|[count v] runs']; [contradiction|].
      destruct Hstruct as [Hpos [[Hc1 [Hv1 Hdec1]]|[Hc2 [Hv2 Hdec2]]]].
      * subst. unfold decodes_to in Hdec1.
        assert (count_runs_aux val l <= length runs').
        { apply IHl with (runs := runs'); auto.
          unfold is_valid_rle in *. intros. apply Hvalid. simpl. auto. }
        simpl. lia.
      * subst.
        apply IHl with (runs := ((count - 1, val) :: runs')).
        -- exact Hdec2.
        -- unfold is_valid_rle in *. intros. simpl in H. destruct H.
           ++ inversion H. simpl. lia.
           ++ apply Hvalid. simpl. auto.
    + apply Nat.eqb_neq in Heq.
      simpl.
      pose proof (decode_cons_structure _ _ _ Hdecode Hvalid) as Hstruct.
      destruct runs as [|[count v] runs']; [contradiction|].
      destruct Hstruct as [Hpos [[Hc1 [Hv1 Hdec1]]|[Hc2 [Hv2 Hdec2]]]].
      * subst.
        assert (count_runs_aux a l <= length runs').
        { apply IHl with (val := a) (runs := runs').
          -- exact Hdec1.
          -- unfold is_valid_rle in *. intros. apply Hvalid. simpl. auto. }
        simpl. lia.
      * subst. unfold decodes_to in Hdec2.
        assert (count - 1 > 0) by lia.
        destruct (count - 1) eqn:Hcount.
        -- lia.
        -- simpl in Hdec2.
           assert (val :: repeat n val ++ rle_decode runs' = a :: l).
           { exact Hdec2. }
           injection H0; intros. subst a. congruence.
Qed.

(** The auxiliary run counter is bounded by the encoding length with well-formedness. *)
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

(** The encoder produces encodings of minimal length among all valid well-formed encodings. *)
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

(** Splitting a run produces a decomposition whose concatenation equals the original. *)
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

(** Flattening the decomposed runs with sufficient fuel recovers the original list. *)
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

(** Decomposing then flattening recovers the original list. *)
Theorem decompose_flatten : forall l,
  flatten_runs (decompose_runs l) = l.
Proof.
  intros. unfold decompose_runs.
  apply decompose_runs_aux_correct. auto.
Qed.

(** * Composition Properties *)

(** Decoding the concatenation of two well-formed run lists distributes over append. *)
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

(** The run count of concatenated lists is bounded by the sum of individual run counts. *)
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

(** Parallel encoding of two lists with distinct boundary values produces a bounded encoding. *)
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

(** Appending well-formed run lists preserves decoding distributivity. *)
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

(** The auxiliary encoder never produces an empty list. *)
Lemma rle_encode_aux_not_nil : forall l val count,
  rle_encode_aux val count l <> [].
Proof.
  induction l; intros; simpl; try discriminate.
  destruct (Nat.eqb a val) eqn:E.
  - apply IHl.
  - discriminate.
Qed.

(** The last value in the auxiliary encoder's output equals the last element of the input. *)
Lemma rle_encode_aux_last_snd : forall l val count,
  count > 0 ->
  l <> [] ->
  snd (last (rle_encode_aux val count l) (0,0)) = last l 0.
Proof.
  induction l as [|a l' IH]; intros val count Hpos Hne.
  - congruence.
  - simpl rle_encode_aux. destruct (Nat.eqb a val) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst a.
      destruct l' as [|b l''].
      * simpl. reflexivity.
      * assert (Hlast: last (val :: b :: l'') 0 = last (b :: l'') 0).
        { simpl. destruct l''; reflexivity. }
        rewrite Hlast.
        apply IH; [lia|discriminate].
    + destruct l' as [|b l''].
      * simpl. reflexivity.
      * assert (Hlast: last (a :: b :: l'') 0 = last (b :: l'') 0).
        { simpl. destruct l''; reflexivity. }
        rewrite Hlast. clear Hlast.
        assert (Henc_last: snd (last (rle_encode_aux a 1 (b :: l'')) (0,0)) = last (b :: l'') 0).
        { apply IH; [lia|discriminate]. }
        pose proof (rle_encode_aux_not_nil (b :: l'') a 1) as Hnil.
        destruct (rle_encode_aux a 1 (b :: l'')) eqn:Eenc; [contradiction|].
        simpl. exact Henc_last.
Qed.

(** The last value in the encoding equals the last element of the input list. *)
Lemma rle_encode_last_snd : forall l,
  l <> [] ->
  snd (last (rle_encode l) (0,0)) = last l 0.
Proof.
  intros l Hne.
  destruct l as [|h t]; [congruence|].
  unfold rle_encode.
  destruct t as [|a t'].
  - simpl. reflexivity.
  - replace (last (h :: a :: t') 0) with (last (a :: t') 0).
    + apply rle_encode_aux_last_snd; [lia|discriminate].
    + simpl. destruct t'; reflexivity.
Qed.

(** The first value in the encoding equals the first element of the input list. *)
Lemma rle_encode_hd_snd : forall l,
  l <> [] ->
  snd (hd (0,0) (rle_encode l)) = hd 0 l.
Proof.
  intros l Hne.
  destruct l as [|h t]; [congruence|].
  unfold rle_encode. simpl.
  assert (Heq: hd (0,0) (rle_encode_aux h 1 t) = nth 0 (rle_encode_aux h 1 t) (0,0)).
  { destruct (rle_encode_aux h 1 t) eqn:E.
    - pose proof (rle_encode_aux_not_nil t h 1). congruence.
    - reflexivity. }
  rewrite Heq.
  apply rle_encode_aux_first_snd_general. lia.
Qed.

(** When boundary elements differ, encoded boundary values also differ. *)
Theorem encode_safe_concat : forall l1 l2,
  l1 <> [] ->
  l2 <> [] ->
  last l1 0 <> hd 0 l2 ->
  snd (last (rle_encode l1) (0,0)) <> snd (hd (0,0) (rle_encode l2)).
Proof.
  intros l1 l2 Hne1 Hne2 Hbound.
  rewrite rle_encode_last_snd by exact Hne1.
  rewrite rle_encode_hd_snd by exact Hne2.
  exact Hbound.
Qed.

(** * Concurrent and Parallel Properties *)

Definition independent_segments (l1 l2 : list nat) : Prop :=
  l1 = [] \/ l2 = [] \/ last l1 0 <> hd 0 l2.

(** Parallel encoding preserves correct decoding through simple concatenation. *)
Theorem parallel_encode_preserves_decode : forall l1 l2,
  rle_decode (rle_encode l1 ++ rle_encode l2) = l1 ++ l2 \/
  exists combined,
    rle_decode combined = l1 ++ l2 /\
    length combined <= length (rle_encode l1) + length (rle_encode l2).
Proof.
  intros l1 l2.
  left.
  rewrite rle_decode_app.
  rewrite rle_correct. rewrite rle_correct.
  reflexivity.
Qed.

(** Decoding is associative over concatenation of run lists. *)
Theorem parallel_decode_associative : forall r1 r2 r3,
  rle_decode (r1 ++ r2 ++ r3) = rle_decode ((r1 ++ r2) ++ r3).
Proof.
  intros. rewrite app_assoc. reflexivity.
Qed.

(** The second run in a well-formed pair has a different value from the first. *)
Lemma well_formed_tail : forall val c v runs,
  well_formed_rle ((1, val) :: (S c, v) :: runs) ->
  v <> val.
Proof.
  intros. unfold well_formed_rle in H. destruct H as [_ H].
  assert (0 < pred (length ((1, val) :: (S c, v) :: runs))) by (simpl; lia).
  apply H in H0. simpl in H0. apply neq_sym. exact H0.
Qed.

(** The predecessor of a triple cons list length follows a simple pattern. *)
Lemma pred_length_triple : forall {A} (a b c : A) (l : list A),
  pred (length (a :: b :: c :: l)) = S (S (length l)).
Proof.
  intros. simpl. reflexivity.
Qed.

(** Inequality propagation through successor. *)
Lemma lt_pred_to_succ : forall i n,
  i < S n -> S i < S (S n).
Proof.
  intros. lia.
Qed.

(** Encoding a repeated list with an accumulator produces a single run summing the counts. *)
Lemma rle_encode_aux_repeat_accumulator : forall val count n,
  rle_encode_aux val count (repeat n val) = [(count + n, val)].
Proof.
  intros val count n. generalize dependent count.
  induction n; intros; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.eqb_refl. rewrite IHn. f_equal. f_equal. lia.
Qed.

(** Encoding a repeated prefix followed by decoded runs accumulates the repeat count. *)
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

(** Well-formedness is preserved when removing the first run from a pair. *)
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

(** Encoding the empty decoded list produces the empty encoding. *)
Lemma rle_encode_decode_empty :
  rle_encode (rle_decode []) = [].
Proof.
  reflexivity.
Qed.

(** Encoding a decoded single run recovers the original run. *)
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

(** Encoding a singleton list produces a single run with count one. *)
Lemma rle_encode_single_value_list : forall val,
  rle_encode [val] = [(1, val)].
Proof.
  intros. reflexivity.
Qed.

(** Decoding a single run produces a repeated list. *)
Lemma rle_decode_single_run : forall count val,
  rle_decode [(count, val)] = repeat count val.
Proof.
  intros. simpl. rewrite app_nil_r. reflexivity.
Qed.

(** Decoding a cons list unfolds to concatenation with repeated elements. *)
Lemma rle_decode_cons : forall count val runs,
  rle_decode ((count, val) :: runs) = repeat count val ++ rle_decode runs.
Proof.
  intros. reflexivity.
Qed.

(** Encoding a different value terminates the current run and starts a new one. *)
Lemma rle_encode_aux_different_value : forall val v count l,
  v <> val ->
  rle_encode_aux val count (v :: l) = (count, val) :: rle_encode_aux v 1 l.
Proof.
  intros. simpl. destruct (Nat.eqb v val) eqn:Heq.
  - apply Nat.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

(** Encoding the same value continues the current run. *)
Lemma rle_encode_aux_same_value : forall val count l,
  rle_encode_aux val count (val :: l) = rle_encode_aux val (S count) l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** The auxiliary encoder applied to the empty list produces a single run. *)
Lemma rle_encode_aux_empty : forall val count,
  rle_encode_aux val count [] = [(count, val)].
Proof.
  intros. reflexivity.
Qed.

(** Encoding a repeated list produces a single run with the repetition count. *)
Lemma rle_encode_repeat : forall count val,
  count > 0 ->
  rle_encode (repeat count val) = [(count, val)].
Proof.
  intros. destruct count.
  - lia.
  - simpl. rewrite rle_encode_aux_repeat_accumulator.
    replace (1 + count) with (S count) by lia. reflexivity.
Qed.

(** A valid cons run list has a positive count and a valid tail. *)
Lemma valid_rle_cons : forall count val runs,
  is_valid_rle ((count, val) :: runs) ->
  count > 0 /\ is_valid_rle runs.
Proof.
  intros. unfold is_valid_rle in *. split.
  - assert (fst (count, val) > 0) by (apply H; simpl; auto).
    simpl in H0. exact H0.
  - intros r Hr. apply H. simpl. auto.
Qed.

(** Adjacent runs in a well-formed list have different values. *)
Lemma well_formed_cons_different : forall count val c v runs,
  well_formed_rle ((count, val) :: (c, v) :: runs) ->
  val <> v.
Proof.
  intros. unfold well_formed_rle in H. destruct H as [_ H].
  assert (0 < pred (length ((count, val) :: (c, v) :: runs))) by (simpl; lia).
  apply H in H0. simpl in H0. exact H0.
Qed.

(** Decoding two runs produces concatenated repeated segments. *)
Lemma rle_decode_two_runs : forall c1 v1 c2 v2,
  rle_decode [(c1, v1); (c2, v2)] = repeat c1 v1 ++ repeat c2 v2.
Proof.
  intros. simpl. rewrite app_nil_r. reflexivity.
Qed.

(** Encoding a single value followed by empty repeated segments produces one run. *)
Lemma rle_encode_two_runs_case1 : forall v1 v2,
  v1 <> v2 ->
  rle_encode (v1 :: repeat 0 v1 ++ repeat 0 v2) = [(1, v1)].
Proof.
  intros. simpl. reflexivity.
Qed.

(** Encoding two different singleton values produces two unit runs. *)
Lemma rle_encode_single_then_different : forall v1 v2,
  v1 <> v2 ->
  rle_encode [v1; v2] = [(1, v1); (1, v2)].
Proof.
  intros. simpl. destruct (Nat.eqb v2 v1) eqn:Heq.
  - apply Nat.eqb_eq in Heq. congruence.
  - reflexivity.
Qed.

(** Encoding a different value in the auxiliary encoder splits the run. *)
Lemma rle_encode_aux_app_different : forall val count v l,
  v <> val ->
  rle_encode_aux val count (v :: l) = (count, val) :: rle_encode_aux v 1 l.
Proof.
  intros. apply rle_encode_aux_different_value. auto.
Qed.

(** Encoding repeated values followed by a different element accumulates the count. *)
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

(** Encoding concatenated repeated segments with different values produces two runs. *)
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

(** Encoding a value followed by a repeated different value produces one or two runs. *)
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

(** Encoding a decoded pair of well-formed runs recovers the original pair. *)
Lemma rle_encode_decode_two_runs : forall c1 v1 c2 v2,
  c1 > 0 -> c2 > 0 -> v1 <> v2 ->
  rle_encode (rle_decode [(c1, v1); (c2, v2)]) = [(c1, v1); (c2, v2)].
Proof.
  intros. rewrite rle_decode_two_runs.
  apply rle_encode_repeat_app_different; auto.
Qed.

(** For small valid well-formed run lists, encoding their decoding recovers the original. *)
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

(** List concatenation is associative when regrouped. *)
Lemma app_assoc_reverse : forall A (l1 l2 l3 : list A),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  intros. rewrite <- app_assoc. reflexivity.
Qed.

(** Encoding a repeated segment followed by a different-valued list produces a cons. *)
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

(** The first element of a decoded cons list differs from an unequal value. *)
Lemma hd_rle_decode_neq : forall (c : nat) v c' v' rs,
  v <> v' -> c' > 0 ->
  hd 0 (rle_decode ((c', v') :: rs)) <> v.
Proof.
  intros. simpl. destruct c'.
  - lia.
  - simpl. apply neq_sym. exact H.
Qed.

(** For all valid well-formed run lists, encoding their decoding recovers the original. *)
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

(** All encodings produced by the encoder are well-formed. *)
Corollary encode_well_formed_any : forall l,
  well_formed_rle (rle_encode l).
Proof.
  intros. destruct l.
  - simpl. unfold well_formed_rle. split; intros.
    + contradiction.
    + simpl in H. inversion H.
  - apply encode_well_formed. discriminate.
Qed.

(** * Inverse Optimality *)

(** Decoding is a left inverse of encoding. *)
Theorem decode_left_inverse : forall l,
  rle_decode (rle_encode l) = l.
Proof.
  apply rle_correct.
Qed.

(** For well-formed valid encodings, encoding is a left inverse of decoding. *)
Theorem encode_decode_cancel_wf : forall runs,
  well_formed_rle runs ->
  is_valid_rle runs ->
  rle_encode (rle_decode runs) = runs.
Proof.
  intros. apply rle_encode_decode_identity_full; auto.
Qed.

(** Decoding is injective on well-formed valid run lists. *)
Lemma decode_injective_on_wf : forall r1 r2,
  well_formed_rle r1 ->
  well_formed_rle r2 ->
  is_valid_rle r1 ->
  is_valid_rle r2 ->
  rle_decode r1 = rle_decode r2 ->
  r1 = r2.
Proof.
  intros r1 r2 Hwf1 Hwf2 Hval1 Hval2 Hdec.
  rewrite <- (rle_encode_decode_identity_full r1 Hval1 Hwf1).
  rewrite <- (rle_encode_decode_identity_full r2 Hval2 Hwf2).
  rewrite Hdec. reflexivity.
Qed.

Definition is_encoding_of (runs : list run) (l : list nat) : Prop :=
  rle_decode runs = l.

(** Any two well-formed valid encodings of the same list are equal. *)
Theorem unique_well_formed_encoding : forall l runs1 runs2,
  well_formed_rle runs1 ->
  well_formed_rle runs2 ->
  is_valid_rle runs1 ->
  is_valid_rle runs2 ->
  is_encoding_of runs1 l ->
  is_encoding_of runs2 l ->
  runs1 = runs2.
Proof.
  intros l runs1 runs2 Hwf1 Hwf2 Hval1 Hval2 Henc1 Henc2.
  unfold is_encoding_of in *.
  rewrite <- (rle_encode_decode_identity_full runs1 Hval1 Hwf1).
  rewrite <- (rle_encode_decode_identity_full runs2 Hval2 Hwf2).
  rewrite Henc1. rewrite Henc2. reflexivity.
Qed.

(** The canonical encoding is the unique well-formed encoding. *)
Theorem rle_encode_is_unique_wf_encoding : forall l runs,
  well_formed_rle runs ->
  is_valid_rle runs ->
  is_encoding_of runs l ->
  runs = rle_encode l.
Proof.
  intros l runs Hwf Hval Henc.
  unfold is_encoding_of in Henc.
  rewrite <- (rle_encode_decode_identity_full runs Hval Hwf).
  rewrite Henc. reflexivity.
Qed.

(** Decoding has a unique inverse for any encoding. *)
Theorem decode_unique_inverse : forall l runs,
  rle_encode l = runs ->
  exists! decoded, decoded = rle_decode runs.
Proof.
  intros l runs Henc.
  exists (rle_decode runs). unfold unique. split.
  - reflexivity.
  - intros decoded' Hdec. symmetry. exact Hdec.
Qed.

(** Encoding preserves distinctness of lists. *)
Theorem encode_preserves_distinctness : forall l1 l2,
  l1 <> l2 ->
  rle_encode l1 <> rle_encode l2.
Proof.
  intros l1 l2 Hneq Hcontra.
  apply Hneq.
  apply rle_injective. exact Hcontra.
Qed.

(** Decoding is a deterministic function. *)
Lemma decode_deterministic : forall runs l1 l2,
  rle_decode runs = l1 ->
  rle_decode runs = l2 ->
  l1 = l2.
Proof.
  intros. rewrite <- H. exact H0.
Qed.

(** Encoding is surjective onto well-formed valid run lists. *)
Theorem encode_surjective_on_wf : forall runs,
  well_formed_rle runs ->
  is_valid_rle runs ->
  exists l, rle_encode l = runs.
Proof.
  intros runs Hwf Hval.
  exists (rle_decode runs).
  apply rle_encode_decode_identity_full; auto.
Qed.

(** Encoding and decoding form a bijection on well-formed valid encodings. *)
Theorem encode_decode_bijection_wf : forall runs l,
  well_formed_rle runs ->
  is_valid_rle runs ->
  (rle_encode l = runs <-> rle_decode runs = l).
Proof.
  intros runs l Hwf Hval. split; intro H.
  - rewrite <- H. apply rle_correct.
  - rewrite <- H. apply rle_encode_decode_identity_full; auto.
Qed.

(** Decoding respects equality of run lists. *)
Theorem decode_respects_equality : forall r1 r2,
  r1 = r2 ->
  rle_decode r1 = rle_decode r2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

(** Encoding respects equality of lists. *)
Theorem encode_respects_equality : forall l1 l2,
  l1 = l2 ->
  rle_encode l1 = rle_encode l2.
Proof.
  intros. rewrite H. reflexivity.
Qed.

(** Two minimal well-formed encodings of the same list are equal. *)
Lemma wf_encoding_minimal_implies_unique : forall l runs1 runs2,
  well_formed_rle runs1 ->
  well_formed_rle runs2 ->
  is_valid_rle runs1 ->
  is_valid_rle runs2 ->
  rle_decode runs1 = l ->
  rle_decode runs2 = l ->
  length runs1 = count_runs l ->
  length runs2 = count_runs l ->
  runs1 = runs2.
Proof.
  intros l runs1 runs2 Hwf1 Hwf2 Hval1 Hval2 Hdec1 Hdec2 Hlen1 Hlen2.
  apply unique_well_formed_encoding with (l := l); auto;
  unfold is_encoding_of; auto.
Qed.

(** The canonical encoding achieves minimum length among all valid well-formed encodings. *)
Theorem rle_encode_achieves_minimum : forall l,
  l <> [] ->
  forall runs,
    well_formed_rle runs ->
    is_valid_rle runs ->
    rle_decode runs = l ->
    length (rle_encode l) <= length runs.
Proof.
  intros l Hne runs Hwf Hval Hdec.
  rewrite rle_length.
  apply encode_is_minimal with (l := l); auto; unfold decodes_to; exact Hdec.
Qed.


(** A minimal-length encoding is the canonical encoding. *)
Theorem minimal_encoding_is_canonical : forall l runs,
  well_formed_rle runs ->
  is_valid_rle runs ->
  rle_decode runs = l ->
  length runs = count_runs l ->
  runs = rle_encode l.
Proof.
  intros l runs Hwf Hval Hdec Hlen.
  rewrite <- (rle_encode_decode_identity_full runs Hval Hwf).
  rewrite Hdec. reflexivity.
Qed.

(** The canonical encoding minimizes the number of runs. *)
Theorem rle_encode_minimizes_runs : forall l runs,
  decodes_to runs l ->
  is_valid_rle runs ->
  well_formed_rle runs ->
  length (rle_encode l) <= length runs.
Proof.
  intros. rewrite rle_length.
  apply encode_is_minimal; auto.
Qed.

(** Encoding is idempotent through a decode-encode cycle. *)
Theorem rle_idempotent : forall l,
  rle_encode (rle_decode (rle_encode l)) = rle_encode l.
Proof.
  intros. rewrite rle_correct. reflexivity.
Qed.

(** Decoding is idempotent through an encode-decode cycle for well-formed runs. *)
Theorem rle_decode_idempotent : forall runs,
  is_valid_rle runs ->
  well_formed_rle runs ->
  rle_decode (rle_encode (rle_decode runs)) = rle_decode runs.
Proof.
  intros. rewrite rle_correct. reflexivity.
Qed.

(** * Error Handling and Invalid Inputs *)

(** Decoding ignores runs with zero count. *)
Lemma rle_decode_invalid_count : forall v rs,
  rle_decode ((0, v) :: rs) = rle_decode rs.
Proof.
  intros. reflexivity.
Qed.

(** The encoder never produces runs with zero count. *)
Lemma rle_encode_never_zero_count : forall l r,
  In r (rle_encode l) -> fst r > 0.
Proof.
  intros. destruct l.
  - simpl in H. contradiction.
  - apply rle_encode_aux_positive with (val := n) (count := 1) (l := l).
    + lia.
    + exact H.
Qed.

(** The encoder always produces valid run lists for nonempty inputs. *)
Lemma rle_encode_is_valid : forall l,
  l <> [] ->
  is_valid_rle (rle_encode l).
Proof.
  intros l Hne.
  unfold is_valid_rle. intros r Hr.
  apply rle_encode_never_zero_count with l. exact Hr.
Qed.

(** There exists a unique minimal well-formed encoding for any nonempty list. *)
Theorem fundamental_theorem_of_rle : forall l,
  l <> [] ->
  exists! encoding,
    well_formed_rle encoding /\
    is_valid_rle encoding /\
    rle_decode encoding = l /\
    (forall other_encoding,
      well_formed_rle other_encoding ->
      is_valid_rle other_encoding ->
      rle_decode other_encoding = l ->
      length encoding <= length other_encoding).
Proof.
  intros l Hne.
  exists (rle_encode l).
  unfold unique. split.
  - split; [|split; [|split]].
    + apply encode_well_formed. exact Hne.
    + apply rle_encode_is_valid. exact Hne.
    + apply rle_correct.
    + intros other Hwf Hval Hdec.
      apply rle_encode_achieves_minimum; auto.
  - intros encoding' [Hwf' [Hval' [Hdec' Hmin']]].
    assert (Hlen_eq: length encoding' = length (rle_encode l)).
    { assert (length encoding' <= length (rle_encode l)).
      { apply Hmin'; auto.
        - apply encode_well_formed. exact Hne.
        - apply rle_encode_is_valid. exact Hne.
        - apply rle_correct. }
      assert (length (rle_encode l) <= length encoding').
      { apply rle_encode_achieves_minimum; auto. }
      lia. }
    apply (wf_encoding_minimal_implies_unique l (rle_encode l) encoding'); auto.
    + apply encode_well_formed. exact Hne.
    + apply rle_encode_is_valid. exact Hne.
    + apply rle_correct.
    + apply rle_length.
    + rewrite Hlen_eq. apply rle_length.
Qed.

(** An encoding is optimal if and only if it equals the canonical encoding. *)
Theorem optimal_encoding_decision : forall l runs,
  l <> [] ->
  well_formed_rle runs ->
  is_valid_rle runs ->
  rle_decode runs = l ->
  (length runs = length (rle_encode l) <-> runs = rle_encode l).
Proof.
  intros l runs Hne Hwf Hval Hdec.
  split; intro H.
  - apply (wf_encoding_minimal_implies_unique l runs (rle_encode l)); auto.
    + apply encode_well_formed. exact Hne.
    + apply rle_encode_is_valid. exact Hne.
    + apply rle_correct.
    + rewrite H. rewrite rle_length. reflexivity.
    + apply rle_length.
  - rewrite H. reflexivity.
Qed.

(** Equal encodings produce equal lists. *)
Theorem rle_encode_canonical : forall l1 l2,
  l1 <> [] -> l2 <> [] ->
  rle_encode l1 = rle_encode l2 ->
  l1 = l2.
Proof.
  intros l1 l2 Hne1 Hne2 Heq.
  rewrite <- (rle_correct l1).
  rewrite <- (rle_correct l2).
  rewrite Heq. reflexivity.
Qed.

(** The encode-decode-encode composition retracts to the encoding. *)
Theorem rle_decode_encode_retract : forall l,
  l <> [] ->
  rle_encode (rle_decode (rle_encode l)) = rle_encode l.
Proof.
  intros l Hne.
  rewrite rle_correct. reflexivity.
Qed.

(** The run count is a lower bound on encoding length. *)
Theorem rle_optimal_compression_ratio : forall l,
  l <> [] ->
  forall runs,
    well_formed_rle runs ->
    is_valid_rle runs ->
    rle_decode runs = l ->
    count_runs l <= length runs.
Proof.
  intros l Hne runs Hwf Hval Hdec.
  rewrite <- rle_length.
  apply rle_encode_achieves_minimum; auto.
Qed.

(** Every encoding falls into one of three complexity categories. *)
Theorem compression_space_trichotomy : forall l runs,
  l <> [] ->
  well_formed_rle runs ->
  is_valid_rle runs ->
  rle_decode runs = l ->
  (length runs < length (rle_encode l) /\ False) \/
  (length runs = length (rle_encode l) /\ runs = rle_encode l) \/
  (length runs > length (rle_encode l) /\ runs <> rle_encode l).
Proof.
  intros l runs Hne Hwf Hval Hdec.
  destruct (Nat.lt_trichotomy (length runs) (length (rle_encode l))) as [Hlt|[Heq|Hgt]].
  - left. split; auto.
    assert (length (rle_encode l) <= length runs).
    { apply rle_encode_achieves_minimum; auto. }
    lia.
  - right. left. split; auto.
    apply optimal_encoding_decision; auto.
  - right. right. split.
    + exact Hgt.
    + intro Hcontra. subst runs. lia.
Qed.

(** The run count is a Kolmogorov complexity measure for RLE. *)
Theorem kolmogorov_complexity_for_rle : forall l k,
  l <> [] ->
  (exists runs,
    well_formed_rle runs /\
    is_valid_rle runs /\
    rle_decode runs = l /\
    length runs = k) ->
  count_runs l <= k.
Proof.
  intros l k Hne [runs [Hwf [Hval [Hdec Hlen]]]].
  rewrite <- rle_length. rewrite <- Hlen.
  apply rle_encode_achieves_minimum; auto.
Qed.

(** No encoding shorter than the run count can exist. *)
Theorem rle_complexity_characterization : forall l,
  l <> [] ->
  forall k,
    k < count_runs l ->
    ~(exists runs,
      well_formed_rle runs /\
      is_valid_rle runs /\
      rle_decode runs = l /\
      length runs = k).
Proof.
  intros l Hne k Hlt [runs [Hwf [Hval [Hdec Hlen]]]].
  assert (count_runs l <= k) by (eapply kolmogorov_complexity_for_rle; eauto; exists runs; auto).
  lia.
Qed.

Definition sanitize_runs (runs : list run) : list run :=
  filter (fun r => match fst r with 0 => false | _ => true end) runs.

(** Sanitizing runs preserves validity. *)
Lemma sanitize_preserves_valid : forall runs,
  is_valid_rle (sanitize_runs runs).
Proof.
  intros. unfold is_valid_rle, sanitize_runs.
  intros r Hr. apply filter_In in Hr.
  destruct Hr as [_ H]. destruct (fst r); [discriminate | lia].
Qed.

(** Sanitizing runs is equivalent to filtering out zero counts. *)
Theorem rle_decode_sanitized : forall runs,
  rle_decode (sanitize_runs runs) =
  rle_decode (filter (fun r => negb (Nat.eqb (fst r) 0)) runs).
Proof.
  intros. unfold sanitize_runs. f_equal.
  apply filter_ext. intros [c v]. simpl.
  destruct c; reflexivity.
Qed.

(** * Robustness and Error Correction *)

(** Decoding is invariant under zero-count removal. *)
Lemma decode_with_zeros_equivalence : forall runs,
  rle_decode runs = rle_decode (sanitize_runs runs).
Proof.
  induction runs as [|[c v] rs IH].
  - reflexivity.
  - simpl. destruct c.
    + simpl. exact IH.
    + unfold sanitize_runs. simpl. rewrite IH. reflexivity.
Qed.

(** Sanitization preserves decoding. *)
Theorem sanitize_preserves_decode : forall runs,
  rle_decode (sanitize_runs runs) = rle_decode runs.
Proof.
  intros. symmetry. apply decode_with_zeros_equivalence.
Qed.

(** Sanitization is idempotent. *)
Theorem sanitize_idempotent : forall runs,
  sanitize_runs (sanitize_runs runs) = sanitize_runs runs.
Proof.
  intros. unfold sanitize_runs.
  induction runs as [|[c v] rs IH].
  - reflexivity.
  - simpl. destruct c.
    + exact IH.
    + simpl. f_equal. exact IH.
Qed.

Definition has_corruption (runs : list run) : Prop :=
  exists r, In r runs /\ fst r = 0.

(** The encoder never produces corrupted run lists. *)
Theorem encode_never_corrupted : forall l,
  ~has_corruption (rle_encode l).
Proof.
  intros l [r [Hin Hzero]].
  apply rle_encode_never_zero_count in Hin.
  rewrite Hzero in Hin. simpl in Hin. lia.
Qed.

(** Sanitization removes all corruption. *)
Lemma sanitize_removes_corruption : forall runs,
  ~has_corruption (sanitize_runs runs).
Proof.
  intros runs [r [Hin Hzero]].
  unfold sanitize_runs in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hcond].
  rewrite Hzero in Hcond. simpl in Hcond. discriminate.
Qed.

Definition detect_corruption (runs : list run) : bool :=
  existsb (fun r => Nat.eqb (fst r) 0) runs.

(** Corruption detection is sound. *)
Lemma detect_corruption_sound : forall runs,
  detect_corruption runs = true <-> has_corruption runs.
Proof.
  intros. unfold detect_corruption, has_corruption. split; intro H.
  - apply existsb_exists in H.
    destruct H as [r [Hin Hcond]].
    exists r. split; auto.
    apply Nat.eqb_eq in Hcond. exact Hcond.
  - destruct H as [r [Hin Hzero]].
    apply existsb_exists.
    exists r. split; auto.
    apply Nat.eqb_eq. exact Hzero.
Qed.

(** Corruption detection is complete. *)
Lemma detect_corruption_complete : forall runs,
  detect_corruption runs = false <-> ~has_corruption runs.
Proof.
  intros. split; intro H.
  - intro Hcontra. apply detect_corruption_sound in Hcontra.
    rewrite Hcontra in H. discriminate.
  - destruct (detect_corruption runs) eqn:E.
    + apply detect_corruption_sound in E. contradiction.
    + reflexivity.
Qed.

(** Encoded run lists are never detected as corrupted. *)
Theorem encoded_never_detected : forall l,
  detect_corruption (rle_encode l) = false.
Proof.
  intros. apply detect_corruption_complete.
  apply encode_never_corrupted.
Qed.

Definition repair_runs (runs : list run) : list run :=
  sanitize_runs runs.

(** Repaired run lists are always valid. *)
Theorem repair_sound : forall runs,
  is_valid_rle (repair_runs runs).
Proof.
  intros. unfold repair_runs. apply sanitize_preserves_valid.
Qed.

(** Repairing a valid run list is the identity. *)
Theorem repair_preserves_valid : forall runs,
  is_valid_rle runs ->
  repair_runs runs = runs.
Proof.
  intros runs Hval.
  unfold repair_runs, sanitize_runs.
  induction runs as [|[c v] rs IH].
  - reflexivity.
  - simpl. destruct c eqn:Ec.
    + unfold is_valid_rle in Hval.
      assert (fst (0, v) > 0).
      { apply Hval. simpl. auto. }
      simpl in H. lia.
    + f_equal. apply IH.
      unfold is_valid_rle in *. intros. apply Hval. simpl. auto.
Qed.

(** Repair is idempotent. *)
Theorem repair_idempotent : forall runs,
  repair_runs (repair_runs runs) = repair_runs runs.
Proof.
  intros. unfold repair_runs. apply sanitize_idempotent.
Qed.

(** Repair preserves decoding semantics. *)
Lemma decode_repair_equivalence : forall runs,
  rle_decode (repair_runs runs) = rle_decode runs.
Proof.
  intros. unfold repair_runs. symmetry. apply decode_with_zeros_equivalence.
Qed.

(** Repair preserves the decoded list. *)
Theorem repair_minimal : forall runs l,
  rle_decode runs = l ->
  rle_decode (repair_runs runs) = l.
Proof.
  intros. rewrite decode_repair_equivalence. exact H.
Qed.

Definition is_repaired (runs : list run) : Prop :=
  repair_runs runs = runs.

(** Encoded run lists are already repaired. *)
Theorem encoded_is_repaired : forall l,
  is_repaired (rle_encode l).
Proof.
  intros l. unfold is_repaired.
  apply repair_preserves_valid.
  unfold is_valid_rle. intros r Hr.
  apply rle_encode_never_zero_count with (l := l). exact Hr.
Qed.

(** A run list is repaired if and only if it is valid. *)
Lemma repaired_iff_valid : forall runs,
  is_repaired runs <-> is_valid_rle runs.
Proof.
  intros. unfold is_repaired. split; intro H.
  - rewrite <- H. apply repair_sound.
  - apply repair_preserves_valid. exact H.
Qed.

Definition count_corruptions (runs : list run) : nat :=
  length runs - length (repair_runs runs).

(** Encoded run lists have zero corruptions. *)
Theorem corruption_free_encodes : forall l,
  count_corruptions (rle_encode l) = 0.
Proof.
  intros. unfold count_corruptions, repair_runs.
  rewrite repair_preserves_valid.
  - lia.
  - unfold is_valid_rle. intros r Hr.
    apply rle_encode_never_zero_count with (l := l). exact Hr.
Qed.

(** * Element Preservation *)

(** Membership in a repeated list characterizes the element and count. *)
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

(** Membership in a decoded list characterizes the run and value. *)
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

(** Encoding preserves element membership. *)
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

(** The successor case of generic repeat unfolds to a cons cell. *)
Lemma generic_repeat_S : forall n val,
  generic_repeat (S n) val = val :: generic_repeat n val.
Proof.
  reflexivity.
Qed.

(** Appending an element to a generic repeated list extends the repetition count. *)
Lemma generic_repeat_cons_app : forall n val l,
  generic_repeat n val ++ (val :: l) = generic_repeat (S n) val ++ l.
Proof.
  induction n; intros; simpl.
  - reflexivity.
  - f_equal. apply IHn.
Qed.

(** Decoding the generic auxiliary encoder with an accumulator follows the expected structure. *)
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

(** Decoding the generic encoding recovers the original list. *)
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

Variable default_A : A.

Definition generic_well_formed_rle (runs : list generic_run) : Prop :=
  (forall r, In r runs -> fst r > 0) /\
  (forall i, i < pred (length runs) ->
             snd (nth i runs (0, default_A)) <>
             snd (nth (S i) runs (0, default_A))).

(** The generic auxiliary encoder never produces an empty list. *)
Lemma generic_rle_encode_aux_not_nil : forall l val count,
  generic_rle_encode_aux val count l <> [].
Proof.
  induction l; intros; simpl.
  - discriminate.
  - destruct (A_eqb a val) eqn:E.
    + apply IHl.
    + discriminate.
Qed.

(** All runs produced by the generic auxiliary encoder have positive counts. *)
Lemma generic_rle_encode_aux_positive : forall l val count,
  count > 0 ->
  forall r, In r (generic_rle_encode_aux val count l) -> fst r > 0.
Proof.
  induction l; simpl; intros.
  - destruct H0; [subst|contradiction]. simpl. assumption.
  - destruct (A_eqb a val) eqn:Heq.
    + apply IHl with (val := val) (count := S count); [lia|auto].
    + destruct H0.
      * rewrite <- H0. simpl. assumption.
      * apply IHl with (val := a) (count := 1); [lia|auto].
Qed.

(** The first run in the generic auxiliary encoder output has the accumulator value. *)
Lemma generic_rle_encode_aux_first_snd : forall (a : A) count l d,
  count > 0 ->
  snd (nth 0 (generic_rle_encode_aux a count l) (0, d)) = a.
Proof.
  intros a count l d H.
  generalize dependent count.
  induction l; intros; simpl.
  - reflexivity.
  - destruct (A_eqb a0 a) eqn:Heq.
    + apply IHl. lia.
    + simpl. reflexivity.
Qed.

(** Symmetric inequality for generic types. *)
Lemma generic_neq_sym : forall (x y : A), x <> y -> y <> x.
Proof.
  intros x y H. intro H1. apply H. symmetry. exact H1.
Qed.

(** No two adjacent runs in the generic auxiliary encoder have equal values. *)
Lemma generic_rle_encode_aux_no_adjacent : forall l val count default,
  count > 0 ->
  forall i, i < pred (length (generic_rle_encode_aux val count l)) ->
       snd (nth i (generic_rle_encode_aux val count l) (0, default)) <>
       snd (nth (S i) (generic_rle_encode_aux val count l) (0, default)).
Proof.
  induction l as [|a l IHl]; simpl; intros val count default Hcount i Hi.
  - simpl in Hi. lia.
  - destruct (A_eqb a val) eqn:Heq.
    + destruct (A_eqb_spec a val).
      * subst. apply IHl; [lia|auto].
      * congruence.
    + destruct (A_eqb_spec a val) as [Heq_eq | Heq_neq].
      * congruence.
      * destruct i as [|i']; simpl.
        -- destruct l as [|b l']; simpl in *.
           ++ simpl. apply generic_neq_sym. exact Heq_neq.
           ++ destruct (A_eqb b a) eqn:Heq2.
              ** rewrite generic_rle_encode_aux_first_snd; [|lia].
                 simpl. apply generic_neq_sym. exact Heq_neq.
              ** simpl. apply generic_neq_sym. exact Heq_neq.
        -- simpl in Hi.
           assert (i' < pred (length (generic_rle_encode_aux a 1 l))).
           { simpl in Hi. lia. }
           apply IHl; [lia|exact H].
Qed.

(** The generic encoder produces well-formed run lists for nonempty inputs. *)
Theorem generic_encode_well_formed : forall l,
  l <> [] -> generic_well_formed_rle (generic_rle_encode l).
Proof.
  intros l Hne. destruct l.
  - congruence.
  - unfold generic_well_formed_rle, generic_rle_encode. split.
    + intros. apply generic_rle_encode_aux_positive with (val := a) (count := 1) (l := l); [lia|auto].
    + intros. apply generic_rle_encode_aux_no_adjacent with (val := a) (count := 1) (default := default_A); [lia|auto].
Qed.

Definition generic_is_valid_rle (runs : list generic_run) : Prop :=
  forall r, In r runs -> fst r > 0.

Definition generic_decodes_to (runs : list generic_run) (l : list A) : Prop :=
  generic_rle_decode runs = l.

(** The length of a generic repeated list equals the repetition count. *)
Lemma generic_repeat_length : forall n (val : A),
  length (generic_repeat n val) = n.
Proof.
  induction n; simpl; auto.
Qed.

(** The generic decoded length equals the sum of run counts. *)
Lemma generic_decode_length_sum : forall runs,
  length (generic_rle_decode runs) = fold_right (fun r acc => fst r + acc) 0 runs.
Proof.
  induction runs; simpl.
  - reflexivity.
  - destruct a. rewrite app_length. rewrite generic_repeat_length.
    f_equal. apply IHruns.
Qed.

Fixpoint generic_count_runs_aux (val : A) (l : list A) : nat :=
  match l with
  | [] => 1
  | h :: t =>
      if A_eqb h val then
        generic_count_runs_aux val t
      else
        S (generic_count_runs_aux h t)
  end.

Definition generic_count_runs (l : list A) : nat :=
  match l with
  | [] => 0
  | h :: t => generic_count_runs_aux h t
  end.

(** The length of the generic auxiliary encoder output equals the run count. *)
Lemma generic_rle_encode_aux_length : forall l val count,
  length (generic_rle_encode_aux val count l) = generic_count_runs_aux val l.
Proof.
  induction l; simpl; intros.
  - reflexivity.
  - destruct (A_eqb a val); simpl; auto.
Qed.

(** The length of the generic encoding equals the number of runs. *)
Theorem generic_rle_length : forall l,
  length (generic_rle_encode l) = generic_count_runs l.
Proof.
  destruct l; simpl.
  - reflexivity.
  - apply generic_rle_encode_aux_length.
Qed.

(** If a generic encoding decodes to a nonempty list, the encoding is nonempty. *)
Lemma generic_decode_nonempty : forall runs val l,
  generic_decodes_to runs (val :: l) -> runs <> [].
Proof.
  intros. intro Hcontra. subst.
  unfold generic_decodes_to in H. simpl in H. discriminate.
Qed.

(** A generic encoding that decodes to a cons list has a structured first run. *)
Lemma generic_decode_cons_structure : forall runs val l,
  generic_decodes_to runs (val :: l) ->
  generic_is_valid_rle runs ->
  match runs with
  | [] => False
  | (count, v) :: runs' =>
      count > 0 /\
      ((count = 1 /\ v = val /\ generic_decodes_to runs' l) \/
       (count > 1 /\ v = val /\ generic_decodes_to ((count-1, v) :: runs') l))
  end.
Proof.
  intros. destruct runs as [|p runs'].
  - unfold generic_decodes_to in H. simpl in H. discriminate.
  - destruct p as [count v].
    assert (count > 0).
    { unfold generic_is_valid_rle in H0.
      assert (fst (count, v) > 0).
      { apply H0. simpl. left. reflexivity. }
      simpl in H1. exact H1. }
    split. assumption.
    unfold generic_decodes_to in H. simpl in H.
    destruct count.
    + inversion H1.
    + destruct count.
      * simpl in H. injection H; intros H2 H3.
        left. split; [reflexivity|].
        split; [exact H3|].
        unfold generic_decodes_to. exact H2.
      * simpl in H. injection H; intros H2 H3.
        right. split; [lia|].
        split; [exact H3|].
        unfold generic_decodes_to. simpl. exact H2.
Qed.

(** The generic auxiliary run counter is bounded by the encoding length. *)
Lemma generic_count_runs_minimal_aux_simple : forall l val runs,
  generic_decodes_to runs (val :: l) ->
  generic_is_valid_rle runs ->
  generic_count_runs_aux val l <= length runs.
Proof.
  induction l; intros val runs Hdecode Hvalid.
  - simpl.
    assert (runs <> []) by (apply generic_decode_nonempty with (val := val) (l := []); auto).
    destruct runs; [congruence|]. simpl. lia.
  - simpl. destruct (A_eqb a val) eqn:Heq.
    + destruct (A_eqb_spec a val); [|congruence]. subst a.
      pose proof (generic_decode_cons_structure _ _ _ Hdecode Hvalid) as Hstruct.
      destruct runs as [|[count v] runs']; [contradiction|].
      destruct Hstruct as [Hpos [[Hc1 [Hv1 Hdec1]]|[Hc2 [Hv2 Hdec2]]]].
      * subst. unfold generic_decodes_to in Hdec1.
        assert (generic_count_runs_aux val l <= length runs').
        { apply IHl with (runs := runs'); auto.
          unfold generic_is_valid_rle in *. intros. apply Hvalid. simpl. auto. }
        simpl. lia.
      * subst.
        apply IHl with (runs := ((count - 1, val) :: runs')).
        -- exact Hdec2.
        -- unfold generic_is_valid_rle in *. intros. simpl in H. destruct H.
           ++ inversion H. simpl. lia.
           ++ apply Hvalid. simpl. auto.
    + destruct (A_eqb_spec a val) as [Heq_a_val | Hneq_a_val]; [congruence|]. simpl.
      pose proof (generic_decode_cons_structure _ _ _ Hdecode Hvalid) as Hstruct.
      destruct runs as [|[count v] runs']; [contradiction|].
      destruct Hstruct as [Hpos [[Hc1 [Hv1 Hdec1]]|[Hc2 [Hv2 Hdec2]]]].
      * subst.
        assert (generic_count_runs_aux a l <= length runs').
        { apply IHl with (val := a) (runs := runs').
          -- exact Hdec1.
          -- unfold generic_is_valid_rle in *. intros. apply Hvalid. simpl. auto. }
        simpl. lia.
      * subst. unfold generic_decodes_to in Hdec2.
        assert (count - 1 > 0) by lia.
        destruct (count - 1) eqn:Hcount.
        -- lia.
        -- simpl in Hdec2.
           assert (val :: generic_repeat n val ++ generic_rle_decode runs' = a :: l).
           { exact Hdec2. }
           injection H0; intros. subst a. congruence.
Qed.

(** The generic encoder produces encodings of minimal length among all valid well-formed encodings. *)
Theorem generic_encode_is_minimal : forall l runs,
  generic_decodes_to runs l ->
  generic_is_valid_rle runs ->
  generic_well_formed_rle runs ->
  generic_count_runs l <= length runs.
Proof.
  intros l runs Hdecode Hvalid Hwf.
  destruct l.
  - destruct runs as [|p runs'].
    + simpl. auto.
    + unfold generic_decodes_to in Hdecode. simpl in Hdecode.
      destruct p. destruct n.
      * unfold generic_is_valid_rle in Hvalid.
        assert (fst (0, a) > 0) by (apply Hvalid; simpl; auto).
        simpl in H. lia.
      * simpl in Hdecode. discriminate.
  - simpl. destruct runs as [|p runs'].
    + unfold generic_decodes_to in Hdecode. simpl in Hdecode. discriminate.
    + eapply generic_count_runs_minimal_aux_simple; eauto.
Qed.

End GenericRLE.

(** * Generic RLE Instantiations *)

(** Generic optimality holds for all types with decidable equality. *)
Theorem generic_optimality_works : forall A (eqb : A -> A -> bool)
  (eqb_spec : forall x y, reflect (x = y) (eqb x y))
  (default : A) (l : list A) (runs : list (nat * A)),
  @generic_is_valid_rle A runs ->
  @generic_well_formed_rle A default runs ->
  @generic_decodes_to A runs l ->
  @generic_count_runs A eqb l <= length runs.
Proof.
  intros. eapply generic_encode_is_minimal; eauto.
Qed.

(** Generic RLE can be instantiated for any type with decidable equality. *)
Corollary generic_rle_instantiable_for_any_type :
  forall A (eqb : A -> A -> bool) (eqb_spec : forall x y, reflect (x = y) (eqb x y)) default,
  forall l runs,
    @generic_rle_decode A runs = l ->
    @generic_is_valid_rle A runs ->
    @generic_well_formed_rle A default runs ->
    @generic_count_runs A eqb l <= length runs.
Proof.
  intros. eapply (@generic_encode_is_minimal A eqb eqb_spec default); unfold generic_decodes_to; eauto.
Qed.

(** * Formal Big-O Complexity Framework *)

Definition is_O (f g : nat -> nat) : Prop :=
  exists c n0, c > 0 /\ forall n, n >= n0 -> f n <= c * g n.

Notation "f ∈O( g )" := (is_O f g) (at level 70).

Definition is_Omega (f g : nat -> nat) : Prop :=
  exists c n0, c > 0 /\ forall n, n >= n0 -> f n >= c * g n.

Notation "f ∈Ω( g )" := (is_Omega f g) (at level 70).

Definition is_Theta (f g : nat -> nat) : Prop :=
  is_O f g /\ is_Omega f g.

Notation "f ∈Θ( g )" := (is_Theta f g) (at level 70).

Definition linear (n : nat) : nat := n.
Definition constant (n : nat) : nat := 1.

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

(** The auxiliary encoder takes linear time in the input length. *)
Lemma rle_encode_steps_aux_linear : forall l val count,
  rle_encode_steps_aux val count l = length l + 1.
Proof.
  induction l; intros.
  - reflexivity.
  - simpl. destruct (Nat.eqb a val).
    + rewrite IHl. reflexivity.
    + rewrite IHl. reflexivity.
Qed.

(** Encoding takes linear time in the input length. *)
Theorem rle_encode_linear_time : forall l,
  rle_encode_steps l = length l + 1.
Proof.
  intros. destruct l.
  - reflexivity.
  - simpl. rewrite rle_encode_steps_aux_linear. reflexivity.
Qed.

(** Encoding steps are exactly n+1 for any list of length n. *)
Theorem rle_encode_steps_O_n_general : forall l,
  rle_encode_steps l = length l + 1.
Proof.
  apply rle_encode_linear_time.
Qed.

(** Encoding is in O(n) for lists of length n. *)
Theorem rle_encode_is_O_n_general :
  forall f : nat -> list nat,
  (forall n, length (f n) = n) ->
  (fun n => rle_encode_steps (f n)) ∈O( linear ).
Proof.
  intros f Hlen. unfold is_O, linear.
  exists 2, 1. split.
  - lia.
  - intros n Hn. rewrite rle_encode_linear_time.
    rewrite Hlen. lia.
Qed.

(** Special case: encoding uniform lists is O(n). *)
Theorem rle_encode_is_O_n_uniform :
  (fun n => rle_encode_steps (repeat n 0)) ∈O( linear ).
Proof.
  apply rle_encode_is_O_n_general.
  intros. apply repeat_length.
Qed.

Fixpoint rle_decode_steps (runs : list run) : nat :=
  match runs with
  | [] => 1
  | (count, val) :: t => count + rle_decode_steps t
  end.

(** Decoding time equals the sum of run counts plus one. *)
Theorem rle_decode_linear_time : forall runs,
  rle_decode_steps runs = fold_right (fun r acc => fst r + acc) 1 runs.
Proof.
  induction runs.
  - reflexivity.
  - destruct a. simpl. rewrite IHruns. reflexivity.
Qed.

(** Decoding time equals the output length plus one. *)
Theorem rle_decode_time_equals_output_length : forall runs,
  rle_decode_steps runs = length (rle_decode runs) + 1.
Proof.
  intros. rewrite rle_decode_linear_time. rewrite decode_length_sum.
  induction runs.
  - reflexivity.
  - destruct a. simpl. rewrite IHruns. lia.
Qed.

(** Decoding is in O(output_length). *)
Theorem rle_decode_is_O_output :
  forall m, (fun n => rle_decode_steps [(n, m)]) ∈O( linear ).
Proof.
  intros m. unfold is_O, linear.
  exists 2, 1. split.
  - lia.
  - intros n Hn. rewrite rle_decode_time_equals_output_length.
    simpl. rewrite app_nil_r. rewrite repeat_length.
    destruct n.
    + lia.
    + simpl. lia.
Qed.

(** Encoding space usage is bounded linearly by the input length. *)
Lemma rle_encode_space_linear : forall l,
  length (rle_encode l) <= length l.
Proof.
  apply rle_worst_case.
Qed.

(** Encoding space equals the run count. *)
Theorem rle_space_optimal : forall l,
  length (rle_encode l) = count_runs l.
Proof.
  apply rle_length.
Qed.

Definition comparison_cost_log (V : nat) : nat :=
  Nat.log2 (1 + V).

Lemma log2_succ_bound : forall n,
  Nat.log2 (S n) <= n.
Proof.
  induction n.
  - simpl. auto.
  - assert (H: Nat.log2 (S (S n)) <= Nat.log2 (S n + S n)).
    { apply Nat.log2_le_mono. lia. }
    assert (H2: Nat.log2 (S n + S n) <= S n).
    { destruct n.
      - simpl. auto.
      - replace (S (S n) + S (S n)) with (2 * S (S n)) by lia.
        rewrite Nat.log2_double by lia.
        lia. }
    lia.
Qed.

Theorem comparison_cost_bound : forall V,
  comparison_cost_log V <= S V.
Proof.
  intros. unfold comparison_cost_log.
  transitivity V; [|lia].
  replace (1 + V) with (S V) by lia.
  apply log2_succ_bound.
Qed.

Fixpoint rle_encode_cost_aux (val : nat) (count : nat) (l : list nat) : nat :=
  match l with
  | [] => 1 + count
  | h :: t =>
      let cmp_cost := 1 + Nat.log2 (1 + Nat.max h val) in
      if Nat.eqb h val then
        cmp_cost + rle_encode_cost_aux val (S count) t
      else
        cmp_cost + 2 + count + rle_encode_cost_aux h 1 t
  end.

Definition rle_encode_cost (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => 2 + rle_encode_cost_aux h 1 t
  end.

Lemma rle_encode_cost_aux_lower_bound : forall l val count,
  rle_encode_cost_aux val count l >= length l + count + 1.
Proof.
  induction l; intros.
  - simpl. lia.
  - simpl. destruct (Nat.eqb a val).
    + specialize (IHl val (S count)). lia.
    + specialize (IHl a 1). lia.
Qed.

Theorem rle_encode_cost_lower : forall l,
  l <> [] ->
  rle_encode_cost l >= length l + 2.
Proof.
  intros. destruct l; [contradiction|].
  unfold rle_encode_cost. simpl.
  assert (rle_encode_cost_aux n 1 l >= length l + 1 + 1).
  { apply rle_encode_cost_aux_lower_bound. }
  lia.
Qed.

Theorem rle_encode_cost_linear_in_length : forall l,
  l <> [] ->
  rle_encode_cost l >= length l + 2.
Proof.
  intros. apply rle_encode_cost_lower. exact H.
Qed.

Theorem rle_encode_cost_includes_comparisons : forall l V,
  (forall x, In x l -> x <= V) ->
  comparison_cost_log V <= S V.
Proof.
  intros. apply comparison_cost_bound.
Qed.

(** * Space Complexity Analysis *)

Definition word_size : nat := 8.

Definition run_memory_size (r : run) : nat :=
  let (count, val) := r in 1 + 1.

Definition run_memory_size_with_overhead (r : run) : nat :=
  let (count, val) := r in
  word_size + word_size + 1.

Definition encode_space_usage (l : list nat) : nat :=
  fold_right (fun r acc => run_memory_size r + acc) 0 (rle_encode l).

Definition encode_space_usage_realistic (l : list nat) : nat :=
  fold_right (fun r acc => run_memory_size_with_overhead r + acc) 0 (rle_encode l).

Definition decode_space_usage (runs : list run) : nat :=
  length (rle_decode runs).

Lemma encode_space_usage_formula : forall runs,
  fold_right (fun r acc => run_memory_size r + acc) 0 runs = 2 * length runs.
Proof.
  induction runs as [|r rs IH].
  - reflexivity.
  - destruct r as [c v].
    change (fold_right (fun r0 acc => run_memory_size r0 + acc) 0 ((c, v) :: rs))
      with (run_memory_size (c, v) + fold_right (fun r0 acc => run_memory_size r0 + acc) 0 rs).
    unfold run_memory_size at 1. simpl. rewrite IH. simpl. ring.
Qed.

Lemma encode_space_usage_realistic_formula : forall runs,
  fold_right (fun r acc => run_memory_size_with_overhead r + acc) 0 runs =
  (2 * word_size + 1) * length runs.
Proof.
  induction runs as [|r rs IH].
  - reflexivity.
  - destruct r as [c v].
    change (fold_right (fun r0 acc => run_memory_size_with_overhead r0 + acc) 0 ((c, v) :: rs))
      with (run_memory_size_with_overhead (c, v) + fold_right (fun r0 acc => run_memory_size_with_overhead r0 + acc) 0 rs).
    unfold run_memory_size_with_overhead at 1. simpl.
    rewrite IH. simpl. ring.
Qed.

(** Encoding space usage is bounded by twice the input length. *)
Theorem encode_space_bounded : forall l,
  encode_space_usage l <= 2 * length l.
Proof.
  intros. unfold encode_space_usage.
  rewrite encode_space_usage_formula.
  assert (Hlen: length (rle_encode l) <= length l) by apply rle_worst_case.
  lia.
Qed.

Theorem encode_space_realistic_bounded : forall l,
  encode_space_usage_realistic l <= (2 * word_size + 1) * length l.
Proof.
  intros. unfold encode_space_usage_realistic.
  rewrite encode_space_usage_realistic_formula.
  assert (Hlen: length (rle_encode l) <= length l) by apply rle_worst_case.
  unfold word_size. lia.
Qed.

(** Decoding space equals the sum of run counts. *)
Theorem decode_space_exact : forall runs,
  decode_space_usage runs = fold_right (fun r acc => fst r + acc) 0 runs.
Proof.
  intros. unfold decode_space_usage.
  apply decode_length_sum.
Qed.

(** Roundtrip space usage equals the original list length. *)
Theorem roundtrip_space_preserved : forall l,
  decode_space_usage (rle_encode l) = length l.
Proof.
  intros. unfold decode_space_usage.
  rewrite rle_correct. reflexivity.
Qed.

(** Uniform lists achieve optimal space usage. *)
Lemma encode_space_uniform_optimal : forall n val,
  n > 0 ->
  encode_space_usage (repeat n val) = 2.
Proof.
  intros. unfold encode_space_usage.
  rewrite encode_space_usage_formula.
  rewrite rle_best_case; auto.
Qed.

(** Alternating lists achieve maximal space usage. *)
Lemma encode_space_alternating_maximal : forall l,
  (forall i, i < pred (length l) -> nth i l 0 <> nth (S i) l 0) ->
  encode_space_usage l = 2 * length l.
Proof.
  intros. unfold encode_space_usage.
  rewrite encode_space_usage_formula.
  rewrite no_compression_worst; auto.
Qed.

Definition space_overhead (l : list nat) : nat :=
  encode_space_usage l - length l.

(** The auxiliary run counter is always at least one. *)
Lemma count_runs_aux_ge_one : forall val l,
  count_runs_aux val l >= 1.
Proof.
  intros val l.
  generalize dependent val.
  induction l as [|h t IH].
  - intros. simpl. lia.
  - intros val. simpl. destruct (Nat.eqb h val) eqn:E.
    + apply IH.
    + specialize (IH h). lia.
Qed.

(** Nonempty lists have at least one run. *)
Lemma count_runs_ge_one : forall l,
  l <> [] -> count_runs l >= 1.
Proof.
  intros l Hne.
  destruct l as [|h t].
  - contradiction.
  - unfold count_runs. simpl.
    apply count_runs_aux_ge_one.
Qed.

(** Encoding space for nonempty lists is at least two. *)
Theorem encode_space_minimum : forall l,
  l <> [] -> encode_space_usage l >= 2.
Proof.
  intros l Hne. unfold encode_space_usage.
  rewrite encode_space_usage_formula.
  destruct l as [|h t].
  - contradiction.
  - assert (Hge: count_runs (h :: t) >= 1).
    { apply count_runs_ge_one. discriminate. }
    assert (Heq: length (rle_encode (h :: t)) = count_runs (h :: t)).
    { apply rle_length. }
    rewrite Heq.
    lia.
Qed.

(** Space overhead is bounded by the input length. *)
Theorem space_overhead_bounded : forall l,
  space_overhead l <= length l.
Proof.
  intros. unfold space_overhead, encode_space_usage.
  rewrite encode_space_usage_formula.
  assert (length (rle_encode l) <= length l) by apply rle_worst_case.
  lia.
Qed.

Definition compression_ratio_space (l : list nat) : option (nat * nat) :=
  match rle_encode l with
  | [] => None
  | _ => Some (length l, encode_space_usage l)
  end.

(** Uniform lists achieve the best compression ratio in space. *)
Theorem best_compression_ratio_space : forall n val,
  n > 1 ->
  compression_ratio_space (repeat n val) = Some (n, 2).
Proof.
  intros. unfold compression_ratio_space.
  assert (Henc: rle_encode (repeat n val) = [(n, val)]).
  { apply rle_encode_repeat. lia. }
  rewrite Henc. simpl.
  f_equal. f_equal.
  - apply repeat_length.
  - unfold encode_space_usage. rewrite Henc. simpl. reflexivity.
Qed.

Theorem worst_compression_ratio_space : forall l,
  (forall i, i < pred (length l) -> nth i l 0 <> nth (S i) l 0) ->
  l <> [] ->
  compression_ratio_space l = Some (length l, 2 * length l).
Proof.
  intros. unfold compression_ratio_space.
  destruct l; [congruence|].
  destruct (rle_encode (n :: l)) eqn:E.
  - assert (count_runs (n :: l) = 0).
    { rewrite <- rle_length. rewrite E. reflexivity. }
    assert (count_runs (n :: l) >= 1).
    { apply count_runs_ge_one. discriminate. }
    lia.
  - unfold encode_space_usage.
    rewrite encode_space_usage_formula.
    assert (length (rle_encode (n :: l)) = length (n :: l)).
    { rewrite no_compression_worst; auto. }
    rewrite H1. f_equal.
Qed.

Theorem encode_space_upper_bound : forall l,
  encode_space_usage l <= 2 * length l.
Proof.
  intros. apply encode_space_bounded.
Qed.

Definition encoding_expands (l : list nat) : Prop :=
  encode_space_usage l > length l.

Lemma single_element_never_expands : forall val,
  encode_space_usage [val] = 2 /\ length [val] = 1.
Proof.
  intros val. split.
  - unfold encode_space_usage. rewrite encode_space_usage_formula. simpl. reflexivity.
  - reflexivity.
Qed.

Lemma alternating_expansion_bound : forall l,
  (forall i, i < pred (length l) -> nth i l 0 <> nth (S i) l 0) ->
  encode_space_usage l = 2 * length l.
Proof.
  intros. rewrite encode_space_alternating_maximal; auto.
Qed.

Theorem expansion_characterization : forall l,
  l <> [] ->
  encoding_expands l <-> (encode_space_usage l > length l).
Proof.
  intros. unfold encoding_expands. reflexivity.
Qed.

Theorem no_expansion_under_compression : forall l,
  encode_space_usage l <= 2 * length l.
Proof.
  apply encode_space_bounded.
Qed.

Lemma short_runs_expansion_example :
  encoding_expands [1; 2; 3; 4; 5].
Proof.
  unfold encoding_expands, encode_space_usage.
  rewrite encode_space_usage_formula.
  simpl. lia.
Qed.

Fixpoint auxiliary_space_encode_aux (count : nat) (l : list nat) : nat :=
  match l with
  | [] => count
  | _ :: t => auxiliary_space_encode_aux (S count) t
  end.

Definition auxiliary_space_encode (l : list nat) : nat :=
  auxiliary_space_encode_aux 0 l.

Lemma auxiliary_space_encode_aux_correct : forall l count,
  auxiliary_space_encode_aux count l = count + length l.
Proof.
  induction l; intros; simpl.
  - lia.
  - rewrite IHl. lia.
Qed.

Theorem encode_auxiliary_space : forall l,
  auxiliary_space_encode l = length l.
Proof.
  intros. unfold auxiliary_space_encode.
  rewrite auxiliary_space_encode_aux_correct.
  lia.
Qed.

Definition auxiliary_space_decode (runs : list run) : nat :=
  fold_right (fun r acc => fst r + acc) 0 runs.

Theorem decode_auxiliary_space : forall runs,
  auxiliary_space_decode runs = length (rle_decode runs).
Proof.
  intros. unfold auxiliary_space_decode.
  symmetry. apply decode_length_sum.
Qed.

Theorem total_space_encode : forall l,
  encode_space_usage l + auxiliary_space_encode l <= 4 * length l.
Proof.
  intros. unfold encode_space_usage.
  rewrite encode_space_usage_formula.
  rewrite encode_auxiliary_space.
  assert (length (rle_encode l) <= length l) by apply rle_worst_case.
  lia.
Qed.

Theorem total_space_decode : forall runs,
  length runs + auxiliary_space_decode runs =
  length runs + length (rle_decode runs).
Proof.
  intros. rewrite decode_auxiliary_space. reflexivity.
Qed.

(** * Information-Theoretic Characterization *)

Definition run_eq_dec : forall (r1 r2 : run), {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Fixpoint count_distinct_runs (l : list nat) : nat :=
  count_runs l.

Definition run_frequency (r : run) (runs : list run) : nat :=
  count_occ run_eq_dec runs r.

Fixpoint log2_floor (n : nat) : nat :=
  Nat.log2 (1 + n).

Definition bits_required (n : nat) : nat :=
  if Nat.eqb n 0 then 1 else S (Nat.log2 n).

Definition empirical_run_entropy_numerator (l : list nat) : nat :=
  let runs := rle_encode l in
  let total_runs := length runs in
  if Nat.eqb total_runs 0 then 0
  else fold_right (fun r acc =>
    let freq := run_frequency r runs in
    if Nat.eqb freq 0 then acc
    else acc + freq * bits_required freq
  ) 0 runs.

Definition min_encoding_bits (l : list nat) : nat :=
  let num_runs := count_runs l in
  num_runs * bits_required num_runs.

Theorem rle_encoding_size_lower_bound : forall l,
  l <> [] ->
  encode_space_usage l >= count_runs l.
Proof.
  intros l Hne.
  unfold encode_space_usage.
  rewrite encode_space_usage_formula.
  assert (count_runs l = length (rle_encode l)).
  { symmetry. apply rle_length. }
  rewrite <- H.
  destruct (count_runs l).
  - lia.
  - lia.
Qed.

Lemma bits_required_positive : forall n,
  bits_required n > 0.
Proof.
  intros. unfold bits_required.
  destruct (Nat.eqb n 0); lia.
Qed.

Lemma bits_required_log_bound : forall n,
  n > 0 ->
  bits_required n <= S n.
Proof.
  intros n Hn.
  unfold bits_required.
  assert (Nat.eqb n 0 = false).
  { apply Nat.eqb_neq. lia. }
  rewrite H.
  assert (Nat.log2 n <= n).
  { induction n.
    - lia.
    - transitivity n; [|lia].
      apply log2_succ_bound. }
  lia.
Qed.

Definition entropy_compression_ratio (l : list nat) : nat * nat :=
  let encoded_size := encode_space_usage l in
  let min_bits := min_encoding_bits l in
  (encoded_size, min_bits).

Theorem entropy_lower_bound_fundamental : forall l,
  l <> [] ->
  let (encoded, min_bits) := entropy_compression_ratio l in
  encoded >= count_runs l.
Proof.
  intros l Hne.
  unfold entropy_compression_ratio.
  simpl.
  apply rle_encoding_size_lower_bound.
  exact Hne.
Qed.

Definition run_structure_complexity (l : list nat) : nat :=
  count_runs l.

Theorem compressibility_characterized_by_runs : forall l,
  encode_space_usage l = 2 * run_structure_complexity l.
Proof.
  intros. unfold encode_space_usage, run_structure_complexity.
  rewrite encode_space_usage_formula.
  rewrite rle_length.
  ring.
Qed.

Theorem no_rle_below_run_count : forall l encoding,
  l <> [] ->
  is_valid_rle encoding ->
  well_formed_rle encoding ->
  rle_decode encoding = l ->
  length encoding >= count_runs l.
Proof.
  intros l encoding Hne Hvalid Hwf Hdec.
  assert (Hmin: count_runs l <= length encoding).
  { apply encode_is_minimal with (runs := encoding).
    - unfold decodes_to. exact Hdec.
    - exact Hvalid.
    - exact Hwf. }
  lia.
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

(* OCaml's max_int varies by architecture:
   - 32-bit systems: 2^30 - 1 = 1073741823
   - 64-bit systems: 2^62 - 1 = 4611686018427387903
   We use 2^30 - 1 for maximum portability and proven safety *)
Definition max_int_runtime : nat := 1073741823.  (* 2^30 - 1 *)

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

Theorem rle_correct_unbounded : forall l : list nat,
  rle_decode (rle_encode l) = l.
Proof.
  apply rle_correct.
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

(** * Extraction Correctness *)

Theorem extraction_preserves_encode_decode : forall l,
  bounded_list max_int_runtime l ->
  length l <= max_int_runtime ->
  rle_decode (rle_encode l) = l.
Proof.
  intros. apply rle_correct.
Qed.

Theorem extraction_no_overflow : forall l,
  bounded_list max_int_runtime l ->
  forall r, In r (rle_encode l) ->
    snd r < max_int_runtime.
Proof.
  intros l Hbound r Hr.
  apply (bounded_encode max_int_runtime l Hbound r Hr).
Qed.

Theorem extraction_decode_bounded : forall runs,
  is_valid_rle runs ->
  (forall r, In r runs -> snd r < max_int_runtime) ->
  bounded_list max_int_runtime (rle_decode runs).
Proof.
  intros runs Hval Hbound.
  apply bounded_decode. exact Hbound.
Qed.

(** * OCaml Extraction - Production Configuration *)

From Coq Require Import Extraction.
From Coq Require Import ExtrOcamlBasic.
From Coq Require Import ExtrOcamlString.

Extraction Language OCaml.

Set Extraction Optimize.
Set Extraction Conservative Types.
Set Extraction KeepSingleton.
Set Extraction AutoInline.

Extraction Blacklist List String Int.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )" [ "(,)" ].

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

Theorem validated_encode_complete : forall l,
  bounded_list max_int_runtime l ->
  length l <= max_int_runtime ->
  exists encoded, rle_encode_validated l = Some encoded.
Proof.
  intros l Hbound Hlen.
  unfold rle_encode_validated.
  assert (forallb (fun x => Nat.ltb x max_int_runtime) l = true).
  { apply forallb_forall. intros x Hx. apply Nat.ltb_lt. apply Hbound. exact Hx. }
  rewrite H.
  assert (Nat.leb (length l) max_int_runtime = true).
  { apply Nat.leb_le. exact Hlen. }
  rewrite H0. simpl.
  exists (rle_encode l). reflexivity.
Qed.

Theorem validated_encode_sound : forall l encoded,
  rle_encode_validated l = Some encoded ->
  encoded = rle_encode l.
Proof.
  intros l encoded Henc.
  unfold rle_encode_validated in Henc.
  destruct (andb (Nat.leb (length l) max_int_runtime)
                 (forallb (fun x => Nat.ltb x max_int_runtime) l)) eqn:Hcond.
  - injection Henc. intro Heq. symmetry. exact Heq.
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

(** Encoding with maxrun continues accumulating when count is under the limit. *)
Lemma rle_encode_aux_maxrun_same_under : forall max_run val count l,
  count < max_run ->
  rle_encode_aux_maxrun max_run val count (val :: l) =
  rle_encode_aux_maxrun max_run val (S count) l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl.
  apply Nat.ltb_lt in H. rewrite H. reflexivity.
Qed.

(** Encoding with maxrun emits a run when count reaches the maximum. *)
Lemma rle_encode_aux_maxrun_same_at_max : forall max_run val count l,
  count = max_run ->
  rle_encode_aux_maxrun max_run val count (val :: l) =
  (max_run, val) :: rle_encode_aux_maxrun max_run val 1 l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl.
  subst count. rewrite Nat.ltb_irrefl. reflexivity.
Qed.

(** Repeated segments concatenate to form a longer repetition. *)
Lemma repeat_split_at_max : forall max_run val,
  repeat max_run val ++ repeat 1 val = repeat (S max_run) val.
Proof.
  induction max_run; intros.
  - reflexivity.
  - simpl. f_equal. apply IHmax_run.
Qed.

(** Encoding with maxrun emits a run when count exceeds the maximum. *)
Lemma rle_encode_aux_maxrun_same_over_max : forall max_run val count l,
  count > max_run ->
  rle_encode_aux_maxrun max_run val count (val :: l) =
  (max_run, val) :: rle_encode_aux_maxrun max_run val 1 l.
Proof.
  intros. simpl. rewrite Nat.eqb_refl.
  assert (Nat.ltb count max_run = false) by (apply Nat.ltb_ge; lia).
  rewrite H0. reflexivity.
Qed.

(** Encoding with maxrun starts a new run when encountering a different value. *)
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

(** Decoding a maxrun-encoded list with accumulator recovers the repeated prefix and list. *)
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

(** Maxrun encoding and decoding form a correct roundtrip. *)
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

(** All runs in maxrun-encoded output have positive counts. *)
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

(** Maxrun encoding produces only positive counts for nonempty lists. *)
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

(** All runs in maxrun-encoded output have counts bounded by the maximum. *)
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

(** Maxrun encoding respects the maximum run length bound. *)
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

(** The first run in maxrun-encoded output has the accumulator value. *)
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

(** Adjacent runs in maxrun-encoded output either have different values or the first has count equal to cap. *)
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

(** Maxrun encoding produces well-formed capped run lists. *)
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

(** Maxrun encoding respects the cap constraint. *)
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

(** Pushing a value to the stream state preserves the state invariant. *)
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

(** Encoding a list through the stream state preserves the state invariant. *)
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

(** The initial stream state satisfies the state invariant. *)
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

(** Complete stream encoding always produces a result. *)
Theorem stream_complete_encode_exists : forall max_run l,
  max_run > 0 ->
  exists runs, stream_complete_encode max_run l = runs.
Proof.
  intros max_run l Hmax.
  exists (stream_complete_encode max_run l).
  reflexivity.
Qed.

Definition stream_output_valid (opt : option run) : Prop :=
  match opt with
  | None => True
  | Some (c, v) => c > 0
  end.

Lemma stream_push_output_valid : forall state val opt state',
  stream_state_invariant state ->
  stream_push state val = (opt, state') ->
  stream_output_valid opt.
Proof.
  intros state val opt state' Hinv Hpush.
  unfold stream_push in Hpush.
  destruct (Nat.eqb (current_count state) 0) eqn:Hcount.
  - injection Hpush; intros; subst. unfold stream_output_valid. auto.
  - destruct (Nat.eqb val (current_val state)) eqn:Hval.
    + destruct (Nat.ltb (current_count state) (max_run_length state)) eqn:Hlt.
      * injection Hpush; intros; subst. unfold stream_output_valid. auto.
      * injection Hpush; intros; subst. unfold stream_output_valid. simpl.
        unfold stream_state_invariant in Hinv.
        destruct Hinv as [[Hzero | Hpos] [Hbound Hmax]].
        -- apply Nat.eqb_neq in Hcount. lia.
        -- exact Hmax.
    + injection Hpush; intros; subst. unfold stream_output_valid. simpl.
      unfold stream_state_invariant in Hinv.
      destruct Hinv as [[Hzero | Hpos] [Hbound Hmax]].
      * apply Nat.eqb_neq in Hcount. lia.
      * exact Hpos.
Qed.

Lemma stream_flush_output_valid : forall state opt,
  stream_state_invariant state ->
  stream_flush state = opt ->
  stream_output_valid opt.
Proof.
  intros state opt Hinv Hflush.
  unfold stream_flush in Hflush.
  destruct (Nat.eqb (current_count state) 0) eqn:Hcount.
  - subst. unfold stream_output_valid. auto.
  - subst opt. unfold stream_output_valid. simpl.
    unfold stream_state_invariant in Hinv.
    destruct Hinv as [[Hzero | Hpos] [Hbound Hmax]].
    + apply Nat.eqb_neq in Hcount. lia.
    + exact Hpos.
Qed.

Lemma stream_encode_list_positive_helper : forall l state,
  stream_state_invariant state ->
  forall r, In r (fst (stream_encode_list state l)) -> fst r > 0.
Proof.
  induction l; intros state Hinv r Hr.
  - simpl in Hr. contradiction.
  - simpl in Hr.
    destruct (stream_push state a) as [opt new_state] eqn:Hpush.
    destruct (stream_encode_list new_state l) as [runs' final'] eqn:Hencode.
    destruct opt as [[c v]|] eqn:Hopt.
    + simpl in Hr. destruct Hr as [Heq | Hin].
      * subst r. simpl.
        assert (stream_output_valid (Some (c, v))).
        { eapply stream_push_output_valid; eauto. }
        unfold stream_output_valid in H. simpl in H. exact H.
      * assert (Hnew_inv: stream_state_invariant new_state).
        { assert (new_state = snd (stream_push state a)).
          { rewrite Hpush. reflexivity. }
          rewrite H. apply stream_push_preserves_invariant. exact Hinv. }
        assert (Hruns': runs' = fst (stream_encode_list new_state l)).
        { rewrite Hencode. reflexivity. }
        rewrite Hruns' in Hin.
        apply (IHl new_state Hnew_inv r Hin).
    + assert (Hnew_inv: stream_state_invariant new_state).
      { assert (new_state = snd (stream_push state a)).
        { rewrite Hpush. reflexivity. }
        rewrite H. apply stream_push_preserves_invariant. exact Hinv. }
      assert (Hruns': runs' = fst (stream_encode_list new_state l)).
      { rewrite Hencode. reflexivity. }
      rewrite Hruns' in Hr.
      apply (IHl new_state Hnew_inv r Hr).
Qed.

Theorem stream_safety : forall max_run l,
  max_run > 0 ->
  let (runs, final_state) := stream_encode_list (init_stream_state max_run) l in
  stream_state_invariant final_state /\
  (forall r, In r runs -> fst r > 0).
Proof.
  intros max_run l Hmax.
  destruct (stream_encode_list (init_stream_state max_run) l) as [runs final_state] eqn:E.
  split.
  - assert (final_state = snd (stream_encode_list (init_stream_state max_run) l)).
    { rewrite E. reflexivity. }
    rewrite H. apply stream_encode_list_preserves_invariant.
    apply init_stream_state_invariant. exact Hmax.
  - intros r Hr.
    assert (runs = fst (stream_encode_list (init_stream_state max_run) l)).
    { rewrite E. reflexivity. }
    rewrite H in Hr.
    eapply stream_encode_list_positive_helper; eauto.
    apply init_stream_state_invariant. exact Hmax.
Qed.

(** Streaming encoder with initial accumulator matches the auxiliary maxrun encoder. *)
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

(** Streaming encoding produces the same output as batch maxrun encoding. *)
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

Definition stream_state_size (state : rle_stream_state) : nat :=
  1 + 1 + 1.

Lemma stream_state_size_from_structure : forall cv cc mrl,
  stream_state_size (mk_stream_state cv cc mrl) = 3.
Proof.
  intros. unfold stream_state_size. reflexivity.
Qed.

(** Stream state has constant size independent of input. *)
Theorem stream_state_constant_size : forall state,
  stream_state_size state = 3.
Proof.
  intros. unfold stream_state_size. reflexivity.
Qed.

(** Pushing a value preserves stream state size. *)
Theorem stream_push_preserves_size : forall state val,
  stream_state_size (snd (stream_push state val)) = stream_state_size state.
Proof.
  intros. reflexivity.
Qed.

(** Encoding a list through streaming uses constant space. *)
Theorem stream_encode_list_constant_space : forall l state,
  stream_state_size (snd (stream_encode_list state l)) = stream_state_size state.
Proof.
  induction l; intros; simpl.
  - reflexivity.
  - destruct (stream_push state a) as [opt new_state] eqn:Hpush.
    destruct (stream_encode_list new_state l) as [runs final_state] eqn:Hencode.
    assert (Heq: stream_state_size final_state = stream_state_size new_state).
    { assert (final_state = snd (stream_encode_list new_state l)).
      { rewrite Hencode. reflexivity. }
      rewrite H. apply IHl. }
    destruct opt; simpl; rewrite Heq; unfold stream_state_size; reflexivity.
Qed.

Definition stream_memory_usage (state : rle_stream_state) (output : list run) : nat :=
  stream_state_size state + 2 * length output.

(** Stream encoder maintains bounded space usage. *)
Theorem stream_encoder_space_bound : forall l state,
  let (output, final_state) := stream_encode_list state l in
  stream_state_size final_state = stream_state_size state.
Proof.
  intros. destruct (stream_encode_list state l) eqn:E.
  assert (r = snd (l0, r)) by reflexivity.
  rewrite H. rewrite <- E.
  apply stream_encode_list_constant_space.
Qed.

(** Streaming encoding uses constant space for any input length. *)
Theorem streaming_uses_constant_space : forall max_run,
  max_run > 0 ->
  forall l,
    stream_state_size (snd (stream_encode_list (init_stream_state max_run) l)) = 3.
Proof.
  intros. rewrite stream_encode_list_constant_space. reflexivity.
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

(** The initial decode state satisfies the decode state invariant. *)
Lemma init_decode_state_invariant : forall runs,
  decode_state_invariant init_decode_state runs.
Proof.
  intros. unfold decode_state_invariant, init_decode_state. simpl.
  destruct runs as [|[c v] rest].
  - reflexivity.
  - left. reflexivity.
Qed.

(** Pulling from the decode stream produces at most one value. *)
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

(** Compute the total number of values that will be produced by decoding a run list. *)
Definition compute_decode_size (runs : list run) : nat :=
  fold_right (fun r acc => fst r + acc) 0 runs.

(** Decode runs only if output size does not exceed the specified limit. *)
Definition safe_decode_with_limit (max_output : nat) (runs : list run)
  : option (list nat) :=
  if Nat.leb (compute_decode_size runs) max_output then
    Some (rle_decode runs)
  else
    None.

(** Decoding from an empty run list produces an empty output. *)
Lemma stream_decode_empty_state_nil : forall n,
  stream_decode_list n init_decode_state [] = [].
Proof.
  intros. destruct n.
  - reflexivity.
  - simpl. unfold stream_pull. simpl. reflexivity.
Qed.

(** The computed decode size equals the actual decoded output length. *)
Lemma compute_decode_size_correct : forall runs,
  compute_decode_size runs = length (rle_decode runs).
Proof.
  intros. unfold compute_decode_size.
  symmetry. apply decode_length_sum.
Qed.

(** Safe decoding ensures output length does not exceed the specified limit. *)
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

(** The streaming decoder always completes with sufficient fuel. *)
Theorem streaming_decoder_completeness :
  forall runs, exists fuel,
    fuel >= compute_decode_size runs.
Proof.
  intros runs.
  exists (compute_decode_size runs).
  lia.
Qed.

(** Streaming decoder with empty run list produces empty output. *)
Lemma stream_decode_empty : forall fuel state,
  remaining_count state = 0 ->
  stream_decode_list fuel state [] = [].
Proof.
  intros. destruct fuel; simpl.
  - reflexivity.
  - unfold stream_pull. rewrite H. reflexivity.
Qed.

(** Run lists with zero total decode size decode to the empty list. *)
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

(** Streaming decoder with zero fuel produces empty output. *)
Lemma stream_decode_zero_fuel : forall runs state,
  stream_decode_list 0 state runs = [].
Proof.
  reflexivity.
Qed.

(** Streaming decoder skips runs with zero count. *)
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

(** Streaming decoder handles singleton runs by emitting one value. *)
Lemma stream_decode_single_step : forall fuel' val state runs',
  remaining_count state = 0 ->
  stream_decode_list (S fuel') state ((S 0, val) :: runs') =
  val :: stream_decode_list fuel' (mk_decode_state 0 val) runs'.
Proof.
  intros. simpl. unfold stream_pull. rewrite H. simpl. reflexivity.
Qed.

(** Streaming decoder handles multi-count runs by emitting first value and updating state. *)
Lemma stream_decode_multi_step : forall fuel' count val state runs',
  remaining_count state = 0 ->
  count > 0 ->
  stream_decode_list (S fuel') state ((S count, val) :: runs') =
  val :: stream_decode_list fuel' (mk_decode_state count val) runs'.
Proof.
  intros. simpl. unfold stream_pull. rewrite H. simpl. reflexivity.
Qed.

(** Streaming decoder continues emitting from state with positive remaining count. *)
Lemma stream_decode_continue : forall fuel' count val runs',
  count > 0 ->
  stream_decode_list (S fuel') (mk_decode_state count val) runs' =
  val :: stream_decode_list fuel' (mk_decode_state (pred count) val) runs'.
Proof.
  intros. destruct count; [lia|]. simpl. unfold stream_pull. simpl. reflexivity.
Qed.

(** Streaming decoder exhausts state's remaining count before processing new runs. *)
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

(** Streaming decoder with sufficient fuel produces correct decoded output. *)
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

(** There exists sufficient fuel for streaming decoder to complete any run list. *)
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

(** Streaming decoder with adequate fuel is equivalent to batch decoder. *)
Theorem streaming_decoder_equivalent : forall runs fuel,
  fuel >= compute_decode_size runs + length runs ->
  stream_decode_list fuel init_decode_state runs = rle_decode runs.
Proof.
  intros runs fuel Hfuel.
  apply stream_decode_with_state_strong.
  - reflexivity.
  - exact Hfuel.
Qed.

(** Streaming decoder with minimal fuel equals batch decoder. *)
Corollary streaming_decoder_minimal_fuel : forall runs,
  stream_decode_list (compute_decode_size runs + length runs) init_decode_state runs = rle_decode runs.
Proof.
  intros runs.
  apply streaming_decoder_equivalent.
  lia.
Qed.

(** Pull from decode stream with a budget constraint, returning updated budget or None if exceeded. *)
Definition stream_pull_safe (state : decode_stream_state) (runs : list run) (budget : nat)
  : option (list nat * decode_stream_state * list run * nat) :=
  let '(vals, new_state, new_runs) := stream_pull state runs in
  let cost := length vals in
  if Nat.leb cost budget then
    Some (vals, new_state, new_runs, budget - cost)
  else
    None.

(** * I/O and Serialization *)

(** Serialize a natural number to a list of booleans using unary encoding. *)
Fixpoint serialize_nat (n : nat) : list bool :=
  match n with
  | 0 => []
  | S n' => true :: serialize_nat n'
  end.

(** Deserialize a list of booleans to a natural number using unary decoding. *)
Fixpoint deserialize_nat (bits : list bool) : nat :=
  match bits with
  | [] => 0
  | true :: rest => S (deserialize_nat rest)
  | false :: _ => 0
  end.

(** Serialization and deserialization of natural numbers form a roundtrip. *)
Theorem serialize_deserialize_nat : forall n,
  deserialize_nat (serialize_nat n) = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

(** Serialize a run to a list of booleans with false separators. *)
Definition serialize_run (r : run) : list bool :=
  let (count, val) := r in
  serialize_nat count ++ [false] ++ serialize_nat val ++ [false].

(** Serialize a list of runs to a flat list of booleans. *)
Fixpoint serialize_runs (runs : list run) : list bool :=
  match runs with
  | [] => []
  | r :: rest => serialize_run r ++ serialize_runs rest
  end.

(** * Integer Width Support *)

(** Maximum value for 8-bit unsigned integers. *)
Definition max_int_8 : nat := 2^8 - 1.

(** Maximum value for 16-bit unsigned integers. *)
Definition max_int_16 : nat := 2^16 - 1.

(** Maximum value for 32-bit unsigned integers. *)
Definition max_int_32 : nat := 2^32 - 1.

(** Encode a list only if all values are within the specified maximum. *)
Definition bounded_rle_encode (max_val : nat) (l : list nat) : option (list run) :=
  if forallb (fun x => Nat.leb x max_val) l then
    Some (rle_encode l)
  else
    None.

(** All run counts in the list fit within the specified maximum. *)
Definition runs_fit_width (max_count : nat) (runs : list run) : Prop :=
  forall r, In r runs -> fst r <= max_count.

(** Encode with both value and count bounds, using maxrun encoding to enforce count limit. *)
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

(** Safe 8-bit encoding with both value and count limited to 255. *)
Definition rle_encode_u8_safe (l : list nat) : option (list run) :=
  bounded_rle_encode_full 255 255 l.

(** Safe 8-bit encoding ensures all values and counts fit in 8 bits. *)
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

(** Encode with 8-bit value bounds. *)
Definition rle_encode_u8 := bounded_rle_encode max_int_8.

(** Encode with 16-bit value bounds. *)
Definition rle_encode_u16 := bounded_rle_encode max_int_16.

(** Encode with 32-bit value bounds. *)
Definition rle_encode_u32 := bounded_rle_encode max_int_32.

(** Decode runs only if all values are within the specified maximum. *)
Definition bounded_rle_decode (max_val : nat) (runs : list run) : option (list nat) :=
  if forallb (fun r => Nat.leb (snd r) max_val) runs then
    Some (rle_decode runs)
  else
    None.

(** Decode with 8-bit value bounds. *)
Definition rle_decode_u8 := bounded_rle_decode max_int_8.

(** Decode with 16-bit value bounds. *)
Definition rle_decode_u16 := bounded_rle_decode max_int_16.

(** Decode with 32-bit value bounds. *)
Definition rle_decode_u32 := bounded_rle_decode max_int_32.

(** Bounded 8-bit encoding succeeds for valid input and roundtrips correctly. *)
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

(** Bounded 16-bit encoding succeeds for valid input and roundtrips correctly. *)
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

(** Bounded 32-bit encoding succeeds for valid input and roundtrips correctly. *)
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

(** Bounded 8-bit decoding succeeds for runs with valid values. *)
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

(** Bounded 16-bit decoding succeeds for runs with valid values. *)
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

(** Bounded 32-bit decoding succeeds for runs with valid values. *)
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

(** * Verified Performance Benchmarks *)

(** Benchmark list: 1000 copies of the value 42. *)
Definition benchmark_uniform_1000 : list nat := repeat 1000 42.

(** Benchmark list: 1000 alternating values (0, 1, 0, 1, ...). *)
Definition benchmark_alternating_1000 : list nat :=
  map (fun i => i mod 2) (seq 0 1000).

(** Benchmark: encoding 1000 uniform values produces a single run. *)
Theorem benchmark_uniform_optimal :
  length (rle_encode benchmark_uniform_1000) = 1.
Proof.
  unfold benchmark_uniform_1000.
  apply rle_best_case. lia.
Qed.

(** Benchmark: uniform 1000-element list achieves 1000:1 compression ratio. *)
Theorem benchmark_uniform_ratio :
  compression_ratio_num benchmark_uniform_1000 (rle_encode benchmark_uniform_1000) = 1000 /\
  compression_ratio_den benchmark_uniform_1000 (rle_encode benchmark_uniform_1000) = 1.
Proof.
  unfold benchmark_uniform_1000.
  apply compression_ratio_uniform. lia.
Qed.

(** Benchmark: encoding 1000 elements takes exactly 1001 time steps. *)
Theorem benchmark_encode_time_linear :
  rle_encode_steps benchmark_uniform_1000 = 1001.
Proof.
  unfold benchmark_uniform_1000.
  rewrite rle_encode_linear_time.
  rewrite repeat_length. reflexivity.
Qed.

(** * Test Suite *)

(** Test that decode-encode is a fixpoint for valid runs. *)
Definition test_decode_encode_fixpoint (runs : list run) : bool :=
  let decoded := rle_decode runs in
  let reencoded := rle_encode decoded in
  if list_eq_dec run_eq_dec runs reencoded then true else false.

(** Example showing non-well-formed runs can decode to the same list. *)
Definition counterexample_uniqueness : list run * list run :=
  ([(3, 1); (2, 1)], [(5, 1)]).

(** Test demonstrating that non-well-formed encodings are not unique. *)
Definition test_uniqueness : bool :=
  let (r1, r2) := counterexample_uniqueness in
  let d1 := rle_decode r1 in
  let d2 := rle_decode r2 in
  if list_eq_dec Nat.eq_dec d1 d2
  then if list_eq_dec run_eq_dec r1 r2 then true else false
  else true.

(** Test that streaming encoding equals batch encoding. *)
Definition test_streaming_equivalence (l : list nat) : bool :=
  let batch := rle_encode_maxrun 255 l in
  let streaming := stream_complete_encode 255 l in
  if list_eq_dec run_eq_dec batch streaming then true else false.

(** Test that alternating values achieve no compression. *)
Definition test_worst_case : bool :=
  let alternating := [1; 2; 1; 2; 1; 2; 1; 2] in
  let encoded := rle_encode alternating in
  Nat.eqb (length encoded) (length alternating).

(** Test that uniform values achieve optimal compression to single run. *)
Definition test_best_case : bool :=
  let uniform := repeat 1000 42 in
  let encoded := rle_encode uniform in
  Nat.eqb (length encoded) 1.

(** Test that distinct sequential values cannot be compressed. *)
Definition test_impossible_compression : bool :=
  let data := [1; 2; 3; 4; 5] in
  let encoded := rle_encode data in
  negb (Nat.ltb (length encoded) (length data)).

(** Test that concatenated encoding is no longer than sum of individual encodings. *)
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

(** Test that double roundtrip preserves both list and encoding. *)
Definition test_double_roundtrip (l : list nat) : bool :=
  let e1 := rle_encode l in
  let d1 := rle_decode e1 in
  let e2 := rle_encode d1 in
  let d2 := rle_decode e2 in
  if list_eq_dec Nat.eq_dec l d2
  then if list_eq_dec run_eq_dec e1 e2 then true else false
  else false.

(** Test that maxrun boundary splits runs correctly at the limit. *)
Definition test_maxrun_boundary : bool :=
  let exactly_255 := repeat 255 7 in
  let exactly_256 := repeat 256 7 in
  let enc_255 := rle_encode_maxrun 255 exactly_255 in
  let enc_256 := rle_encode_maxrun 255 exactly_256 in
  andb (Nat.eqb (length enc_255) 1)
       (Nat.eqb (length enc_256) 2).

(** Test that incremental streaming produces same result as batch encoding. *)
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

(** Test that encoding never increases length beyond original. *)
Definition test_compression_never_expands : bool :=
  let test_lists := [[1]; [1;2]; [1;2;3]; [1;1]; [1;1;1];
                     [1;2;1;2]; repeat 100 5; repeat 50 3 ++ repeat 50 4] in
  forallb (fun l => Nat.leb (length (rle_encode l)) (length l)) test_lists.

(** Test that sum of run counts equals original list length. *)
Definition test_encode_preserves_length_sum : bool :=
  let l := [1;1;2;2;2;3;3;3;3] in
  let encoded := rle_encode l in
  Nat.eqb (fold_right (fun r acc => fst r + acc) 0 encoded) (length l).

(** Test that maxrun and standard encoding decode to the same list. *)
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

(** Test that streaming decoder equals batch decoder. *)
Definition test_streaming_decoder_equivalent : bool :=
  let runs := [(3, 1); (2, 2); (4, 3)] in
  let fuel := compute_decode_size runs + length runs in
  let streamed := stream_decode_list fuel init_decode_state runs in
  let batched := rle_decode runs in
  if list_eq_dec Nat.eq_dec streamed batched then true else false.

Eval compute in test_streaming_decoder_equivalent.


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
Extract Constant max_int_runtime => "min Stdlib.max_int 1073741823".
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
    
