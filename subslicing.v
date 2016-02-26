Require Import Omega.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Subslicing.

Variable A:Type.
Implicit Type l:list A.

Definition subslice n m l :=
  skipn n (firstn m l).

Lemma skipn_nil : forall n,
  @skipn A n [] = [].
Proof.
  induction n; cbn; auto.
Qed.

Lemma firstn_nil : forall n,
  @firstn A n [] = [].
Proof.
  induction n; cbn; auto.
Qed.

Lemma subslice_nil : forall n m,
  subslice n m [] = [].
Proof.
  unfold subslice; intros.
  rewrite firstn_nil; rewrite skipn_nil; auto.
Qed.

Hint Rewrite skipn_nil firstn_nil subslice_nil : subslice.

Section ReverseDefinition.

Definition subslice' n m l :=
  firstn (m - n) (skipn n l).

Lemma subslice'_nil : forall n m,
  subslice' n m [] = [].
Proof.
  unfold subslice'; intros;
  autorewrite with subslice; auto.
Qed.

Theorem subslice'_correct : forall l n m,
  subslice n m l = subslice' n m l.
Proof.
  induction l; intros; cbn; auto.
  rewrite subslice_nil; rewrite subslice'_nil; auto.
  destruct n, m; cbn; auto.
  apply IHl.
Qed.

End ReverseDefinition.

Ltac inductive_case :=
    match goal with
    | [ H: forall _, _ |- _ ] =>
      rewrite H by (auto; omega)
    end.

Ltac dispatch :=
  let dispatcher :=
    (intros; cbn in *; subst;
    autorewrite with subslice in *;
    try inductive_case;
    auto;
    try omega) in
  dispatcher; try solve [ unfold subslice; dispatcher ].

Ltac induct a :=
  induction a; dispatch;
    try solve [
     repeat match goal with
     | [ |- context[firstn ?n (_ :: _)] ] =>
      destruct n; dispatch
     | [ |- context[skipn ?n (_ :: _)] ] =>
      destruct n; dispatch
    end ].

Hint Extern 4 (_ <= _) => abstract omega.

Theorem firstn_oob : forall l n,
  n = 0 ->
  firstn n l = [].
Proof.
  dispatch.
Qed.

Theorem skipn_oob : forall l n,
  n >= length l ->
  skipn n l = [].
Proof.
  induct l.
Qed.

Theorem subslice_oob : forall l n m,
  n >= m ->
  subslice n m l = [].
Proof.
  intros; rewrite subslice'_correct; unfold subslice'.
  replace (m - n) with 0 by omega.
  auto.
Qed.

Section SubsliceLength.

Lemma skipn_length : forall l n,
  length (skipn n l) = length l - n.
Proof.
  induct l.
Qed.

Lemma firstn_length : forall l n,
  n <= length l ->
  length (firstn n l) = n.
Proof.
  induct l.
Qed.

Lemma firstn_length_oob : forall l n,
  n >= length l ->
  length (firstn n l) = length l.
Proof.
  induct l.
Qed.

Hint Rewrite Min.min_l Min.min_r using omega : min.

Corollary firstn_length_min : forall l n,
  length (firstn n l) = Nat.min n (length l).
Proof.
  intros.
  destruct (le_dec n (length l));
  autorewrite with min;
  auto using firstn_length, firstn_length_oob.
Qed.

Theorem subslice_length : forall n m l,
  m <= length l ->
  length (subslice n m l) = m - n.
Proof.
  unfold subslice; intros.
  rewrite skipn_length.
  rewrite firstn_length; auto.
Qed.

Theorem subslice_length_oob : forall n m l,
  m >= length l ->
  length (subslice n m l) = length l - n.
Proof.
  unfold subslice; dispatch.
  rewrite skipn_length.
  rewrite firstn_length_oob by omega; auto.
Qed.

End SubsliceLength.

Theorem subslice_prefix : forall n m l,
  n = 0 ->
  subslice n m l = firstn m l.
Proof.
  unfold subslice; intros; subst; auto.
Qed.

Lemma firstn_past_end : forall n l,
  n >= length l ->
  firstn n l = l.
Proof.
  induct n.
  destruct l; dispatch.
  destruct l; dispatch.
Qed.

Corollary firstn_to_length : forall n l,
  n = length l ->
  firstn n l = l.
Proof.
  dispatch; auto using firstn_past_end.
Qed.

Lemma subslice_suffix : forall n m l,
  m = length l ->
  subslice n m l = skipn n l.
Proof.
  unfold subslice; dispatch.
  rewrite firstn_past_end; auto.
Qed.

Hint Rewrite app_nil_l app_nil_r : subslice.
Hint Rewrite subslice_prefix subslice_suffix using omega : subslice.

Lemma firstn_repeat_outer : forall l n m,
  n <= m ->
  firstn n (firstn m l) = firstn n l.
Proof.
  induct l.
Qed.

Lemma firstn_repeat_inner : forall l n m,
  n > m ->
  firstn n (firstn m l) = firstn m l.
Proof.
  induct l.
Qed.

Hint Rewrite <- plus_n_O : subslice.
Hint Rewrite <- plus_n_Sm : subslice.

Lemma skipn_repeat : forall l n m,
  skipn n (skipn m l) = skipn (n+m) l.
Proof.
  induct l.
Qed.

Lemma firstn_skipn_subslice : forall n m l,
  firstn m (skipn n l) = subslice n (m+n) l.
Proof.
  intros.
  rewrite subslice'_correct; unfold subslice'.
  replace (m + n - n) with m by omega.
  auto.
Qed.

Lemma subslice_overlap : forall l n m,
  n > m ->
  subslice n m l = [].
Proof.
  unfold subslice; induct l.
Qed.

Hint Rewrite firstn_repeat_outer firstn_repeat_inner
  skipn_repeat subslice_overlap
  using omega : subslice.

Lemma firstn_subslice_narrow : forall l n m m',
  m <= m' ->
  subslice n m (firstn m' l) = subslice n m l.
Proof.
  dispatch.
Qed.

Lemma firstn_subslice_expand : forall l n m m',
  m > m' ->
  subslice n m (firstn m' l) = subslice n m' l.
Proof.
  dispatch.
Qed.

Theorem subslice_repeat_narrow : forall n m n' m' l,
  m' + n <= m ->
  subslice n' m' (subslice n m l) =
  subslice (n'+n) (m'+n) l.
Proof.
  intros.
  destruct (le_dec n' m'), (le_dec n m);
    repeat rewrite subslice_overlap by omega;
    dispatch.
  rewrite subslice'_correct with (n := n').
  unfold subslice, subslice'; dispatch.
  rewrite firstn_skipn_subslice.
  replace (m' - n' + (n' + n)) with (m' + n) by omega.
  dispatch.
Qed.

Theorem subslice_repeat_expand : forall n m n' m' l,
  m' + n > m ->
  subslice n' m' (subslice n m l) =
  subslice (n'+n) m l.
Proof.
  intros.
  destruct (le_dec n' m'), (le_dec n m);
    repeat rewrite subslice_overlap by omega;
    dispatch.
  - rewrite subslice'_correct with (n := n').
    unfold subslice, subslice'; dispatch.
    rewrite firstn_skipn_subslice.
    replace (m' - n' + (n' + n)) with (m' + n) by omega.
    dispatch.
  - repeat rewrite subslice_overlap with (l := l) by omega.
    dispatch.
Qed.

Section Appending.

Theorem subslice_combine : forall l n m k,
  n <= k ->
  k <= m ->
  subslice n k l ++ subslice k m l = subslice n m l.
Proof.
  unfold subslice; induct l.
  destruct n, k, m; dispatch.
  specialize (IHl 0); cbn in *.
  rewrite IHl; auto.
Qed.

Theorem subslice_combine_all : forall n m l,
  m = length l ->
  subslice 0 n l ++ subslice n m l = l.
Proof.
  unfold subslice; dispatch; subst.
  rewrite firstn_to_length with (n := length l); auto.
  generalize n.
  induct l.
Qed.

Lemma app_firstn : forall l l' n,
  n <= length l ->
  firstn n (l ++ l') = firstn n l.
Proof.
  induct l.
  inversion H; auto.
Qed.

Theorem app_subslice_first : forall l' l n m,
  m <= length l ->
  subslice n m (l ++ l') = subslice n m l.
Proof.
  unfold subslice at 1.
  induct l.
  inversion H; dispatch.
  destruct m; dispatch.
  destruct n; dispatch.
  specialize (IHl 0); cbn in *.
  rewrite IHl; auto.
Qed.

End Appending.

End Subslicing.

Module Examples.

Example numbers_1 : seq 1 1 = [1].
Proof. reflexivity. Qed.

Example subslice_1_4 :
  subslice 1 4 (seq 1 10) =
  [2; 3; 4].
Proof. reflexivity. Qed.

End Examples.