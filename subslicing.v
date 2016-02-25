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

Ltac dispatch :=
  intros; cbn in *;
  autorewrite with subslice in *;
  auto;
  try omega.

Ltac induct a :=
  induction a; dispatch.

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
  induct l.
  rewrite subslice'_nil; auto.
  destruct n, m; cbn; auto.
  apply IHl.
Qed.

End ReverseDefinition.

Hint Extern 4 (_ <= _) => abstract omega.

Theorem firstn_oob : forall l n,
  n = 0 ->
  firstn n l = [].
Proof.
  intros; subst; auto.
Qed.

Theorem skipn_oob : forall l n,
  n >= length l ->
  skipn n l = [].
Proof.
  induct l.
  destruct n; dispatch.
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

Theorem skipn_length : forall l n,
  length (skipn n l) = length l - n.
Proof.
  induct l; destruct n; dispatch.
Qed.

Theorem firstn_length : forall l n,
  n < length l ->
  length (firstn n l) = n.
Proof.
  induct l; destruct n; dispatch.
Qed.

Theorem subslice_length : forall n m l,
  m < length l ->
  length (subslice n m l) = m - n.
Proof.
  unfold subslice; intros.
  rewrite skipn_length.
  rewrite firstn_length; auto.
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
  induction n; dispatch.
  destruct l; dispatch.
  destruct l; dispatch.
  rewrite IHn; auto.
Qed.

Corollary firstn_to_length : forall n l,
  n = length l ->
  firstn n l = l.
Proof.
  intros; apply firstn_past_end; subst; auto.
Qed.

Lemma subslice_suffix : forall n m l,
  m = length l ->
  subslice n m l = skipn n l.
Proof.
  unfold subslice; intros; subst; auto.
  rewrite firstn_past_end; auto.
Qed.

Hint Rewrite app_nil_l : subslice.
Hint Rewrite app_nil_r : subslice.

Theorem subslice_combine : forall l n m k,
  n <= k ->
  k <= m ->
  subslice n k l ++ subslice k m l = subslice n m l.
Proof.
  unfold subslice; induct l.
  destruct n, k, m; dispatch.
  f_equal.
  specialize (IHl 0); cbn in *.
  eauto.
Qed.

Theorem subslice_combine_all : forall n l,
  subslice 0 n l ++ subslice n (length l) l = l.
Proof.
  unfold subslice; intros; cbn.
  rewrite firstn_to_length with (n := length l); auto.
  generalize n.
  induct l; destruct n0; dispatch.
  rewrite IHl; auto.
Qed.

Lemma firstn_repeat_outer : forall l n m,
  n <= m ->
  firstn n (firstn m l) = firstn n l.
Proof.
  induct l.
  destruct n, m; dispatch.
  rewrite IHl; auto.
Qed.

Lemma firstn_repeat_inner : forall l n m,
  n > m ->
  firstn n (firstn m l) = firstn m l.
Proof.
  induct l.
  destruct n, m; dispatch.
  rewrite IHl; auto.
Qed.

Lemma skipn_repeat : forall l n m,
  skipn n (skipn m l) = skipn (n+m) l.
Proof.
  induct l.
  destruct m; dispatch.
  destruct n; dispatch.
  replace (n+0) with n by omega; auto.

  replace (n + S m) with (S (n+m)) by omega; dispatch.
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
  destruct n, m; dispatch.
Qed.

Lemma firstn_subslice_narrow : forall l n m m',
  m <= m' ->
  subslice n m (firstn m' l) = subslice n m l.
Proof.
  unfold subslice; intros.
  rewrite firstn_repeat_outer by auto; auto.
Qed.

Lemma firstn_subslice_expand : forall l n m m',
  m > m' ->
  subslice n m (firstn m' l) = subslice n m' l.
Proof.
  unfold subslice; intros.
  rewrite firstn_repeat_inner by auto; auto.
Qed.

Theorem subslice_repeat_narrow : forall n m n' m' l,
  m' + n <= m ->
  subslice n' m' (subslice n m l) =
  subslice (n'+n) (m'+n) l.
Proof.
  intros.
  destruct (le_dec n' m'), (le_dec n m);
    repeat rewrite subslice_overlap by omega;
    auto.
  rewrite subslice'_correct with (n := n').
  unfold subslice at 1.
  unfold subslice'.
  rewrite skipn_repeat.
  rewrite firstn_skipn_subslice.
  replace (m' - n' + (n' + n)) with (m' + n) by omega.
  rewrite firstn_subslice_narrow by auto; auto.
Qed.

Theorem subslice_repeat_expand : forall n m n' m' l,
  m' + n > m ->
  subslice n' m' (subslice n m l) =
  subslice (n'+n) m l.
Proof.
  intros.
  destruct (le_dec n' m'), (le_dec n m);
    repeat rewrite subslice_overlap by omega;
    auto.
  - rewrite subslice'_correct with (n := n').
    unfold subslice at 1.
    unfold subslice'.
    rewrite skipn_repeat.
    rewrite firstn_skipn_subslice.
    replace (m' - n' + (n' + n)) with (m' + n) by omega.
    rewrite firstn_subslice_expand; auto.

  - repeat rewrite subslice_overlap with (l := l) by omega.
    rewrite subslice_nil.
    auto.
Qed.

End Subslicing.

Module Examples.

Example numbers_1 : seq 1 1 = [1].
Proof. reflexivity. Qed.

Example subslice_1_4 :
  subslice 1 4 (seq 1 10) =
  [2; 3; 4].
Proof. reflexivity. Qed.

End Examples.