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

Section ReverseDefinition.

Definition subslice' n m l :=
  firstn (m - n) (skipn n l).

Lemma subslice'_nil : forall n m,
  subslice' n m [] = [].
Proof.
  unfold subslice'; intros.
  rewrite skipn_nil; rewrite firstn_nil; auto.
Qed.

Theorem subslice'_correct : forall l n m,
  subslice n m l = subslice' n m l.
Proof.
  induction l; intros; cbn.
  rewrite subslice_nil; rewrite subslice'_nil; auto.
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
  induction l; intros; cbn.
  rewrite skipn_nil; auto.
  destruct n; cbn in *; auto; omega.
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
  induction l; intros; cbn.
  rewrite skipn_nil; auto.
  destruct n; cbn; auto.
Qed.

Theorem firstn_length : forall l n,
  n < length l ->
  length (firstn n l) = n.
Proof.
  induction l; intros; cbn.
  inversion H.
  destruct n; cbn in *; auto.
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
  induction n; intros; cbn; auto.
  destruct l; auto.
  inversion H.
  destruct l; cbn in *; auto.
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

End Subslicing.

Module Examples.

Example numbers_1 : seq 1 1 = [1].
Proof. reflexivity. Qed.

Example subslice_1_4 :
  subslice 1 4 (seq 1 10) =
  [2; 3; 4].
Proof. reflexivity. Qed.

End Examples.