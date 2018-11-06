From Subslice Require Import Subslice.

Require Import List.
Import ListNotations.
Open Scope list.

Module Examples.

Example numbers_1 : seq 1 1 = [1].
Proof. reflexivity. Qed.

Example subslice_1_4 :
  subslice 1 4 (seq 1 10) =
  [2; 3; 4].
Proof. reflexivity. Qed.

End Examples.
