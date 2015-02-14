Require Import Computation.

Import C.Notations.

Definition packages {A : Type} (repository : LString.t)
  (k : option (list (LString.t * list LString.t)) -> C.t A) : C.t A :=
  k None.

Definition main : C.t unit :=
  ret tt.
