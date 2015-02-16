(** Specifications. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Import Main.

Import ListNotations.
Import C.Notations.
Local Open Scope char.

(** A run is an execution of the program with explicit answers for the
    system calls. *)
Module Run.
  (** We define a run by induction on the structure of a computation. *)
  Inductive t {A : Type} : C.t A -> Type :=
  | Ret : forall (x : A), t (C.Ret x)
  | Call : forall (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t A}, t (handler answer) ->
    t (C.Call command handler)
  | Intro : forall (B : Type) {x : C.t A}, (B -> t x) -> t x.
End Run.

Module Packages.
  Import Run.

  (*Definition versions_of_package_ok (repository : LString.t)
    (package : LString.t)
    : Run.t (Packages.versions_of_package repository package).
    apply (Intro (list LString.t)); intro files.
    apply (Call (Command.ListFiles _) (Some files)).
    apply (Ret (Some _)).
  Defined.*)

  Definition versions_of_package_ok_bind {A : Type} (repository : LString.t)
    (package : LString.t) {k : option (list LString.t) -> C.t A}
    (run_k : forall versions, Run.t (k (Some versions)))
    : Run.t (Packages.versions_of_package repository package k).
    apply (Intro (list LString.t)); intro files.
    apply (Call (Command.ListFiles _) (Some files)).
    apply (run_k _).
  Defined.

  (*Definition versions_of_package_wrong (repository : LString.t)
    (package : LString.t)
    : Run.t (Packages.versions_of_package repository package).
    apply (Call (Command.ListFiles _) None).
    apply (Call (Command.Log _) tt).
    apply (Ret None).
  Defined.*)

  Fixpoint versions_of_packages_ok_bind {A : Type} (repository : LString.t)
    (packages : list LString.t)
    {k : option (list (LString.t * list LString.t)) -> C.t A}
    (run_k : forall packages, Run.t (k (Some packages))) {struct packages}
    : Run.t (Packages.versions_of_packages repository packages k).
    destruct packages as [|package packages].
    - apply (run_k []).
    - apply (versions_of_package_ok_bind repository package); intro versions.
      apply versions_of_packages_ok_bind; intro next.
      apply (run_k _).
  Defined.

  (*Definition packages_ok (repository : LString.t)
    : Run.t (Packages.packages repository).
    apply (Call (Command.ListFiles repository) None).
    apply (Call (Command.Log _) tt).
    apply (Ret None).
  Defined.*)

  (*Definition packages_wrong (repository : LString.t)
    : Run.t (Packages.packages repository).
    apply (Call (Command.ListFiles repository) None).
    apply (Call (Command.Log _) tt).
    apply (Ret None).
  Defined.*)
End Packages.
