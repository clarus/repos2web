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

  Definition versions_of_package_wrong (repository : LString.t)
    (package : LString.t) {A : Type} {k : _ -> C.t A} (run_k : Run.t (k None))
    : Run.t (Packages.versions_of_package repository package _ k).
    apply (Call (Command.ListFiles _) None).
    apply (Call (Command.Log _) tt).
    apply run_k.
  Defined.

  Definition versions_of_package_ok (repository : LString.t)
    (package : LString.t) {A : Type} {k : _ -> C.t A}
    (run_k : forall versions, Run.t (k (Some versions)))
    : Run.t (Packages.versions_of_package repository package _ k).
    apply (Intro (list LString.t)); intro files.
    apply (Call (Command.ListFiles _) (Some files)).
    apply run_k.
  Defined.

  Fixpoint versions_of_packages_ok (repository : LString.t)
    (packages : list LString.t) {A : Type} {k : _ -> C.t A}
    (run_k : forall packages, Run.t (k (Some packages))) {struct packages}
    : Run.t (Packages.versions_of_packages repository packages _ k).
    destruct packages as [|package packages].
    - apply (run_k []).
    - apply (versions_of_package_ok repository package); intro versions.
      apply versions_of_packages_ok; intro next.
      apply (run_k _).
  Defined.

  Definition packages_ok (repository : LString.t) {A : Type} {k : _ -> C.t A}
    (run_k : forall packages, Run.t (k (Some packages)))
    : Run.t (Packages.packages repository _ k).
    apply (Intro (list LString.t)); intro files.
    apply (Call (Command.ListFiles repository) (Some files)).
    apply versions_of_packages_ok.
    apply run_k.
  Defined.

  Definition packages_wrong (repository : LString.t) {A : Type} {k : _ -> C.t A}
    (run_k : Run.t (k None))
    : Run.t (Packages.packages repository _ k).
    apply (Call (Command.ListFiles repository) None).
    apply (Call (Command.Log _) tt).
    apply run_k.
  Defined.
End Packages.
