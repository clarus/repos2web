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
  Inductive t : forall {A : Type}, C.t A -> A -> Type :=
  | Ret : forall {A : Type} (x : A), t (C.Ret x) x
  | Call : forall {A : Type} (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t A} {x : A}, t (handler answer) x ->
    t (C.Call command handler) x
  | Bind : forall {A B : Type} {c_x : C.t B} {x : B} {c_f : B -> C.t A} {y : A},
    t c_x x -> t (c_f x) y -> t (C.Bind c_x c_f) y
  | Intro : forall {A : Type} (B : Type) {c : C.t A} {x : A}, (B -> t c x) -> t c x.
End Run.

Module Packages.
  Import Run.

  Definition list_files_ok (folder : LString.t) (files : list LString.t)
    : Run.t (Packages.list_files folder) (Some (Packages.filter_coq_files files)).
    apply (Call (Command.ListFiles folder) (Some files)).
    apply Ret.
  Defined.

  (*Definition versions_of_package_wrong (repository : LString.t)
    (package : LString.t)
    : Run.t (Packages.versions_of_package repository package) None.
    apply (Call (Command.ListFiles _) None).
    apply (Call (Command.Log _) tt).
    apply run_k.
  Defined.*)

  Definition versions_of_package_ok (repository : LString.t)
    (package : LString.t) (files : list LString.t)
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
      apply run_k.
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
