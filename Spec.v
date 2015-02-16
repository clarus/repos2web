(** Specifications. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Import Main.

Import ListNotations.
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
  Definition versions_of_package_wrong (repository : LString.t)
    (package : LString.t)
    : Run.t (Packages.versions_of_package repository package).
    apply (Run.Call (Command.ListFiles _) None).
    apply (Run.Call (Command.Log _) tt).
    apply (Run.Ret None).
  Defined.

  Definition packages_wrong (repository : LString.t)
    : Run.t (Packages.packages repository).
    apply (Run.Call (Command.ListFiles repository) None).
    apply (Run.Call (Command.Log _) tt).
    apply (Run.Ret None).
  Defined.
End Packages.
