(** Specifications. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Main.
Require Import Model.

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

Module Main.
  Import Run.

  Definition list_files_ok (folder : LString.t) (files : list LString.t)
    : Run.t (Main.list_files folder) (Some (Main.filter_coq_files files)).
    apply (Call (Command.ListFiles folder) (Some files)).
    apply Ret.
  Defined.

  Lemma filter_coq_files_of_version_folders (package : Package.t)
    : Main.filter_coq_files (Package.to_folders package) = Package.to_folders package.
  Admitted.

  Definition list_files_versions (folder : LString.t) (package : Package.t)
    : Run.t (Main.list_files folder) (Some (Package.to_folders package)).
    apply (Call (Command.ListFiles folder) (Some (Package.to_folders package))).
    rewrite filter_coq_files_of_version_folders.
    apply Ret.
  Defined.

  Lemma filter_coq_files_of_package_folders (packages : Packages.t)
    : Main.filter_coq_files (Packages.to_folders packages) = Packages.to_folders packages.
  Admitted.

  Definition list_files_packages (folder : LString.t) (packages : Packages.t)
    : Run.t (Main.list_files folder) (Some (Packages.to_folders packages)).
    apply (Call (Command.ListFiles folder) (Some (Packages.to_folders packages))).
    rewrite filter_coq_files_of_package_folders.
    apply Ret.
  Defined.

  (*Definition versions_of_package_wrong (repository : LString.t)
    (package : LString.t)
    : Run.t (Packages.versions_of_package repository package) None.
    apply (Call (Command.ListFiles _) None).
    apply (Call (Command.Log _) tt).
    apply run_k.
  Defined.*)

  Definition package_of_name_ok (repository : LString.t)
    (package : Package.t)
    : Run.t (Main.package_of_name repository (Package.name package))
      (Some package).
    apply (Bind (list_files_versions _ package)).
    rewrite Package.of_to_folders.
    apply Ret.
  Defined.

  Fixpoint packages_of_names_ok (repository : LString.t) (packages : Packages.t)
    : Run.t (Main.packages_of_names repository (List.map Package.name packages))
      (Some packages).
    destruct packages as [|package packages].
    - apply Ret.
    - apply (Bind (package_of_name_ok repository package)).
      apply (Bind (packages_of_names_ok repository packages)).
      apply Ret.
  Defined.

  Definition packages_ok (repository : LString.t) (packages : Packages.t)
    : Run.t (Main.packages repository) (Some packages).
    apply (Bind (list_files_packages repository packages)).
    apply (packages_of_names_ok repository packages).
  Defined.

  (*Definition packages_wrong (repository : LString.t) {A : Type} {k : _ -> C.t A}
    (run_k : Run.t (k None))
    : Run.t (Packages.packages repository _ k).
    apply (Call (Command.ListFiles repository) None).
    apply (Call (Command.Log _) tt).
    apply run_k.
  Defined.*)
End Main.
