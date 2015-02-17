(** Scenarios. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.
Require Import Main.
Require Import Model.

Import ListNotations.
Import C.Notations.
Local Open Scope char.

(** A run is an execution of the program with explicit answers for the
    system calls. We define a run by induction on a computation. *)
Inductive t : forall {A : Type}, C.t A -> A -> Type :=
| Ret : forall {A : Type} (x : A), t (C.Ret x) x
| Call : forall {A : Type} (command : Command.t) (answer : Command.answer command)
  {handler : Command.answer command -> C.t A} {x : A}, t (handler answer) x ->
  t (C.Call command handler) x
| Let : forall {A B : Type} {c_x : C.t B} {x : B} {c_f : B -> C.t A} {y : A},
  t c_x x -> t (c_f x) y -> t (C.Let c_x c_f) y
| Intro : forall {A : Type} (B : Type) {c : C.t A} {x : A}, (B -> t c x) -> t c x.

Definition log_ok (message : LString.t) : t (log message) tt.
  apply (Call (Command.Print _) true).
  apply Ret.
Defined.

Module Basic.
  Definition list_files_error (folder : LString.t)
    : t (Basic.list_files folder) None.
    apply (Call (Command.ListFiles folder) None).
    apply (Let (log_ok _)).
    apply Ret.
  Defined.

  Definition list_files_ok (folder : LString.t) (files : list LString.t)
    : t (Basic.list_files folder) (Some (Basic.filter_coq_files files)).
    apply (Call (Command.ListFiles folder) (Some (LString.s "." :: LString.s ".." :: files))).
    apply Ret.
  Defined.

  Lemma filter_coq_files_of_version_folders (package : Package.t)
    : Basic.filter_coq_files (Package.to_folders package) = Package.to_folders package.
  Admitted.

  Definition list_files_versions (folder : LString.t) (package : Package.t)
    : t (Basic.list_files folder) (Some (Package.to_folders package)).
    apply (Call (Command.ListFiles folder) (Some (Package.to_folders package))).
    rewrite filter_coq_files_of_version_folders.
    apply Ret.
  Defined.

  Lemma filter_coq_files_of_package_folders (packages : Packages.t)
    : Basic.filter_coq_files (Packages.to_folders packages) = Packages.to_folders packages.
  Admitted.

  Definition list_files_packages (folder : LString.t) (packages : Packages.t)
    : t (Basic.list_files folder) (Some (Packages.to_folders packages)).
    apply (Call (Command.ListFiles folder) (Some (Packages.to_folders packages))).
    rewrite filter_coq_files_of_package_folders.
    apply Ret.
  Defined.

  Definition get_package_of_name_error (repository : LString.t) (name : LString.t)
    : t (Basic.get_package_of_name repository name) None.
    apply (Let (list_files_error _)).
    apply Ret.
  Defined.

  Definition get_package_of_name_ok (repository : LString.t)
    (package : Package.t)
    : t (Basic.get_package_of_name repository (Package.name package))
      (Some package).
    apply (Let (list_files_versions _ package)).
    rewrite Package.of_to_folders.
    apply Ret.
  Defined.

  Fixpoint get_packages_of_names_ok (repository : LString.t) (packages : Packages.t)
    : t (Basic.get_packages_of_names repository (List.map Package.name packages))
      (Some packages).
    destruct packages as [|package packages].
    - apply Ret.
    - apply (Let (get_package_of_name_ok repository package)).
      apply (Let (get_packages_of_names_ok repository packages)).
      apply Ret.
  Defined.

  Definition get_packages_ok (repository : LString.t) (packages : Packages.t)
    : t (Basic.get_packages repository) (Some packages).
    apply (Let (list_files_packages repository packages)).
    apply (get_packages_of_names_ok repository packages).
  Defined.

  Definition get_packages_error (repository : LString.t)
    : t (Basic.get_packages repository) None.
    apply (Let (list_files_error repository)).
    apply Ret.
  Defined.
End Basic.

Module Full.
  Definition get_version_ok (repository name : LString.t) (version : Version.t)
    : t (Full.get_version repository name (Version.id version)) (Some version).
    apply (Call (Command.ReadFile _) (Some (Version.description version))).
    destruct version.
    apply Ret.
  Defined.

  Fixpoint get_versions_ok (repository name : LString.t) (versions : list Version.t)
    : t (Full.get_versions repository name (List.map Version.id versions))
      versions.
    destruct versions as [|version versions].
    - apply Ret.
    - apply (Let (get_version_ok repository name version)).
      apply (Let (get_versions_ok repository name versions)).
      apply Ret.
  Defined.

  Definition max_version_ge (version1 version2 : Version.t)
    : t (Full.max_version version1 version2) (Some version1).
    apply (Call (Command.System _) (Some true)).
    apply Ret.
  Defined.

  Fixpoint last_version_ge (versions : list Version.t)
    : t (Full.last_version versions) (List.hd_error versions).
    destruct versions as [|version versions].
    - apply Ret.
    - apply (Let (last_version_ge versions)).
      destruct (List.hd_error versions) as [version'|].
      + apply (max_version_ge version version').
      + apply Ret.
  Defined.

  Definition get_package_ok (repository : LString.t) (package : FullPackage.t)
    : t (Full.get_package repository (FullPackage.basic package))
      (FullPackage.last_version_hd package).
    destruct package as [name versions last_version].
    apply (Let (get_versions_ok repository _ versions)).
    apply (Let (last_version_ge versions)).
    apply Ret.
  Defined.

  Fixpoint get_packages_ok (repository : LString.t) (packages : FullPackages.t)
    : t (Full.get_packages repository (FullPackages.basic packages))
      (FullPackages.last_version_hd packages).
    destruct packages as [|package packages].
    - apply Ret.
    - apply (Let (get_package_ok repository package)).
      apply (Let (get_packages_ok repository packages)).
      apply Ret.
  Defined.
End Full.
