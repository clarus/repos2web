(** Scenarios. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import IoEffects.All.
Require Import IoEffectsUnix.All.
Require Import ListString.All.
Require Import Main.
Require Import Model.

Import ListNotations.
Import C.Notations.
Import IoEffects.Run.
Local Open Scope char.

Module Basic.
  Definition list_coq_files_error (folder : LString.t)
    : Run.t (Basic.list_coq_files folder) None.
    apply (Let (Unix.Run.list_files_error _)).
    apply (Let (Unix.Run.log_ok _)).
    apply Ret.
  Defined.

  Definition list_coq_files_ok (folder : LString.t) (files : list Name.t)
    : Run.t (Basic.list_coq_files folder) (Some files).
    apply (Let (Unix.Run.list_files_ok _ (LString.s "." :: LString.s ".." :: Name.to_strings files))).
    unfold Name.of_strings; simpl.
    rewrite Name.of_to_strings.
    apply Ret.
  Defined.

  Definition get_package_of_name_error (repository : LString.t) (name : Name.t)
    : Run.t (Basic.get_package_of_name repository name) None.
    apply (Let (list_coq_files_error _)).
    apply Ret.
  Defined.

  Definition get_package_of_name_ok (repository : LString.t)
    (package : Package.t)
    : Run.t (Basic.get_package_of_name repository (Package.name package))
      (Some package).
    apply (Let (list_coq_files_ok _ (Package.to_folders package))).
    rewrite Package.of_to_folders.
    apply Ret.
  Defined.

  Fixpoint get_packages_of_names_ok (repository : LString.t) (packages : Packages.t)
    : Run.t (Basic.get_packages_of_names repository (List.map Package.name packages))
      (Some packages).
    destruct packages as [|package packages].
    - apply Ret.
    - apply (Let (get_package_of_name_ok repository package)).
      apply (Let (get_packages_of_names_ok repository packages)).
      apply Ret.
  Defined.

  Definition get_packages_ok (repository : LString.t) (packages : Packages.t)
    : Run.t (Basic.get_packages repository) (Some packages).
    apply (Let (list_coq_files_ok _ (Packages.to_folders packages))).
    apply (get_packages_of_names_ok repository packages).
  Defined.

  Definition get_packages_error (repository : LString.t)
    : Run.t (Basic.get_packages repository) None.
    apply (Let (list_coq_files_error repository)).
    apply Ret.
  Defined.
End Basic.

Module Full.
  Definition get_version_ok (repository : LString.t) (name : Name.t)
    (version : Version.t)
    : Run.t (Full.get_version repository name (Version.id version)) (Some version).
    apply (Let (Unix.Run.read_file_ok _ (Version.description version))).
    destruct version.
    apply Ret.
  Defined.

  Fixpoint get_versions_ok (repository : LString.t) (name : Name.t)
    (versions : list Version.t)
    : Run.t (Full.get_versions repository name (List.map Version.id versions))
      versions.
    destruct versions as [|version versions].
    - apply Ret.
    - apply (Let (get_version_ok repository name version)).
      apply (Let (get_versions_ok repository name versions)).
      apply Ret.
  Defined.

  Definition max_version_ge (version1 version2 : Version.t)
    : Run.t (Full.max_version version1 version2) (Some version1).
    apply (Let (Unix.Run.system_ok _ true)).
    apply Ret.
  Defined.

  Fixpoint last_version_ge (versions : list Version.t)
    : Run.t (Full.last_version versions) (List.hd_error versions).
    destruct versions as [|version versions].
    - apply Ret.
    - apply (Let (last_version_ge versions)).
      destruct (List.hd_error versions) as [version'|].
      + apply (max_version_ge version version').
      + apply Ret.
  Defined.

  Definition get_package_ok (repository : LString.t) (package : FullPackage.t)
    : Run.t (Full.get_package repository (FullPackage.basic package))
      (FullPackage.last_version_hd package).
    destruct package as [name versions last_version].
    apply (Let (get_versions_ok repository _ versions)).
    apply (Let (last_version_ge versions)).
    apply Ret.
  Defined.

  Fixpoint get_packages_ok (repository : LString.t) (packages : FullPackages.t)
    : Run.t (Full.get_packages repository (FullPackages.basic packages))
      (FullPackages.last_version_hd packages).
    destruct packages as [|package packages].
    - apply Ret.
    - apply (Let (get_package_ok repository package)).
      apply (Let (get_packages_ok repository packages)).
      apply Ret.
  Defined.
End Full.
