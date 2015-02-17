Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.
Require Import FunctionNinjas.All.
Require Import Computation.
Require Import Model.
Require View.

Import ListNotations.
Import C.Notations.
Local Open Scope char.

(** Get basic informations about the packages. *)
Module Basic.
  Definition filter_coq_files (files : list LString.t) : list LString.t :=
    files |> List.filter (fun name =>
      match name with
      | "c" :: "o" :: "q" :: _ => true
      | _ => false
      end).

  (** List the files which are starting with `coq` in a folder. *)
  Definition list_files (folder : LString.t) : C.t (option (list LString.t)) :=
    call! names := Command.ListFiles folder in
    match names with
    | None =>
      do_call! Command.Log (LString.s "The folder " ++ folder ++ LString.s " cannot be listed.") in
      ret None
    | Some names => ret @@ Some (filter_coq_files names)
    end.

  Definition package_of_name (repository : LString.t) (name : LString.t)
    : C.t (option Package.t) :=
    let package_folder := repository ++ ["/"] ++ name in
    let! folders := list_files package_folder in
    match folders with
    | None => ret None
    | Some folders => ret @@ Some (Package.of_folders name folders)
    end.

  Fixpoint packages_of_names (repository : LString.t)
    (names : list LString.t) : C.t (option Packages.t) :=
    match names with
    | [] => ret (Some [])
    | name :: names =>
      let! package := package_of_name repository name in
      let! packages := packages_of_names repository names in
      match (package, packages) with
      | (Some package, Some packages) => ret @@ Some (package :: packages)
      | _ => ret None
      end
    end.

  Definition packages (repository : LString.t) : C.t (option Packages.t) :=
    let! names := list_files repository in
    match names with
    | None => ret None
    | Some names => packages_of_names repository names
    end.
End Basic.

(** Get the full description of the packages. *)
Module Full.
  Definition get_version (repository name version : LString.t)
    : C.t (option Version.t) :=
    let descr_path := repository ++ ["/"] ++ name ++ ["/"] ++ name ++ ["."] ++
      version ++ LString.s "/descr" in
    call! content := Command.ReadFile descr_path in
    match content with
    | None =>
      do_call! Command.Log (descr_path ++ LString.s " not found.") in
      ret None
    | Some content => ret @@ Some (Version.New version content)
    end.

  Fixpoint get_versions (repository name : LString.t) (versions : list LString.t)
    : C.t (list Version.t) :=
    match versions with
    | [] => ret []
    | version :: versions =>
      let! version := get_version repository name version in
      let! versions := get_versions repository name versions in
      match version with
      | None => ret versions
      | Some version => ret (version :: versions)
      end
    end.

  (** Use Debian `dpkg` to compare version numbers. *)
  Definition max_versions (version1 version2 : Version.t)
    : C.t (option Version.t) :=
    let command := LString.s "dpkg --compare-versions " ++
      Version.id version1 ++ LString.s " ge " ++ Version.id version2 in
    call! output := Command.Eval command in
    ret match output with
    | Some (is_success, _) =>
      if is_success then
        Some version1
      else
        Some version2
    | None => None
    end.

  Definition get_full_package (repository : LString.t) (package : Package.t)
    : C.t FullPackage.t :=
    let (name, versions) := package in
    let! versions := get_versions repository name versions in
    ret @@ FullPackage.New name versions.

  Fixpoint get_full_packages (repository : LString.t) (packages : Packages.t)
    : C.t FullPackages.t :=
    match packages with
    | [] => ret []
    | package :: packages =>
      let! full_package := get_full_package repository package in
      let! full_packages := get_full_packages repository packages in
      ret (full_package :: full_packages)
    end.
End Full.

Definition main : C.t unit :=
  let repository := LString.s "repo-stable/packages" in
  let! packages := Basic.packages repository in
  match packages with
  | None =>
    do_call! Command.Log @@ LString.s "The packages cannot be listed." in
    C.Ret tt
  | Some packages =>
    let! full_packages := Full.get_full_packages repository packages in
    let index := View.index full_packages in
    do_call! Command.WriteFile (LString.s "html/index.html") index in
    ret tt
  end.

Require Import Extraction.

Definition repo2web : unit := Extraction.Lwt.run @@ Extraction.eval main.
Extraction "extraction/repo2web" repo2web.
