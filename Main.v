(** The interactive program. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import Io.All.
Require Import Io.System.All.
Require Import ListPlus.All.
Require Import ListString.All.
Require Import Model.
Require View.

Import ListNotations.
Import C.Notations.
Local Open Scope char.

(** Notation for computations with System effects. *)
Definition C := C.t System.effects.

(** Get basic informations about the packages. *)
Module Basic.
  (** List the files which are starting with `coq:` in a folder. *)
  Definition list_coq_files (folder : LString.t) : C (option (list Name.t)) :=
    let! folders := System.list_files folder in
    match folders with
    | None =>
      do! log (LString.s "The folder " ++ folder ++ LString.s " cannot be listed.") in
      ret None
    | Some folders => ret @@ Some (Name.of_strings folders)
    end.

  (** Get the versions of a package's name to form a package. *)
  Definition get_package_of_name (repository : LString.t) (name : Name.t)
    : C (option Package.t) :=
    let package_folder := repository ++ ["/"] ++ Name.to_string name in
    let! folders := list_coq_files package_folder in
    match folders with
    | None => ret None
    | Some folders => ret @@ Some (Package.of_folders name folders)
    end.

  (** Get a list of packages from a list of names. *)
  Fixpoint get_packages_of_names (repository : LString.t)
    (names : list Name.t) : C (option Packages.t) :=
    match names with
    | [] => ret (Some [])
    | name :: names =>
      let! package := get_package_of_name repository name in
      let! packages := get_packages_of_names repository names in
      match (package, packages) with
      | (Some package, Some packages) => ret @@ Some (package :: packages)
      | _ => ret None
      end
    end.

  (** Get the list of packages of a repository. *)
  Definition get_packages (repository : LString.t) : C (option Packages.t) :=
    let! names := list_coq_files repository in
    match names with
    | None => ret None
    | Some names => get_packages_of_names repository names
    end.
End Basic.

(** Get the full description of the packages. *)
Module Full.
  (** Get the description of a version of a package. *)
  Definition get_version (repository : LString.t) (name : Name.t)
    (version : LString.t) : C (option Version.t) :=
    let descr_path :=
      repository ++ ["/"] ++ Name.to_string name ++ ["/"] ++
      Name.to_string name ++ ["."] ++ version ++ LString.s "/descr" in
    let! content := System.read_file descr_path in
    match content with
    | None =>
      do! log (descr_path ++ LString.s " not found.") in
      ret None
    | Some content => ret @@ Some (Version.New version content)
    end.

  (** Get the list of full versions of packages. *)
  Fixpoint get_versions (repository : LString.t) (name : Name.t)
    (versions : list LString.t) : C (list Version.t) :=
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

  (** Return the latest version, using Debian `dpkg` for comparison. *)
  Definition max_version (version1 version2 : Version.t)
    : C (option Version.t) :=
    let command := LString.s "dpkg --compare-versions " ++
      Version.id version1 ++ LString.s " ge " ++ Version.id version2 ++
      LString.s " 2>/dev/null" in
    let! is_success := System.system command in
    match is_success with
    | Some is_success =>
      ret (if is_success then
        Some version1
      else
        Some version2)
    | None =>
      do! log @@ LString.s "Cannot call the dpkg command." in
      ret None
    end.

  (** The latest version of a list of versions. *)
  Fixpoint last_version (versions : list Version.t) : C (option Version.t) :=
    match versions with
    | [] => ret None
    | version :: versions =>
      let! version' := last_version versions in
      match version' with
      | Some version' => max_version version version'
      | None => ret (Some version)
      end
    end.

  (** Get the full package of a package. *)
  Definition get_package (repository : LString.t) (package : Package.t)
    : C FullPackage.t :=
    let (name, versions) := package in
    let! versions := get_versions repository name versions in
    let! last_version := last_version versions in
    ret @@ FullPackage.New name versions last_version.

  (** Get the list of full package of a list of packages. *)
  Fixpoint get_packages (repository : LString.t) (packages : Packages.t)
    : C FullPackages.t :=
    match packages with
    | [] => ret []
    | package :: packages =>
      let! full_package := get_package repository package in
      let! full_packages := get_packages repository packages in
      ret (full_package :: full_packages)
    end.
End Full.

(** The main function. *)
Definition main : C unit :=
  let repository := LString.s "repo-stable/packages" in
  let! packages := Basic.get_packages repository in
  match packages with
  | None => log @@ LString.s "The packages cannot be listed."
  | Some packages =>
    let! full_packages := Full.get_packages repository packages in
    let index_content := View.index full_packages in
    let index_name := LString.s "html/index.html" in
    let! is_success := System.write_file index_name index_content in
    if is_success then
      log (index_name ++ LString.s " generated.")
    else
      log (LString.s "Cannot generate " ++ index_name ++ LString.s ".")
  end.

Require Import Extraction.

(** The extracted program. *)
Definition repos2web : unit := Extraction.Lwt.run @@ Extraction.eval main.
Extraction "extraction/repos2web" repos2web.
