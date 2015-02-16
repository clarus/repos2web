Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.
Require Import FunctionNinjas.All.
Require Import Computation.
Require Import Model.

Import ListNotations.
Import C.Notations.
Local Open Scope char.

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
  let package_folder := repository ++ LString.s "/" ++ name in
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

(*Definition main : C.t unit :=
  let! packages := packages (LString.s "repo-stable/packages") in
  match packages with
  | None =>
    do_call! Command.Log @@ LString.s "The packages cannot be listed." in
    C.Ret tt
  | Some packages =>
    do_call! Command.Log @@ Packages.to_string packages in
    C.Ret tt
  end.

Require Import Extraction.

Definition repo2web : unit := Extraction.Lwt.run @@ Extraction.eval main.
Extraction "extraction/repo2web" repo2web.*)
