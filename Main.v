Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import ListString.All.
Require Import FunctionNinjas.All.
Require Import Computation.

Import ListNotations.
Import C.Notations.
Local Open Scope char.

Module Packages.
  (** List the files in a folder starting with `coq`. *)
  Definition list_files (folder : LString.t) : C.t (option (list LString.t)) :=
    call! names := Command.ListFiles folder in
    match names with
    | None =>
      do_call! Command.Log (LString.s "The folder " ++ folder ++ LString.s " cannot be listed.") in
      ret None
    | Some names =>
      ret @@ Some (names |> List.filter (fun name =>
        match name with
        | "c" :: "o" :: "q" :: _ => true
        | _ => false
        end))
    end.

  Definition versions_of_package (repository : LString.t) (package : LString.t)
    : C.t (option (list LString.t)) :=
     let package_folder := repository ++ LString.s "/" ++ package in
    let! versions := list_files package_folder in
    match versions with
    | None => ret None
    | Some versions =>
      ret @@ List.fold_left (fun (versions : option _) (version : LString.t) =>
        match (versions, LString.split_limit version "." 2) with
        | (Some versions, [_; version]) => Some (version :: versions)
        | _ => None
        end)
        (versions : list LString.t) (Some [])
    end.

  Fixpoint versions_of_packages (repository : LString.t)
    (packages : list LString.t)
    : C.t (option (list (LString.t * list LString.t))) :=
    match packages with
    | [] => ret (Some [])
    | package :: packages =>
      let base_name := List.last (LString.split package "/") [] in
      match package with
      | "c" :: "o" :: "q" :: _ =>
        let! versions := versions_of_package repository package in
        let! next := versions_of_packages repository packages in
        match (versions, next) with
        | (Some versions, Some next) => ret @@ Some ((package, versions) :: next)
        | _ => ret None
        end
      | _ => versions_of_packages repository packages
      end
    end.

  Definition packages (repository : LString.t)
    : C.t (option (list (LString.t * list LString.t))) :=
    let! packages := list_files repository in
    match packages with
    | None => ret None
    | Some packages => versions_of_packages repository packages
    end.

  Definition to_string (packages : list (LString.t * list LString.t))
    : LString.t :=
    LString.join [LString.Char.n] (packages |> List.map (fun package : _ * _=>
      let (name, versions) := package in
      name ++ LString.s ": " ++ LString.join (LString.s ", ") versions)).
End Packages.

Definition main : C.t unit :=
  let! packages := Packages.packages @@ LString.s "repo-stable/packages" in
  match packages with
  | None =>
    do_call! Command.Log @@ LString.s "The packages cannot be listed." in
    ret tt
  | Some packages =>
    do_call! Command.Log @@ Packages.to_string packages in
    ret tt
  end.

Require Import Extraction.

Definition repo2web : unit := Extraction.Lwt.run @@ Extraction.eval main.
Extraction "extraction/repo2web" repo2web.
