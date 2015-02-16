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
  Definition list_files (folder : LString.t) {A : Type}
    (k : option (list LString.t) -> C.t A) : C.t A :=
    call! names := Command.ListFiles folder in
    match names with
    | None =>
      do_call! Command.Log (LString.s "The folder " ++ folder ++ LString.s " cannot be listed.") in
      k None
    | Some names =>
      k @@ Some (names |> List.filter (fun name =>
        match name with
        | "c" :: "o" :: "q" :: _ => true
        | _ => false
        end))
    end.

  Definition versions_of_package (repository : LString.t) (package : LString.t)
    {A : Type} (k : option (list LString.t) -> C.t A) : C.t A :=
     let package_folder := repository ++ LString.s "/" ++ package in
    let! versions := list_files package_folder in
    match versions with
    | None => k None
    | Some versions =>
      k @@ Some (List.fold_left (fun versions version =>
        match LString.split_limit version "." 2 with
        | [_; version] => version :: versions
        | _ => versions
        end)
        versions [])
    end.

  Fixpoint versions_of_packages (repository : LString.t)
    (packages : list LString.t) {A : Type}
    (k : option (list (LString.t * list LString.t)) -> C.t A) : C.t A :=
    match packages with
    | [] => k (Some [])
    | package :: packages =>
      let! versions := versions_of_package repository package in
      let! next := versions_of_packages repository packages in
      match (versions, next) with
      | (Some versions, Some next) => k @@ Some ((package, versions) :: next)
      | _ => k None
      end
    end.

  Definition packages (repository : LString.t) {A : Type}
    (k : option (list (LString.t * list LString.t)) -> C.t A) : C.t A :=
    let! packages := list_files repository in
    match packages with
    | None => k None
    | Some packages => versions_of_packages repository packages k
    end.

  Definition to_string (packages : list (LString.t * list LString.t))
    : LString.t :=
    LString.join [LString.Char.n] (packages |> List.map (fun package : _ * _=>
      let (name, versions) := package in
      name ++ LString.s ": " ++ LString.join (LString.s ", ") versions)).
End Packages.

Definition main : C.t unit :=
  let! packages := Packages.packages (LString.s "repo-stable/packages") in
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
