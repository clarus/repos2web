Require Import Coq.Lists.List.
Require Import ListString.All.
Require Import FunctionNinjas.All.
Require Import Computation.

Import ListNotations.
Import C.Notations.

Definition versions_of_package (repository : LString.t) (package : LString.t)
  : C.t (option (list LString.t)) :=
  let package_folder := repository ++ LString.s "/" ++ package in
  call! versions := Command.ListFiles package_folder in
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
    let! versions := versions_of_package repository package in
    let! next := versions_of_packages repository packages in
    match (versions, next) with
    | (Some versions, Some next) => ret @@ Some ((package, versions) :: next)
    | _ => ret None
    end
  end.

Definition packages (repository : LString.t)
  : C.t (option (list (LString.t * list LString.t))) :=
  call! packages := Command.ListFiles repository in
  match packages with
  | None => ret None
  | Some packages => versions_of_packages repository packages
  end.

Definition main : C.t unit :=
  let! packages := packages @@ LString.s "repo-stable" in
  let message :=
    LString.s match packages with
    | None => "None"
    | Some _ => "Some"
    end in
  do_call! Command.Log message in
  ret tt.

Require Import Extraction.

Definition repo2web : unit := Extraction.Lwt.run @@ Extraction.eval main.
Extraction "extraction/repo2web" repo2web.
