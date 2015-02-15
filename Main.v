Require Import Coq.Lists.List.
Require Import ListString.All.
Require Import FunctionNinjas.All.
Require Import Computation.

Import ListNotations.
Import C.Notations.

Definition versions_of_package {A : Type} (repository : LString.t)
  (package : LString.t) (k : option (list LString.t) -> C.t A) : C.t A :=
  let package_folder := repository ++ LString.s "/" ++ package in
  call! versions := Command.ListFolders package_folder in
  match versions with
  | None => k None
  | Some versions =>
    k @@ List.fold_left (fun (versions : option _) (version : LString.t) =>
      match (versions, LString.split_limit version "." 2) with
      | (Some versions, [_; version]) => Some (version :: versions)
      | _ => None
      end)
      (versions : list LString.t) (Some [])
  end.

Fixpoint versions_of_packages {A : Type} (repository : LString.t)
  (packages : list LString.t)
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

Definition packages {A : Type} (repository : LString.t)
  (k : option (list (LString.t * list LString.t)) -> C.t A) : C.t A :=
  call! packages := Command.ListFolders repository in
  match packages with
  | None => k None
  | Some packages => versions_of_packages repository packages k
  end.

Definition main : C.t unit :=
  ret tt.
