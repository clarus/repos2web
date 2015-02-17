(** Extraction to OCaml. New primitives are defined in `extraction/utils.ml`. *)
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlBigIntConv.
Require Import ExtrOcamlString.
Require Import ErrorHandlers.All.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.

Import ListNotations.
Local Open Scope type.

(** Interface with the OCaml strings. *)
Module String.
  (** The OCaml `string` type. *)
  Parameter t : Type.
  Extract Constant t => "string".

  (** Export to an OCaml string. *)
  Parameter of_lstring : LString.t -> t.
  Extract Constant of_lstring => "Utils.String.of_lstring".

  (** Import an OCaml string. *)
  Parameter to_lstring : t -> LString.t.
  Extract Constant to_lstring => "Utils.String.to_lstring".
End String.

(** Unbounded integers. *)
Module BigInt.
  (** The OCaml's `bigint` type. *)
  Definition t : Type := bigint.

  (** Export to a `Z`. *)
  Definition to_Z : t -> Z := z_of_bigint.
End BigInt.

(** Interface to the Lwt library. *)
Module Lwt.
  (** The `Lwt.t` type. *)
  Parameter t : Type -> Type.
  Extract Constant t "'a" => "'a Lwt.t".

  (** Return. *)
  Parameter ret : forall {A : Type}, A -> t A.
  Extract Constant ret => "Lwt.return".

  (** Bind. *)
  Parameter bind : forall {A B : Type}, t A -> (A -> t B) -> t B.
  Extract Constant bind => "Lwt.bind".

  (** Run. *)
  Parameter run : forall {A : Type}, t A -> A.
  Extract Constant run => "Lwt_main.run".

  (** Print a new line. *)
  Parameter printl : String.t -> t unit.
  Extract Constant printl => "Lwt_io.printl".

  (** List the files of a directory. *)
  Parameter list_files : String.t -> t (option (list String.t)).
  Extract Constant list_files => "Utils.list_files".

  (** The the content of a file. *)
  Parameter read_file : String.t -> t (option String.t).
  Extract Constant read_file => "Utils.read_file".

  (** Update (or create) a file with some content. *)
  Parameter write_file : String.t -> String.t -> t bool.
  Extract Constant write_file => "Utils.write_file".

  (** Delete a file. *)
  Parameter delete_file : String.t -> t bool.
  Extract Constant delete_file => "Utils.delete_file".

  (** Evaluate a command. *)
  Parameter eval : String.t -> t (option (bool * String.t)).
  Extract Constant eval => "Utils.eval".
End Lwt.

(** Evaluate a command using Lwt. *)
Definition eval_command (c : Command.t) : Lwt.t (Command.answer c) :=
  match c return (Lwt.t (Command.answer c)) with
  | Command.ListFiles folder =>
    Lwt.bind (Lwt.list_files @@ String.of_lstring folder) (fun files =>
    Lwt.ret @@ Option.bind files (fun files =>
    Some (List.map String.to_lstring files)))
  | Command.ReadFile file_name =>
    Lwt.bind (Lwt.read_file @@ String.of_lstring file_name) (fun content =>
    Lwt.ret @@ option_map String.to_lstring content)
  | Command.WriteFile file_name content =>
    let file_name := String.of_lstring file_name in
    let content := String.of_lstring content in
    Lwt.write_file file_name content
  | Command.DeleteFile file_name =>
    Lwt.delete_file @@ String.of_lstring file_name
  | Command.Eval command =>
    Lwt.bind (Lwt.eval (String.of_lstring command)) (fun output =>
    Lwt.ret (output |> option_map (fun output : _ * _ =>
      let (is_success, message) := output in
      (is_success, String.to_lstring message))))
  | Command.Log message =>
    let message := String.of_lstring message in
    Lwt.printl message
  end.

(** Evaluate an expression using Lwt. *)
Fixpoint eval {A : Type} (x : C.t A) : Lwt.t A :=
  match x with
  | C.Ret x => Lwt.ret x
  | C.Call command handler =>
    Lwt.bind (eval_command command) (fun answer =>
    eval @@ handler answer)
  | C.Let _ x f => Lwt.bind (eval x) (fun x => eval (f x))
  end.
