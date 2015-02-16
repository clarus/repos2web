(** The definition of computations, used to represent interactive programs. *)
Require Import ListString.All.

Local Open Scope type.

(** External calls. *)
Module Command.
  Inductive t :=
  (** List the files of a directory. *)
  | ListFiles (directory : LString.t)
  (** Read the content of a file. *)
  | ReadFile (file_name : LString.t)
  (** Update (or create) a file with some content. *)
  | WriteFile (file_name : LString.t) (content : LString.t)
  (** Delete a file. *)
  | DeleteFile (file_name : LString.t)
  (** Evaluate a command. *)
  (* | Eval (command : LString.t) *)
  (** Write a message on the standard output. *)
  | Log (message : LString.t).

  (** The type of an answer for a command depends on the value of the command. *)
  Definition answer (command : t) : Type :=
    match command with
    | ListFiles _ => option (list LString.t)
    | ReadFile _ => option LString.t
    | WriteFile _ _ => bool
    | DeleteFile _ => bool
    (* | Eval _ => option LString.t *)
    | Log _ => unit
    end.
End Command.

(** Computations with I/Os. *)
Module C.
  (** A computation can either return a pure value, or do a system call and wait
      for the answer to run another computation. *)
  Inductive t (A : Type) : Type :=
  | Ret : forall (x : A), t A
  | Call : forall (command : Command.t), (Command.answer command -> t A) -> t A.
  Arguments Ret {A} _.
  Arguments Call {A} _ _.

  (** Some optional notations. *)
  Module Notations.
    (** System call. *)
    Notation "'call!' answer ':=' command 'in' X" :=
      (Call command (fun answer => X))
      (at level 200, answer ident, command at level 100, X at level 200).

    (** System call with typed answer. *)
    Notation "'call!' answer : A ':=' command 'in' X" :=
      (Call command (fun (answer : A) => X))
      (at level 200, answer ident, command at level 100, A at level 200, X at level 200).

    (** System call ignoring the answer. *)
    Notation "'do_call!' command 'in' X" :=
      (Call command (fun _ => X))
      (at level 200, command at level 100, X at level 200).

    (** We define an explicit apply function so that Coq does not try to expand
        the notations everywhere. *)
    Definition apply {A B} (f : A -> B) (x : A) := f x.

    (** This notation is useful to compose computations which wait for a
        continuation. We do not have an explicit bind operator to simplify the
        language and the proofs. *)
    Notation "'let!' x ':=' X 'in' Y" :=
      (apply (X _) (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'let!' x : A ':=' X 'in' Y" :=
      (apply (X _) (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the answer. *)
    Notation "'do_let!' X 'in' Y" :=
      (apply (X _) (fun _ => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End C.

Module M.
  Definition t (A : Type) : Type := forall (B : Type), (A -> C.t B) -> C.t B.
End M.
