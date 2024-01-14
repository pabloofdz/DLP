(*
Diego Suárez Ramos : diego.suarez.ramos@udc.es
Pablo Fernández Perez : pablo.fperez@udc.es   
*)
type ty =
    TyBool
  | TyNat
  | TyArr of ty * ty
  | TyString
  | TyTuple of ty list
  | TyRecord of (string * ty) list
  | TyList of ty
  | TyVariant of (string * ty) list
  | TyName of string
;;


type 'a context =
  (string * 'a) list;;
;;

type term =
    TmTrue
  | TmFalse
  | TmIf of term * term * term
  | TmZero
  | TmSucc of term
  | TmPred of term
  | TmIsZero of term
  | TmVar of string
  | TmAbs of string * ty * term
  | TmApp of term * term
  | TmLetIn of string * term * term
  | TmFix of term
  | TmString of string
  | TmConcat of term * term
  | TmLength of term
  | TmCompare of term * term
  | TmTuple of term list
  | TmProjection of term * string
  | TmRecord of (string * term) list
  | TmNil of ty
  | TmCons of ty * term * term
  | TmIsNil of ty * term
  | TmHead of ty * term
  | TmTail of ty * term
  | TmVariant of ty * (string * term)
  | TmCase of term * (string * string * term) list

;;

type command = 
  Eval of term
| Bind of string * term
| TyBind of string * ty
| EvalTy of string
;;

val emptyctx : 'a context;;
val addbinding : 'a context -> string -> 'a  -> 'a context;;
val getbinding : 'a context -> string -> 'a;;

(* val string_of_ty : ty -> string;; *)
exception Type_error of string;;
val typeof : ty context -> term -> ty;;

(* val string_of_term : term -> string;; *)
exception NoRuleApplies;;
val eval : term context -> ty context-> term -> term

val pretty_print : ty context -> term -> unit
val pretty_print_ty : ty context -> ty -> string;;

val execute : term context * ty context -> command -> term context * ty context;;
