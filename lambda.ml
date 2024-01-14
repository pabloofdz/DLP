(*
Diego Suárez Ramos : diego.suarez.ramos@udc.es
Pablo Fernández Perez : pablo.fperez@udc.es   
*)

(* TYPE DEFINITIONS *)

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
  (string * 'a) list
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


exception Type_error of string


(* CONTEXT MANAGEMENT *)

let emptyctx =
  []
;;


let addbinding ctx x bind =
  (x, bind) :: ctx
;;


let getbinding ctx x =
  try List.assoc x ctx with 
    Not_found -> raise (Type_error "type does not exist")
;;


(* TYPE MANAGEMENT (TYPING) *)

let rec is_atomicTy typectx ty = match ty with
    TyBool -> true
  | TyNat -> true
  | TyString -> true
  | TyTuple tyl -> true
  | TyRecord tyl -> true
  | TyList tyl -> true
  | TyVariant tyv -> true
  | TyName s -> if is_atomicTy typectx (getbinding typectx s) then true else false
  | _ -> false
;;


let rec pretty_print_ty typectx ty = match ty with
    TyBool ->
      "Bool"

  | TyNat ->
      "Nat"

  | TyArr (t1, t2) ->
      if is_atomicTy typectx t1 && is_atomicTy typectx t2 then pretty_print_ty typectx t1 ^ " -> "  ^ pretty_print_ty typectx t2
      else if is_atomicTy typectx t1 && not (is_atomicTy typectx t2) then pretty_print_ty typectx t1 ^ " -> " ^ pretty_print_ty typectx t2
      else if not (is_atomicTy typectx t1) && is_atomicTy typectx t2 then "(" ^ pretty_print_ty typectx t1 ^ ") -> " ^ pretty_print_ty typectx t2
      else "(" ^ pretty_print_ty typectx t1 ^ ")" ^ " -> " ^ pretty_print_ty typectx t2
  
  | TyString ->
      "String"

  | TyTuple tyr ->
        let rec printTuple = function
          [] -> ""
        | (ty::[]) -> (pretty_print_ty typectx ty)
        | (ty::t) -> (pretty_print_ty typectx ty) ^ ", " ^ printTuple t
    in "{" ^  (printTuple tyr) ^ "}"

  | TyRecord tyr ->
      let rec printrecord = function
        [] -> ""
        |((s,ty)::[]) -> s ^ " : " ^ (pretty_print_ty typectx ty)
        |((s,ty)::t) ->  s ^ " : " ^ (pretty_print_ty typectx ty) ^ ", " ^ printrecord t
      in "{" ^ (printrecord tyr) ^ "}"

  | TyList tyl -> "List["^ pretty_print_ty typectx tyl ^ "]"

  | TyVariant (tyv) -> 
    let rec printvariant = function
      [] -> ""
      |((s,ty)::[]) -> s ^ " : " ^ (pretty_print_ty typectx ty)
      |((s,ty)::t) ->  s ^ " : " ^ (pretty_print_ty typectx ty) ^ ", " ^ printvariant t
    in "<" ^ (printvariant tyv) ^ ">"

  | TyName s ->
    (pretty_print_ty typectx (getbinding typectx s))
;;


let rec subtypeof subty superty = match (subty, superty) with

  (* S-Arrow *)
  | (TyArr(subty1, subty2), TyArr(superty1, superty2)) -> ((subtypeof superty1 subty1) && (subtypeof subty2 superty2))
  
  (* Lists *)
  | (TyList(tysub), TyList(tysuper)) -> (subtypeof tysub tysuper)

  (* S-RcdWidth / S-RcdPerm / S-RcdDepth*)
  | (TyRecord(lsub), TyRecord(lsuper)) ->
    let findKeys l (k, ty) = 
      try 
        subtypeof (List.assoc k l) ty
      with _ -> false
    (*Vamos comprobando si todas las claves de lsuper estan en lsub*)
    (*Si el tipo de estas claves en lsub es subtipo del tipo de las claves de lsuper, el reg1 es subtipo del reg2.*)
    in let rec cont lsub lsuper = match lsuper with
      | []     -> true
      | (h::t) -> (findKeys lsub h) && (cont lsub t)
    in cont lsub lsuper

  (* S-VariantWidth / S-VariantPerm / S-VariantDepth*)
  | (TyVariant(lsub),TyVariant(lsuper)) -> 
    let findKeys (k, ty) l = 
      try 
        subtypeof ty (List.assoc k l)
      with _ -> false
    (*Vamos comprobando si todas las claves de lsub estan en lsuper*)
    (*Si el tipo de estas claves en lsub es subtipo del tipo de las claves de lsuper, el reg1 es subtipo del reg2.*)
    in let rec cont lsub lsuper = match lsub with
      | []     -> true
      | (h::t) -> (findKeys h lsuper) && (cont t lsuper)
    in cont lsub lsuper

  (* S-Refl *)
  | (subty, superty) -> subty = superty
;;


let rec typeof ctx tm =
  let rec obtTy = function
    TyName t -> getbinding ctx t
  | s -> s in
  let rec tyarrowtolarge = function
    TyArr (t1,t2) -> (TyArr(tyarrowtolarge t1,tyarrowtolarge t2))
    | TyList t -> TyList (obtTy t)
    | s -> (obtTy s) in
  match tm with
    (* T-True *)
    TmTrue ->
      TyBool

    (* T-False *)
  | TmFalse ->
      TyBool

    (* T-If *)
  | TmIf (t1, t2, t3) ->
      if obtTy(typeof ctx t1) = TyBool then
        let tyT2 = obtTy(typeof ctx t2) in
        if obtTy(typeof ctx t3) = tyT2 then tyT2
        else raise (Type_error "arms of conditional have different types")
      else
        raise (Type_error "guard of conditional not a boolean")

    (* T-Zero *)
  | TmZero ->
      TyNat

    (* T-Succ *)
  | TmSucc t1 ->
      if obtTy(typeof ctx t1) = TyNat then TyNat
      else raise (Type_error "argument of succ is not a number")

    (* T-Pred *)
  | TmPred t1 ->
      if obtTy(typeof ctx t1) = TyNat then TyNat
      else raise (Type_error "argument of pred is not a number")

    (* T-Iszero *)
  | TmIsZero t1 ->
      if obtTy(typeof ctx t1) = TyNat then TyBool
      else raise (Type_error "argument of iszero is not a number")

    (* T-Var *)
  | TmVar x ->
      (try getbinding ctx x with
       _ -> raise (Type_error ("no binding type for variable " ^ x)))

    (* T-Abs *)
  | TmAbs (x, tyT1, t2) ->
      let ctx' = addbinding ctx x (obtTy(tyT1)) in
      let tyT2 = obtTy(typeof ctx' t2) in
      TyArr (tyT1, tyT2)

    (* T-App *)
    |TmApp (t1, t2) ->
      let tyT1 = obtTy(typeof ctx t1) in
      let tyT2 = obtTy(typeof ctx t2) in
      (match tyT1 with
           TyArr (tyT11, tyT12) ->
             if (subtypeof (tyarrowtolarge(tyT2)) (tyarrowtolarge(tyT11))) then (obtTy(tyT12))
             else raise (Type_error "parameter type mismatch!")
         | _ -> raise (Type_error "arrow type expected"))

    (* T-Let *)
  | TmLetIn (x, t1, t2) ->
      let tyT1 = obtTy(typeof ctx t1) in
      let ctx' = addbinding ctx x tyT1 in
      obtTy(typeof ctx' t2)

    (* T-Fix *)
  | TmFix t1 ->
      let tyT1 = obtTy(typeof ctx t1) in
      (match tyT1 with
        TyArr (tyT11, tyT12) ->
          if (subtypeof (tyarrowtolarge(tyT12)) (tyarrowtolarge(tyT11))) then (obtTy(tyT12))
          else raise (Type_error "result of body not compatible with domain2")
      | _ -> raise (Type_error "arrow type expected"))
    
    (* new rule for string *)
  | TmString _ ->
      TyString

    (* new rule for string *)
  | TmConcat (t1, t2) ->
      if obtTy(typeof ctx t1) = TyString && (obtTy(typeof ctx t2)) = TyString then TyString
      else raise (Type_error "argument of concat is not a string")   

    (* new rule for string *)
  | TmLength (t1) ->
      if obtTy(typeof ctx t1) = TyString then TyNat
      else raise (Type_error "argument of length is not a string")   
    
      (* new rule for string *)
  | TmCompare (t1, t2) ->
      if obtTy(typeof ctx t1) = TyString && (obtTy(typeof ctx t2)) = TyString then TyNat
      else raise (Type_error "argument of compare is not a string")

      (* T-Tuple *)
  | TmTuple list ->
      let rec types = function
        [] -> []
        | (h::t) -> ((obtTy(typeof ctx h))::(types t))
      in TyTuple (types list) 

      (* T-Rcd *)
  |TmRecord tmr -> 
      let rec types = function
       [] -> []
       |((s,tm)::t) -> ((s,(obtTy(typeof ctx tm)))::(types t))
      in TyRecord (types tmr)

      (* T-Variant *)
  |TmVariant ((TyVariant ty),(s,tm)) -> 
    let tyTm = obtTy(typeof ctx tm) in
      let rec types = function
        [] -> raise (Type_error ("label does not exist"))
      | ((s1,t1)::t) -> if (s=s1) then t1 else (types t)
      in  if (tyTm = (types ty)) then TyVariant ty else raise (Type_error ("incorrect type1"))

  | TmVariant ((TyName s1),(s,tm)) -> 
    let rec buscar = function
    TyVariant ty -> ty
    | _ -> raise (Type_error ("Error")) in 
    let ty = buscar(getbinding ctx s1) in
    let tyTm = obtTy(typeof ctx tm) in
    let rec types = function
    [] -> raise (Type_error ("label does not exist"))
    | ((s1,t1)::t) ->  if (s=s1) then t1 else (types t)
    in  if (tyTm = (types ty)) then TyVariant ty else raise (Type_error ("incorrect type2"))

  | TmVariant (_,_) ->  raise (Type_error ("incorrect type3"))

      (* T-Proj *)
  | TmProjection (t,n) ->
      (match(obtTy(typeof ctx t), n) with
        |(TyList (ty), _) -> obtTy(ty)
        |(TyRecord (tyr), s) ->
        (try List.assoc s tyr with
        _ -> raise (Type_error ("key "^ s ^ " does not exist in the record"))) 
        |(TyTuple (tyr), s) ->
          (try List.nth tyr (int_of_string s - 1) with
          _ -> raise (Type_error ("key "^ s ^ " does not exist in the record")))
        | _ -> raise (Type_error ("only Tuples")))

      (* T-Nil *)
  | TmNil ty -> TyList (obtTy(ty))

      (* T-Cons, check the type of the elements of the list*)
  | TmCons (ty,h,t) ->
        let tyTh = obtTy(typeof ctx h) in
          let tyTt = obtTy(typeof ctx t) in
            if ((subtypeof (tyarrowtolarge(tyTh)) (tyarrowtolarge(obtTy(ty)))) && (subtypeof (TyList(tyarrowtolarge((obtTy ty)))) (tyarrowtolarge(tyTt)))) then 
              TyList(ty) else raise (Type_error "elements of list have different types")

      (* T-IsNil *)
  | TmIsNil (ty,t) ->
        if (tyarrowtolarge(typeof ctx t)) = (tyarrowtolarge(TyList(obtTy(ty)))) then TyBool
        else raise (Type_error ("argument of isnil is not a type list"))

      (* T-Head *)
  | TmHead (ty,t) ->
        if tyarrowtolarge(typeof ctx t) = (tyarrowtolarge(TyList(obtTy(ty)))) then obtTy(ty)
        else raise (Type_error ("argument of isnil is not a type list"))

      (* T-Tail *)
  | TmTail (ty,t) ->
        if tyarrowtolarge(typeof ctx t) = (tyarrowtolarge(TyList(obtTy(ty)))) then TyList(obtTy(ty))
        else raise (Type_error ("argument of isnil is not a type list"))

      (* T-Case *)
  | TmCase (tm,(nametm,p,t1)::l) ->
    let rec buscartipovariable n = function
      TyVariant [] -> raise (Type_error ("Error1"))
      | TyVariant ((name,ty1)::t) -> if (name=n) then obtTy(ty1) else (buscartipovariable n (TyVariant t))
      | TyName s ->(buscartipovariable n (getbinding ctx s))
      | _-> raise (Type_error ("Error2")) in
    let tipopname = buscartipovariable nametm (obtTy(typeof ctx tm)) in
    let ctx2 = (addbinding ctx p tipopname) in
    let tyHead = typeof ctx2 t1 in
    let rec tipo t2 = function
    [] -> obtTy(t2)
    | (pname2,pname,t1)::t ->let ctx' = (addbinding ctx pname (buscartipovariable pname2 (obtTy(typeof ctx tm)))) in if(t2=(typeof ctx' t1)) then (tipo t2 t) else (raise (Type_error ("tipos imcompatibles en el case")))
  in (tipo tyHead l)
  | TmCase (_,[]) -> (raise (Type_error ("cases required")))
;;


let rec ldif l1 l2 = match l1 with
    [] -> []
  | h::t -> if List.mem h l2 then ldif t l2 else h::(ldif t l2)
;;


let rec lunion l1 l2 = match l1 with
    [] -> l2
  | h::t -> if List.mem h l2 then lunion t l2 else h::(lunion t l2)
;;


let rec free_vars tm = match tm with
    TmTrue ->
      []

  | TmFalse ->
      []

  | TmIf (t1, t2, t3) ->
      lunion (lunion (free_vars t1) (free_vars t2)) (free_vars t3)

  | TmZero ->
      []

  | TmSucc t ->
      free_vars t

  | TmPred t ->
      free_vars t

  | TmIsZero t ->
      free_vars t

  | TmVar s ->
      [s]

  | TmAbs (s, _, t) ->
      ldif (free_vars t) [s]

  | TmApp (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)

  | TmLetIn (s, t1, t2) ->
      lunion (ldif (free_vars t2) [s]) (free_vars t1)

  | TmFix t ->
      free_vars t

  | TmString _ ->
      []

  | TmConcat (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)

  | TmLength t ->
      free_vars t

  | TmCompare (t1, t2) ->
      lunion (free_vars t1) (free_vars t2)

  | TmTuple list ->
      let rec freevars = function
        [] -> []
        | (h::t) -> lunion (free_vars h) (freevars t)
      in freevars list 

  | TmProjection (t, n) ->
      free_vars t

  | TmRecord tmr ->
     let rec get_free = function
      [] -> []  
      |((_,tm)::t) -> lunion (free_vars tm) (get_free t)
     in get_free tmr

  | TmVariant (_,(_,t)) -> (free_vars t)

  | TmNil ty ->
      []
      
  | TmCons (ty,t1,t2) ->
        lunion (free_vars t1) (free_vars t2)
        
  | TmIsNil (ty,t) ->
      free_vars t
     
  | TmHead (ty,t) ->
      free_vars t
      
  | TmTail (ty,t) ->
      free_vars t

  | TmCase (t1,l) -> 
    let rec get_free = function
      [] ->[]  
      | ((_,s,term)::[]) -> (ldif (free_vars term) [s])
      |((_,s,term)::termt) -> lunion (ldif (free_vars term) [s]) (get_free termt)
     in (lunion (free_vars t1) (get_free l))
;;


let rec fresh_name x l =
  if not (List.mem x l) then x else fresh_name (x ^ "'") l
;;


let rec subst x s tm = match tm with
    TmTrue ->
      TmTrue

  | TmFalse ->
      TmFalse

  | TmIf (t1, t2, t3) ->
      TmIf (subst x s t1, subst x s t2, subst x s t3)

  | TmZero ->
      TmZero

  | TmSucc t ->
      TmSucc (subst x s t)

  | TmPred t ->
      TmPred (subst x s t)

  | TmIsZero t ->
      TmIsZero (subst x s t)

  | TmVar y ->
      if y = x then s else tm

  | TmAbs (y, tyY, t) ->
      if y = x then tm
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmAbs (y, tyY, subst x s t)
           else let z = fresh_name y (free_vars t @ fvs) in
                TmAbs (z, tyY, subst x s (subst y (TmVar z) t))

  | TmApp (t1, t2) ->
      TmApp (subst x s t1, subst x s t2)

  | TmLetIn (y, t1, t2) ->
      if y = x then TmLetIn (y, subst x s t1, t2)
      else let fvs = free_vars s in
           if not (List.mem y fvs)
           then TmLetIn (y, subst x s t1, subst x s t2)
           else let z = fresh_name y (free_vars t2 @ fvs) in
                TmLetIn (z, subst x s t1, subst x s (subst y (TmVar z) t2))

  | TmFix t ->
      TmFix (subst x s t)

  | TmString st ->
      TmString st

  | TmConcat (t1, t2) ->
      TmConcat (subst x s t1, subst x s t2)

  | TmLength t ->
      TmLength (subst x s t)

  | TmCompare (t1, t2) ->
      TmCompare (subst x s t1, subst x s t2)

  | TmTuple list ->
      let rec substterms = function
        [] -> []
        | (h::t) -> (subst x s h)::(substterms t)
      in TmTuple (substterms list) 

  | TmRecord tmr ->
     let rec subsrecord = function
       [] -> []
       |((str,tm)::t) -> (str,(subst x s tm))::(subsrecord t)
      in TmRecord (subsrecord tmr)

  | TmVariant (ty,(s1,t)) -> TmVariant(ty,(s1,(subst x s t)))

  | TmProjection (t,n) ->
      TmProjection  (subst x s t, n)
      
  | TmNil ty ->
      tm
      
  | TmCons (ty,t1,t2) ->
        TmCons (ty, (subst x s t1), (subst x s t2))
    
  | TmIsNil (ty,t) ->
       TmIsNil (ty, (subst x s t))
       
  | TmHead (ty,t) ->
       TmHead (ty, (subst x s t))
       
  | TmTail (ty,t) ->
       TmTail (ty, (subst x s t))

  | TmCase (t1,l) -> let rec sustincases = function 
  []-> []
  | ((s1,s2,ter)::t) -> ((s1,s2,(subst x s ter))::(sustincases t))
  in (TmCase ((subst x s t1), (sustincases l)))
;;


let rec isnumericval tm = match tm with
    TmZero -> true

  | TmSucc t -> isnumericval t

  | _ -> false
;;


let rec isval tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmAbs _ -> true
  | TmString _ -> true
  | t when isnumericval t -> true
  | TmRecord [] -> true 
  | TmRecord l -> List.for_all(fun (s,t) -> isval(t)) l 
  | TmTuple list -> List.for_all(fun t -> isval(t)) list
  | TmNil _ -> true
  | TmCons(_,h,t) -> (isval h) && (isval t)
  | TmVariant (_,(_,t)) -> (isval t)
  | _ -> false
;;


exception NoRuleApplies;;


let rec eval1 ctx typectx tm = match tm with
    (* E-IfTrue *)
    TmIf (TmTrue, t2, _) ->
      t2

    (* E-IfFalse *)
  | TmIf (TmFalse, _, t3) ->
      t3

    (* E-If *)
  | TmIf (t1, t2, t3) ->
      let t1' = eval1 ctx typectx t1 in
      TmIf (t1', t2, t3)

    (* E-Succ *)
  | TmSucc t1 ->
      let t1' = eval1 ctx typectx t1 in
      TmSucc t1'

    (* E-PredZero *)
  | TmPred TmZero ->
      TmZero

    (* E-PredSucc *)
  | TmPred (TmSucc nv1) when isnumericval nv1 ->
      nv1

    (* E-Pred *)
  | TmPred t1 ->
      let t1' = eval1 ctx typectx t1 in
      TmPred t1'

    (* E-IszeroZero *)
  | TmIsZero TmZero ->
      TmTrue

    (* E-IszeroSucc *)
  | TmIsZero (TmSucc nv1) when isnumericval nv1 ->
      TmFalse
    (* E-Iszero *)
  | TmIsZero t1 ->
      let t1' = eval1 ctx typectx t1 in
      TmIsZero t1'

    (* E-AppAbs *)
  | TmApp (TmAbs(x, _, t12), v2) when isval v2 ->
      subst x v2 t12

    (* E-App2: evaluate argument before applying function *)
  | TmApp (v1, t2) when isval v1 ->
      let t2' = eval1 ctx typectx t2 in
      TmApp (v1, t2')

    (* E-App1: evaluate function before argument *)
  | TmApp (t1, t2) ->
      let t1' = eval1 ctx typectx t1 in
      TmApp (t1', t2)

    (* E-LetV *)
  | TmLetIn (x, v1, t2) when isval v1 ->
      subst x v1 t2

    (* E-Let *)
  | TmLetIn(x, t1, t2) ->
      let t1' = eval1 ctx typectx t1 in
      TmLetIn (x, t1', t2)

    (* E-FixBeta *)
  | TmFix (TmAbs (x, _, t2)) ->
      subst x tm t2

    (* E-Fix *)
  | TmFix t1 ->
      let t1' = eval1 ctx typectx t1 in
      TmFix t1'
  
    (* new rule for string *)
  | TmConcat (TmString s1, TmString s2) ->
      TmString (s1 ^ s2)

    (* new rule for string *)    
  | TmConcat (TmString s1, t2) ->
      let t2' = eval1 ctx typectx t2 in
      TmConcat (TmString s1, t2')

    (* new rule for string *)      
  | TmConcat (t1, t2) ->
      let t1' = eval1 ctx typectx t1 in
      TmConcat (t1', t2)

    (* new rule for string *)    
  | TmLength (TmString s1) ->
      let l1 = (String.length s1) in
      let rec f = function
      0 -> TmZero
      | n -> TmSucc (f (n-1))
      in f l1

    (* new rule for string *)      
  | TmLength t1 ->
      let t1' = eval1 ctx typectx t1 in
      TmLength t1'
    
    (* new rule for string *)
  | TmCompare (TmString s1, TmString s2) ->
      let t1 = (String.compare s1 s2) in  
      if t1=0 then TmZero
      else if t1<0 then TmSucc (TmSucc (TmZero))
      else TmSucc (TmZero)

    (* new rule for string *)    
  | TmCompare (TmString s1, t2) ->
      let t2' = eval1 ctx typectx t2 in
      TmCompare (TmString s1, t2')

    (* new rule for string *)      
  | TmCompare (t1, t2) ->
      let t1' = eval1 ctx typectx t1 in
      TmCompare (t1', t2)

  | TmVar s -> 
        getbinding ctx s

  | TmTuple list ->
    let rec evalterms = function
      [] -> raise NoRuleApplies
      | (h::t) when isval h -> h::(evalterms t)
      | (h::t) -> (eval1 ctx typectx h)::t
    in TmTuple (evalterms list)  

    (*E-Proj*)
  | TmProjection (TmTuple l as v , s) when isval(v) -> 
    List.nth l (int_of_string s - 1)
  |TmProjection (TmRecord l as v , s) when isval(v) -> 
    List.assoc s l 

    (*E-ProjRcd*)
  |TmProjection (TmRecord (tmr), n) ->
     List.assoc n tmr 

  | TmProjection (t,n) ->
    TmProjection ((eval1 ctx typectx t), n)   
    
    (*E-Rcd*)
  | TmRecord tmr ->
     let rec evalrecord = function
       [] -> raise NoRuleApplies
       |((str,tm)::t) when isval tm -> (str,tm)::(evalrecord t)
       |((str,tm)::t) -> (str,(eval1 ctx typectx tm))::t
      in 
      let rec checkRecord l= function
      []-> true
      | ((str,_)::t) -> if (List.mem str l) then false else (checkRecord (str::l) t)
    in if (checkRecord [] tmr) then TmRecord (evalrecord tmr) else (raise (Type_error ("Nombres repetidos")))

  | TmVariant (TyName s1,(s,tm)) ->TmVariant ((getbinding typectx s1),(s,(eval1 ctx typectx tm)))

    (* E-Variant *)
  | TmVariant (ty,(s,tm)) ->TmVariant (ty,(s,(eval1 ctx typectx tm)))
  
    (* E-Cons2 *)
  |TmCons(ty,h,t) when isval h -> TmCons(ty,h,(eval1 ctx typectx t))
  
    (* E-Cons1 *)
  |TmCons(ty,h,t) -> TmCons(ty,(eval1 ctx typectx h),t)
  
    (* E-IsNilNil *)
  |TmIsNil(ty,TmNil(_)) -> TmTrue
  
    (* E-IsNilCons *)
  |TmIsNil(ty,TmCons(_,_,_)) -> TmFalse
  
    (* E-IsNil *)
  |TmIsNil(ty,t) -> TmIsNil(ty,eval1 ctx typectx t)
  
    (* E-HeadCons *)
  |TmHead(ty,TmCons(_,h,_))-> h
  
    (* E-Head *)
  |TmHead(ty,t) -> TmHead(ty,eval1 ctx typectx t)
  
    (* E-TailCons *)
  |TmTail(ty,TmCons(_,_,t)) -> t
  
    (* E-Tail *)
  |TmTail(ty,t) -> TmTail(ty,eval1 ctx typectx t)

    (* T-Case *)
  | TmCase ((TmVariant(ty,(s,t1))),l)  ->
    let rec buscar = function
    [] -> raise (Type_error ("Error"))
    | (namePos,nameVar,t2)::t -> if (namePos=s) then (nameVar,t2) else (buscar t)
  in let (nameVar,t2) = buscar l in
    (subst nameVar t1 t2) 
  | TmCase (_,_) ->raise (Type_error ("Error"))

  | _ ->
      raise NoRuleApplies
;;


let apply_ctx ctx tm = 
  List.fold_left (fun t x ->subst x (getbinding ctx x) t) tm (free_vars tm)
 ;;


let rec eval ctx typectx tm = 
  (try
    let tm' = eval1 ctx typectx tm in
    eval ctx typectx tm'
  with
    NoRuleApplies -> apply_ctx ctx tm)
;;


let is_atomic_term tm = match tm with
    TmTrue  -> true
  | TmFalse -> true
  | TmVar _ -> true
  | TmString _ -> true
  | TmZero -> true
  | _ -> false
;;


let rec pretty_print typectx = function 
  TmTrue ->
    Printf.printf "true"

| TmFalse ->
    Printf.printf "false"

| TmIf (t1,t2,t3) ->
    Printf.printf "\n  if "; (pretty_print typectx t1); Printf.printf "\n    then "; (pretty_print typectx t2); Printf.printf "\n    else "; (pretty_print typectx t3);

| TmZero ->
    Printf.printf "0"

| TmSucc t ->
   let rec f n t' = match t' with
        TmZero -> Printf.printf "%d" n
      | TmSucc s -> f (n+1) s
      | _ -> Printf.printf "succ ("; (pretty_print typectx t); Printf.printf ")"
    in f 1 t

| TmPred t ->
   if is_atomic_term t then (Printf.printf "pred "; (pretty_print typectx t))
   else (Printf.printf "pred ("; (pretty_print typectx t); Printf.printf ")")

| TmIsZero t ->
    if is_atomic_term t then (Printf.printf "iszero "; (pretty_print typectx t))
    else (Printf.printf "iszero ("; (pretty_print typectx t); Printf.printf ")")

| TmVar s ->
    Printf.printf "%s" s;

| TmAbs (s, tyS, t) ->
    Printf.printf "lambda %s:%s." s (pretty_print_ty typectx tyS);Printf.printf " "; (pretty_print typectx t)

| TmApp (t1, t2) ->
    if is_atomic_term t1 && is_atomic_term t2 then ((pretty_print typectx t1);Printf.printf " "; (pretty_print typectx t2))
    else if is_atomic_term t1 && not (is_atomic_term t2) then ((pretty_print typectx t1); Printf.printf " ("; (pretty_print typectx t2); Printf.printf ")")
    else if not (is_atomic_term t1) && is_atomic_term t2 then (Printf.printf "("; (pretty_print typectx t1); Printf.printf ") "; (pretty_print typectx t2))
    else (Printf.printf "("; (pretty_print typectx t1);Printf.printf ") ("; (pretty_print typectx t2); Printf.printf ")")

| TmLetIn (s, t1, t2) ->
    Printf.printf "let %s = " s ; (pretty_print typectx t1); Printf.printf "\nin "; (pretty_print typectx t2)

| TmFix t ->
    if is_atomic_term t then (Printf.printf "fix "; (pretty_print typectx t))
    else (Printf.printf "fix ("; (pretty_print typectx t); Printf.printf ")" )

| TmString s ->
    Printf.printf "\"%s\"" s

| TmConcat (t1, t2) ->
    if is_atomic_term t1 && is_atomic_term t2 then (Printf.printf "concat "; (pretty_print typectx t1); Printf.printf " "; (pretty_print typectx t2))
    else if is_atomic_term t1 && not (is_atomic_term t2) then (Printf.printf "concat "; (pretty_print typectx t1); Printf.printf " ("; (pretty_print typectx t2); Printf.printf ")")
    else if not (is_atomic_term t1) && is_atomic_term t2 then (Printf.printf "concat ("; (pretty_print typectx t1); Printf.printf ") "; (pretty_print typectx t2))
    else (Printf.printf "concat (";(pretty_print typectx t1); Printf.printf ") ("; (pretty_print typectx t2);Printf.printf ")")

| TmLength t ->
    if is_atomic_term t then (Printf.printf "length "; (pretty_print typectx t))
    else (Printf.printf "length ("; (pretty_print typectx t); Printf.printf ")")

| TmCompare (t1, t2) ->
    if is_atomic_term t1 && is_atomic_term t2 then (Printf.printf "compare "; (pretty_print typectx t1); Printf.printf " "; (pretty_print typectx t2))
    else if is_atomic_term t1 && not (is_atomic_term t2) then (Printf.printf "compare "; (pretty_print typectx t1); Printf.printf " ("; (pretty_print typectx t2);Printf.printf ")")
    else if not (is_atomic_term t1) && is_atomic_term t2 then (Printf.printf "compare ("; (pretty_print typectx t1); Printf.printf ") "; (pretty_print typectx t2))
    else (Printf.printf "compare ("; (pretty_print typectx t1); Printf.printf ") ("; (pretty_print typectx t2); Printf.printf ")")

| TmTuple t ->
  let rec printTuple = function
    [] -> Printf.printf ""
    |(tm::[]) -> (pretty_print typectx tm)
    |(tm::t) -> (pretty_print typectx tm); Printf.printf ", "; printTuple t
  in (Printf.printf "{"; (printTuple t); Printf.printf "}" )  

| TmProjection (t,n) ->
    pretty_print typectx t; Printf.printf "."; Printf.printf "%s" n

| TmRecord tmr ->
    let rec printrecord = function
      [] -> Printf.printf ""
      |((s,tm)::[]) -> Printf.printf "%s" s; Printf.printf " = "; (pretty_print typectx tm)
      |((s,tm)::t) ->  Printf.printf "%s" s; Printf.printf " = "; (pretty_print typectx tm); Printf.printf ", "; printrecord t
     in (Printf.printf "{"; (printrecord tmr); Printf.printf "}" )

| TmNil ty -> Printf.printf "nil[%s]" (pretty_print_ty typectx ty)

| TmCons (ty,h,(TmNil ty2)) -> Printf.printf "cons[%s]" (pretty_print_ty typectx ty); Printf.printf " "; pretty_print typectx h; Printf.printf " "; pretty_print typectx (TmNil ty2);

| TmCons (ty,h,t) -> Printf.printf "cons[%s]" (pretty_print_ty typectx ty); Printf.printf " "; pretty_print typectx h; Printf.printf " ("; pretty_print typectx t; Printf.printf ")"

| TmIsNil (ty,t) -> Printf.printf "isnil[%s]" (pretty_print_ty typectx ty); Printf.printf "("; pretty_print typectx t; Printf.printf ")"

| TmHead (ty,t) -> Printf.printf "head[%s]" (pretty_print_ty typectx ty); Printf.printf "("; pretty_print typectx t; Printf.printf ")"

| TmTail (ty,t) -> Printf.printf "tail[%s]" (pretty_print_ty typectx ty); Printf.printf "("; pretty_print typectx t; Printf.printf ")"

| TmVariant (ty,(s,t)) -> Printf.printf "<%s = " s; pretty_print typectx t; Printf.printf ">"

| TmCase (t1,(s11,s12,t21)::l) ->
    let rec printCase = function
    [] -> Printf.printf ""
    | ((s1,s2,t2)::t)->  (Printf.printf("\n    | <%s = %s> => ") s1 s2; pretty_print typectx t2; printCase t)
  in Printf.printf("\n  case "); pretty_print typectx t1; Printf.printf (" of\n") ;(Printf.printf("      <%s = %s> => ") s11 s12; pretty_print typectx t21; printCase l)

| TmCase (_,_) ->  raise (Type_error ("there must be cases"))
;;


let is_nat tm = match tm with
    TmSucc x -> true
  | TmPred x -> true
  | _ -> false
;;

let execute (defctx, typectx) = function
    Eval tm ->
      let tyTm = typeof typectx tm in
      let tm' = eval defctx typectx tm in
      if ((is_atomic_term tm') || (is_nat tm')) then (Printf.printf "- : %s = " (pretty_print_ty typectx tyTm);  pretty_print typectx tm'; print_endline(""))
      else
        (Printf.printf "- : %s = \n" (pretty_print_ty typectx tyTm);  pretty_print typectx tm'; print_endline(""));
      (defctx, typectx)

  | Bind (s, tm) ->
      let tyTm = typeof typectx tm in
      let tm' = eval defctx typectx tm in
      if ((is_atomic_term tm') || (is_nat tm')) then (Printf.printf "%s : %s = " (s) (pretty_print_ty typectx tyTm) ;pretty_print typectx tm'; print_endline(""))
      else 
        (Printf.printf "%s : %s = \n" (s) (pretty_print_ty typectx tyTm) ;pretty_print typectx tm'; print_endline("")); 
      (addbinding defctx s tm', addbinding typectx s tyTm)

  | TyBind(s,ty) ->
      let rec checkVariants l = function
      TyVariant []-> true
      | TyVariant ((s1,ty1)::t) ->if ((List.mem s1 l) || not(checkVariants [] ty1)) then false else (checkVariants (s1::l) (TyVariant t))
      | TyArr (t1,t2) -> (checkVariants [] t1) && (checkVariants [] t2)
      | TyRecord [] -> true
      | TyRecord ((s1,ty1)::t) -> if ((List.mem s1 l) || not(checkVariants [] ty1)) then false else (checkVariants (s1::l) (TyRecord t))
      | TyTuple [] -> true
      | TyTuple (h::t) -> if not(checkVariants [] h) then  false else (checkVariants [] (TyTuple t))
      | TyList t -> (checkVariants [] t)
      | _ ->true
  in if (checkVariants [] ty) then
      (Printf.printf "type %s = %s" (s) (pretty_print_ty typectx ty); print_endline("");
      (defctx, addbinding typectx s ty)) else (raise (Type_error ("Nombres repetidos")))

  | EvalTy s ->
      let tyTm = getbinding typectx s in
      Printf.printf "type %s = %s" (s) (pretty_print_ty typectx tyTm); print_endline("");
      (defctx, typectx)
;;