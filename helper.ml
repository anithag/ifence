open Ast

exception HelperError 
exception HelperError1 
exception HelperError2 
exception HelperError3 

(* [typ_eq t1 t2] returns [true] iff [t1] and [t2] are equal *)  
let typ_eq (t1:labeltype) (t2:labeltype) : bool = 
  t1 = t2

(* ---------- SUBSTITUTIONS ----------- *)

(* [subst_typ p0 x p] replaces [ModeVar x] with [p] in [p0] *)
let rec subst_modetype (p0:mode) (x:var) (p:mode) : mode =
  match p0 with
  |Enclave -> Enclave
  |Normal  -> Normal
  |ModeVar y -> if x = y then p else p0

(* [apply_subst s p0] applies the substitution [s] to [p0] *)
let rec apply_subst (s:subst) (p0:mode) : mode =
  match p0 with
  | Enclave -> Enclave
  | Normal  -> Normal
  | ModeVar y -> (try (apply_subst s (ModeVarMap.find y s)) with Not_found -> p0)

(* [subst_constr c0 x rho] replaces [ModeVar x] with [rho] in [c0] *)
let rec subst_constr (c0:constr) (x:var) (rho:mode): constr =
  Constr.fold
    (fun (p1,p2) -> Constr.add (subst_modetype p1 x rho, subst_modetype p2 x rho))
    c0 Constr.empty

(* ------------Conversion functions ----------*)

let construct_enc_lam_exp (e:exp) (es: encstmt) (rho:mode) (rho':mode) : encexp =
  match e with
 |Lam(p,u,q,s) -> ELam(rho, rho',p,u,q, es)
 | _  -> raise HelperError
 
let construct_enc_exp (e:exp) (rho:mode) (rho':mode) : encexp =
  match e with
 |Loc l ->ELoc(rho, rho', l)
 |Var x ->EVar(rho,x)
 |_    -> raise HelperError

(* -----------UPDATE CONSTRAINTS ------------*)

let rec update_constraints (t: (mode * mode) list) (c:constr): constr = 
  match t with
 | [] -> c
 | h::ts -> let c' = (Constr.add h c) in
		update_constraints ts c'

let get_src_content_type (t : labeltype) =
     match t with
    |(BtRef lt), p -> lt
    | _    -> raise HelperError1


let get_content_type (t : enclabeltype) =
     match t with
    |EBtRef(m, lt), p -> lt
    | _    -> raise HelperError2

let get_mode (t: enclabeltype) =
   match t with
   |EBtRef(m, lt), p -> m
   |EBtFunc(m,p,u), q -> m
   | _ -> raise HelperError3

let rec countCondConstraints (c:constr2) =
	  let rec outerloop c2 num_constraints =
          	let a, b = Constr2.choose c2 in
          	let c2' = Constr2.remove (a,b) c2 in
	  	let rec count li = match li with
			|[] -> 0
			|h::tail -> 1 + count tail
	   	in
	   	let constraints_per_row = count b in
		let totalconstraints = constraints_per_row + num_constraints in
                if (Constr2.is_empty c2') then totalconstraints else outerloop c2' totalconstraints 
         in
         outerloop c 0
          
let cost_is_zero = function
 |(PMonoterm (n, (Mono _)), PMonoterm (n', (Mono _))) -> if (n=0)&&(n'=0) then true else false 
 | _ -> false

(* ---------- FRESH TYPE VARIABLES ---------- *)
let tvar_cell = ref 1

(* [next_tvar ()] generates a fresh type variable *)
let next_tvar () : mode =
  let x = !tvar_cell in
  let s = "x" ^ string_of_int x in
  incr tvar_cell; ModeVar s

(* ------- Flatten Sequence ------------ *)
let rec flattenseq s = match s with
|Seq(c1, c2) -> flattenseq c1 @ flattenseq c2
| _   -> [s]

let getexpmode = function
  | EVar(rho, v) -> rho
  | ELam(rho, rho', p, u, q, s) -> rho 
  | EPlus (rho, l,r) -> rho
  | EConstant(rho,n) ->  rho
  | ETrue rho ->  rho
  | EFalse rho  -> rho
  | EEq (rho, l,r) -> rho
  | ELoc(rho, rho', l) ->rho
  | EDeref(rho,e) -> rho
  | EIsunset(rho,x) -> rho

let getstmtmode   = function
  | EIf (m,e,c1,c2) -> m
  | EAssign(m, x, e) ->m 
  | ESeq(m,s1, s2) -> m
  | ECall(m,e)    -> m
  | EUpdate(m,e1, e2) ->m
  | EWhile(m, b, s) -> m
  | ESkip (m, m') -> m'
  | EOutput(m,ch, e) ->m
  | ESet(m,x)	-> m
  | EESeq (m, _) -> m

