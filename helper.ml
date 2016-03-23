open Ast

exception HelperError 

(* [typ_eq t1 t2] returns [true] iff [t1] and [t2] are equal *)  
let typ_eq (t1:labeltype) (t2:labeltype) : bool = 
  t1 = t2


let number_of_enclaves = 10

let get_src_content_type (t : labeltype) =
     match t with
    |(BtRef lt), p -> lt
    | _    -> raise HelperError


let get_content_type (t : enclabeltype) =
     match t with
    |EBtRef(m, lt), p -> lt
    | _    -> raise HelperError

let get_mode (t: enclabeltype) =
   match t with
   |EBtRef(m, lt), p -> m
   |EBtFunc(m,_,p,u,_), q -> m
   |EBtCond m, p -> m
   | _ -> raise HelperError

let get_enc_precontext (t:enclabeltype) =
   match t with
   |EBtFunc(m,gencpre,p,u, gencpost), q -> gencpre
   |_ -> raise HelperError


let get_enc_postcontext (t:enclabeltype) =
   match t with
   |EBtFunc(m,gencpre,p,u, gencpost), q -> gencpost
   |_ -> raise HelperError

let get_src_precontext (t:labeltype) =
   match t with
   |BtFunc(gpre,p,u, gpost), q -> gpre
   |_ -> raise HelperError


let get_src_postcontext (t:labeltype) =
   match t with
   |BtFunc(gpre,p,u, gpost), q -> gpost
   |_ -> raise HelperError

let get_src_policy_lower_bound (t:labeltype) =
   match t with
   |BtFunc(gencpre,p,u, gencpost), q -> p
   |_ -> raise HelperError

let get_enc_policy_lower_bound (t:enclabeltype) =
   match t with
   |EBtFunc(m,gencpre,p,u, gencpost), q -> p
   |_ -> raise HelperError

(* Check if base types are same. Ignore policy for comparison 
*)
let rec check_src_base_type b1 b2 = match (b1, b2) with 
  | BtRef lt1, BtRef lt2 -> check_src_base_type (fst lt1) (fst lt2)
  | BtFunc (gpre1, p1, u1, gpost1), BtFunc (gpre2, p2, u2, gpost2) -> 
		      let ispreequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1=p2) && (check_src_base_type b1 b2) then true
				else false
			| _ -> false  
			end) gpre1 gpre2 in
		      let ispostequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1=p2) && (check_src_base_type b1 b2) then true
				else false
			| _ -> false  
			end ) gpost1 gpost2 in
			(* For functions lower bounds should be equal *)
			(ispreequal && ispostequal && (p1 = p2) && (VarSet.equal u1 u2))
  | BtInt, BtInt -> true
  | BtBool, BtBool -> true
  | BtCond, BtCond -> true
  | _ ,_ -> false (* int, bool, cond *)

(* Check if base types are same. What about rho? 
   Ignore rho and policy for comparison 
*)
let rec check_enc_base_type b1 b2 = match (b1, b2) with 
  | EBtRef (rho1, lt1), EBtRef (rho2, lt2) -> check_enc_base_type (fst lt1) (fst lt2)
  | EBtFunc (rho1, gencpre1, p1, u1, gencpost1), EBtFunc (rho2, gencpre2, p2, u2, gencpost2) -> 
		      let ispreequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1 =p2) && (check_enc_base_type b1 b2) then true
				else false
			| _ -> false  
			end) gencpre1 gencpre2 in
		      let ispostequal = VarLocMap.equal (fun bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|((b1, p1), (b2, p2)) -> 
				if (p1=p2) && (check_enc_base_type b1 b2) then true
				else false
			| _ -> false  
			end ) gencpost1 gencpost2 in
			(* For functions lower bounds should be equal *)
			(ispreequal && ispostequal && (p1 = p2) && (VarSet.equal u1 u2))
  | EBtInt, EBtInt -> true
  | EBtBool, EBtBool -> true
  | EBtCond rho1, EBtCond rho2 -> true
  | _ ,_ -> false (* int, bool, cond *)

(* ---------- FRESH TYPE VARIABLES ---------- *)
let tvar_cell = ref 1

(* [next_tid ()] generates a fresh type variable *)
let next_tid () : var =
  let x = !tvar_cell in
  let s = "x" ^ string_of_int x in
  incr tvar_cell;  s

(* [next_tvar ()] generates a fresh type variable *)
let next_tvar () : mode =
  let x = !tvar_cell in
  let s = "x" ^ string_of_int x in
  let _ = incr tvar_cell in
  let newidvar = next_tid() in 
  ModeVar (s, newidvar)

let next_kvar() : var =
   let x = !tvar_cell in
   let s = "x" ^ string_of_int x in
   let _ = incr tvar_cell in
 	s

let get_bij_var rho1 rho2 eidmap eidrevmap = 
			let (bij, eidmap', eidrevmap')  = if EnclaveidRevMap.mem (rho1, rho2) eidrevmap then
					(EnclaveidRevMap.find (rho1, rho2) eidrevmap, eidmap, eidrevmap)
				  else
					let b12 = next_tid() in
					let tempeidrevmap = EnclaveidRevMap.add (rho1, rho2) b12 eidrevmap in
					(b12, EnclaveidMap.add b12 (rho1, rho2) eidmap, EnclaveidRevMap.add (rho1, rho2) b12 tempeidrevmap)
			in
			(bij, eidmap', eidrevmap')

(* Fulfil all combinations of bij *)
let rec fill_eidrevmap ms eidmap eidrevmap =
	if not (ModeSet.is_empty ms) then
		let rho = ModeSet.choose ms in
		let ms' = ModeSet.remove rho ms in
		(* Check if bij exists for each element of ms' *)
		let rec check_bij ms eidmap eidrevmap = 
			if not (ModeSet.is_empty ms) then
				let rho' = ModeSet.choose ms in
				let ms'  = ModeSet.remove rho' ms in
				let (_, eidmap', eidrevmap') = get_bij_var  rho rho' eidmap eidrevmap
				in check_bij ms' eidmap' eidrevmap'
			else
				(eidmap, eidrevmap)
		in
		let (eidmap', eidrevmap') = check_bij ms' eidmap eidrevmap in
		fill_eidrevmap ms' eidmap' eidrevmap'
	else
		(eidmap, eidrevmap)
	
let rec countCondConstraints (c:constr2) =
	  let rec outerloop c2 num_constraints =
          	let a, b = Constr2.choose c2 in
          	let c2' = Constr2.remove (a,b) c2 in
	   	let constraints_per_row = 1  in
		let totalconstraints = constraints_per_row + num_constraints in
                if (Constr2.is_empty c2') then totalconstraints else outerloop c2' totalconstraints 
         in
         if (Constr2.is_empty c) then 0 else outerloop c 0

(* -----------UPDATE CONSTRAINTS ------------*)

let rec update_constraints (t: (mode * mode) list) (c:constr) eidmap eidrevmap = 
  match t with
 | [] -> (c, eidmap, eidrevmap)
 | (rho1, rho2)::ts -> let c' = (Constr.add (Modecond (rho1, rho2)) c) in
		       let (bij, eidmap1, eidrevmap1) = get_bij_var rho1 rho2 eidmap eidrevmap in
			update_constraints ts (Constr.add (Eidcond (bij, 0)) c') eidmap1 eidrevmap1

let rec add_bij_equiv_constraints eidmap eidrevmap c = 
  let (bij, (rhoi, rhoj)) = EnclaveidMap.choose eidmap in
  let eidmap' = EnclaveidMap.remove bij eidmap in
  if not (EnclaveidMap.is_empty eidmap') then
      (* Find all bindings where fst(key) or snd(key) = rhoj *)
      let eidrevmapj = EnclaveidRevMap.filter (fun key a -> if ((fst key) = rhoj && (not ((snd key) = rhoi))) || 
							 ((not ((fst key) = rhoi)) && (snd key) = rhoj) then true
						      else   false ) eidrevmap
      in 
      let bindinglist = EnclaveidRevMap.bindings eidrevmapj in
      let rec update_bij_constraints c blist =
		match blist with
		|[] -> c
		|((rho1, rho2), bjk)::tail -> let rhok = if (rho1 = rhoj) then rho2 else rho1 in
 
						(* find if a binding exists for (rhoi, rhok) and get bik *)
						(* Note that eidmap/eidrevmap cannot get updated because we filled it before *)
						let (bik, _, _) = get_bij_var rhoi rhok eidmap eidrevmap in
						(* Update Constraints bij = 0 /\ bjk = 0 -> bik =0 *)
						let c' = Constr2.add (Preeidcond ((bij, 0), (bjk, 0)), Eidcond (bik, 0)) c in
						(* Update Constraints bij = 1 /\ bjk = 0 -> bik =1 *)
						let c'' = Constr2.add (Preeidcond ((bij, 1), (bjk, 0)), Eidcond (bik, 1)) c' in
      						update_bij_constraints c'' tail 
     in 
     let c' = update_bij_constraints c bindinglist  in
      (* Find all bindings where fst(key) or snd(key) = rhoi *)
      let eidrevmapi = EnclaveidRevMap.filter (fun key a -> if ((fst key) = rhoi && (not ((snd key) = rhoj))) || 
							 ((not ((fst key) = rhoj)) && (snd key) = rhoi) then true
						      else   false ) eidrevmap
      in 
      let bindinglisti = EnclaveidRevMap.bindings eidrevmapi in
      let rec update_bji_constraints c blist =
		match blist with
		|[] -> c
		|((rho1, rho2), bik)::tail -> let rhok = if (rho1 = rhoi) then rho2 else rho1 in
 
						(* find if a binding exists for (rhoj, rhok) and get bjk *)
						let (bjk, _, _) = get_bij_var rhoj rhok eidmap eidrevmap in
						(* Update Constraints bij = 0 /\ bik = 0 -> bjk =0 *)
						let c' = Constr2.add (Preeidcond ((bij, 0), (bik, 0)), Eidcond (bjk, 0)) c in
						(* Update Constraints bij = 1 /\ bik = 0 -> bjk =1 *)
						let c'' = Constr2.add (Preeidcond ((bij, 1), (bik, 0)), Eidcond (bjk, 1)) c' in
      						update_bij_constraints c'' tail
     in 
     let c'' = update_bji_constraints c' bindinglisti in
     add_bij_equiv_constraints eidmap' eidrevmap c''
  else
	c
						
 
(* ------- Flatten Sequence ------------ *)
let rec flattenseq s = match s with
|Seq(c1, c2) -> flattenseq c1 @ flattenseq c2
| _   -> [s]

let getexpmode = function
  | EVar(rho, v) -> rho
  | ELam(rho, rho', gpre, p, u, q, gpost, s) -> rho 
  | EPlus (rho, l,r) -> rho
  | EConstant(rho,n) ->  rho
  | ETrue rho ->  rho
  | EFalse rho  -> rho
  | EEq (rho, l,r) -> rho
  | ELoc(rho, rho', l) ->rho
  | EDeref(rho,e) -> rho
  | EIsunset(rho,x) -> rho

let getstmtmode   = function
  | EIf (m,e,c1,c2,_) -> m
  | EAssign(m, x, e,_) ->m 
  | EDeclassify(m, x, e,_) ->m 
  | ESeq(m,s1, s2,_) -> m
  | ECall(m,e,_)    -> m
  | EUpdate(m,e1, e2,_) ->m
  | EWhile(m, b, s,_) -> m
  | ESkip (m, m',_) -> m'
  | EOutput(m,ch, e,_) ->m
  | ESet(m,x,_)	-> m
  | EESeq (m, _,_) -> m

let getrhovar = function
| ModeVar(x, _) -> x
| _ -> raise HelperError

(* -----------Typing Context Checks ---------- *)

(* Returns true when all registers all low *)
let check_typing_context_reg_low (genc1:enccontext) = 
  VarLocMap.for_all (fun key value -> begin match key with
				| Reg x -> begin match (snd value) with
						| Low -> true
						| _ -> false
					   end
				| _ -> true
				end) genc1


