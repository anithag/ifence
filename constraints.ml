open Ast
open Helper
open Cost

exception TypeError 
exception TypeNotFoundError 
exception TypeNotFoundError1 
exception UnificationError
exception UnimplementedError

(* [unify c0] solves [c0] (if possible), yielding a substitution. Raise UnificationError if constraints cannot be unified. *)
let rec unify (c0:constr) : subst = 
 match Constr.is_empty c0 with
        | true -> ModeVarMap.empty
        | false ->
          let a, b = Constr.choose c0 in
          let c1 = Constr.remove (a,b) c0 in
          if a = b then unify(c1) else
          begin match (a,b) with
                |ModeVar x, ModeVar y -> 
                        let unified_subst = unify(subst_constr c1 x (ModeVar y)) in
                        let mode_t = apply_subst unified_subst (ModeVar y) in
                        ModeVarMap.add x mode_t unified_subst
		|ModeVar x, Enclave
		|Enclave, ModeVar x  ->
			let unified_subst = unify(subst_constr c1 x Enclave) in
			ModeVarMap.add x Enclave unified_subst	(* Add x = Enclave to map *)
		|ModeVar x, Normal
		|Normal, ModeVar x ->
			let unified_subst = unify(subst_constr c1 x Normal) in
			ModeVarMap.add x Normal unified_subst	(* Add x = Normal to map *)
                | _ , _ -> raise UnificationError
	 end

(* Conditional unification
  + c0: Set of constraints of form a = Enclave/Normal
  + c1: Set of conditional constraints of form if a = Enclave/Normal -> c = Enclave/Normal....
  + tmp : Temporary conditional constraints which needs further processing 
  + s  : Map from mode variables to Enclave/Normal
  + The below unification algorithm terminates

 Algorithm:
 
 1. If c1 is not empty
	1. Choose (a, b) from c1. Note that a is pre-cond and b is the list of post-cond
	2. If 'a' is satisfied in c0, then 
			a. add 'a' and all 'b' to c0 (updated as c0'')
        		b. Remove (a, b) from c1  (updated as c2)
			c. Update map s with the list 'b' (updated as unified_subst)
			d. call cond_unify c0'' c2 tmp unified_subst
	3. If 'a' is not satisfied in c0, then
			a. add (a,b) to tmp  (updated as tmp')
			b. remove (a,b) from c1 (updated as c2)
  			c. call cond_unify c0 c2 tmp' s
 2. If c1 is empty, then
	1. Check if tmp is also empty. If yes, return s
	2. If tmp is not empty, check if fixed point is reached i.e. c0 is unchanged. 
			a. If yes, return s. This step guarantees termination.
			b. If not, Remove (a, b) from tmp
			c. Add (a,b) to c1
			d. cond_unify c0 c1 tmp s
 *)
let rec cond_unify (c0:constr) (c1:constr2) (tmp:constr2) (c0_prev:constr) (s:subst): subst*constr2 =
 match Constr2.is_empty c1 with
        | true -> begin match Constr2.is_empty tmp with
		  | true -> (s, tmp)
		  | false -> if Constr.equal c0 c0_prev then (s, tmp)  (* Fixed point reached *)
			     else 
			     let a,b = Constr2.choose tmp in
			     let tmp' = Constr2.remove (a,b) tmp in
			     let c1' = Constr2.add (a,b) c1 in
				cond_unify c0 c1' tmp' c0 s  (* Note that c0_prev is updated here to use c0 *)
		 end
        | false ->
          let a, b = Constr2.choose c1 in
          begin match a with
                |ModeVar x, Enclave
		|Enclave, ModeVar x ->
			(* Check if the pre-condition is satisfied *)
                        let mode_t = apply_subst s (ModeVar x) in
			if mode_t = Enclave then 
				(* pre-condition satisfied *)
				let c0' = Constr.add a c0 in

				(* Add corresponding pre and post conditions to c0 *)
				let c0'' = List.fold_right (fun elm (c:constr)  -> Constr.add elm c) b c0' in  
          			let c2 = Constr2.remove (a,b) c1 in
				
				(* Update Map *)
				let rec update_map (xl:mode list ) (rho:mode) (s0:subst) = 
					begin match xl with
					[] -> s0
					|(ModeVar y)::xs -> let s0' =
                        				ModeVarMap.add y rho  s0
							in update_map xs Enclave s0'
					end
					(* already know that x = Enclave which is a constant, no further propagation is required *)
					in
				let unified_subst = update_map (fst (List.split b)) Enclave s in
				(* substitution not required here, as constraints are of form x = Enclave/Normal *)
                        	cond_unify c0'' c2 tmp c0_prev unified_subst  
			else  
				(* Remove from c1 and add to tmp for future processing *)
				let c2 = Constr2.remove (a, b) c1  in
				let tmp' = Constr2.add (a,b) tmp   in
				 cond_unify c0 c2 tmp' c0_prev s
				
                |ModeVar x, Normal
		|Normal, ModeVar x ->
			(* Check if the pre-condition is satisfied *)
                        let mode_t = apply_subst s (ModeVar x) in
			if mode_t = Normal then 
				(* pre-condition satisfied *)
				let c0' = Constr.add a c0 in

				(* Add corresponding pre and post conditions to c0 *)
				let c0'' = List.fold_right (fun elm (c:constr)  -> Constr.add elm c) b c0' in  
          			let c2 = Constr2.remove (a,b) c1 in
				
				(* Update Map *)
				let rec update_map (xl:mode list ) (rho:mode) (s0:subst) = 
					begin match xl with
					[] -> s0
					|(ModeVar y)::xs -> let s0' =
                        				ModeVarMap.add y rho  s0
							in update_map xs rho s0'
					end
					(* already know that x = Normal which is a constant, no further propagation is required *)
					in
				let unified_subst = update_map (fst (List.split b)) Normal s in
				(* substitution not required here, as constraints are of form x = Enclave/Normal *)
                        	cond_unify c0'' c2 tmp c0_prev unified_subst  
			else  
				(* Remove from c1 and add to tmp for future processing *)
				let c2 = Constr2.remove (a, b) c1  in
				let tmp' = Constr2.add (a,b) tmp   in
				 cond_unify c0 c2 tmp' c0_prev s
                | ModeVar x, ModeVar y -> raise UnificationError (* How to handle this? *)
	end
 
(* Return join of policies in policy lattice *)
let join = function
  |_, High
  |High, _ -> High
  |Erase(l, c, h), Low -> Erase(l, c, h)
  |Low, Erase(l,c,h) -> Erase(l, c, h)
  |Low, Low -> Low
  |Erase(l1, c1, h1), Erase(l2, c2, h2) -> High

let rec get_exp_type (g:context) (e:exp) : labeltype =
  match e with
   | Var x -> (try VarLocMap.find (Reg x) g with Not_found -> raise TypeNotFoundError)
   | Loc l -> (try VarLocMap.find (Mem l) g with Not_found -> raise TypeNotFoundError)
   | Lam(p,u,q, s) -> (BtFunc(p,u), q)
   | Constant n -> (BtInt, Low)
   | True    -> (BtBool, Low)
   | False -> (BtBool, Low)
   | Eq(e1, e2) -> (BtBool, join (snd (get_exp_type g e1), snd (get_exp_type g e2)))
   | Plus(e1, e2) -> (BtInt, join (snd (get_exp_type g e1), snd (get_exp_type g e2)))
   | Isunset x -> (BtBool, Low)
   | Deref e   -> begin match (get_exp_type g e) with
		  | ((BtRef lt), p) -> (fst lt, join ((snd lt), p))
		  | _  -> raise TypeError
		 end
 
let rec get_exp_label lt = (snd lt)
		
let rec translatetype (s:labeltype) : enclabeltype = 
	match s with
	| (BtInt, p ) -> (EBtInt, p)
	| (BtBool, p) -> (EBtBool, p)
	| (BtCond, p) -> (EBtCond, p)
	| (BtRef b, p)-> let rho = next_tvar () in
			(EBtRef(rho, (translatetype b)), p)
        | (BtFunc(p, u), q) -> let rho = next_tvar () in
			 (EBtFunc(rho, p, u), q)
	    
let rec get_enc_exp_type (e:encexp) (genc:enccontext) : enclabeltype =
  match e with
   | EVar(rho,x) -> (try VarLocMap.find (Reg x) genc with Not_found -> raise TypeNotFoundError)
   | ELoc(rho, rho', l) -> (try VarLocMap.find (Mem l) genc with Not_found -> raise TypeNotFoundError)
   | ELam(rho, rho',p,u,q,s) -> (EBtFunc(rho',p,u), q) 
   | EConstant(_,n) -> (EBtInt, Low)
   | ETrue _    -> (EBtBool, Low)
   | EFalse _ -> (EBtBool, Low)
   | EEq(rho,e1, e2) -> (EBtBool, join (snd (get_enc_exp_type e1 genc), snd (get_enc_exp_type e2 genc)))
   | EPlus(rho,e1, e2) -> (EBtInt, join (snd (get_enc_exp_type e1 genc ), snd (get_enc_exp_type e2 genc)))
   | EIsunset(rho,x) -> (EBtBool, Low)
   | EDeref(rho, e)   -> begin match (get_enc_exp_type e genc) with
		  | (EBtRef(rho, lt), p) -> (fst lt, join ((snd lt), p))
		  | _  -> raise TypeError
		 end
 
let rec get_exp_label lt = (snd lt)
		


let rec gen_constraints_type (s1: enclabeltype) (s2:enclabeltype) = 
   match (s1, s2) with
   |(EBtRef(m1,s1'), p), (EBtRef( m2, s2'), q) -> let t1 = gen_constraints_type s1' s2' in  [(m1, m2)]@ t1 (*FIX ME: Return type *)
   |(EBtFunc(m1, p1, u1), q1), (EBtFunc(m2, p2, u2), q2) -> [(m1, m2)]
   | _ -> []
     

(* [gen_constraints g e] typegen_constraintss [e] in the context [g] generating a type and a set of constraints. Raise TypeError if constraints cannot be generated. *)
(* Return type is a pair of constraint sets. First set are hard constraints of form P = Q, second set has conditional constraints of form If P then Q *)
let rec gen_constraints_exp (g:context) (rho:mode)  (e:exp) (genc: enccontext) : constr * constr2 * modeenv * modeset * enccontext * encexp = 
 let m = ModeProgSet.add (rho, (Exp e)) ModeProgSet.empty in
 let ms = ModeSet.add rho ModeSet.empty in
  match e with
    |Constant n -> (Constr.empty, Constr2.empty, m, ms, genc, EConstant(rho,n))
    | Var x     ->  let srctype = get_exp_type g e in
		    let genc' = if (VarLocMap.mem (Reg x) genc) then genc
		    		else
		    		  let enctype = translatetype srctype in
				  VarLocMap.add (Reg x) enctype genc in 
			begin match rho with
			    |Normal -> let pol       = get_exp_label srctype in
						       begin match pol with
						       | High
						       | Erase(_,_,_) -> (Constr.add (rho, Enclave) Constr.empty, Constr2.empty, m, ms, genc', EVar(rho, x))
						       |_ -> (Constr.empty, Constr2.empty, m, ms, genc', EVar(rho,x))
						       end 
			    |Enclave ->  (Constr.empty, Constr2.empty, m, ms, genc', EVar(rho,x))         
			    |ModeVar y -> 
					  let pol    = get_exp_label srctype in
                                                       begin match pol with
                                                  	| High
                                                  	| Erase(_,_,_) -> ((Constr.add (rho, Enclave) Constr.empty), Constr2.empty, m, ms, genc', EVar(rho,x))
                                                  	|_ -> (Constr.empty, Constr2.empty, m, ms, genc', EVar(rho,x))                
                                                	end
			end 
    |Loc l -> let srctype = get_exp_type g e in
	      let genc' = if (VarLocMap.mem (Mem l) genc) then  genc
			 else 
			  let enctype = translatetype srctype in
			  VarLocMap.add (Mem l) enctype genc in
	      let creftype = get_src_content_type srctype in (* Since gammasrc(loc) = b_p -> gammasrc(loc)|- (b_p ref)_l*)
	      (* let creftype = srctype in  For locations, contenttype determine the label *) 
	      let rho' = get_mode (VarLocMap.find (Mem l) genc') in
	      begin match rho with 
		| Normal ->
			begin match get_exp_label creftype with
					 (* Normal mode should access only normal memory locations *)
				| Low -> 
			      ((Constr.add (rho', Normal) Constr.empty), Constr2.empty, ModeProgSet.add (rho', (EncExp (construct_enc_exp e rho rho'))) m, ModeSet.add rho' ms, genc', ELoc(rho, rho', l))
				| Erase(_,_,_)
				| High -> raise TypeError
	      		end
		| Enclave ->
			begin match get_exp_label creftype with
					(* A low content location is unconstrained. *)
				| Low -> (Constr.empty, Constr2.empty, ModeProgSet.add (rho', (EncExp (construct_enc_exp e rho rho'))) m, ModeSet.add rho' ms, genc', ELoc(rho, rho', l) )
				| Erase(_,_,_)
				| High -> 
						let c1, c2, m1, ms1 = 
				(Constr.add (rho, Enclave) Constr.empty, Constr2.empty, ModeProgSet.add (rho', (EncExp (construct_enc_exp e rho rho'))) m, ModeSet.add rho' ms ) in
						(Constr.add (rho', Enclave) c1, c2, m1, ms1, genc', ELoc(rho, rho', l))	
	      		end
		| ModeVar y ->
			begin match get_exp_label creftype with
					(* rho = Normal -> rho'= Normal *)
				| Low -> 
(Constr.empty, Constr2.add ((rho, Normal), [(rho', Normal)]) Constr2.empty, ModeProgSet.add (rho', (EncExp (construct_enc_exp e rho rho'))) m, ModeSet.add rho' ms, genc', ELoc(rho, rho',l) )
				| Erase(_,_,_)
				| High -> let c1, c2, m1, ms1 = 
				(Constr.add (rho, Enclave) Constr.empty, Constr2.empty, ModeProgSet.add (rho', (EncExp (construct_enc_exp e rho rho'))) m, ModeSet.add rho' ms ) in
					 (Constr.add (rho', Enclave) c1, c2, m1, ms1, genc', ELoc(rho, rho', l))	
	      		end
	       end
    |Eq(e1, e2) -> 
		   let c1, c2, m1, ms1, genc1, ee1 = gen_constraints_exp g rho e1 genc in
		   let c3, c4, m2, ms2, genc2, ee2 = gen_constraints_exp g rho e2 genc1 in
		   let c5, c6,m3, ms3 = (Constr.union c1 c3, Constr2.union c2 c4, ModeProgSet.union m1 m2, ModeSet.union ms1 ms2) in
		   begin match get_exp_label (get_exp_type g e) with (* FIX ME: Collect constraints here *)
		   | Low -> (c5, c6, m3, ms3, genc2, EEq(rho, ee1, ee2) )
		   | Erase(_,_,_)
		   | High -> (Constr.add (rho, Enclave) c5, c6, m3, ms3, genc2, EEq(rho, ee1, ee2) )
		   end
    |Plus(e1, e2) -> 
		   let c1, c2, m1, ms1, genc1, ee1 = gen_constraints_exp g rho e1 genc in
		   let c3, c4, m2, ms2, genc2, ee2 = gen_constraints_exp g rho e2 genc1 in
		   let c5, c6,m3, ms3 = (Constr.union c1 c3, Constr2.union c2 c4, ModeProgSet.union m1 m2, ModeSet.union ms1 ms2) in
		   begin match get_exp_label (get_exp_type g e) with
		   | Low -> (c5, c6, m3, ms3, genc2, EPlus(rho, ee1, ee2))
		   | Erase(_,_,_)
		   | High -> (Constr.add (rho, Enclave) c5, c6, m3, ms3, genc2, EPlus(rho, ee1, ee2))
		   end
    |Lam(p,u,q,s)	 -> 
    		   (*let srctype = get_exp_type g e in *)
		   let srctype = (BtFunc(p, u), q) in 
		   let enctype = translatetype srctype in
	           let rho' = get_mode enctype in
		   let rho'' = next_tvar () in
		   let c1, c2, m1, ms1, genc1, _, es = gen_constraints g rho'' s genc in
			(* rho' = rho''*)
		   let c3 = Constr.add (rho', rho'') c1 in
			(* rho = rho'*)
		   let c4, c5, m2, ms2, genc2 = (Constr.add (rho, rho') c3, c2, ModeProgSet.add (rho',(EncExp (construct_enc_lam_exp e es rho rho'))) m1, ModeSet.add rho' ms1, genc1) in 
			 begin match get_exp_label srctype with
		  	 | Low -> (c4, c5, m2, ms2, genc2, ELam(rho, rho',p,u,q,es))
			 | Erase(_,_,_) 
			 | High -> let c6 = (Constr.add (rho, Enclave) c4) in
					(Constr.add (rho', Enclave) c6, c5, m2, ms2, genc2, ELam(rho,rho',p,u,q,es))
		         end
    |Deref e	->  let c1, c2, m1, ms1, genc1, ee = gen_constraints_exp g rho e genc in
			begin match get_exp_label (get_exp_type g e) with
			| Low  -> (c1, c2, (ModeProgSet.union m1 m), ModeSet.union ms1 ms, genc1, EDeref(rho,ee))
			| Erase(_,_,_)
			| High -> (Constr.add (rho, Enclave) c1, c2, (ModeProgSet.union m1 m), ModeSet.union ms1 ms, genc1, EDeref(rho,ee))
			end  
    |True	-> (Constr.empty, Constr2.empty, m, ms, genc, ETrue rho )
    |False-> (Constr.empty, Constr2.empty, m, ms, genc, EFalse rho )
    |Isunset x -> (Constr.empty, Constr2.empty, m, ms, genc, EIsunset(rho,x) )
    | _ -> raise UnimplementedError

(* + Maintain a different set for collecting implication constraints
     e.g: rho = E -> rho' = E 
   + Return type is a pair of constraint sets. First set are hard constraints of form P = Q, second set has conditional constraints of form If P then Q 
   + modeenv - maps rho to program statements and expressions - for readability
   + modeset - set of mode variables
*)
and gen_constraints (g:context) (rho: mode) (s0:stmt) (genc:enccontext) : constr * constr2 * modeenv * modeset*enccontext*totalcost * encstmt = 
 let m = ModeProgSet.add (rho, (Stmt s0)) ModeProgSet.empty in
 let ms = ModeSet.add rho ModeSet.empty in
  match s0 with
    | Skip ->let rho' = next_tvar () in
		      let entrycost = compute_assign_entry_cost rho rho' in
		      let trustedcost = compute_assign_trusted_cost rho rho' in
 		      let totalc = (entrycost, trustedcost) in
		 (Constr.empty, (Constr2.add ((rho, Enclave), [(rho', Enclave)]) Constr2.empty), m, ms, genc, totalc, ESkip (rho, rho'))

    | Assign(x, e) -> let rho' = next_tvar () in (* for e *)
		      let rho'' = next_tvar () in (* for Var x *)
		      let c1, c2, m1, ms1, genc1, ee = gen_constraints_exp g rho' e genc in
		      let c3, c4, m2, ms2, genc2, _ = gen_constraints_exp g rho'' (Var x) genc1 in
		      let c5, c6 = (Constr.union c1 c3, Constr2.union c2 c4) in
		      let m4, ms4 = (ModeProgSet.union m m1, ModeSet.union ms ms1) in 
		      let m5, ms5 = (ModeProgSet.union m2 m4, ModeSet.union ms2 ms4) in 
			(* gammaenc(x) = b s.t. gammaenc|-e:b *)
		      let enclt1 = (VarLocMap.find (Reg x) genc2) in
		      let enclt2 = (get_enc_exp_type ee genc2) in

		      let t1 = gen_constraints_type enclt1 enclt2 in
		      let c7 = update_constraints t1 c5 in			
		
		       (* rho = E -> rho' = rho'' = E *)
		      let c8 = Constr2.add ((rho, Enclave),[(rho', Enclave); (rho'', Enclave)]) c6 in

		      let entrycost = compute_assign_entry_cost rho rho' in
			(* x:=e adds a cost of 1 if (a) rho = E or (2) rho = N and rho' = E *)
		      let trustedcost = compute_assign_trusted_cost rho rho' in
 		      let totalc = (entrycost, trustedcost) in
		      
			
			begin match rho with 
			 | Normal ->   begin match get_exp_label enclt1 with
					|Low -> (c7, c8, m5, ms5, genc2, totalc, EAssign(rho, x, ee))
					|Erase(_,_,_)
					|High -> raise TypeError
					end
			 |Enclave -> let c9 = Constr.add (rho'', Enclave) c7 in
					(* Use c6 or c8, does not make difference to solver *)
					(Constr.add (rho', Enclave) c9, c8, m5, ms5, genc2, totalc, EAssign(rho, x, ee))
			 |ModeVar y -> begin match get_exp_label enclt1 with
					|Low -> (c7, c8, m5, ms5, genc2, totalc, EAssign(rho, x, ee))
					|Erase(_,_,_)
					|High -> let c9 = Constr.add (rho'', Enclave) c7 in 
						(Constr.add (rho', Enclave) c9, c8, m5, ms5, genc2, totalc, EAssign(rho, x, ee))
					end
			end
				
    | Update(e1, e2) -> let rho'' = next_tvar () in
			let c1, c2, m1, ms1, genc1, ee1 =   gen_constraints_exp g rho'' e1 genc in
			let c3, c4, m2, ms2, genc2, ee2 =   gen_constraints_exp g rho'' e2 genc1 in
		        let c5, c6 = (Constr.union c1 c3, Constr2.union c2 c4) in
		        let m4, ms4 = (ModeProgSet.union m m1, ModeSet.union ms ms1) in 
		        let m5, ms5 = (ModeProgSet.union m2 m4, ModeSet.union ms2 ms4) in 

			(* Get the translated type of e1 *)
		        let refenclt1 = (get_enc_exp_type ee1 genc2) in
			let rho'      = get_mode refenclt1 in 
			let enclt1   = get_content_type refenclt1 in (* Fetches pointer type e.g.: ((int_h) ref) gives int_h *)
			let enclt2   =  (get_enc_exp_type ee2 genc2) in

			(* types of content and rhs should match   *)
			let t1       = gen_constraints_type enclt1 enclt2 in 
		        let c7       = update_constraints t1 c5 in			
			
			let entrycost = compute_assign_entry_cost rho rho'' in
		        let trustedcost = compute_assign_trusted_cost rho rho'' in
 		        let totalc = (entrycost, trustedcost) in
			
			begin match rho with
			    |Normal  -> 
		        		let c9, c10,m6, ms6 = begin match get_exp_label enclt1 with
					(* rho' = E -> rho'' = E *) 
					| Low -> (c7, Constr2.add ((rho', Enclave), [(rho'', Enclave)]) c6, ModeProgSet.add (rho', (EncExp (construct_enc_exp e1 rho rho'))) m5, ModeSet.add rho' ms5)
					| Erase(_,_,_) 
					| High -> (* p != L -> rho' = rho'' = E *)
						 let c8 = Constr.add (rho', Enclave) c7 in
						  (Constr.add (rho'', Enclave) c8, c6, ModeProgSet.add (rho', (EncExp (construct_enc_exp e1 rho rho'))) m5, ModeSet.add rho' ms5)
	 
	      				end 
					in
					(c9, c10, m6, ms6, genc2, totalc, EUpdate(rho, ee1, ee2))

			    |Enclave -> 
		        		let c8, c9, m6, ms6, es = begin match get_exp_label enclt1 with
					(* A low content location is unconstrained. *)
					| Low -> (c7, c6, ModeProgSet.add (rho', (EncExp (construct_enc_exp e1 rho rho'))) m5, ModeSet.add rho' ms5, EUpdate(rho, ee1, ee2)) 
					| Erase(_,_,_)
					| High -> 
						(Constr.add (rho', Enclave) c7, c6, ModeProgSet.add (rho', (EncExp (construct_enc_exp e1 rho rho'))) m5, ModeSet.add rho' ms5, EUpdate(rho, ee1, ee2))
	      				end in
					 (* rho = E -> rho'' = E. Specifically note that if rho = E does not imply rho' = E *)            
				        ((Constr.add (rho'', Enclave) c8), c9, m6, ms6, genc2, totalc,es)

			    |ModeVar y -> 
					let c8, c9,m6, ms6, es = begin match get_exp_label enclt1 with
					(* rho' = Enclave -> rho''= Enclave *)
					| Low -> 
						(c7, Constr2.add ((rho', Enclave), [(rho'', Enclave)]) c6, 
							ModeProgSet.add (rho', (EncExp (construct_enc_exp e1 rho rho'))) m5, ModeSet.add rho' ms5, EUpdate(rho, ee1, ee2))
					| Erase(_,_,_)
					| High -> let c8', c9', m6', ms6' = 
				         (Constr.add (rho', Enclave) c7, c6, ModeProgSet.add (rho', (EncExp (construct_enc_exp e1 rho rho'))) m5, ModeSet.add rho' ms5 ) in
						 (Constr.add (rho'', Enclave) c8', c9', m6', ms6', EUpdate(rho, ee1, ee2))	
	      				end in
					 (* rho = E -> rho'' = E and rho' = E -> rho'' = E *) 
					 let c10 = Constr2.add ((rho', Enclave), [(rho'', Enclave)]) c9 in
					 (c8, (Constr2.add ((rho, Enclave), [(rho'', Enclave)]) c10),m5, ms5, genc2, totalc, es)
			end 
    |If(e, s1, s2) -> let rho' = next_tvar () in (* for e *)
		      let rho''= next_tvar () in (* for c1 *)
		      let rho''' = next_tvar () in (* for c2 *)
		      let entrycost = compute_if_entry_cost rho rho' rho'' rho''' in
			(* if e then c1 else c2 : trusted cost will be similar to assign statement depending on rho mode *)
		      let trustedcost = compute_assign_trusted_cost rho rho' in
		      let c1, c2, m1, ms1, genc1, ee = gen_constraints_exp g rho' e genc in
		      let c3, c4, m2, ms2, genc2, fcost1, es1 = gen_constraints g rho'' s1 genc1 in
		      let c5, c6, m3, ms3, genc3, fcost2, es2 = gen_constraints g rho''' s2 genc2 in
		      let fcost3 = (PPlus(fst fcost1, fst fcost2), PPlus(snd fcost1, snd fcost2)) in
	     	      let totalc = (PPlus(entrycost, fst fcost3), PPlus(trustedcost, snd fcost3)) in
		      begin match rho with
			    |Normal ->  
					let c7, c8, m4, ms4 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
					let c9, c10, m5, ms5= ((Constr.union c5 c7), (Constr2.union c6 c8), (ModeProgSet.union m4 m3), ModeSet.union ms3 ms4) in
					 	     (* rho'= E -> rho'' = rho''' = E *)
						     (c9, (Constr2.add ((rho', Enclave), [(rho'', Enclave);(rho''', Enclave)]) c10), (ModeProgSet.union m m5), 
								ModeSet.union ms ms5,genc3, totalc, EIf(rho, ee, es1, es2)) 
			    |Enclave -> 
					let c7, c8, m4, ms4 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
					let c9, c10, m5, ms5= ((Constr.union c5 c7), (Constr2.union c6 c8), (ModeProgSet.union m4 m3), ModeSet.union ms3 ms4) in
					let c11     = (Constr.add (rho', Enclave) c9) in
					let c12     = (Constr.add (rho'', Enclave) c11) in
					let c13     = (Constr.add (rho''', Enclave) c12) in
						     ((Constr.add (rho, Enclave) c13), c10, (ModeProgSet.union m m5), ModeSet.union ms ms5, genc3, totalc, EIf(rho, ee, es1, es2))
			    |ModeVar y -> 
					let c7, c8, m4, ms4 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
					let c9, c10, m5, ms5= ((Constr.union c5 c7), (Constr2.union c6 c8), (ModeProgSet.union m4 m3), ModeSet.union ms3 ms4) in
							(* rho = E -> rho' = rho''= rho''' = E *)
							(* rho' = E -> rho''= rho''' = E *)
					let c11 = (Constr2.add ((rho', Enclave), [ (rho'', Enclave); (rho''', Enclave)]) c10) in
							(c9, (Constr2.add ((rho, Enclave), [(rho', Enclave); (rho'', Enclave); (rho''', Enclave)]) c11), (ModeProgSet.union m m5),
								 ModeSet.union ms ms5, genc3, totalc, EIf(rho, ee, es1, es2))
			    end	
    |Seq(s1, s2)  -> let rho' = next_tvar () in
		     let rho'' = next_tvar () in
		     let entrycost = compute_seq_entry_cost rho rho' rho'' in
		     let c1, c2, m1, ms1, genc1, fcost1, es1 = gen_constraints g rho' s1 genc in
		     let c3, c4, m2, ms2, genc2, fcost2, es2 = gen_constraints g rho'' s2 genc1 in
		     let fcost3 = (PPlus (fst fcost1, fst fcost2), PPlus(snd fcost1, snd fcost2)) in
			(* No trusted cost *)
		     let totalc = (PPlus (fst fcost3, entrycost), snd fcost3) in
			begin match rho with
			    |Normal -> 
					let m3, ms3        = (ModeProgSet.union m1 m2, ModeSet.union ms1 ms2) in
						    ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m m3), ModeSet.union ms ms3, genc2, totalc, ESeq(rho, es1, es2) )
			    |Enclave-> 
			               let c5, c6, m3, ms3 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
				       let c7	  =  Constr.add (rho', Enclave) c5 in
						    (Constr.add (rho'', Enclave) c7, c6, (ModeProgSet.union m m3), ModeSet.union ms ms3, genc2, totalc, ESeq(rho, es1, es2))
			    |ModeVar x -> 
                                       let c5, c6, m3, ms3 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
				       		    (c5, Constr2.add ((rho, Enclave), [(rho', Enclave); (rho'', Enclave)]) c6, (ModeProgSet.union m m3), ModeSet.union ms ms3, genc2, totalc, ESeq(rho, es1, es2))
			end
    |Call e -> let rho' = next_tvar () in
			let c1, c2, m1, ms1, genc1, ee = gen_constraints_exp g rho' e genc in
			let m2, ms2 = (ModeProgSet.union m m1, ModeSet.union ms ms1) in
			(* get mode of e *)
			let rho'' = get_mode (get_enc_exp_type ee genc1) in
			let entrycost = compute_assign_entry_cost rho rho' in
		        let trustedcost = compute_assign_trusted_cost rho rho' in
			(*FIXME: Add cost of function here *)
			let totalc = (entrycost, trustedcost) in
			begin match rho with
					(* rho' = rho'' *)
			  | Normal  -> (Constr.add (rho', rho'') c1, c2, m2 , ModeSet.add rho'' ms2, genc1, totalc, ECall(rho, ee))
			  | Enclave -> let c3 = (Constr.add (rho', Enclave) c1) in
						(Constr.add (rho', rho'') c3, c2, m2, ModeSet.add rho'' ms2, genc1, totalc, ECall(rho, ee))
			  | ModeVar x -> 
						 (* rho = E -> rho ' = E *)
					 	 (Constr.add (rho', rho'') c1, (Constr2.add ((rho, Enclave), [(rho', Enclave)]) c2), m2, ModeSet.add rho'' ms2, genc1, totalc, ECall(rho, ee))
			end 
   |While(e, s) -> let rho' = next_tvar () in
   		   let rho'' = next_tvar () in
		 
		   let entrycost = compute_assign_entry_cost rho rho'' in (* Note that the entry cost function gets simplified to this *)
		   let trustedcost = compute_assign_trusted_cost rho rho'' in (* Note that the trusted cost function gets simplified to this *)
		   let c1, c2, m1, ms1, genc1, ee = gen_constraints_exp g rho' e genc in
		   let c3, c4, m2, ms2, genc2, fcost1, es = gen_constraints g rho'' s genc1 in
		   let totalc = (PPlus (fst fcost1, entrycost), PPlus (snd fcost1, trustedcost)) in
			   begin match rho with
			   |Normal   -> 
					let c5, c6, m3, ms3 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
						     (* rho'=E -> rho'' = E *)
			    (c5, Constr2.add ((rho', Enclave), [(rho'', Enclave)]) c6, (ModeProgSet.union m m3), ModeSet.union ms ms3, genc2, totalc, EWhile(rho, ee, es))  
			   |Enclave  -> 
					let c5, c6, m3, ms3 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
					let c7     = Constr.add (rho', Enclave) c5 in
						     (* rho = E -> rho' = rho'' = E *)
						     (Constr.add (rho'', Enclave) c7, c6, (ModeProgSet.union m m3), ModeSet.union ms ms3, genc2, totalc, EWhile(rho, ee, es)) 
			   |ModeVar x -> 
					let c5, c6, m3, ms3 = ((Constr.union c1 c3), (Constr2.union c2 c4), (ModeProgSet.union m1 m2), ModeSet.union ms1 ms2) in
						     (* rho = E -> rho' = rho'' = E *)
						     (* rho' = E -> rho'' = E *)
                                        let  c7 =    Constr2.add ((rho, Enclave),[(rho', Enclave); (rho'', Enclave)]) c6 in         
						     (c5, Constr2.add ((rho', Enclave),[(rho'', Enclave)]) c7, (ModeProgSet.union m m3), ModeSet.union ms ms3, genc2, totalc, EWhile(rho, ee, es))
			   end
    |Output(x, e) -> let rho' = next_tvar () in
		     let entrycost = compute_assign_entry_cost rho rho' in 
		     let trustedcost = compute_assign_trusted_cost rho rho' in 
		     let totalc = (entrycost, trustedcost) in
	             let c1, c2, m1, ms1, genc1, ee = gen_constraints_exp g rho' e genc in
			  begin match rho with
			  | Normal   -> 
					begin match x with
					| 'H'  -> (Constr.add (rho', Enclave) c1, c2, (ModeProgSet.union m m1), ModeSet.union ms ms1, genc1, totalc, EOutput(rho, x, ee))
					|_     -> (c1, c2, (ModeProgSet.union m m1), ModeSet.union ms ms1, genc1, totalc, EOutput(rho, x, ee))
					end
			 | Enclave  -> 
				       (Constr.add (rho', Enclave) c1, c2, (ModeProgSet.union m m1), ModeSet.union ms ms1, genc1, totalc, EOutput(rho, x, ee))
			 | ModeVar y -> 
					let c3 = (Constr2.add ((rho, Enclave), [(rho', Enclave)]) c2) in
					begin match x with
					|'H' -> (Constr.add (rho', Enclave) c1, c3, ModeProgSet.union m m1, ModeSet.union ms ms1, genc1, totalc, EOutput(rho, x, ee))
					| _  -> (c1, c3, ModeProgSet.union m m1, ModeSet.union ms ms1, genc1, totalc, EOutput(rho, x, ee))
					end 
			end
    | Set x	-> let rho' = next_tvar () in (* x is always low for a well-typed source program *)
		      let entrycost = compute_assign_entry_cost rho rho' in
		      let trustedcost = compute_assign_trusted_cost rho rho' in
 		      let totalc = (entrycost, trustedcost) in
				(Constr.empty, Constr2.empty, m, ModeSet.add rho' ms, genc, totalc, ESet(rho, x))
    | _ -> raise UnimplementedError
