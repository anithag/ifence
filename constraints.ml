open Ast
open Helper
open Cost

exception TypeError 
exception ModeError
exception TranslationError of string
exception TypeNotFoundError 
exception TypeNotFoundError1 
exception UnificationError
exception UnimplementedError of string
exception EmptySeqError
exception JoinError

(* Return join of policies in policy lattice *)
let join = function
  |_, High
  |High, _ -> High
  |Erase(l, c, h), Low -> Erase(l, c, h)
  |Low, Erase(l,c,h) -> Erase(l, c, h)
  |Low, Low -> Low
  |Erase(l1, c1, h1), Erase(l2, c2, h2) -> High

let rec join_src_tau = function
 |((BtInt, p1), (BtInt, p2)) -> (BtInt, join (p1, p2))
 |((BtBool, p1), (BtBool, p2)) -> (BtBool, join (p1, p2))
 |((BtCond, p1), (BtCond, p2)) -> (BtCond, join (p1, p2))
 |((BtRef (lt1), p1), (BtRef (lt2), p2)) -> (* Assume that rho1 = rho2 constraint will be generated *)
							 (BtRef (join_src_tau (lt1,lt2)), join (p1, p2))
 |((BtFunc(gpre1, p1, u1, gpost1), q1), (BtFunc (gpre2, p2, u2, gpost2), q2)) ->
							(* FIXME: Not implementing function subtyping for now *) 
							(* gpre1 = gpre2 and gpost1 = gpost2*)
							(BtFunc (join_src_context (gpre1, gpre2), p1, u1, 
							join_src_context (gpost1, gpost2)), join (q1, q2))
 | _,_ -> raise JoinError

(* Only modes should differ, remaining should be same *)
and join_src_context (g1, g2) = 
  let rec join_tau_special = function
 	|((BtInt, p1), (BtInt, p2)) -> if not (p1=p2) then raise JoinError else (BtInt, p1)
 	|((BtBool, p1), (BtBool, p2)) -> if not (p1=p2) then raise JoinError else (BtBool, p1)
 	|((BtCond, p1), (BtCond, p2)) -> if not (p1=p2) then raise JoinError else (BtCond, p1)
 	|((BtRef lt1, p1), (BtRef lt2, p2)) -> 
						if not (p1=p2) then raise JoinError else  (BtRef (join_tau_special (lt1,lt2)), p1)
 	|((BtFunc(gpre1, p1, u1, gpost1), q1), (BtFunc (gpre2, p2, u2, gpost2), q2)) ->
						(* FIXME: Note the special condition q1 = q2 *)
						let istrue = (p1=p2) && (VarSet.equal u1 u2) && (q1=q2) in
						if not (istrue) then raise JoinError else  (BtFunc (join_src_context (gpre1,gpre2), p1, u1, 
												join_src_context (gpost1, gpost2) ), q1)
  in
  let g' = VarLocMap.merge (fun key a b -> begin match (a,b) with
 				| (Some a, Some b) -> Some (join_tau_special (a,b)) 
				| (None, Some b) -> raise JoinError 
				| (Some a, None) -> raise JoinError 
				end) g1 g2
  in g'
 
let rec join_enc_tau = function
 |((EBtInt, p1), (EBtInt, p2)) -> (EBtInt, join (p1, p2))
 |((EBtBool, p1), (EBtBool, p2)) -> (EBtBool, join (p1, p2))
 |((EBtCond, p1), (EBtCond, p2)) -> (EBtCond, join (p1, p2))
 |((EBtRef (rho1, lt1), p1), (EBtRef (rho2, lt2), p2)) -> (* Assume that rho1 = rho2 constraint will be generated *)
							 (EBtRef (rho1, join_enc_tau (lt1,lt2)), join (p1, p2))
 |((EBtFunc(rho1, gencpre1, p1, u1, gencpost1), q1), (EBtFunc (rho2, gencpre2, p2, u2, gencpost2), q2)) ->
							(* FIXME: Not implementing function subtyping for now *) 
							(* gencpre1 = gencpre2 and gencpost1 = gencpost2*)
							(EBtFunc (rho1, join_enc_context (gencpre1, gencpre2), p1, u1, 
							join_enc_context (gencpost1, gencpost2)), join (q1, q2))
 | _,_ -> raise JoinError

(* Only modes should differ, remaining should be same *)
and join_enc_context (g1, g2) = 
  let rec join_tau_special = function
 	|((EBtInt, p1), (EBtInt, p2)) -> if not (p1=p2) then raise JoinError else (EBtInt, p1)
 	|((EBtBool, p1), (EBtBool, p2)) -> if not (p1=p2) then raise JoinError else (EBtBool, p1)
 	|((EBtCond, p1), (EBtCond, p2)) -> if not (p1=p2) then raise JoinError else (EBtCond, p1)
 	|((EBtRef (rho1, lt1), p1), (EBtRef (rho2, lt2), p2)) -> (* Assume that rho1 = rho2 constraint will be generated *)
						if not (p1=p2) then raise JoinError else  (EBtRef (rho1, join_tau_special (lt1,lt2)), p1)
 	|((EBtFunc(rho1, gencpre1, p1, u1, gencpost1), q1), (EBtFunc (rho2, gencpre2, p2, u2, gencpost2), q2)) ->
						(* FIXME: Note the special condition q1 = q2 *)
						let istrue = (p1=p2) && (VarSet.equal u1 u2) && (q1=q2) in
						if not (istrue) then raise JoinError else  (EBtFunc (rho1, join_enc_context (gencpre1,gencpre2), p1, u1, 
												join_enc_context (gencpost1, gencpost2) ), q1)
  in
  let g' = VarLocMap.merge (fun key a b -> begin match (a,b) with
 				| (Some a, Some b) -> Some (join_tau_special (a,b)) 
				| (None, Some b) -> raise JoinError 
				| (Some a, None) -> raise JoinError 
				end) g1 g2
  in g'
 

let rec get_exp_type (g:context) (e:exp) : labeltype =
  match e with
   | Var x -> (try VarLocMap.find (Reg x) g with Not_found -> raise TypeNotFoundError)
   | Loc l -> (try VarLocMap.find (Mem l) g with Not_found -> raise TypeNotFoundError)
   | Lam(gpre, p,u, gpost,q, s) -> (BtFunc(gpre, p,u, gpost), q)
   | Constant n -> (BtInt, Low)
   | True    -> (BtBool, Low)
   | False -> (BtBool, Low)
   | Eq(e1, e2) -> (BtBool, join (snd (get_exp_type g e1), snd (get_exp_type g e2)))
   | Plus(e1, e2) -> (BtInt, join (snd (get_exp_type g e1), snd (get_exp_type g e2)))
   | Isunset x -> (BtBool, Low)
   | Deref e1   -> begin match (get_exp_type g e1) with
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
        | (BtFunc(gpre, p, u, gpost), q) -> let rho = next_tvar () in
			(* Convert gpre and gpost*)
			let gencpre = (VarLocMap.map (fun a -> translatetype a) gpre) in
			let gencpost = (VarLocMap.map (fun a -> translatetype a) gpost) in
			 (EBtFunc(rho, gencpre, p, u,gencpost), q)
	    
let rec get_enc_exp_type (genc:enccontext) (e:encexp) : enclabeltype =
  match e with
   | EVar(rho,x) -> (try VarLocMap.find (Reg x) genc with Not_found -> raise TypeNotFoundError)
   | ELoc(rho, rho', l) -> (try VarLocMap.find (Mem l) genc with Not_found -> raise TypeNotFoundError)
   | ELam(rho, rho', gpre, p,u, gpost, q,s) -> (EBtFunc(rho',gpre,p,u, gpost), q) 
   | EConstant(_,n) -> (EBtInt, Low)
   | ETrue _    -> (EBtBool, Low)
   | EFalse _ -> (EBtBool, Low)
   | EEq(rho,e1, e2) -> (EBtBool, join (snd (get_enc_exp_type genc e1), snd (get_enc_exp_type genc e2)))
   | EPlus(rho,e1, e2) -> (EBtInt, join (snd (get_enc_exp_type genc e1 ), snd (get_enc_exp_type genc e2)))
   | EIsunset(rho,x) -> (EBtBool, Low)
   | EDeref(rho, e)   -> begin match (get_enc_exp_type genc e) with
		  | (EBtRef(rho, lt), p) -> (fst lt, join ((snd lt), p))
		  | _  -> raise TypeError
		 end
 
let rec get_enc_exp_label lt = (snd lt)
		
let get_enclave_id = function
 |Enclave id -> id
 |ModeVar (rho, id) -> id
 | Normal -> raise ModeError

let rec gen_constraints_type (s1: enclabeltype) (s2:enclabeltype) = 
   match (s1, s2) with
   |(EBtRef(m1,s1'), p), (EBtRef( m2, s2'), q) -> let t1 = gen_constraints_type s1' s2' in  [(m1, m2)]@t1 
							(* FIXME: equate gencpre1 and gencpre2; likewise equate gencpost1 and gencpost2 *)
   |(EBtFunc(m1, gencpre1, p1, u1, gencpost1), q1), (EBtFunc(m2, gencpre2, p2, u2, gencpost2), q2) -> 
						let rec gen_constraints_type_for_context genc1 genc2 c =
							let c' = if (not (VarLocMap.is_empty genc1)) && (not (VarLocMap.is_empty genc2)) then
									let (key, value1) = VarLocMap.choose genc1 in
									let value2 = (try VarLocMap.find key genc2 with Not_found -> 
										raise (TranslationError " Error in generating type constraints for functions ")) in
									let c' = gen_constraints_type value1 value2 in
									let genc1', genc2' = (VarLocMap.remove key genc1, VarLocMap.remove key genc2) in
									gen_constraints_type_for_context genc1' genc2' c@c'
								else
									c
							in c'
						in  
						let c1 = gen_constraints_type_for_context gencpre1 gencpre2 [(m1, m2)] in
						let c2 = gen_constraints_type_for_context gencpost1 gencpost2 c1 in
						c2
   | _ -> []
     

(* Code borrowed from gen_constraints_type. This is called whenever a join is performed i.e. in If *)
let rec gen_constraints_join g1 g2 =
			let rec gen_constraints_for_context_join genc1 genc2 c =
					let c' = if (not (VarLocMap.is_empty genc1)) && (not (VarLocMap.is_empty genc2)) then
							let (key, value1) = VarLocMap.choose genc1 in
								let value2 = (try VarLocMap.find key genc2 with Not_found -> 
											raise (TranslationError "Error in generating constraints for join operation")) in
								let c' = gen_constraints_type value1 value2 in
								let genc1', genc2' = (VarLocMap.remove key genc1, VarLocMap.remove key genc2) in
								gen_constraints_for_context_join genc1' genc2' c@c'
							else
								c
					in c'
			in  
			let c1 = gen_constraints_for_context_join g1 g2 []  in
			c1

(* Given a src statement, compute the resulting typing context after the execution of statement *)
let rec src_flow_sensitive_type_infer (pc:policy) (g:context) = function
    |Assign(x,e) -> 
		      let srctype = get_exp_type  g e in
		      let srcvarlabtype = join (pc, (get_exp_label srctype)) in
		      let g1 = VarLocMap.add (Reg x) (fst srctype, srcvarlabtype) g in
		      g1
    |Update(e1, e2) -> g
    |Seq(s1, s2)  ->  let g1 = src_flow_sensitive_type_infer pc g s1 in
		      let g2 = src_flow_sensitive_type_infer pc g1 s2 in
		      g2 
    |Set x	-> g
    |Skip -> g
    |If(e, s1, s2) ->   
		      let pc' = join (get_exp_label (get_exp_type g e), pc) in
    		      let g1 = src_flow_sensitive_type_infer pc' g s1 in
		      let g2 = src_flow_sensitive_type_infer pc' g s2 in
		      let g' = VarLocMap.merge (fun key bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|(Some (b1, p1), Some (b2, p2)) -> 
				if (check_src_base_type b1 b2 ) then Some (join_src_tau ((b1, p1), (b2, p2)))
				else raise (TranslationError "Join of source contexts not possible. Different base types.")
			| _ -> raise (TranslationError "Join of source contexts not possible. Domain of contexts is not same.") 
			end ) g1 g2
			in g'
    |While(e, s) -> (* Compute Fixpoint *)
		    let rec compute_fixpoint s gi'  = 
		    	 let pc' = join (get_exp_label (get_exp_type gi' e), pc) in
			 let gi'' = src_flow_sensitive_type_infer pc' gi' s in
		         let gn = VarLocMap.merge (fun key bp1 bp2 -> 
						begin match (bp1, bp2)  with
						|(Some (b1, p1), Some (b2, p2)) -> 
								if (check_src_base_type b1 b2 ) then Some (join_src_tau ((b1, p1), (b2, p2)))
								else raise (TranslationError "Join of source contexts not possible. Different base types.")
						| _ -> raise (TranslationError "Join of source contexts not possible. Domain of contexts is not same.") 
						end ) g gi''
			in 
			 if (VarLocMap.equal (fun a b -> if a = b then true else false) gi' gi'') then
			 	gn
			 else 
				compute_fixpoint s  gn
		     in compute_fixpoint s g

    |Call e ->  let srctype = get_exp_type g e in
		let gpost = get_src_postcontext srctype in
		(* G_out(x) = G_post(x) if x is in Dom(G_post)
			    = G(x) o.w *)
		let gout = VarLocMap.merge (fun key left right -> begin match (left, right) with
							| Some x, Some y -> left
							| None, right -> right 
							| left, None  -> None (* error *)
							end) gpost g
		in
		gout
		 
		
    |Output(x, e) -> g
    | _  -> raise (UnimplementedError "src flow sensitive typing not implemented for this statement")
    (*
    *)

let rec enc_flow_sensitive_type_infer (pc:policy) (genc:enccontext) = function
    |EAssign(rho, x, e) -> 
		      let enctype = get_enc_exp_type  genc e in
		      let encvarlabtype = join (pc, (get_enc_exp_label enctype)) in
		      let genc1 = VarLocMap.add (Reg x) (fst enctype, encvarlabtype) genc in
		      genc1
    |EUpdate(rho, e1, e2) -> genc
    |ESeq(rho, s1, s2)  ->  let g1 = enc_flow_sensitive_type_infer pc genc s1 in
		            let g2 = enc_flow_sensitive_type_infer pc g1 s2 in
		      	    g2 
    |EESeq(rho, slist)  -> let rec seq_flow_sensitive genc = function
				|[] -> genc
				|s::tail ->
			    		let genc' = enc_flow_sensitive_type_infer pc genc s in
					seq_flow_sensitive genc' tail
			   in seq_flow_sensitive genc slist

    |ESet(rho, x)	-> genc
    |ESkip(rho, rho') -> genc
    |EIf(rho, e, s1, s2) ->   
		      let pc' = get_enc_exp_label (get_enc_exp_type genc e) in
    		      let g1 = enc_flow_sensitive_type_infer pc' genc s1 in
		      let g2 = enc_flow_sensitive_type_infer pc' genc s2 in
		      let g' = VarLocMap.merge (fun key bp1 bp2 -> 
			begin match (bp1, bp2)  with
			|(Some (b1, p1), Some (b2, p2)) -> 
				if (check_enc_base_type b1 b2 ) then Some (join_enc_tau ((b1, p1), (b2, p2)))
				else raise (TranslationError "Join of target contexts not possible. Different base types.")
			| _ -> raise (TranslationError "Join of target contexts not possible. Domain of contexts is not same.") 
			end ) g1 g2
			in g'
    |EWhile(rho, e, s) -> (* Compute Fixpoint *)
		    let rec compute_fixpoint s gi'  = 
		    	 let pc' = join (get_enc_exp_label (get_enc_exp_type gi' e), pc) in
			 let gi'' = enc_flow_sensitive_type_infer pc' gi' s in
		         let gn = VarLocMap.merge (fun key bp1 bp2 -> 
						begin match (bp1, bp2)  with
						|(Some (b1, p1), Some (b2, p2)) -> 
								if (check_enc_base_type b1 b2 ) then Some (join_enc_tau ((b1, p1), (b2, p2)))
								else raise (TranslationError "Join of enclave contexts not possible. Different base types.")
						| _ -> raise (TranslationError "Join of enclave contexts not possible. Domain of contexts is not same.") 
						end ) genc gi''
			in 
			 if (VarLocMap.equal (fun a b -> if a = b then true else false) gi' gi'') then
			 	gn
			 else 
				compute_fixpoint s  gn
		     in compute_fixpoint s genc
    |ECall (rho, e) ->  let enctype = get_enc_exp_type genc e in
			let gencpost = get_enc_postcontext enctype in
			(* Genc_out(x) = Genc_post(x) if x is in Dom(Genc_post)
			    = Genc(x) o.w *)
			let gencout = VarLocMap.merge (fun key left right -> begin match (left, right) with
							| Some x, Some y -> left
							| None, right -> right 
							| left, None  -> None (* error *)
							end) gencpost genc
			in
			gencout
    |EOutput(rho, x, e) -> genc
    | _  -> raise (UnimplementedError "Enclave flow sensitive typing not implemented for this statement")

(* [gen_constraints g e] typegen_constraintss [e] in the context [g] generating a type and a set of constraints. Raise TypeError if constraints cannot be generated. *)
(* Return type is a pair of constraint sets. First set are hard constraints of form P = Q, second set has conditional constraints of form If P then Q *)
let rec gen_constraints_exp (g:context) (rho:mode)  (e:exp) (genc: enccontext) (eidmap:enclaveidmap) (eidrevmap:enclaveidrevmap) : constr * constr2 * modeset * enccontext * enclaveidmap* enclaveidrevmap*totalcost * encexp = 
 let ms = ModeSet.add rho ModeSet.empty in
  match e with
    |Constant n -> (Constr.empty, Constr2.empty, ms, genc, eidmap, eidrevmap,(PMonoterm (0, (Mono (Mode rho))), PMonoterm (0, (Mono (Mode rho)))), EConstant(rho,n))
    | Var x     ->  let srctype = get_exp_type g e in
		    let genc' = if (VarLocMap.mem (Reg x) genc) then genc
		    		else
		    		  let enctype = translatetype srctype in
				  VarLocMap.add (Reg x) enctype genc in 
		    let pol    = get_exp_label srctype in
                                 begin match pol with
                               	| High
                               	| Erase(_,_,_) -> ((Constr.add (Modecond (rho, (Enclave (get_enclave_id rho)))) Constr.empty), Constr2.empty, ms, genc', eidmap, eidrevmap,
								(PMonoterm (0, (Mono (Mode rho))), PMonoterm (0, (Mono (Mode rho)))), EVar(rho,x))
                               	|_ -> (Constr.empty, Constr2.empty, ms, genc', eidmap, eidrevmap,(PMonoterm (0, (Mono (Mode rho))), PMonoterm (0, (Mono (Mode rho)))), EVar(rho,x))                
                             	end
    |Loc l -> let srctype = get_exp_type g e in
	      let genc' = if (VarLocMap.mem (Mem l) genc) then  genc
			   else 
			  	let enctype = translatetype srctype in
			  	VarLocMap.add (Mem l) enctype genc
	      in
	      let creftype = get_src_content_type srctype in (* Since gammasrc(loc) = b_p -> gammasrc(loc)|- (b_p ref)_l*)
	      (* let creftype = srctype in  For locations, contenttype determine the label *) 
	      let rho' = get_mode (VarLocMap.find (Mem l) genc') in
	      begin match get_exp_label creftype with
			| Low -> (Constr.empty, Constr2.empty, ModeSet.add rho' ms, genc', eidmap, eidrevmap,(PMonoterm (0, (Mono (Mode rho))), PMonoterm (0, (Mono (Mode rho)))), ELoc(rho, rho',l) )
			| Erase(_,_,_)
			| High -> let c1, c2, ms1 = 
				(Constr.empty, Constr2.empty, ModeSet.add rho' ms ) in
			 (* p != L -> rho' = E *)
			 (Constr.add (Modecond (rho', (Enclave (get_enclave_id rho')))) c1, c2, ms1, genc', eidmap, eidrevmap,
					(PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))), ELoc(rho, rho', l))	
	      end
    |Eq(e1, e2) -> 
		   let c1, c2, ms1, genc1, eidmap1, eidrevmap1,_, ee1 = gen_constraints_exp g rho e1 genc eidmap eidrevmap in
		   let c3, c4, ms2, genc2, eidmap2, eidrevmap2, _, ee2 = gen_constraints_exp g rho e2 genc1 eidmap1 eidrevmap1 in
		   let c5, c6, ms3 = (Constr.union c1 c3, Constr2.union c2 c4, ModeSet.union ms1 ms2) in
		   begin match get_exp_label (get_exp_type g e) with 
		   | Low -> (c5, c6, ms3, genc2, eidmap2, eidrevmap2, (PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))), EEq(rho, ee1, ee2) )
		   | Erase(_,_,_)
		   | High -> (Constr.add (Modecond (rho, (Enclave (get_enclave_id rho)))) c5, c6, ms3, genc2, eidmap2, eidrevmap2, 
				(PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))), EEq(rho, ee1, ee2) )
		   end
    |Plus(e1, e2) -> 
		   let c1, c2, ms1, genc1, eidmap1,eidrevmap2,  _, ee1 = gen_constraints_exp g rho e1 genc eidmap eidrevmap in
		   let c3, c4, ms2, genc2, eidmap2, eidrevmap2, _, ee2 = gen_constraints_exp g rho e2 genc1 eidmap1 eidrevmap2 in
		   let c5, c6, ms3 = (Constr.union c1 c3, Constr2.union c2 c4, ModeSet.union ms1 ms2) in
		   begin match get_exp_label (get_exp_type g e) with
		   | Low -> (c5, c6, ms3, genc2, eidmap2, eidrevmap2, (PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))), EPlus(rho, ee1, ee2))
		   | Erase(_,_,_)
		   | High -> (Constr.add (Modecond (rho, (Enclave (get_enclave_id rho)))) c5, c6, ms3, genc2, eidmap2, eidrevmap2, 
				(PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))), EPlus(rho, ee1, ee2))
		   end
    |Lam(gpre,p,u, gpost, q,s) -> 
    		   (*let srctype = get_exp_type g e in *)
		   let srctype = (BtFunc(gpre,p, u, gpost), q) in 
		   let enctype = translatetype srctype in
	           let rho' = get_mode enctype in
		   let gencpre = get_enc_precontext enctype in
		   let gencpost = get_enc_postcontext enctype in
		   let c1, c2, ms1, g1, genc1, eidmap1, eidrevmap1, scost, es = gen_constraints p g rho' s genc eidmap eidrevmap true in
		   (* rho = rho'*)
		   let rhoid = (get_enclave_id  rho) in
		   let rho'id = (get_enclave_id  rho') in
		   let c4, c5, ms2, genc2 = (Constr.add (Modecond (rho, rho')) c1, c2, ModeSet.add rho' ms1, genc1) in 
		   (* add bij = 0 *)
		   let (bij, eidmap2, eidrevmap2) = get_bij_var rho rho' eidmap1 eidrevmap1 in
		   let c6 = Constr.add (Eidcond (bij, 0)) c4 in 
		   (* TODO: If u is non-empty, then rho' = E. Add this to constraint *)
		   let ee = ELam(rho, rho',gencpre,p,u,gencpost,q,es) in
			 begin match get_exp_label srctype with
		  	 | Low -> (c6, c5, ms2, genc2, eidmap2, eidrevmap2, scost, ee)
			 | Erase(_,_,_)  (* q !=L -> rho = E *)
			 | High -> (Constr.add (Modecond (rho, (Enclave rhoid))) c6 , c5, ms2, genc2, eidmap2, eidrevmap2, scost, ee)
		         end
    |Deref e1	->  let c1, c2,ms1, genc1, eidmap1, eidrevmap1, ecost, ee = gen_constraints_exp g rho e1 genc eidmap eidrevmap in
		    let enclt =	get_enc_exp_type genc1 ee  in
		    let rho' = get_mode enclt in
		    (*  e1 : b_p ref_q then get (p join q) *)
		    let loctype = get_exp_type g e in
		    (* rho = N -> rho' = N *)
		    let c3 = Constr2.add (Premodecond (rho, Normal), (Modecond (rho', Normal))) c2 in
		    let rhoid = (get_enclave_id  rho) in
		    (* rho' = E -> rho =E *)
		    let c4 = Constr2.add (Premodecond (rho', (Enclave rhoid)), (Modecond (rho, (Enclave rhoid)))) c3 in
		    let (bij, eidmap2, eidrevmap2) = get_bij_var rho rho' eidmap1 eidrevmap1 in
		    let c5 = Constr2.add (Premodecond (rho', (Enclave rhoid)), (Eidcond (bij, 0))) c4 in
			begin match get_exp_label loctype  with
			| Low  -> (c1, c5, ModeSet.union ms1 ms, genc1, eidmap2, eidrevmap2, ecost, EDeref(rho,ee))
			| Erase(_,_,_) (* p join q !=L -> rho = rho' = E *)
			| High -> let c6 = Constr.add (Modecond (rho, (Enclave rhoid ))) c1 in
				  let c7 = Constr.add (Modecond (rho', (Enclave rhoid))) c6 in
				  (Constr.add (Eidcond (bij,0)) c7, c5, ModeSet.union ms1 ms, genc1, eidmap2, eidrevmap2, ecost, EDeref(rho,ee))
			end  
    |True	-> (Constr.empty, Constr2.empty,ms, genc, eidmap, eidrevmap, (PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))),ETrue rho )
    |False-> (Constr.empty, Constr2.empty,ms, genc, eidmap, eidrevmap, (PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))), EFalse rho )
    |Isunset x -> (Constr.empty, Constr2.empty, ms, genc, eidmap, eidrevmap, (PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))),EIsunset(rho,x) )


(* + Maintain a different set for collecting implication constraints
     e.g: rho = E -> rho' = E 
   + Return type is a pair of constraint sets. First set are hard constraints of form P = Q, second set has conditional constraints of form If P then Q 
   + modeenv - maps rho to program statements and expressions - for readability
   + modeset - set of mode variables
*)
and gen_constraints (pc:policy) (g:context) (rho: mode) (s0:stmt) (genc:enccontext) (eidmap: enclaveidmap) (eidrevmap:enclaveidrevmap) (toplevel:bool) : constr * constr2 * modeset * context * enccontext * enclaveidmap * enclaveidrevmap* totalcost * encstmt = 
 let ms = ModeSet.add rho ModeSet.empty in
  match s0 with
    | Assign(x, e) -> 
		      let c1, c2, ms1, genc1, eidmap1, eidrevmap1, ecost, ee = gen_constraints_exp g rho e genc eidmap eidrevmap in
		      (* Update source typing context *)
		      let g2 = src_flow_sensitive_type_infer pc g s0 in
		      (* get enclave type of ee *)
		      let enclt = get_enc_exp_type genc1 ee in
		      let varlabtype = join (pc, (get_exp_label enclt)) in
		      (* update genc1 *)
		      let genc2 =  VarLocMap.add (Reg x) (fst enclt, varlabtype) genc1 in
		      let totalc = ecost in
		      let estmt = EAssign(rho, x, ee) in
		      let ms2 = ModeSet.union ms ms1 in
		      begin match varlabtype with
			| Erase(_,_,_)
			| High -> let c3 = (Constr.add (Modecond (rho, (Enclave (get_enclave_id rho)))) c1) in
				  (c3, c2, ms2, g2, genc2, eidmap1, eidrevmap1, totalc, estmt)
			| _ -> (c1, c2, ms2, g2, genc2, eidmap1, eidrevmap1, totalc,  estmt)
		      end
    |Update(e1, e2) -> 
		      let c1, c2, ms1, genc1, eidmap1, eidrevmap1, ecost1, ee1 = gen_constraints_exp g rho e1 genc eidmap eidrevmap in
		      let c3, c4, ms2, genc2, eidmap2, eidrevmap2, ecost2, ee2 = gen_constraints_exp g rho e2 genc1 eidmap1 eidrevmap1 in
		
		      let c5, c6 = (Constr.union c1 c3, Constr2.union c2 c4) in
		      let ms3 = ModeSet.union ms ms1 in 
		      let ms4 = ModeSet.union ms2 ms3 in 

		      let totalc = (PPlus (fst ecost1, fst ecost2), PPlus (snd ecost1, snd ecost2)) in
		      let estmt = EUpdate(rho, ee1, ee2) in


		      (* Get the translated type of e1 *)
		      let refenclt1 = (get_enc_exp_type genc2 ee1 ) in
		      let rho'      = get_mode refenclt1 in 
		      let enclt1   = get_content_type refenclt1 in (* Fetches pointer type e.g.: ((int_h) ref) gives int_h *)
		      let enclt2   =  (get_enc_exp_type genc2 ee2 ) in

		      (* types of content and rhs should match   *)
		      let t1       = gen_constraints_type enclt1 enclt2 in 
		      let (c7, eidmap2', eidrevmap2')   = update_constraints t1 c5 eidmap2 eidrevmap2 in	
			
		      let rhoid = get_enclave_id rho in
		      let rho'id =get_enclave_id rho' in

		      (* rho'= E -> rho = E *)
		      let c8 = Constr2.add ( Premodecond (rho', (Enclave rho'id)), (Modecond (rho, (Enclave rho'id)))) c6 in
		      let (bij, eidmap3, eidrevmap3) = get_bij_var rho rho' eidmap2' eidrevmap2' in
		      (* rho'= E -> bij = 0 *)
		      let c9 = Constr2.add ( Premodecond (rho', (Enclave rho'id)), (Eidcond (bij,0)))  c8 in

		      begin match get_exp_label enclt1 with
			| Erase(_,_,_)	(* rho' = E, rho = E *)
			| High -> let c10 = (Constr.add (Modecond (rho, (Enclave rhoid))) c7) in
				  let c11 = (Constr.add (Modecond (rho', (Enclave rhoid))) c10) in
				  (* bij = 0 *)
				  let (bij, eidmap4, eidrevmap4)  = get_bij_var rho rho' eidmap3 eidrevmap3 in 
				   (Constr.add (Eidcond (bij, 0)) c11,	c9, ms4, g, genc2, eidmap4, eidrevmap4, totalc, estmt)
			| _ -> (c7, c9, ms4, g, genc2, eidmap3, eidrevmap3, totalc, estmt)
		      end
    |Seq(s1, s2)  -> let seqlist = flattenseq s0 in
			let rec seqloop pc c1 c2 rhoi  ms scost g genc eidmap eidrevmap eslist = function
			| [] -> (c1, c2, ms, g,  genc, eidmap, eidrevmap, scost, eslist)
			| xs::tail -> 
				    let  c3, c4, ms1, g1, genc1, eidmap1, eidrevmap1, scost1, es1 = gen_constraints pc g rhoi xs genc eidmap eidrevmap false in
				    if not (List.length tail = 0) then
				    	let rhoj = next_tvar () in
					let (bij, eidmap2, eidrevmap2) = get_bij_var rhoi rhoj eidmap1 eidrevmap1 in
				    	(* Check if genc1 has any high registers. If yes, then generate the constraints *)
				     	let allreglow = check_typing_context_reg_low genc1 in
				     	let c5 =
							if (not allreglow) then
					       			(* ~(rho=N /\ rhoi = E /\ rho_(i+1) = N) *)
					       			let t = (Constr.add (Cnfclause [Modecond (rho, Enclave (get_enclave_id rho)); Modecond (rhoi, Normal); 
											Modecond (rhoj, Enclave (get_enclave_id rhoj))]) c3) in 
					       			(* (rho=E \/ ( rhoi = E /\ rho_(i+1) = E) -> b_i(i+1) = 0) *)
					        		(Constr.add (Cnfclause [Modecond (rho, Enclave (get_enclave_id rho)); Modecond (rhoi, Normal); 
										Modecond (rhoj, Normal); Eidcond (bij, 0)]) t)
					       		else
								c3
 				     	in
				     	let (c6, eidmap3, eidrevmap3) = begin match rho with
						| Normal -> (c4, eidmap2, eidrevmap2) (* no enclave id exists *)
						| _ ->
 						        let c4' = 
				     			(* rho = E -> rhoi = E *)
				     			Constr2.add (Premodecond (rho, (Enclave (get_enclave_id rho))), (Modecond (rhoi, (Enclave (get_enclave_id rho))))) c4 
							in
				     			(* rho = E -> bij = 0 *)
							let (bij, eidmap3, eidrevmap3) = get_bij_var rho rhoi eidmap2 eidrevmap2 in
				     			(Constr2.add (Premodecond (rho, (Enclave (get_enclave_id rho))), (Eidcond (bij, 0))) c4', eidmap3, eidrevmap3)
							 
						end
					in
				     	let entrycost = compute_one_seq_entry_cost rho rhoi rhoj bij (PPlus (fst scost, fst scost1)) in
				     	(* Trusted cost on next statement in the list *)
				     	let trustedcost = if (List.length tail = 0) then
								(PPlus (snd scost, snd scost1)) 
							  else
								compute_one_seq_trusted_cost rho rhoj (List.hd tail) (PPlus (snd scost, snd scost1))
				     	in
				     	let totalc = (entrycost, trustedcost) in
				     	seqloop pc (Constr.union c1 c5) (Constr2.union c2 c6) rhoj (ModeSet.union ms ms1) totalc g1 genc1 eidmap3 eidrevmap3 (eslist @ [es1]) tail
				     else
				     	let (c6, eidmap3, eidrevmap3) = begin match rho with
						| Normal -> (c4, eidmap1, eidrevmap1) (* no enclave id exists *)
						| _ ->
 						        let c4' = 
				     			(* rho = E -> rhoi = E *)
				     			Constr2.add (Premodecond (rho, (Enclave (get_enclave_id rho))), (Modecond (rhoi, (Enclave (get_enclave_id rho))))) c4 
							in
				     			(* rho = E -> bij = 0 *)
							let (bij, eidmap3, eidrevmap3) = get_bij_var rho rhoi eidmap1 eidrevmap1 in
				     			(Constr2.add (Premodecond (rho, (Enclave (get_enclave_id rho))), (Eidcond (bij, 0))) c4', eidmap3, eidrevmap3)
							 
						end
					in
				    	(* Check if genc1 has any high registers. If yes, raise error. Translation not possible*)
				     	let allreglow = check_typing_context_reg_low genc1 in
					if (not allreglow) && toplevel then raise (TranslationError "Registers may contain secrets when exiting enclave.")
					else
				     	seqloop pc (Constr.union c1 c3) (Constr2.union c2 c6) rhoi (ModeSet.union ms ms1) scost g1 genc1 eidmap3 eidrevmap3 (eslist @ [es1]) tail
		     in
		     (* initially zero cost, compute later *)
		     let zerocost = (PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))) in 
		     let rho0 = next_tvar () in
		     let c1, c2, ms1, g1, genc1, eidmap1, eidrevmap1, fcost, eslist = seqloop pc Constr.empty Constr2.empty rho0  ms zerocost  g genc  eidmap eidrevmap [] seqlist in
		     (* compute additional entry cost *)
		     let rho1 = begin match eslist with
				|[] -> raise EmptySeqError
				|xs::tail-> getstmtmode xs
				end in
		     (* init statement cost. e.g., c1;c2;c3..., then initcost gets entry cost for c1 as (1-rho)rho1 *)
		     let initentrycost = (PMinus (PMonoterm (1, (Mono (Mode rho1))), (PMonoterm (1, (Poly ((Mode rho), ((Mono (Mode rho1))))))))) in
		     let inittrustedcost = if List.length seqlist = 0 then
						raise (TranslationError "Invalid sequence list")
					   else
					       let s = List.hd seqlist in
					       let sweight = num_atomic_stmt s in
					       (PMinus (PMonoterm (sweight, (Mono (Mode rho1))), (PMonoterm (sweight, (Poly ((Mode rho), ((Mono (Mode rho1)))))))))
		     in
		     let seqentrycost = (PPlus (fst fcost, initentrycost)) in
		     let seqtrustedcost = (PPlus (snd fcost, inittrustedcost)) in
		     (* Add diffenclave id cost to trusted cost *)
		     let rec compute_diff_id_cost eslist (rho:mode) eidmap eidrevmap fcost =
 			begin match eslist with
		     	| [] -> (fcost, eidmap, eidrevmap)
		     	| xs::tail -> (* iterate on tail *)
				    let one_diffid_cost, eidmap2, eidrevmap2 = compute_seq_diffencid_cost tail rho xs eidmap eidrevmap fcost in
				    compute_diff_id_cost tail rho eidmap2 eidrevmap2 one_diffid_cost
			end
		     in
		     let (total_diff_id_cost, eidmap3, eidrevmap3) = compute_diff_id_cost eslist rho eidmap1 eidrevmap1 seqtrustedcost in			   
		     let totalc = (seqentrycost, total_diff_id_cost) in
		     let es = (EESeq (rho, eslist)) in
		     (c1, c2, ms1, g1, genc1, eidmap3, eidrevmap3, totalc, es) 
    |If(e, s1, s2) -> 
			(* TODO: Implement isunset() translation here *)
		      let c1, c2, ms1, genc1, eidmap1, eidrevmap1, ecost, ee = gen_constraints_exp g rho e genc eidmap eidrevmap in
		      let rho1 = next_tvar() in
		      let rho2 = next_tvar() in
		      let pc' = get_exp_label (get_exp_type g e) in
		      (* Note use only genc1! *)
		      let c3, c4, ms2, g2, genc2, eidmap2, eidrevmap2, fcost1, es1 = gen_constraints pc' g rho1 s1 genc1 eidmap1 eidrevmap1 false in
		      let c5, c6, ms3, g3, genc3, eidmap3, eidrevmap3, fcost2, es2 = gen_constraints pc' g rho2 s2 genc1 eidmap2 eidrevmap2 false in
		      let c7, c8 = (Constr.union c1 c3, Constr2.union c2 c4) in
		      let c9, c10 = (Constr.union c5 c7, Constr2.union c6 c8) in
		      let allreglow1 = check_typing_context_reg_low genc2 in
		      let c11 = if (not allreglow1) then 
					(* Add constraint ~(rho=N) *)
					Constr.add (Modecond (rho, (Enclave (get_enclave_id rho)))) c9	
				else
					c9
		       in
		      let allreglow2 = check_typing_context_reg_low genc3 in
		      let c12 = if (not allreglow2) then 
					(* Add constraint ~(rho=N) *)
					Constr.add (Modecond (rho, (Enclave (get_enclave_id rho)))) c11	
				else
					c11
			in
			(* Add constraint rho = E -> rhoi = E *)
			let c13 = Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Modecond (rho1, Enclave (get_enclave_id rho))) c10 in
			let (bij, eidmap', eidrevmap') = get_bij_var rho rho1 eidmap3 eidrevmap3 in
			let c13' = Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Eidcond(bij, 0)) c13 in
			let c14 = Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Modecond (rho2, Enclave (get_enclave_id rho))) c13' in
			let (bij', eidmap'', eidrevmap'') = get_bij_var rho rho1 eidmap' eidrevmap' in
			let c14' = Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Eidcond(bij', 0)) c14 in

			let es0 = EIf(rho, ee, es1, es2) in
			(* Update source and target typing contexts *)
			let g' = src_flow_sensitive_type_infer pc g s0 in
			let genc' = enc_flow_sensitive_type_infer pc genc1 es0 in

		        (* After join, enclave modes should match *)
		        let t1       = gen_constraints_join genc2 genc3 in 
		        let (c15, eidmap''', eidrevmap''')       = update_constraints t1 c12 eidmap'' eidrevmap'' in	
			
			(* Handle cost for introducing enclave. i.e. rho = N and rho_i =E *)
			let init_entry_cost = PPlus (fst ecost, fst fcost1) in
			let if_entry_cost = (* (1-rho)rho1 + (1-rho)rho2 *)
					   compute_if_entry_cost rho rho1 rho2 (PPlus (init_entry_cost, fst fcost2)) in
			let init_trusted_cost = PPlus (snd ecost, snd fcost1) in
			let if_trusted_cost = 
					   compute_if_trusted_cost rho rho1 rho2 s1 s2 (PPlus (init_trusted_cost, snd fcost2)) in
			let (b12, eidmap4, eidrevmap4)  = get_bij_var rho1 rho2 eidmap''' eidrevmap''' 
			in 
			let if_diffid_cost = (* FIXME MAJOR: We are being locally maximum in using b12. Ideally it should take all id's into consideration *) 
					   compute_if_diffid_cost  rho rho1 rho2 b12 if_trusted_cost 
			in
		 	let (b1, eidmap5, eidrevmap5) = get_bij_var rho rho1 eidmap4 eidrevmap4 in
		 	let (b2, eidmap6, eidrevmap6) = get_bij_var rho rho2 eidmap5 eidrevmap5 in
			let ms4 = ModeSet.union ms ms1 in
			let ms5 = ModeSet.union ms2 ms3 in 
			begin match (get_exp_label (get_exp_type g e)) with
				| Low -> (c15, c14', ModeSet.union ms4 ms5, g', genc', eidmap6, eidrevmap6, (if_entry_cost,if_diffid_cost),  es0)
				| Erase(_,_,_)  (* Add rho = rho1 =rho2 = E *)
				| High ->let c16 = (Constr.add (Modecond (rho, Enclave (get_enclave_id rho))) c15) in
					 let c17 = (Constr.add (Modecond (rho1, Enclave (get_enclave_id rho))) c16) in
					 let c18 = (Constr.add (Eidcond (b1, 0)) c17) in 
					 let c19 = (Constr.add (Eidcond (b2, 0)) c18) in 
					(Constr.add (Modecond (rho2, Enclave (get_enclave_id rho))) c19, c14', ModeSet.union ms4 ms5, g', genc', eidmap6, eidrevmap6, (if_entry_cost,if_diffid_cost), es0)
			end
    |Call e -> 
		      let c1, c2, ms1, genc1, eidmap1, eidrevmap1, ecost, ee = gen_constraints_exp g rho e genc eidmap eidrevmap in
		      let totalc = ecost in
		      (* get mode of e *)
		      let rho' = get_mode (get_enc_exp_type genc1 ee) in
		      let btfunctype = get_exp_type  g e in
		      let gpre = get_src_precontext btfunctype in
		      let gpost = get_src_precontext btfunctype in
		      let ebtfunctype = get_enc_exp_type  genc1 ee in
		      let gencpre = get_enc_precontext ebtfunctype in
		      let gencpost = get_enc_precontext ebtfunctype in
		      (* TODO: Check g <= gpre, gpost <= gout *)
		      let es0 = ECall(rho, ee) in 
		      let gout = src_flow_sensitive_type_infer pc g s0 in
		      let gencout = enc_flow_sensitive_type_infer pc genc1 es0 in
		      (* rho = rho' *)
		      let c3 = (Constr.add (Modecond (rho, rho')) c1) in
		      let (bij, eidmap2, eidrevmap2) = get_bij_var rho rho' eidmap1 eidrevmap1 in
			(Constr.add (Eidcond (bij, 0)) c3, c2, ModeSet.union ms ms1, gout, gencout, eidmap2, eidrevmap2, totalc, ECall(rho, ee))

    |While(e, s) -> 
		      let c1, c2, ms1, genc1, eidmap1, eidrevmap1, ecost, ee = gen_constraints_exp g rho e genc eidmap eidrevmap in
		      let rho' = next_tvar() in
		      let pc' = get_exp_label (get_exp_type g e) in
		      (* Note use only genc1! *)
		      let c3, c4, ms2, g2, genc2, eidmap2, eidrevmap2, fcost, es = gen_constraints pc' g rho' s genc1 eidmap1 eidrevmap1 false in
		      let c7, c8 = (Constr.union c1 c3, Constr2.union c2 c4) in
		      let allreglow1 = check_typing_context_reg_low genc2 in
		      let c9 = if (not allreglow1) then 
					(* Add constraint ~(rho=N) *)
					Constr.add (Modecond (rho, (Enclave (get_enclave_id rho)))) c7	
				else
					c7
		       in
			(* Add constraint rho = E -> rho' = E *)
			let c10 = Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Modecond (rho', Enclave (get_enclave_id rho))) c8 in
			let (bij, eidmap', eidrevmap') = get_bij_var rho rho' eidmap2 eidrevmap2 in
			let c11 = Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Eidcond(bij, 0)) c10 in

			let es0 = EWhile(rho, ee, es) in
			(* Update source and target typing contexts *)
			let g' = src_flow_sensitive_type_infer pc g s0 in
			let genc' = enc_flow_sensitive_type_infer pc genc1 es0 in
			
			(* REVISIT: Should join result in generating constraints for mode?
				  Not necessary. No new mode variables get introduced during join here
			 *)
			
			(* Handle cost for introducing enclave. i.e. rho = N and rho' =E *)
			let while_entry_cost = (* (1-rho)rho'  *)
					   compute_while_entry_cost rho rho' (fst fcost) in
			let while_trusted_cost = 
					   compute_while_trusted_cost rho rho' s (snd fcost) in
		 	let (b1, eidmap2, eidrevmap2) = get_bij_var rho rho' eidmap' eidrevmap' in
			let ms3 = ModeSet.union ms ms1 in
			begin match (get_exp_label (get_exp_type g e)) with
				| Low -> (c9, c11, ModeSet.union ms2 ms3, g', genc', eidmap2, eidrevmap2, (while_entry_cost,while_trusted_cost),  es0)
				| Erase(_,_,_)  (* Add rho = rho1= E *)
				| High ->let c12 = (Constr.add (Modecond (rho, Enclave (get_enclave_id rho))) c9) in
					 let c13 = (Constr.add (Modecond (rho', Enclave (get_enclave_id rho))) c12) in
					 let c14 = (Constr.add (Eidcond (b1, 0)) c13) in 
					(c14, c11, ModeSet.union ms2 ms3, g', genc', eidmap2, eidrevmap2, (while_entry_cost,while_trusted_cost),  es0)
			end
		     
    |Output(x, e) -> 
		      let c1, c2, ms1, genc1, eidmap1, eidrevmap1, ecost, ee = gen_constraints_exp g rho e genc eidmap eidrevmap in
		      let totalc = ecost in
		      let es0 = EOutput(rho, x, ee) in
		 	begin match x with
			| 'H' -> (Constr.add (Modecond (rho, Enclave (get_enclave_id rho))) c1, c2, ModeSet.union ms ms1, g, genc1, eidmap1, eidrevmap1, totalc, es0)
			| _ -> (c1,  c2, ModeSet.union ms ms1, g, genc1, eidmap1, eidrevmap1, totalc, es0)
			end
		
    | _ -> raise (UnimplementedError "Constraint generation not supported for this construct" )
    | Set x	-> 
		      let c1, c2, ms1, genc1, eidmap1, eidrevmap1, ecost, ee = gen_constraints_exp g rho (Var x) genc eidmap eidrevmap in
		      let totalc = ecost in
		      let es0 = ESet(rho, x) in

		      let refenclt1 = (get_enc_exp_type genc1 ee ) in
		      let rho'      = get_mode refenclt1 in 
		      (* rho = E => rho' = E *)
		      let c3 = (Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Modecond (rho', Enclave (get_enclave_id rho))) c2) in
		      let (bij, eidmap', eidrevmap') = get_bij_var rho rho' eidmap1 eidrevmap1 in
		      let c4 = Constr2.add (Premodecond (rho, Enclave (get_enclave_id rho)), Eidcond(bij, 0)) c3 in
			(* Unlike assign, donot update type of cnd *)
		      (c1, c4, ModeSet.union ms ms1, g, genc1, eidmap', eidrevmap', totalc, es0)
    | Skip -> let zerocost = (PMonoterm (0, ((Mono (Mode rho)))), PMonoterm (0, ((Mono (Mode rho))))) in 
		(Constr.empty, Constr2.empty, ms, g, genc, eidmap, eidrevmap, zerocost,  ESkip(rho, rho))
