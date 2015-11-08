open Ast
open Printf
open Pprint

exception PrintError

(* Set of Lam expressions *)
module ELamSet = Set.Make(struct
  type t = encexp
  let compare = Pervasives.compare
end)
type elamset = ELamSet.t

(* 1 - dashed line, 2 - \t, 3 - \n *)
let printSpace (oc:out_channel) (space:int) = 
match space with
 | 1 -> Printf.fprintf oc "\n --------------------------------------\n"
 | 2 -> Printf.fprintf oc "\t"
 | 3 -> Printf.fprintf oc "\n"
 | _ -> raise PrintError
 
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

let rec collectlam elset = function
  | EIf (m,e,c1,c2) -> let es1 = collectlam elset c1 in
			collectlam es1 c2
  | EAssign(m, x, e) ->collectlamexp elset e
  | ESeq(m,s1, s2) -> let es1 = collectlam elset s1 in
			collectlam es1 s2
  | ECall(m,e)    -> collectlamexp elset e
  | EUpdate(m,e1, e2) -> collectlamexp elset e2
  | EWhile(m, b, s) -> collectlam elset s
  | ESkip (m, m') -> elset
  | EOutput(m,ch, e) ->collectlamexp elset e
  | ESet(m,x)	-> elset

and collectlamexp elset = function
  | EVar(rho, v) -> elset
  | ELam(rho, rho', p, u, q, s) -> let es = collectlam elset s in 
				(ELamSet.add (ELam (rho, rho', p, u, q, s)) es)
  | EPlus (rho, l,r) -> elset
  | EConstant(rho,n) -> elset
  | ETrue rho ->  elset
  | EFalse rho  -> elset
  | EEq (rho, l,r) -> elset
  | ELoc(rho, rho', l) ->elset
  | EDeref(rho,e) -> elset
  | EIsunset(rho,x) -> elset

(* Prints only enclave mode statements *)
let rec pprintEncStmtnomode oc  = function
  | rhomap, EIf (m,e,c1,c2),isenc -> if isenc then
					Printf.fprintf oc "enclave(if %a then %a else %a)" pprintEncExpnomode (rhomap, e) pprintEncStmtnomode (rhomap, c1, false) pprintEncStmtnomode (rhomap, c2, false)
				     else
  					Printf.fprintf oc "if %a then %a else %a" pprintEncExpnomode (rhomap, e) pprintEncStmtnomode (rhomap, c1, false) pprintEncStmtnomode (rhomap, c2, false)
  | rhomap, EAssign(m, x, e),isenc -> if isenc then
					Printf.fprintf oc "enclave( %s := %a )" x pprintEncExpnomode (rhomap, e) 
				      else
					Printf.fprintf oc "%s := %a " x pprintEncExpnomode (rhomap, e) 
  | rhomap, ESeq(m,s1, s2),isenc -> if isenc then
					Printf.fprintf oc "enclave( %a ;\n %a )" pprintEncStmtnomode (rhomap, s1, false) pprintEncStmtnomode (rhomap, s2, false)
				    else
					Printf.fprintf oc "%a ;\n %a " pprintEncStmtnomode (rhomap, s1, false) pprintEncStmtnomode (rhomap, s2, false)
  | rhomap, ECall(m,e), isenc    ->  if isenc then
					Printf.fprintf oc "enclave( call(%a) )" pprintEncExpnomode (rhomap, e) 
				    else
					Printf.fprintf oc "call(%a)" pprintEncExpnomode (rhomap, e) 
  | rhomap, EUpdate(m,e1, e2), isenc ->  if isenc then
					Printf.fprintf oc "enclave( %a <- %a )" pprintEncExpnomode (rhomap, e1) pprintEncExpnomode (rhomap, e2)
				    else
					Printf.fprintf oc "%a <- %a" pprintEncExpnomode (rhomap, e1) pprintEncExpnomode (rhomap, e2)
  | rhomap, EWhile(m, b, s), isenc ->  if isenc then
					Printf.fprintf oc "enclave( while %a do %a )" pprintEncExpnomode (rhomap, b) pprintEncStmtnomode (rhomap, s, false)
				    else
					Printf.fprintf oc "while %a do %a" pprintEncExpnomode (rhomap, b) pprintEncStmtnomode (rhomap, s, false)
  | rhomap, ESkip (m, m'), isenc ->  if isenc then
					Printf.fprintf oc "enclave( skip )"
				    else
					Printf.fprintf oc "skip"
  | rhomap, EOutput(m,ch, e), isenc ->  if isenc then
					Printf.fprintf oc "enclave( output(_, %a) )" pprintEncExpnomode (rhomap, e)
				    else
					Printf.fprintf oc "output(_, %a)" pprintEncExpnomode (rhomap, e)
  | rhomap, ESet(m,x), isenc	->  if isenc then
					Printf.fprintf oc "enclave( set(%s) )" x
				    else
					Printf.fprintf oc "set(%s)" x

and pprintEncExpnomode oc  = function
  | rhomap, EVar(rho, v) -> Printf.fprintf oc "%s" v
  | rhomap, ELam(rho, rho', p, u, q, s) -> Printf.fprintf oc "(lambda^%d(_,_).%a)" (ModeSAT.find rho' rhomap) prettytranslate (s, rhomap)
  | rhomap, EPlus (rho, l,r) -> Printf.fprintf oc "%a + %a" pprintEncExpnomode (rhomap, l) pprintEncExpnomode (rhomap, r)
  | rhomap, EConstant(rho,n) -> Printf.fprintf oc "%d" n
  | rhomap, ETrue rho ->  Printf.fprintf oc "true"
  | rhomap, EFalse rho  -> Printf.fprintf oc "false"
  | rhomap, EEq (rho, l,r) -> Printf.fprintf oc "%a == %a" pprintEncExpnomode (rhomap, l) pprintEncExpnomode (rhomap, r)
  | rhomap, ELoc(rho, rho', l) ->Printf.fprintf oc "l%d" l
  | rhomap, EDeref(rho,e) -> Printf.fprintf oc "*%a" pprintEncExpnomode (rhomap, e)
  | rhomap, EIsunset(rho,x) -> Printf.fprintf oc "isunset(%s)" x

and prettytranslate oc (s, rhomap) = 
match s with
 |ESkip (rho, rho') ->  let rhoprimeenc = (ModeSAT.find rho' rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			pprintEncStmtnomode oc (rhomap, s, insertenc)
 |EAssign(rho, x, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			pprintEncStmtnomode oc (rhomap, s, insertenc) 
 |EUpdate(rho, e1, e2) -> let rhoprimeenc = (ModeSAT.find (getexpmode e2) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			pprintEncStmtnomode oc (rhomap, s, insertenc) 
 |EIf(rho, b, s1, s2) ->let rhoprimeenc = (ModeSAT.find (getexpmode b) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			if insertenc || (rhonorm = 1) then
				(* inserting enclave statement or printing in enclave mode. done *)
				pprintEncStmtnomode oc (rhomap, s, insertenc)
			else
				(* Recursively translate *)
				Printf.fprintf oc "if %a then %a else %a\n" pprintEncExpnomode (rhomap, b) prettytranslate (s1, rhomap) prettytranslate (s2, rhomap)

 |ESeq(rho, s1, s2) -> let rhoprimeenc = (ModeSAT.find (getstmtmode s1) rhomap) in
			let rhodoubprimeenc = (ModeSAT.find (getstmtmode s2) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1)&&(rhodoubprimeenc = 1) then true else false in
			if insertenc || (rhonorm = 1) then
				(* inserting enclave statement or printing in enclave mode. done *)
				pprintEncStmtnomode oc (rhomap, s, insertenc)
			else
				if (rhonorm = 0)&&(rhoprimeenc=1)&&(rhodoubprimeenc = 0) then
					(pprintEncStmtnomode oc (rhomap, s1, true); Printf.fprintf oc ";\n"; prettytranslate oc (s2, rhomap))
				else
				   if (rhonorm = 0)&&(rhoprimeenc = 0)&& (rhodoubprimeenc=1) then
					(prettytranslate oc (s1, rhomap); Printf.fprintf oc ";\n"; pprintEncStmtnomode oc (rhomap, s2, true))
				   else
					(* Recursively translate *)
					(prettytranslate oc (s1, rhomap); Printf.fprintf oc ";\n"; prettytranslate oc (s2, rhomap))

 |ECall(rho, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			pprintEncStmtnomode oc (rhomap, s, insertenc) 
 |EWhile(rho,b,s1) -> let rhoprimeenc = (ModeSAT.find (getexpmode b) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			if insertenc || (rhonorm = 1) then
				(* inserting enclave statement or printing in enclave mode. done *)
				pprintEncStmtnomode oc (rhomap, s, insertenc)
			else
				(* Recursively translate *)
				Printf.fprintf oc "while %a then %a \n" pprintEncExpnomode (rhomap, b) prettytranslate (s1, rhomap)

 |EOutput(rho,ch, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			pprintEncStmtnomode oc (rhomap, s, insertenc) 
 |ESet(rho,x)	->      pprintEncStmtnomode oc (rhomap, s, false) 
 |_  ->Printf.fprintf oc "EOF"

let rec translate oc (s, rhomap, space) = 
match s with
 |ESkip (rho, rho') ->  let rhoprimeenc = (ModeSAT.find rho' rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap, s, insertenc) ;
			printSpace oc 2
 |EAssign(rho, x, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap, s, insertenc) ;
			printSpace oc 2
 |EUpdate(rho, e1, e2) -> let rhoprimeenc = (ModeSAT.find (getexpmode e2) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap, s, insertenc) ;
			printSpace oc 2
 |EIf(rho, b, s1, s2) ->let rhoprimeenc = (ModeSAT.find (getexpmode b) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap, s, insertenc) ;
			printSpace oc 1;  translate oc (s1, rhomap, space) ;
			translate oc (s2, rhomap, space) 
 |ESeq(rho, s1, s2) -> let rhoprimeenc = (ModeSAT.find (getstmtmode s1) rhomap) in
			let rhodoubprimeenc = (ModeSAT.find (getstmtmode s2) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1)&&(rhodoubprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap,s, insertenc) ;
			printSpace oc 1;  translate oc (s1, rhomap, space) ;
			translate oc (s2, rhomap, space)
 |ECall(rho, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap, s, insertenc) ;
			printSpace oc 2
 |EWhile(rho,b,s1) -> let rhoprimeenc = (ModeSAT.find (getexpmode b) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap, s, insertenc) ;
			printSpace oc 1; translate oc (s1, rhomap, space)
 |EOutput(rho,ch, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			printEncStmtwithmode oc (rhomap, s, insertenc) ;
			printSpace oc 2
 |ESet(rho,x)	->      printEncStmtwithmode oc (rhomap, s, false) ;
			printSpace oc 2
 |_  ->Printf.fprintf oc "EOF"

and printEncStmtnomode oc  = function
  | rhomap, EIf (m,e,c1,c2) -> Printf.fprintf oc "if %a then %a else %a" printEncExpnomode (rhomap, e) printEncStmtnomode (rhomap, c1) printEncStmtnomode (rhomap, c2)
  | rhomap, EAssign(m, x, e) -> Printf.fprintf oc "%s := %a " x printEncExpnomode (rhomap, e) 
  | rhomap, ESeq(m,s1, s2) -> Printf.fprintf oc "%a ; %a" printEncStmtnomode (rhomap, s1) printEncStmtnomode (rhomap, s2)
  | rhomap, ECall(m,e)    -> Printf.fprintf oc "call(%a)" printEncExpnomode (rhomap, e) 
  | rhomap, EUpdate(m,e1, e2) -> Printf.fprintf oc "%a <- %a" printEncExpnomode (rhomap, e1) printEncExpnomode (rhomap, e2)
  | rhomap, EWhile(m, b, s) -> Printf.fprintf oc "while %a do %a" printEncExpnomode (rhomap, b) printEncStmtnomode (rhomap, s)
  | rhomap, ESkip (m, m') -> Printf.fprintf oc "skip"
  | rhomap, EOutput(m,ch, e) -> Printf.fprintf oc "output(_, %a)" printEncExpnomode (rhomap, e)
  | rhomap, ESet(m,x)	-> Printf.fprintf oc "set(%s)" x

and printEncExpnomode oc  = function
  | rhomap, EVar(rho, v) -> Printf.fprintf oc "%s" v
  | rhomap, ELam(rho, rho', p, u, q, s) -> Printf.fprintf oc "(lambda^%d(_,_).%a)" (ModeSAT.find rho' rhomap) printEncStmtnomode (rhomap, s)
  | rhomap, EPlus (rho, l,r) -> Printf.fprintf oc "%a + %a" printEncExpnomode (rhomap, l) printEncExpnomode (rhomap, r)
  | rhomap, EConstant(rho,n) -> Printf.fprintf oc "%d" n
  | rhomap, ETrue rho ->  Printf.fprintf oc "true"
  | rhomap, EFalse rho  -> Printf.fprintf oc "false"
  | rhomap, EEq (rho, l,r) -> Printf.fprintf oc "%a = %a" printEncExpnomode (rhomap, l) printEncExpnomode (rhomap, r)
  | rhomap, ELoc(rho, rho', l) ->Printf.fprintf oc "l%d" l
  | rhomap, EDeref(rho,e) -> Printf.fprintf oc "*%a" printEncExpnomode (rhomap, e)
  | rhomap, EIsunset(rho,x) -> Printf.fprintf oc "isunset(%s)" x

and printEncStmtwithmode oc  = function
  | rhomap, (EIf (rho,e,c1,c2)), isenc -> if isenc then
					Printf.fprintf oc "%d|- enclave( if %a then %a else %a )" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e) printEncStmtnomode (rhomap, c1) printEncStmtnomode (rhomap, c2)
					else
					Printf.fprintf oc "%d|- if %a then %a else %a" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e) printEncStmtnomode (rhomap, c1) printEncStmtnomode (rhomap, c2)
  | rhomap, (EAssign(rho, x, e)), isenc -> if isenc then
					Printf.fprintf oc "%d|-enclave( %s := %a ) " (ModeSAT.find rho rhomap) x printEncExpnomode (rhomap, e) 
					else
					Printf.fprintf oc "%d|- %s := %a " (ModeSAT.find rho rhomap) x printEncExpnomode (rhomap, e) 

  | rhomap, (ESeq(rho,s1, s2)), isenc ->if isenc then
					 Printf.fprintf oc "%d|-enclave( %a ; %a )" (ModeSAT.find rho rhomap) printEncStmtnomode (rhomap, s1) printEncStmtnomode (rhomap, s2)
					else
					  let rhonorm = (ModeSAT.find rho rhomap) in
					  let rhoprimeenc1 =  (ModeSAT.find (getstmtmode s1) rhomap) in
					  let rhoprimeenc2 =  (ModeSAT.find (getstmtmode s2) rhomap) in
					  if (rhonorm = 0)&& (rhoprimeenc1 = 1) then
					     Printf.fprintf oc "%d|-enclave( %a ) ; %a" (ModeSAT.find rho rhomap) printEncStmtnomode (rhomap, s1) printEncStmtnomode (rhomap, s2)
					  else 
					     if (rhonorm = 0)&& (rhoprimeenc2 = 1) then
					     Printf.fprintf oc "%d|- %a ; enclave( %a )" (ModeSAT.find rho rhomap) printEncStmtnomode (rhomap, s1) printEncStmtnomode (rhomap, s2)
					  else
					     Printf.fprintf oc "%d|- %a ; %a" (ModeSAT.find rho rhomap) printEncStmtnomode (rhomap, s1) printEncStmtnomode (rhomap, s2)

  | rhomap, (ECall(rho,e)), isenc    -> if isenc then
					Printf.fprintf oc "%d|- enclave( call(%a) )" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e) 
					else
					Printf.fprintf oc "%d|- call(%a)" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e) 
  | rhomap, (EUpdate(rho,e1, e2)), isenc -> if isenc then
					 Printf.fprintf oc "%d|- enclave( %a <- %a )" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e1) printEncExpnomode (rhomap, e2)
					 else
					 Printf.fprintf oc "%d|- %a <- %a" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e1) printEncExpnomode (rhomap, e2)
  | rhomap, (EWhile(rho, b, s)), isenc -> if isenc then
					  Printf.fprintf oc "%d|- enclave( while %a do %a )" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, b) printEncStmtnomode (rhomap, s)
					 else
					  Printf.fprintf oc "%d|- while %a do %a" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, b) printEncStmtnomode (rhomap, s)
  | rhomap, (ESkip (rho, rho')), isenc -> if isenc then
				   Printf.fprintf oc "%d|-enclave(skip)" (ModeSAT.find rho rhomap) 
				  else
				   Printf.fprintf oc "%d|- skip" (ModeSAT.find rho rhomap) 
  | rhomap, (EOutput(rho,ch, e)), isenc -> if isenc then
				  Printf.fprintf oc "%d|-enclave(output(_, %a) )" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e)
				  else
				  Printf.fprintf oc "%d|- output(_, %a)" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e)
  | rhomap, (ESet(rho,x)), isenc -> if isenc then
					Printf.fprintf oc "%d|-enclave( set(%s) )" (ModeSAT.find rho rhomap) x
				    else
					Printf.fprintf oc "%d|- set(%s)" (ModeSAT.find rho rhomap) x

and printEncExpwithmode oc  = function
  | rhomap, EVar(rho, v) -> Printf.fprintf oc "%d|- %s" (ModeSAT.find rho rhomap) v
  | rhomap, ELoc(rho, rho', l) ->Printf.fprintf oc "%d|- l%d^%d" (ModeSAT.find rho rhomap) l (ModeSAT.find rho' rhomap) 
  | rhomap, ELam(rho, rho', p, u, q, s) -> Printf.fprintf oc "%d|- lambda^(_,_).%a" (ModeSAT.find rho rhomap) printEncStmtnomode (rhomap, s)
  | rhomap, EPlus (rho, l,r) -> Printf.fprintf oc "%d|- %a + %a" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, l) printEncExpnomode (rhomap, r)
  | rhomap, EConstant(rho,n) -> Printf.fprintf oc "%d|- %d" (ModeSAT.find rho rhomap) n
  | rhomap, ETrue rho ->  Printf.fprintf oc "%d|- true" (ModeSAT.find rho rhomap) 
  | rhomap, EFalse rho  -> Printf.fprintf oc "%d|- false" (ModeSAT.find rho rhomap) 
  | rhomap, EEq (rho, l,r) -> Printf.fprintf oc "%d|- %a = %a" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, l) printEncExpnomode (rhomap, r)
  | rhomap, EDeref(rho,e) -> Printf.fprintf oc "%d|- *%a" (ModeSAT.find rho rhomap) printEncExpnomode (rhomap, e)
  | rhomap, EIsunset(rho,x) -> Printf.fprintf oc "%d|- isunset(%s)" (ModeSAT.find rho rhomap) x

