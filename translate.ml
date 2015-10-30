open Ast
open Printf
open Pprint

exception PrintError

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
  | ESkip m -> m
  | EOutput(m,ch, e) ->m
  | ESet(m,x)	-> m

let rec printEncExp oc (e,rhomap) = 
match e with
|EVar(rho, x) -> Printf.fprintf oc "%d |- x %a" (ModeSAT.find rho rhomap) printSpace 2
|ELoc(rho, rho', l) -> Printf.fprintf oc "%d |-l%d %a" (ModeSAT.find rho rhomap) l printSpace 2
|ELam(rho, rho',p,u,q,s) ->Printf.fprintf oc "%d |- lambda^%d(,).%a %a" (ModeSAT.find rho rhomap) (ModeSAT.find rho' rhomap) translate (s, rhomap, 2) printSpace 2 
|EPlus(rho, e1, e2) -> Printf.fprintf oc "%d |- %a + %a %a" (ModeSAT.find rho rhomap) printEncExp (e1, rhomap) printEncExp (e2, rhomap) printSpace 2
|EConstant(rho, n) -> Printf.fprintf oc "%d |- %d %a "(ModeSAT.find rho rhomap)  n printSpace 2
|_     ->Printf.fprintf oc "EOF"

and translate oc (s, rhomap, space) = 
match s with
 |ESkip rho -> printEncStmtwithmode oc (rhomap, s, false); printSpace oc 2
 |EAssign(rho, x, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			 printEncStmtwithmode oc (rhomap, s, insertenc); printSpace oc 2
 |EUpdate(rho, e1, e2) -> let rhoprimeenc = (ModeSAT.find (getexpmode e2) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			 printEncStmtwithmode oc (rhomap, s, insertenc); printSpace oc 2
 |EIf(rho, b, s1, s2) ->let rhoprimeenc = (ModeSAT.find (getexpmode b) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			 printEncStmtwithmode oc (rhomap, s, insertenc); printSpace oc 1; translate oc (s1, rhomap, space); translate oc (s2, rhomap, space)
 |ESeq(rho, s1, s2) -> let rhoprimeenc = (ModeSAT.find (getstmtmode s1) rhomap) in
			let rhodoubprimeenc = (ModeSAT.find (getstmtmode s2) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1)&&(rhodoubprimeenc = 1) then true else false in
			 printEncStmtwithmode oc (rhomap,s, insertenc); printSpace oc 1; translate oc (s1, rhomap, space); translate oc (s2, rhomap, space)
 |ECall(rho, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			 printEncStmtwithmode oc (rhomap, s, insertenc); printSpace oc 2
 |EWhile(rho,b,s1) -> let rhoprimeenc = (ModeSAT.find (getexpmode b) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			 printEncStmtwithmode oc (rhomap, s, insertenc); printSpace oc 1;translate oc (s1, rhomap, space)
 |EOutput(rho,ch, e) -> let rhoprimeenc = (ModeSAT.find (getexpmode e) rhomap) in
			let rhonorm = (ModeSAT.find rho rhomap) in  
			let insertenc = if  (rhonorm = 0)&&(rhoprimeenc = 1) then true else false in
			 printEncStmtwithmode oc (rhomap, s, insertenc); printSpace oc 2
 |ESet(rho,x)	-> printEncStmtwithmode oc (rhomap, s, false); printSpace oc 2
 |_  ->Printf.fprintf oc "EOF"

and printEncStmtnomode oc  = function
  | EIf (m,e,c1,c2) -> Printf.fprintf oc "if %a then %a else %a" printEncExpnomode e printEncStmtnomode c1 printEncStmtnomode c2
  | EAssign(m, x, e) -> Printf.fprintf oc "%s := %a " x printEncExpnomode e 
  | ESeq(m,s1, s2) -> Printf.fprintf oc "%a ; %a" printEncStmtnomode s1 printEncStmtnomode s2
  | ECall(m,e)    -> Printf.fprintf oc "call(%a)" printEncExpnomode e 
  | EUpdate(m,e1, e2) -> Printf.fprintf oc "%a <- %a" printEncExpnomode e1 printEncExpnomode e2
  | EWhile(m, b, s) -> Printf.fprintf oc "while %a do %a" printEncExpnomode b printEncStmtnomode s
  | ESkip m -> Printf.fprintf oc "skip"
  | EOutput(m,ch, e) -> Printf.fprintf oc "output(_, %a)" printEncExpnomode e
  | ESet(m,x)	-> Printf.fprintf oc "set(%s)" x

and printEncExpnomode oc  = function
  | EVar(rho, v) -> Printf.fprintf oc "%s" v
  | ELam(rho, rho', p, u, q, s) -> Printf.fprintf oc "lambda^(_,_).%a" printEncStmtnomode s
  | EPlus (rho, l,r) -> Printf.fprintf oc "%a + %a" printEncExpnomode l printEncExpnomode r
  | EConstant(rho,n) -> Printf.fprintf oc "%d" n
  | ETrue rho ->  Printf.fprintf oc "true"
  | EFalse rho  -> Printf.fprintf oc "false"
  | EEq (rho, l,r) -> Printf.fprintf oc "%a = %a" printEncExpnomode l printEncExpnomode r
  | ELoc(rho, rho', l) ->Printf.fprintf oc "l%d" l
  | EDeref(rho,e) -> Printf.fprintf oc "*%a" printEncExpnomode e
  | EIsunset(rho,x) -> Printf.fprintf oc "isunset(%s)" x

and printEncStmtwithmode oc  = function
  | rhomap, (EIf (rho,e,c1,c2)), isenc -> if isenc then
					Printf.fprintf oc "%d|- enclave( if %a then %a else %a )" (ModeSAT.find rho rhomap) printEncExpnomode e printEncStmtnomode c1 printEncStmtnomode c2
					else
					Printf.fprintf oc "%d|- if %a then %a else %a" (ModeSAT.find rho rhomap) printEncExpnomode e printEncStmtnomode c1 printEncStmtnomode c2
  | rhomap, (EAssign(rho, x, e)), isenc -> if isenc then
					Printf.fprintf oc "%d|-enclave( %s := %a ) " (ModeSAT.find rho rhomap) x printEncExpnomode e 
					else
					Printf.fprintf oc "%d|- %s := %a " (ModeSAT.find rho rhomap) x printEncExpnomode e 

  | rhomap, (ESeq(rho,s1, s2)), isenc ->if isenc then
					 Printf.fprintf oc "%d|-enclave( %a ; %a )" (ModeSAT.find rho rhomap) printEncStmtnomode s1 printEncStmtnomode s2
					else
					  let rhonorm = (ModeSAT.find rho rhomap) in
					  let rhoprimeenc1 =  (ModeSAT.find (getstmtmode s1) rhomap) in
					  let rhoprimeenc2 =  (ModeSAT.find (getstmtmode s2) rhomap) in
					  if (rhonorm = 0)&& (rhoprimeenc1 = 1) then
					     Printf.fprintf oc "%d|-enclave( %a ) ; %a" (ModeSAT.find rho rhomap) printEncStmtnomode s1 printEncStmtnomode s2
					  else 
					     if (rhonorm = 0)&& (rhoprimeenc2 = 1) then
					     Printf.fprintf oc "%d|- %a ; enclave( %a )" (ModeSAT.find rho rhomap) printEncStmtnomode s1 printEncStmtnomode s2
					  else
					     Printf.fprintf oc "%d|- %a ; %a" (ModeSAT.find rho rhomap) printEncStmtnomode s1 printEncStmtnomode s2

  | rhomap, (ECall(rho,e)), isenc    -> if isenc then
					Printf.fprintf oc "%d|- enclave( call(%a) )" (ModeSAT.find rho rhomap) printEncExpnomode e 
					else
					Printf.fprintf oc "%d|- call(%a)" (ModeSAT.find rho rhomap) printEncExpnomode e 
  | rhomap, (EUpdate(rho,e1, e2)), isenc -> if isenc then
					 Printf.fprintf oc "%d|- enclave( %a <- %a )" (ModeSAT.find rho rhomap) printEncExpnomode e1 printEncExpnomode e2
					 else
					 Printf.fprintf oc "%d|- %a <- %a" (ModeSAT.find rho rhomap) printEncExpnomode e1 printEncExpnomode e2
  | rhomap, (EWhile(rho, b, s)), isenc -> if isenc then
					  Printf.fprintf oc "%d|- enclave( while %a do %a )" (ModeSAT.find rho rhomap) printEncExpnomode b printEncStmtnomode s
					 else
					  Printf.fprintf oc "%d|- while %a do %a" (ModeSAT.find rho rhomap) printEncExpnomode b printEncStmtnomode s
  | rhomap, (ESkip rho), isenc -> if isenc then
				   Printf.fprintf oc "%d|-enclave(skip)" (ModeSAT.find rho rhomap) 
				  else
				   Printf.fprintf oc "%d|- skip" (ModeSAT.find rho rhomap) 
  | rhomap, (EOutput(rho,ch, e)), isenc -> if isenc then
				  Printf.fprintf oc "%d|-enclave(output(_, %a) )" (ModeSAT.find rho rhomap) printEncExpnomode e
				  else
				  Printf.fprintf oc "%d|- output(_, %a)" (ModeSAT.find rho rhomap) printEncExpnomode e
  | rhomap, (ESet(rho,x)), isenc -> if isenc then
					Printf.fprintf oc "%d|-enclave( set(%s) )" (ModeSAT.find rho rhomap) x
				    else
					Printf.fprintf oc "%d|- set(%s)" (ModeSAT.find rho rhomap) x

and printEncExpwithmode oc  = function
  | rhomap, EVar(rho, v) -> Printf.fprintf oc "%d|- %s" (ModeSAT.find rho rhomap) v
  | rhomap, ELam(rho, rho', p, u, q, s) -> Printf.fprintf oc "%d|- lambda^(_,_).%a" (ModeSAT.find rho rhomap) printEncStmtnomode s
  | rhomap, EPlus (rho, l,r) -> Printf.fprintf oc "%d|- %a + %a" (ModeSAT.find rho rhomap) printEncExpnomode l printEncExpnomode r
  | rhomap, EConstant(rho,n) -> Printf.fprintf oc "%d|- %d" (ModeSAT.find rho rhomap) n
  | rhomap, ETrue rho ->  Printf.fprintf oc "%d|- true" (ModeSAT.find rho rhomap) 
  | rhomap, EFalse rho  -> Printf.fprintf oc "%d|- false" (ModeSAT.find rho rhomap) 
  | rhomap, EEq (rho, l,r) -> Printf.fprintf oc "%d|- %a = %a" (ModeSAT.find rho rhomap) printEncExpnomode l printEncExpnomode r
  | rhomap, ELoc(rho, rho', l) ->Printf.fprintf oc "%d|- l%d" (ModeSAT.find rho rhomap) l
  | rhomap, EDeref(rho,e) -> Printf.fprintf oc "%d|- *%a" (ModeSAT.find rho rhomap) printEncExpnomode e
  | rhomap, EIsunset(rho,x) -> Printf.fprintf oc "%d|- isunset(%s)" (ModeSAT.find rho rhomap) x

