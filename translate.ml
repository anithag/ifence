open Ast
open Printf
open Pprint
open Helper

exception PrintError
exception TranslationError of string

let rec translate oc (model_with_ids, model, encstmt) = match encstmt with
 |EESeq (ModeVar(rho, _), estmtlist) ->let rhoisenclave = ModeSAT.find (Mode (ModeVar(rho, "dummy")))  model in 
			   let rec dispatch listtoprint estmtlist = begin match estmtlist with
				|[] -> let _ = if List.length listtoprint = 0 then () 
					       else if (rhoisenclave=1) then
							(* already part of enclave *)
							Printf.fprintf oc " %a " printeprog (model_with_ids, model, listtoprint) 
						else
							Printf.fprintf oc "enclave (\n %a \n )" printeprog (model_with_ids, model, listtoprint) 
					in ()
				|est::tail -> begin match est with 
   					|EIf (rho', e, s1, s2)-> let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
  					|ESkip(rho', rho'')->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
  					|EAssign (rho',v,e) ->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
  					|EUpdate (rho', e1, e2)->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc 
								 in dispatch list' tail
  					|ESeq  (rho', s1, s2) ->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
  					|EESeq  (rho', es) ->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
  					|EWhile  (rho', e, es) ->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
  					|EOutput (rho', ch, e) ->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
  					|ECall  (rho', e) ->let list' = helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
					|ESet  (rho', v) ->  let list' =helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc
								 in dispatch list' tail
				end
			end
			in dispatch [] estmtlist
 | _ -> raise (TranslationError "Translated program should be a list of statements")


and helperfunc rhoisenclave rho' model_with_ids model listtoprint est oc =
		let rho' = begin match rho' with
			   |ModeVar(rho'var, _ ) -> ModeVar(rho'var, "dummy")
			   | _ -> raise (TranslationError "Improper mode assignment")
			   end in
 		let rho'isenclave = ModeSAT.find (Mode rho')  model in 
		let  listtoprint' = if (rhoisenclave = 0) && (rho'isenclave=1) then 
					listtoprint @ [est]
		     		    else if (rhoisenclave=1) && (rho'isenclave=1) then
					listtoprint @ [est]
		     		    else if (rhoisenclave=0) && (rho'isenclave=1) then
					let _ = if List.length listtoprint = 0 then () else
						Printf.fprintf oc "enclave (\n %a \n )" printeprog (model_with_ids, model, listtoprint) in
					let _ = Printf.fprintf oc " %a \n " printestmt (model_with_ids, model, est) in
						[]	
		     		   else raise (TranslationError "Incorrect mode assignment")
		in listtoprint'


and  printeprog oc (model_with_ids, model, listtoprint) = match listtoprint with
 |[] -> ()
 |xs::tail -> let _ = printestmt oc (model_with_ids, model, xs ) in
 	      printeprog oc (model_with_ids, model, tail)

 and printestmt oc (model_with_ids, model, encstmt) = match encstmt with 
	|EIf (rho', e, s1, s2)-> Printf.fprintf oc "if %a then \n %a \n else %a \n" printeexp (model_with_ids, model, e) translate (model_with_ids, model, s1)  translate (model_with_ids, model, s2)  
  	|ESkip(rho', rho'')-> Printf.fprintf oc "skip \n "
  	|EAssign (rho',v,e)-> Printf.fprintf oc "%s := %a \n" v  printeexp (model_with_ids, model, e)
  	|EUpdate (rho', e1, e2)-> Printf.fprintf oc "%a <- %a \n" printeexp (model_with_ids, model, e1)  printeexp (model_with_ids, model, e2)
  	|ESeq  (rho', s1, s2) -> Printf.fprintf oc "%a ; %a " translate (model_with_ids, model, s1)  translate (model_with_ids, model, s2)  
  	|EESeq  (rho', es) -> raise (TranslationError "Improper statement to print")
  	|EWhile  (rho', e, es) ->Printf.fprintf oc "while ( %a ) %a " printeexp (model_with_ids, model, e) translate (model_with_ids, model, es)
  	|EOutput (rho', ch, e)->Printf.fprintf oc "output(_, %a) \n" printeexp (model_with_ids, model, e)
  	|ECall  (rho', e) ->Printf.fprintf oc "call(%a) \n" printeexp (model_with_ids, model, e)
  	|ESet  (rho', v) ->Printf.fprintf oc "set(%s) \n" v

and printeexp oc  (model_with_ids, model, e) = match e with
  | EVar(rho, v) -> Printf.fprintf oc "%s" v
  | ELam(rho, ModeVar(rho', _), pre, p, u, q, post, s) -> Printf.fprintf oc "(lambda^%d(_,_,_).%a)" (ModeSAT.find (Mode (ModeVar(rho', "dummy"))) model) translate (model_with_ids, model, s)  
  | EPlus (rho, l,r) -> Printf.fprintf oc "%a + %a" printeexp (model_with_ids, model, l) printeexp (model_with_ids, model, r)
  | EConstant(rho,n) -> Printf.fprintf oc "%d" n
  | ETrue rho ->  Printf.fprintf oc "true"
  | EFalse rho  -> Printf.fprintf oc "false"
  | EEq (rho, l,r) -> Printf.fprintf oc "%a == %a" printeexp (model_with_ids, model, l) printeexp (model_with_ids, model, r)
  | ELoc(rho, rho', l) ->Printf.fprintf oc "l%d" l
  | EDeref(rho,e) -> Printf.fprintf oc "*%a" printeexp (model_with_ids, model, e)
  | EIsunset(rho,x) -> Printf.fprintf oc "isunset(%s)" x
