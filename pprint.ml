open Ast
open Format

let printMode' ppf = function
  | Enclave -> printf "Enclave"
  | Normal  -> printf  "Normal"
  | ModeVar x -> printf "%s" x

let printLabel' ppf = function
  | Low -> printf "l"
  | High -> printf "h"
  | Erase(l, c, h) -> printf "@[l ->%s@  h@]" c

let ident v = printf "%s" v
let printBop op p l r = printf "@[(%a@ %s@ %a)@]" p l op p r
let printLam p e = printf "@[<2>lambda.@ (%a)@]" p e
let printIf p e ps c a = printf "@[if@ %a@ then  %a@ else  %a@  fi@]" p e ps c ps a
let printAssign x p e = printf "@[%s:=@ %a @]" x p e
let printSeq  p s1 s2 = printf "@[%a;@  %a @]"  p s1 p s2
let printCall p e     = printf "@[call(%a)@]" p e
let printUpdate p e1 e2 = printf "@[%a@ <-@ %a@]" p e1 p e2   
let printWhile pb b ps s = printf "@[while@ %a@ do@ %a end@]" pb b ps s 
let printOutput ch pe e = printf "@[output(@ %c, @ %a) @]" ch pe e 
let printSet x  = printf "@[set(%s) @]" x
(* Enclave Statements *)
let printEncLam rho p u q pr s = printf "@[lambda^%a(%a, _).(%a)_%a@]" printMode' rho printLabel'  p pr s  printLabel' q
let printEIf m p e ps c a = printf "@[%a |- if@ %a@ then  %a@ else  %a@  fi@]" printMode' m p e ps c ps a
let printEAssign m x p e = printf "@[ %a |-  %s:=@ %a @]" printMode' m x p e
let printESeq m p s1 s2 = printf "@[ %a  |- %a;@  %a @]"  printMode' m p s1 p s2
let printECall m p e     = printf "@[%a  |- call(%a)@]" printMode' m p e
let printEUpdate m p e1 e2 = printf "@[ %a |- %a@ <-@ %a@]" printMode' m p e1 p e2   
let printEWhile m  pb b ps s = printf "@[%a|- while@ %a@ do@ %a end@]" printMode' m pb b ps s 
let printEOutput m ch pe e = printf "@[ %a |- output(@ %c, @ %a) @]" printMode' m ch pe e 
let printESet m x  = printf "@[ %a |- set(%s) @]" printMode' m x
let printESkip m = printf "@[ %a |- skip @]" printMode' m

 
let rec printStmt' ppf  = function
  | If (e,c,a) -> printIf printExp' e printStmt' c a
  | Assign(x, e) -> printAssign x printExp' e
  | Seq(s1, s2) -> printSeq printStmt' s1 s2
  | Call(e)    -> printCall printExp' e
  | Update(e1, e2) -> printUpdate printExp' e1 e2
  | While(b, s) -> printWhile printExp' b printStmt' s
  | Skip  -> printf "skip"
  | Output(ch, e) -> printOutput ch printExp' e
  | Set x	-> printSet x

and printExp' ppf = function
  | Var v -> ident v
  | Lam (_,_,_,s) -> printLam printStmt' s
  | Plus (l,r) -> printBop "+" printExp' l r
  | Constant n -> printf "%d" n
  | True -> ident "true"
  | False -> ident "false"
  | Eq (l,r) -> printBop "==" printExp' l r
  | Loc l  -> printf "l%d" l
  | Deref e -> printf "*%a" printExp' e
  | Isunset x -> printf "isunset(%s)" x

and printEncStmt' ppf  = function
  | EIf (m,e,c,a) -> printEIf m printEncExp' e printEncStmt' c a
  | EAssign(m, x, e) -> printEAssign m x printEncExp' e
  | ESeq(m,s1, s2) -> printESeq m printEncStmt' s1 s2
  | ECall(m,e)    -> printECall m printEncExp' e
  | EUpdate(m,e1, e2) -> printEUpdate m printEncExp' e1 e2
  | EWhile(m, b, s) -> printEWhile m printEncExp' b printEncStmt' s
  | ESkip (m, m') -> printESkip m'
  | EOutput(m,ch, e) -> printEOutput m ch printEncExp' e
  | ESet(m,x)	-> printESet m x
  | EESeq(m, eslist) -> ()

and printEncExp' ppf = function
  | EVar(rho, v) -> ident v
  | ELam(rho, rho', p, u, q, s) -> printEncLam rho' p u q  printEncStmt' s
  | EPlus (rho, l,r) -> printBop "+" printEncExp' l r
  | EConstant(rho,n) -> printf "%d" n
  | ETrue rho -> ident "true"
  | EFalse rho  -> ident "false"
  | EEq (rho, l,r) -> printBop "==" printEncExp' l r
  | ELoc(rho, rho', l) -> printf "@[l%d^%a @]" l printMode' rho'
  | EDeref(rho,e) -> printf "*%a" printEncExp' e
  | EIsunset(rho,x) -> printf "isunset(%s)" x

and printList' ppf = function  
  [] -> printf "@[\n@]"
  |(a,b)::t -> printf "@[(%a = %a), %a@]" printMode' a printMode' b printList' t

and printuset' ppf u = VarSet.iter print_reg  u

and print_reg x = printf "@[%s @]" x 
 
and printTyp' ppf lt  = match lt with
  | (b, l) -> begin match b with
	  		| BtInt -> printf "@[(int)_%a @]" printLabel' l 
 			| BtBool -> printf "@[(bool)_%a @]" printLabel' l
			| BtCond -> printf "@[(cond)_%a @]" printLabel' l
			| BtRef lt -> printf "@[(%a ref)_%a @]" printTyp' lt printLabel' l
			| BtFunc(p, u)-> printf "@[func(%a, { %a })_%a @]" printLabel' p printuset' u printLabel' l
			end
  | _ -> raise Not_found

and printEncTyp' ppf lt  = match lt with
  | (b, l) -> begin match b with
	  		| EBtInt -> printf "@[(int)_%a @]" printLabel' l 
 			| EBtBool -> printf "@[(bool)_%a @]" printLabel' l
			| EBtCond -> printf "@[(cond)_%a @]" printLabel' l
			| EBtRef(m,lt) -> printf "@[(%a ref^%a)_%a @]" printEncTyp' lt printMode' m printLabel' l
			| EBtFunc(m, p, u)-> printf "@[func^%a@ (%a, { %a })_%a@]" printMode' m printLabel' p printuset' u printLabel' l
			end
  | _ -> raise Not_found

and printVal' ppf = function
  | VInt(n) -> printf "%d" n
  | VBool(b) -> printf "%b" b
  | VFun(s) -> printf "@[%sclosure%s@]" "<" ">"

and printMap' ppf m = VarLocMap.iter print_keyval m
and printEncMap' ppf m = VarLocMap.iter print_enckeyval m

and printVarLoc' ppf = function
  | Reg x -> printf "(%s)" x
  | Mem l -> printf  "(l%d)" l

and print_keyval key value = printf "@[%a : %a @]" printVarLoc' key printTyp' value
and print_enckeyval key value = printf "@[%a : %a @]" printVarLoc' key printEncTyp' value

let printStmt s = 
  printStmt' Format.std_formatter s

let printExp e = 
  printExp' Format.std_formatter e

let printEncStmt es = 
  printEncStmt' Format.std_formatter es

let printEncExp ee = 
  printEncExp' Format.std_formatter ee

let printProg p =
  match p with
  | Exp e -> printExp e
  | Stmt s -> printStmt s
  | EncExp e ->printEncExp e
 
let printLabel l =
  printLabel' Format.std_formatter l
 
let printTyp t =
  printTyp' Format.std_formatter t
 
let printMode p =
  printMode' Format.std_formatter p
 
let printList p =
  printList' Format.std_formatter p

let printVal v = 
  printVal' Format.std_formatter v

let printVarLoc v =
  printVarLoc' Format.std_formatter v

let printMap m =
  printMap' Format.std_formatter m

let printEncMap m =
  printEncMap' Format.std_formatter m

let rec printPolyterm chan p = match p with
 | Mono rho -> begin match rho with
		|ModeVar x -> Printf.fprintf chan "%s" x
		| _        -> raise Not_found
		end
 | Poly(rho, p') -> begin match rho with
		| ModeVar x -> Printf.fprintf chan "%s %a" x printPolyterm p'
		| _	  -> raise Not_found
		end

let rec printPolynomial chan fcost = 
      begin match fcost with
      | PConstant n -> Printf.fprintf chan "%d" n 
      | PMonoterm(n, p)  -> Printf.fprintf chan "%d %a" n printPolyterm p 
      | PPlus(p1, p2) -> Printf.fprintf chan "%a +%a" printPolynomial p1 printPolynomial p2
      | PMinus(p1, p2) -> Printf.fprintf chan "%a -%a" printPolynomial p1 printPolynomial p2
      | _ -> Printf.fprintf chan "\t" 	
      end

(* Print in OPB format *)
let printCost fcost max_constraints =
  let oc = open_out "min.opb" in
  let max_var = !(Helper.tvar_cell) - 1  in
     Printf.fprintf oc "* #variable= %d #constraint= %d\n" max_var max_constraints;
     Printf.fprintf oc "min: %a; \n" printPolynomial fcost;
      close_out oc

(* Print single constraint *)
let printConstraint oc c =
 begin match c with
 |(ModeVar x, Enclave) -> Printf.fprintf oc "+1 %s = 1;\n" x
 |(ModeVar x, Normal) -> Printf.fprintf oc "+1 %s = 0;\n" x
 |(ModeVar x, ModeVar y)-> Printf.fprintf oc "+1 %s -1 %s= 0;\n" x y
 end

let printConstraints (c:constr) =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "min.opb" in
  let _  = Constr.iter (printConstraint oc) c in
  close_out oc

(* Print single conditional constraint *)
let printSingleCondConstraint oc (a, b) =
 match a with
|(Enclave, ModeVar x)
|(ModeVar x, Enclave) -> begin match b with
			|(ModeVar y, Enclave) (* Constraint of form x = Enclave -> y = Enclave is converted to 1 -x + y >= 1 *)
			|(Enclave, ModeVar y) -> Printf.fprintf oc "-1 %s +1 %s >= 0;\n" x y

			|(ModeVar y, Normal)(* Constraint of form x = Enclave -> y = Normal is converted to 1 -x - y >= 1 *)
			|(Normal, ModeVar y) -> Printf.fprintf oc "-1 %s -1 %s >= 0;\n" x y
			
			| _    -> raise Not_found (* We don't have constraints of this form *)
			end
|(Normal, ModeVar x)
|(ModeVar x, Normal) -> begin match b with
			|(ModeVar y, Enclave) (* Constraint of form x = Normal -> y = Enclave is converted to 1 +x + y >= 1 *)
			|(Enclave, ModeVar y) -> Printf.fprintf oc "+1 %s +1 %s >= 0;\n" x y

			|(ModeVar y, Normal)(* Constraint of form x = Normal -> y = Normal is converted to 1 +x - y >= 1 *)
			|(Normal, ModeVar y) -> Printf.fprintf oc "+1 %s -1 %s >= 0;\n" x y
			
			| _    -> raise Not_found (* We don't have constraints of this form *)
			end
|(ModeVar x, ModeVar y) -> raise Not_found (* We don't have constraints of this form *)

let printusetchannel oc u = let _ = VarSet.fold (fun el oc -> Printf.fprintf oc "%s, " el; oc )  u oc in ()


let printLabelChannel oc = function
  | Low -> Printf.fprintf oc "l"
  | High ->Printf.fprintf oc "h"
  | Erase(l, c, h) -> Printf.fprintf oc  "l ->%s  h]" c

let rec printEncTypChannel oc (lt, rhomap)  = match lt with
  | (b, l) -> begin match b with
	  		| EBtInt -> Printf.fprintf oc "(int)_%a " printLabelChannel l 
 			| EBtBool -> Printf.fprintf oc "(bool)_%a " printLabelChannel l
			| EBtCond -> Printf.fprintf oc "(cond)_%a " printLabelChannel l
			| EBtRef(m,lt') -> Printf.fprintf oc "(%a ref^%d)_%a " printEncTypChannel (lt', rhomap) (ModeSAT.find  m rhomap) printLabelChannel l
			| EBtFunc(m, p, u)-> Printf.fprintf oc "func^%d@ (%a, { %a })_%a" (ModeSAT.find m rhomap) printLabelChannel p printusetchannel u printLabelChannel l
			end
  | _ -> raise Not_found

let printCondConstraint oc c =
 let l = (snd c) in
 let rec toyprint li  = 
	   begin match li with
	       |[] -> ()
	       |h::tail -> let _ = printSingleCondConstraint oc (fst c, h) in
			    toyprint tail
	   end in
   toyprint l


let printCondConstraints (c:constr2) =
  let oc = open_out_gen [Open_creat; Open_text; Open_append] 0o640 "min.opb" in
  let _  = Constr2.iter (printCondConstraint oc) c in
  close_out oc
