open Ast
open Eval
open Printf
open Helper
open Translate
open Util

exception MainError

let () =
  let _ =
    if (Array.length Sys.argv < 2) || (Array.length Sys.argv > 3) then
      (Format.printf "Usage: lam [-letpoly] <file>\n";
       exit 0) in
  let (letpoly,filearg) =
    if Array.length Sys.argv = 3
    then if Sys.argv.(1) = "-letpoly"
        then (true,2)
        else (Format.printf "Usage: lam [-letpoly] <file>\n"; exit 0)
    else (false,1) in
  let file = open_in (Sys.argv.(filearg)) in
  let lexbuf = Lexing.from_channel file in
  let (gammasrc, stmt) =
    try Parser.program Lexer.token lexbuf
    with Parsing.Parse_error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Format.printf "Syntax error at line %d\n" pos.Lexing.pos_lnum;
      exit 1 in

  let _ =
    Format.printf "@[";
    Format.printf "Gammasrc:@\n  @[";
    Pprint.printMap gammasrc; 
    Format.printf "@]@\n@\n" in

  let _ =
    Format.printf "@[";
    Format.printf "Program:@\n  @[";
    Pprint.printStmt stmt ;
    Format.printf "@]@\n@\n" in
 
  
  
  let rho = next_tvar () in (* rho = Normal *)
  let c0, c1, m,ms, gammaenc, fcost, translation = (Constraints.gen_constraints gammasrc rho stmt VarLocMap.empty) in
  let c0' = Constr.add (rho, Normal) c0 in

(*
  let _ =
    Format.printf "@[";
    Format.printf "Gammaenc:@\n  @[";
    Pprint.printEncMap gammaenc; 
    Format.printf "@]@\n@\n" in

  let _ =
    Format.printf "@[";
    Format.printf "Translation:@\n  @[";
    Pprint.printEncStmt translation ;
    Format.printf "@]@\n@\n" in
 

  let _ =
    Format.printf "Constraints:@\n  @[";
    let _ =
      Constr.fold
        (fun (p1,p2) b ->
          if b then Format.printf "@\n";
          Pprint.printMode p1;
          Format.printf "@ =@ ";
          Pprint.printMode p2;
          true)
        c0' true in
    Format.printf "@]@\n@\n" in

  let _ =
    Format.printf "Conditional Constraints:@\n  @[";
    let _ =
      Constr2.fold
        (fun ((p1, p2), p3) b ->
          if b then Format.printf "@\n";
          Pprint.printMode p1;
          Format.printf "@ =@ ";
          Pprint.printMode p2;
          Format.printf "@ ->@ ";
	  Pprint.printList p3;
          true)
        c1 true in
    Format.printf "@]@\n@\n" in
  let _ =
    Format.printf "Mode Mappings to Program Statements and Expressions :@\n  @[";
    let _ =
      ModeProgSet.fold
        (fun (p1,p2) b ->
          if b then Format.printf "@\n";
          Pprint.printMode p1;
          Format.printf "@ |- @ ";
          Pprint.printProg p2;
          true)
        m true in
    Format.printf "@]@\n@\n" in

  let s = Constraints.unify c0' in
  let s', tmp = Constraints.cond_unify c0' c1 (Constr2.empty) c0' s in
  
  let _ =
    Format.printf "Unification Result:@\n  @["; 
    let _ =
      ModeSet.fold
        (fun rho b ->
          if b then Format.printf "@\n";
          Pprint.printMode rho;
          Format.printf "@ : @ ";
    	  Pprint.printMode (Helper.apply_subst s' rho);
          true)
        ms true in
    Format.printf "@]@\n@\n" in

  let _ =
    Format.printf "Remaining Conditional Constraints:@\n  @[";
    let _ =
      Constr2.fold
        (fun ((p1, p2), p3) b ->
          if b then Format.printf "@\n";
          Pprint.printMode p1;
          Format.printf "@ =@ ";
          Pprint.printMode p2;
          Format.printf "@ ->@ ";
	  Pprint.printList p3;
          true)
        tmp true in
    Format.printf "@]@\n@\n" in

 *)
  (* let v = Eval.eval_stmt VarLocMap.empty stmt in *)
  let totalc = PPlus (fst fcost, snd fcost) in 
  let condconstr_num = Helper.countCondConstraints c1 in
  let _ = Pprint.printCost totalc ((Constr.cardinal c0') + condconstr_num) in
  let _ = Pprint.printConstraints c0' in
  let _ = Pprint.printCondConstraints c1 in
  
  (* Call Solver and get output *) 
  let out= (read_process "java -jar /Users/anithagollamudi/research/solvers/sat4j/sat4j-pb.jar min.opb" ) in 
   let _ = Printf.printf "%s" out in
  
  let model = extractsatmodel out in

  (* print solution *)
  let oc = open_out "output.txt" in
  let _ = Translate.prettytranslate oc (translation, model) in
  let elset = Translate.collectlam ELamSet.empty translation in 
  let locset = Translate.collectloc ELocSet.empty gammaenc in
  let _ = Printf.fprintf oc "\n \n \n \t LOCATIONS \n \t============= \n" in
  let _ = ELocSet.fold (fun e  b -> (if b then
			match e with
			|(locexp, typ) -> begin match locexp with
					 | Reg v -> Printf.fprintf oc "%s: %a\n" v Pprint.printEncTypChannel (typ, model)
					 | Mem loc -> Printf.fprintf oc "l%d: %a\n" loc Pprint.printEncTypChannel (typ, model)
					 end
			|_ -> raise MainError
			);true) locset true in
  let _ = ELamSet.fold (fun e b -> (if b then
			match e with
			|ELam (rho, rho', p, u, q, s) -> 
					Printf.fprintf oc "\n \n \n \t FUNCTION \n \t =========\n lambda^%d(_,_).\n %a" (ModeSAT.find rho' model) Translate.prettytranslate (s, model)
			|_ -> raise MainError
			);true) elset true in
   ()
