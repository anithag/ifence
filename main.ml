open Ast
open Eval
open Printf
open Helper
open Translate
open Util

exception MainError

let () =
  let _ =
    if (Array.length Sys.argv < 2) || (Array.length Sys.argv > 2) then
      (Format.printf "Usage: autopar <file>\n";
       exit 0) in
  let filearg = 1 in
  let file = open_in (Sys.argv.(filearg)) in
  let lexbuf = Lexing.from_channel file in
  let (gammasrc, stmt) =
    try Parser.pprogram Lexer.token lexbuf
    with Parsing.Parse_error ->
      let pos = lexbuf.Lexing.lex_curr_p in
      Format.printf "Syntax error at line %d\n" pos.Lexing.pos_lnum;
      exit 1 in

  let rho = next_tvar () in (* rho = Normal *)
  let alpha = next_kvar () in (* alpha = 0 *)
  let c0, c1, ms, gsrc, gammaenc, eidmap, eidrevmap, fcost, translation, klist = (Constraints.gen_constraints Low gammasrc rho alpha stmt VarLocMap.empty EnclaveidMap.empty EnclaveidRevMap.empty true) in
  let c0'' = Constr.add (Killcond (alpha, 0)) c0 in
  let c0' = Constr.add (Modecond (rho, Normal)) c0'' in
  let totalc = PPlus (fst fcost, snd fcost) in 

  let (eidmap', eidrevmap') = Helper.fill_eidrevmap ms eidmap eidrevmap in

  
  (* Add bij constraints to c1 *)
  (* bij =0 /\ bjk = 0 -> bik = 0 *)
  (* bij = 1 /\ bjk = 0 -> bik = 1 *)
  let c1' = Helper.add_bij_equiv_constraints eidmap' eidrevmap' c1 in

  let condconstr_num = Helper.countCondConstraints c1' in
  let _ = Pprint.printCost totalc ((Constr.cardinal c0') + condconstr_num) in
  let _ = Pprint.printConstraints c0' in
  let _ = Pprint.printCondConstraints c1' in
  
  let _ = Format.printf "Calling Solver \n" in
  (* Call Solver and get output *) 
  (* let out= (read_process "java -jar /Users/anithagollamudi/research/solvers/sat4j/sat4j-pb.jar min.opb" ) in  *)
  (* let out= (read_process "/Users/anithagollamudi/research/solvers/toysolver-master/dist/build/toysat/toysat --pb min.opb") in*)
  let out = (read_process "docker run -it --rm -v `pwd`:/data msakai/toysolver toysat --pb min.opb") in
   let _ = Printf.printf "%s" out in
  
  let model = Util.extractsatmodel out ms klist in
  let _ = Pprint.printEidMap eidmap in

  let eidset = fill_enclave_ids VarSet.empty in
  let (model_with_ids, _, _) =  assign_rho_ids ms model  eidset eidrevmap' in  

  (* print solution *)
  let oc = open_out "output.txt" in
  let _ = Translate.translate oc (model_with_ids, model, translation, (Mode (ModeVar((Helper.getrhovar rho),"dummy")))) in
  (*
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
   *)
   ()
