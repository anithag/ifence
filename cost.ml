open Ast

let rec commandcount (c:stmt) = match c with
 |Seq(c1, c2) -> 1
 |If(e, c1, c2) -> 1
 |While(e, c)  -> 1
 |Call e -> expcommandcount e
 | _ -> 1

and  expcommandcount (e:exp) = match e with
 |Lam(_,_,_,s) -> commandcount s
 |Deref e' -> expcommandcount e'
 | _  -> 0
 
let rec trustedcost (c:stmt) = match c with
 |Seq(c1, c2) -> trustedcost c1 + trustedcost c2
 (*|Enclave c' -> commandcount c' *)
 |If(e, c1, c2) -> trustedcost c1 + trustedcost c2
 |While(e, c')  -> trustedcost c'
 | _ ->  1

let compute_assign_trusted_cost (rho: mode) (rho':mode) =
			(* cost is rho' *)
		      (PMonoterm (1, (Mono rho'))) 


(* Entry given more cost than trusted code *)
let compute_seq_entry_cost (rho:mode) (rho': mode) (rho'' : mode) = 
	(* rho' + rho'' - rho rho' - rho rho'' -rho' rho'' + rho rho' rho'' *)
 let term1 =(PPlus (PMonoterm (2, (Mono rho')), PMonoterm (2, (Mono rho'')))) in
 let term2 = (PMinus (term1, (PMonoterm (2, (Poly (rho, (Mono rho'))))))) in
 let term3 = (PMinus (term2, (PMonoterm (2, (Poly (rho, (Mono rho''))))))) in
 let term4 = (PMinus (term3, (PMonoterm (2, (Poly (rho', (Mono rho''))))))) in
 (PPlus (term4, (PMonoterm (2, (Poly (rho, (Poly (rho', (Mono rho''))))))))) 
 
let compute_if_entry_cost (rho:mode) (rho':mode) (rho'':mode) (rho''':mode) = 
 let term1 =(PPlus (PMonoterm (2, (Mono rho'')), PMonoterm (2, (Mono rho''')))) in
 let term1' = (PMinus (term1, (PMonoterm (2, (Poly (rho'', (Mono rho'''))))))) in
 let term2 = (PMinus (term1', (PMonoterm (2, (Poly (rho', (Mono rho''))))))) in
 let term3 = (PMinus (term2,  (PMonoterm (2, (Poly (rho', (Mono rho'''))))))) in
 let term4 = (PPlus (term3, (PMonoterm (4, (Poly (rho', (Poly (rho'', Mono rho'''))))))))  in
 let term5 = (PMinus (term4, (PMonoterm (2, (Poly (rho, (Mono rho''))))))) in
 let term6 = (PMinus (term5, (PMonoterm (2, (Poly (rho, (Mono rho'''))))))) in
 let term7 = (PPlus (term6, (PMonoterm (2, (Poly (rho, (Poly (rho', (Mono rho''))))))))) in
 let term8 = (PPlus (term7, (PMonoterm (2, (Poly (rho, (Poly (rho'', (Mono rho'''))))))))) in
 let term9 = (PPlus (term8, (PMonoterm (2, (Poly (rho, (Poly (rho', (Mono rho'''))))))))) in
 (PMinus (term8, (PMonoterm (4, (Poly (rho, (Poly (rho', (Poly (rho'', (Mono rho'''))))))))))) 

let compute_assign_entry_cost (rho: mode) (rho':mode) =
 (PMinus (PMonoterm (2, Mono rho'), PMonoterm (2, (Poly (rho, Mono rho')))))

(*
(* Entry given equal weight to trusted code *)
let compute_seq_entry_cost (rho:mode) (rho': mode) (rho'' : mode) = 
	(* rho' + rho'' - rho rho' - rho rho'' -rho' rho'' + rho rho' rho'' *)
 let term1 =(PPlus (PMonoterm (1, (Mono rho')), PMonoterm (1, (Mono rho'')))) in
 let term2 = (PMinus (term1, (PMonoterm (1, (Poly (rho, (Mono rho'))))))) in
 let term3 = (PMinus (term2, (PMonoterm (1, (Poly (rho, (Mono rho''))))))) in
 let term4 = (PMinus (term3, (PMonoterm (1, (Poly (rho', (Mono rho''))))))) in
 (PPlus (term4, (PMonoterm (1, (Poly (rho, (Poly (rho', (Mono rho''))))))))) 
 
let compute_if_entry_cost (rho:mode) (rho':mode) (rho'':mode) (rho''':mode) = 
 let term1 =(PPlus (PMonoterm (1, (Mono rho'')), PMonoterm (1, (Mono rho''')))) in
 let term1' = (PMinus (term1, (PMonoterm (1, (Poly (rho'', (Mono rho'''))))))) in
 let term2 = (PMinus (term1', (PMonoterm (1, (Poly (rho', (Mono rho''))))))) in
 let term3 = (PMinus (term2,  (PMonoterm (1, (Poly (rho', (Mono rho'''))))))) in
 let term4 = (PPlus (term3, (PMonoterm (2, (Poly (rho', (Poly (rho'', Mono rho'''))))))))  in
 let term5 = (PMinus (term4, (PMonoterm (1, (Poly (rho, (Mono rho''))))))) in
 let term6 = (PMinus (term5, (PMonoterm (1, (Poly (rho, (Mono rho'''))))))) in
 let term7 = (PPlus (term6, (PMonoterm (1, (Poly (rho, (Poly (rho', (Mono rho''))))))))) in
 let term8 = (PPlus (term7, (PMonoterm (1, (Poly (rho, (Poly (rho'', (Mono rho'''))))))))) in
 let term9 = (PPlus (term8, (PMonoterm (1, (Poly (rho, (Poly (rho', (Mono rho'''))))))))) in
 (PMinus (term8, (PMonoterm (2, (Poly (rho, (Poly (rho', (Poly (rho'', (Mono rho'''))))))))))) 

let compute_assign_entry_cost (rho: mode) (rho':mode) =
 (PMinus (PMonoterm (1, Mono rho'), PMonoterm (1, (Poly (rho, Mono rho')))))
*)
