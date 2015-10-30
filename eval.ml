open Ast

exception IllformedExpression 
exception BadProgram

let error s = (print_string ("Error: "^ s); raise BadProgram)
(* large-step evaluation function *)
let rec eval_stmt (ev:env) (s:stmt) : env = 
  match s with 
    | If(e1,s2,s3) ->       
      begin match (eval_exp ev e1) with
        | VBool r  -> begin match r with
			| true -> eval_stmt ev s2
			| false -> eval_stmt ev s3
		      end 
        | _ -> raise IllformedExpression
	end
    | Assign(x, e1) ->  
		let value = (eval_exp ev e1) in 
		             (VarLocMap.add (Reg x) value ev)      
    | Update(e1, e2) -> let loc = (eval_exp ev e1) in
			let v = (eval_exp ev e2) in
				begin match loc with
			     	| VLoc l -> (VarLocMap.add (Mem l) v ev)
				| _ -> raise IllformedExpression
				end
    | Seq(s1, s2) -> (eval_stmt (eval_stmt ev s1) s2)
    | While(e, s1)-> eval_stmt ev (If(e, Seq(s1, s), Skip)) 
    | Set(x) -> eval_stmt ev (Assign(x, (Constant 1)))
    | Output(c, e) -> ev
    | Call(e) -> let f = (eval_exp ev e) in 
			begin match f with
			| VFun s1 -> (eval_stmt ev s1)
			| _ -> raise IllformedExpression
			end
    | _ -> VarLocMap.empty

and eval_exp (ev:env) (e:exp) : value = 
  match e with 
    | Var x -> 
      (try VarLocMap.find (Reg x) ev
       with Not_found -> raise IllformedExpression) 
    | Loc l -> VLoc l
    | Constant n -> 
      VInt n
    | True -> 
      VBool true 
    | False -> 
      VBool false
    | Lam(_,_,_,s) ->
      VFun(s)
    | Plus(e1,e2) ->  
      eval_arith ev ( + ) e1 e2
    | Eq(e1,e2) ->
      (match eval_exp ev e1 with
        | VInt n1 -> 
          (match eval_exp ev e2 with
            | VInt n2 -> 
              if n1 = n2 then VBool(true) else VBool(false)
            | _ -> 
              raise IllformedExpression)
        | _ -> 
          raise IllformedExpression)
  | Deref(e1) -> let loc = (eval_exp ev e1) in 
				begin match loc with
				|VLoc l -> (try VarLocMap.find (Mem l) ev
					with Not_found -> raise IllformedExpression)
				| _ -> raise IllformedExpression
				end
  | Isunset(x) -> let b = (try VarLocMap.find (Reg x) ev 
				with Not_found -> raise IllformedExpression) in
			begin match b with
			 VInt v ->
			 (if v <> 0 then (VBool true) else (VBool false))
			|_ -> raise IllformedExpression
			end
and
eval_arith ev op e1 e2 : value = 
      (match eval_exp ev e1 with
        | VInt n1 -> 
          (match eval_exp ev e2 with
            | VInt n2 -> 
              VInt (op n1 n2)
            | _ -> 
              raise IllformedExpression)
        | _ -> 
          raise IllformedExpression)

