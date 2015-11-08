(* variables *)
type var = string
type channel = char
type mode = Enclave | Normal | ModeVar of var

module VarSet = Set.Make(struct
  type t = var
  let compare = Pervasives.compare
end)

(* sets of condition variables *)
type cndset = VarSet.t

(* Base types *)
type basetype = 
    BtInt                             (* int *)
  | BtBool                            (* bool *)
  | BtCond                            (* cond *)
  | BtRef of labeltype		     (* tau ref *)
  | BtFunc of policy * cndset	     (* func *)

and
labeltype = basetype * policy   

and policy =
    Low
   |High
   |Erase of policy * var * policy
 

(* expressions *)
and exp =
    Var of var                      (* x *)
  | Loc of int
  | Lam of policy * cndset * policy * stmt   (* (lambda(p, {}).stmt)_q *)
  | Constant of int                      (* n *)
  | Plus of exp * exp               (* e1 + e2 *)
  | True                            (* true *)
  | False                           (* false *)
  | Eq of exp * exp                 (* e1 = e2 *) 
  | Deref of exp
  | Isunset of var
  
and
stmt = 
   If of exp * stmt * stmt           (* if e1 then e2 else e3 *)
  | Skip
  | Assign of var * exp
  | Update of exp * exp
  | Seq of stmt * stmt
  | While of  exp * stmt
  | Output of channel * exp
  | Call of exp
  | Set of var

(* values *)
type value = 
    VInt of int 
  | VBool of bool 
  | VFun of stmt 
  | VLoc of int 

type encexp =
    EVar of mode * var                       (* mode |- x *)
  | ELoc of mode * mode * int		     (* mode |- l^ mode *)
  | ELam of mode * mode * policy* cndset*policy* encstmt (* First mode|-lambda^mode(p,u)_q *)
  | EConstant of mode * int                  (* n *)
  | EPlus of mode * encexp * encexp          (* e1 + e2 *)
  | ETrue of mode                            (* true *)
  | EFalse of mode                           (* false *)
  | EEq of mode * encexp * encexp            (* e1 = e2 *) 
  | EDeref of mode * encexp
  | EIsunset of mode * var

(* Translation data structure. Each Statement has an associated mode in which it executes *)
and  encstmt = 
   EIf of mode*encexp * encstmt * encstmt           (* if e1 then e2 else e3 *)
  |ESkip of mode * mode
  |EAssign of mode * var * encexp
  |EUpdate of mode * encexp * encexp
  |ESeq of mode * encstmt * encstmt
  |EWhile of mode * encexp * encstmt
  |EOutput of mode* channel * encexp
  |ECall of mode * encexp
  |ESet of mode * var

type progbody = Exp of exp | Stmt of stmt | EncExp of encexp

(* sets of pairs of types *)
module Constr = Set.Make(struct
  type t = mode * mode
  let compare = Pervasives.compare
end)

type pre_cond =  mode * mode
type post_cond= (mode * mode) list

module Constr2 = Set.Make(struct
  type t = pre_cond * post_cond
  let compare = Pervasives.compare
end)


type varloc = Reg of var | Mem of int 

(* maps with variables and locations as keys *)
module VarLocMap = Map.Make(struct
  type t = varloc
  let compare = Pervasives.compare
end)

(* evaluation environments *)
type env = value VarLocMap.t


(* constraints *)
type constr = Constr.t

(* Conditional constrains *)
type constr2 = Constr2.t

(* maps with mode variables as keys *)
module ModeVarMap = Map.Make(struct
  type t = var
  let compare = Pervasives.compare
end)

(* mode substitutions *)
type subst = mode ModeVarMap.t

(* typechecking environments - maps variables to types *)
type context = labeltype VarLocMap.t

type program = context * stmt 

(* maps with mode variables as keys *)
module ModeProgSet = Set.Make(struct
  type t = mode * progbody 
  let compare = Pervasives.compare
end)

(* evaluation environments *)
type modeenv = ModeProgSet.t

(* Set of mode variables *)
module ModeSet = Set.Make(struct
  type t = mode
  let compare = Pervasives.compare
end)
type modeset = ModeSet.t

(* Encalve Base types *)
type encbasetype = 
    EBtInt                             (* int *)
  | EBtBool                            (* bool *)
  | EBtCond                            (* cond *)
  | EBtRef of mode * enclabeltype	      (* tau ref *)
  | EBtFunc of mode* policy * cndset   (* func *)

and
enclabeltype = encbasetype * policy   

(* typechecking environments - maps variables to types *)
type enccontext = enclabeltype VarLocMap.t


(* Ploynomial representation for cost function *)
type polyterm =
 | Mono   of  mode
 | Poly   of  mode * polyterm


type polynomial = 
   |PConstant of int  (* e.g., 42 *)
   |PMonoterm of int * polyterm (* e.g., 42*x_1*x_2 *)
   |PUminusterm of int * polyterm (* e.g., -42*x_1*x_2 *)
   |PPlus     of polynomial * polynomial  (* 1 + 42*x_1*x_2  *)
   |PMinus    of polynomial * polynomial  (* 1 - 42*x_1*x_2  *)

type cost = polynomial
type totalcost = polynomial*polynomial 

(* Mode SAT *)
module ModeSAT = Map.Make(struct
  type t = mode
  let compare = Pervasives.compare
 end)
type modesat = int ModeSAT.t
