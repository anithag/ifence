type token =
  | INTEGER of (int)
  | LOC of (int)
  | VAR of (string)
  | CHANNEL of (char)
  | PLUS
  | UNDERSCORE
  | LPAREN
  | RPAREN
  | LCURLY
  | RCURLY
  | COMMA
  | SEQ
  | COLON
  | DOT
  | EQUALS
  | TRUE
  | FALSE
  | CALL
  | IF
  | THEN
  | ELSE
  | ENDIF
  | LAMBDA
  | EOF
  | DEREF
  | UPDATE
  | SET
  | ISUNSET
  | OUTPUT
  | ASSIGN
  | SKIP
  | WHILE
  | DO
  | END
  | INT
  | BOOL
  | COND
  | FUNC
  | REF
  | LOW
  | HIGH
  | ERASE

open Parsing;;
let _ = parse_error;;
# 1 "parser.mly"

  open Ast
  open Printf
  open Lexing
# 53 "parser.ml"
let yytransl_const = [|
  261 (* PLUS *);
  262 (* UNDERSCORE *);
  263 (* LPAREN *);
  264 (* RPAREN *);
  265 (* LCURLY *);
  266 (* RCURLY *);
  267 (* COMMA *);
  268 (* SEQ *);
  269 (* COLON *);
  270 (* DOT *);
  271 (* EQUALS *);
  272 (* TRUE *);
  273 (* FALSE *);
  274 (* CALL *);
  275 (* IF *);
  276 (* THEN *);
  277 (* ELSE *);
  278 (* ENDIF *);
  279 (* LAMBDA *);
    0 (* EOF *);
  280 (* DEREF *);
  281 (* UPDATE *);
  282 (* SET *);
  283 (* ISUNSET *);
  284 (* OUTPUT *);
  285 (* ASSIGN *);
  286 (* SKIP *);
  287 (* WHILE *);
  288 (* DO *);
  289 (* END *);
  290 (* INT *);
  291 (* BOOL *);
  292 (* COND *);
  293 (* FUNC *);
  294 (* REF *);
  295 (* LOW *);
  296 (* HIGH *);
  297 (* ERASE *);
    0|]

let yytransl_block = [|
  257 (* INTEGER *);
  258 (* LOC *);
  259 (* VAR *);
  260 (* CHANNEL *);
    0|]

let yylhs = "\255\255\
\004\000\004\000\005\000\005\000\006\000\006\000\006\000\007\000\
\007\000\007\000\007\000\007\000\008\000\009\000\009\000\010\000\
\010\000\001\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\003\000\003\000\003\000\003\000\013\000\
\011\000\011\000\011\000\011\000\012\000\012\000\012\000\012\000\
\014\000\000\000"

let yylen = "\002\000\
\002\000\003\000\001\000\003\000\001\000\001\000\004\000\001\000\
\001\000\001\000\006\000\002\000\003\000\003\000\003\000\001\000\
\003\000\002\000\007\000\001\000\003\000\003\000\005\000\003\000\
\006\000\004\000\004\000\001\000\001\000\001\000\002\000\012\000\
\001\000\001\000\003\000\004\000\001\000\001\000\001\000\003\000\
\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\042\000\000\000\000\000\000\000\
\000\000\000\000\038\000\039\000\000\000\000\000\033\000\034\000\
\000\000\000\000\000\000\000\000\000\000\000\000\020\000\000\000\
\000\000\000\000\028\000\000\000\030\000\008\000\009\000\010\000\
\000\000\000\000\000\000\000\000\017\000\000\000\000\000\000\000\
\037\000\000\000\000\000\031\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\012\000\021\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\024\000\000\000\000\000\005\000\006\000\000\000\000\000\000\000\
\026\000\000\000\027\000\036\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\023\000\000\000\000\000\000\000\000\000\
\000\000\025\000\000\000\001\000\000\000\011\000\000\000\000\000\
\019\000\000\000\002\000\000\000\004\000\000\000\000\000\000\000\
\000\000"

let yydgoto = "\002\000\
\005\000\025\000\026\000\086\000\093\000\070\000\034\000\035\000\
\006\000\007\000\027\000\028\000\029\000\000\000"

let yysindex = "\002\000\
\092\255\000\000\004\255\014\255\000\000\017\255\143\255\009\255\
\009\255\092\255\000\000\000\000\002\255\019\255\000\000\000\000\
\042\255\069\255\205\255\051\255\057\255\067\255\000\000\069\255\
\066\255\044\255\000\000\008\255\000\000\000\000\000\000\000\000\
\074\255\086\255\065\255\065\255\000\000\205\255\097\255\205\255\
\000\000\090\255\008\255\000\000\103\255\113\255\114\255\085\255\
\143\255\205\255\088\255\088\255\062\255\062\255\000\000\000\000\
\062\255\115\255\143\255\117\255\118\255\109\255\143\255\066\255\
\000\000\116\255\116\255\000\000\000\000\253\254\091\255\254\254\
\000\000\036\255\000\000\000\000\088\255\255\254\124\255\119\255\
\124\255\143\255\055\255\000\000\011\255\126\255\062\255\127\255\
\006\255\000\000\130\255\000\000\137\255\000\000\091\255\123\255\
\000\000\145\255\000\000\143\255\000\000\007\255\121\255\062\255\
\091\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\174\255\000\000\000\000\
\000\000\000\000\000\000\000\000\005\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\149\000\000\000\000\000\055\000\000\000\000\000\000\000\000\000\
\000\000\000\000\081\255\112\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\022\000\
\000\000\025\000\040\000\000\000\000\000\000\000\049\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\141\255\000\000\000\000\000\000\001\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\062\000"

let yygindex = "\000\000\
\000\000\209\255\242\255\071\000\056\000\206\255\000\000\144\000\
\000\000\145\000\023\000\238\255\000\000\000\000"

let yytablesize = 351
let yytable = "\043\000\
\007\000\064\000\001\000\071\000\044\000\043\000\072\000\079\000\
\081\000\037\000\049\000\074\000\051\000\091\000\103\000\078\000\
\008\000\049\000\049\000\037\000\092\000\022\000\052\000\056\000\
\040\000\058\000\009\000\097\000\010\000\037\000\038\000\084\000\
\066\000\067\000\089\000\065\000\095\000\080\000\080\000\035\000\
\042\000\039\000\030\000\031\000\032\000\033\000\048\000\049\000\
\040\000\013\000\013\000\013\000\102\000\105\000\029\000\013\000\
\082\000\045\000\083\000\051\000\013\000\032\000\090\000\046\000\
\013\000\013\000\013\000\013\000\050\000\011\000\012\000\041\000\
\013\000\047\000\013\000\013\000\013\000\049\000\013\000\013\000\
\053\000\014\000\014\000\014\000\015\000\016\000\013\000\014\000\
\011\000\012\000\041\000\054\000\014\000\003\000\004\000\021\000\
\014\000\014\000\014\000\014\000\068\000\069\000\055\000\057\000\
\014\000\060\000\014\000\014\000\014\000\059\000\014\000\014\000\
\015\000\015\000\015\000\061\000\063\000\062\000\015\000\077\000\
\051\000\087\000\073\000\015\000\075\000\076\000\104\000\015\000\
\015\000\015\000\015\000\080\000\085\000\094\000\096\000\015\000\
\100\000\015\000\015\000\015\000\098\000\015\000\015\000\011\000\
\012\000\013\000\099\000\091\000\018\000\014\000\003\000\088\000\
\036\000\101\000\037\000\000\000\000\000\000\000\015\000\016\000\
\017\000\018\000\000\000\000\000\000\000\000\000\019\000\000\000\
\020\000\021\000\022\000\000\000\023\000\024\000\016\000\016\000\
\016\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\016\000\016\000\016\000\
\016\000\000\000\000\000\000\000\000\000\016\000\000\000\016\000\
\016\000\016\000\000\000\016\000\016\000\011\000\012\000\041\000\
\000\000\000\000\000\000\014\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\015\000\016\000\000\000\000\000\
\000\000\000\000\000\000\000\000\019\000\000\000\000\000\021\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\007\000\007\000\007\000\000\000\000\000\000\000\007\000\
\007\000\000\000\000\000\007\000\007\000\000\000\000\000\000\000\
\007\000\007\000\007\000\007\000\000\000\007\000\007\000\000\000\
\007\000\007\000\007\000\007\000\007\000\022\000\007\000\007\000\
\040\000\007\000\000\000\000\000\040\000\000\000\007\000\040\000\
\000\000\000\000\022\000\022\000\040\000\040\000\040\000\035\000\
\000\000\040\000\000\000\035\000\000\000\000\000\022\000\000\000\
\040\000\040\000\000\000\035\000\035\000\035\000\029\000\000\000\
\035\000\000\000\029\000\000\000\000\000\032\000\000\000\035\000\
\035\000\032\000\000\000\029\000\029\000\000\000\000\000\029\000\
\000\000\000\000\032\000\032\000\000\000\000\000\032\000\029\000\
\000\000\000\000\000\000\000\000\000\000\000\000\032\000"

let yycheck = "\018\000\
\000\000\049\000\001\000\054\000\019\000\024\000\057\000\011\001\
\011\001\005\001\012\001\059\000\005\001\003\001\008\001\063\000\
\013\001\012\001\012\001\015\001\010\001\000\000\015\001\038\000\
\000\000\040\000\013\001\022\001\012\001\025\001\029\001\033\001\
\051\000\052\000\082\000\050\000\087\000\041\001\041\001\000\000\
\018\000\023\001\034\001\035\001\036\001\037\001\024\000\012\001\
\007\001\001\001\002\001\003\001\100\000\104\000\000\000\007\001\
\021\001\007\001\077\000\005\001\012\001\000\000\008\001\007\001\
\016\001\017\001\018\001\019\001\025\001\001\001\002\001\003\001\
\024\001\007\001\026\001\027\001\028\001\012\001\030\001\031\001\
\007\001\001\001\002\001\003\001\016\001\017\001\038\001\007\001\
\001\001\002\001\003\001\006\001\012\001\002\001\003\001\027\001\
\016\001\017\001\018\001\019\001\039\001\040\001\038\001\007\001\
\024\001\003\001\026\001\027\001\028\001\020\001\030\001\031\001\
\001\001\002\001\003\001\003\001\032\001\004\001\007\001\011\001\
\005\001\003\001\008\001\012\001\008\001\008\001\006\001\016\001\
\017\001\018\001\019\001\041\001\009\001\008\001\008\001\024\001\
\014\001\026\001\027\001\028\001\011\001\030\001\031\001\001\001\
\002\001\003\001\010\001\003\001\000\000\007\001\010\001\081\000\
\009\000\098\000\010\000\255\255\255\255\255\255\016\001\017\001\
\018\001\019\001\255\255\255\255\255\255\255\255\024\001\255\255\
\026\001\027\001\028\001\255\255\030\001\031\001\001\001\002\001\
\003\001\255\255\255\255\255\255\007\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\016\001\017\001\018\001\
\019\001\255\255\255\255\255\255\255\255\024\001\255\255\026\001\
\027\001\028\001\255\255\030\001\031\001\001\001\002\001\003\001\
\255\255\255\255\255\255\007\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\016\001\017\001\255\255\255\255\
\255\255\255\255\255\255\255\255\024\001\255\255\255\255\027\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\001\001\002\001\003\001\255\255\255\255\255\255\007\001\
\008\001\255\255\255\255\011\001\012\001\255\255\255\255\255\255\
\016\001\017\001\018\001\019\001\255\255\021\001\022\001\255\255\
\024\001\025\001\026\001\027\001\028\001\008\001\030\001\031\001\
\008\001\033\001\255\255\255\255\012\001\255\255\038\001\015\001\
\255\255\255\255\021\001\022\001\020\001\021\001\022\001\008\001\
\255\255\025\001\255\255\012\001\255\255\255\255\033\001\255\255\
\032\001\033\001\255\255\020\001\021\001\022\001\008\001\255\255\
\025\001\255\255\012\001\255\255\255\255\008\001\255\255\032\001\
\033\001\012\001\255\255\021\001\022\001\255\255\255\255\025\001\
\255\255\255\255\021\001\022\001\255\255\255\255\025\001\033\001\
\255\255\255\255\255\255\255\255\255\255\255\255\033\001"

let yynames_const = "\
  PLUS\000\
  UNDERSCORE\000\
  LPAREN\000\
  RPAREN\000\
  LCURLY\000\
  RCURLY\000\
  COMMA\000\
  SEQ\000\
  COLON\000\
  DOT\000\
  EQUALS\000\
  TRUE\000\
  FALSE\000\
  CALL\000\
  IF\000\
  THEN\000\
  ELSE\000\
  ENDIF\000\
  LAMBDA\000\
  EOF\000\
  DEREF\000\
  UPDATE\000\
  SET\000\
  ISUNSET\000\
  OUTPUT\000\
  ASSIGN\000\
  SKIP\000\
  WHILE\000\
  DO\000\
  END\000\
  INT\000\
  BOOL\000\
  COND\000\
  FUNC\000\
  REF\000\
  LOW\000\
  HIGH\000\
  ERASE\000\
  "

let yynames_block = "\
  INTEGER\000\
  LOC\000\
  VAR\000\
  CHANNEL\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 24 "parser.mly"
                          (VarSet.empty)
# 321 "parser.ml"
               : Ast.cndset))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'unsetcnd) in
    Obj.repr(
# 25 "parser.mly"
                           (VarSet.union _2 VarSet.empty )
# 328 "parser.ml"
               : Ast.cndset))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 27 "parser.mly"
                   (VarSet.add _1 VarSet.empty)
# 335 "parser.ml"
               : 'unsetcnd))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'unsetcnd) in
    Obj.repr(
# 28 "parser.mly"
                        (VarSet.add _1 _3)
# 343 "parser.ml"
               : 'unsetcnd))
; (fun __caml_parser_env ->
    Obj.repr(
# 30 "parser.mly"
                 (Low)
# 349 "parser.ml"
               : 'policy))
; (fun __caml_parser_env ->
    Obj.repr(
# 31 "parser.mly"
                  (High)
# 355 "parser.ml"
               : 'policy))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'policy) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'policy) in
    Obj.repr(
# 32 "parser.mly"
                                   (Erase(_1, _3, _4))
# 364 "parser.ml"
               : 'policy))
; (fun __caml_parser_env ->
    Obj.repr(
# 34 "parser.mly"
                      (BtInt)
# 370 "parser.ml"
               : 'basetype))
; (fun __caml_parser_env ->
    Obj.repr(
# 35 "parser.mly"
                      (BtBool)
# 376 "parser.ml"
               : 'basetype))
; (fun __caml_parser_env ->
    Obj.repr(
# 36 "parser.mly"
                      (BtCond)
# 382 "parser.ml"
               : 'basetype))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'policy) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : Ast.cndset) in
    Obj.repr(
# 37 "parser.mly"
                                                 (BtFunc(_3, _5))
# 390 "parser.ml"
               : 'basetype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'labeltype) in
    Obj.repr(
# 38 "parser.mly"
                       (BtRef(_1))
# 397 "parser.ml"
               : 'basetype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'basetype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'policy) in
    Obj.repr(
# 40 "parser.mly"
                                        ( (_1, _3) )
# 405 "parser.ml"
               : 'labeltype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : int) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'labeltype) in
    Obj.repr(
# 42 "parser.mly"
                                  ( VarLocMap.add (Mem _1) _3 VarLocMap.empty )
# 413 "parser.ml"
               : 'vardecl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'labeltype) in
    Obj.repr(
# 43 "parser.mly"
                                    ( VarLocMap.add (Reg _1) _3 VarLocMap.empty )
# 421 "parser.ml"
               : 'vardecl))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'vardecl) in
    Obj.repr(
# 45 "parser.mly"
                                    ( _1 )
# 428 "parser.ml"
               : 'vardecllist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'vardecl) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'vardecllist) in
    Obj.repr(
# 46 "parser.mly"
                             ( VarLocMap.merge (fun key left right -> match left, right with
							| Some x, Some y -> None (* Error *)
							| None, right -> right
							| left, None  -> left
						      ) _1 _3 )
# 440 "parser.ml"
               : 'vardecllist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'vardecllist) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.stmt) in
    Obj.repr(
# 51 "parser.mly"
                                    ((_1, _2))
# 448 "parser.ml"
               : Ast.program))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'bexp) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : Ast.stmt) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : Ast.stmt) in
    Obj.repr(
# 53 "parser.mly"
                                          ( If(_2, _4, _6) )
# 457 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
                  ( Skip )
# 463 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exp) in
    Obj.repr(
# 55 "parser.mly"
                           ( Assign(_1, _3)  )
# 471 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.stmt) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.stmt) in
    Obj.repr(
# 56 "parser.mly"
                          ( Seq(_1, _3)  )
# 479 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'bexp) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : Ast.stmt) in
    Obj.repr(
# 57 "parser.mly"
                                    ( While(_2, _4) )
# 487 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Ast.exp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : Ast.exp) in
    Obj.repr(
# 58 "parser.mly"
                            ( Update(_1, _3) )
# 495 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : char) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'aexp) in
    Obj.repr(
# 59 "parser.mly"
                                               ( Output(_3, _5) )
# 503 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : Ast.exp) in
    Obj.repr(
# 60 "parser.mly"
                                   ( Call(_3) )
# 510 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 61 "parser.mly"
                                    ( Set(_3) )
# 517 "parser.ml"
               : Ast.stmt))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bexp) in
    Obj.repr(
# 64 "parser.mly"
               ( _1 )
# 524 "parser.ml"
               : Ast.exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 65 "parser.mly"
               ( _1 )
# 531 "parser.ml"
               : Ast.exp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'lexp) in
    Obj.repr(
# 66 "parser.mly"
                                        ( _1 )
# 538 "parser.ml"
               : Ast.exp))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : Ast.exp) in
    Obj.repr(
# 67 "parser.mly"
                   ( Deref(_2) )
# 545 "parser.ml"
               : Ast.exp))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 8 : 'policy) in
    let _6 = (Parsing.peek_val __caml_parser_env 6 : Ast.cndset) in
    let _9 = (Parsing.peek_val __caml_parser_env 3 : Ast.stmt) in
    let _12 = (Parsing.peek_val __caml_parser_env 0 : 'policy) in
    Obj.repr(
# 69 "parser.mly"
                                                                                        ( Lam(_4, _6, _12, _9) )
# 555 "parser.ml"
               : 'lexp))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "parser.mly"
                ( True  )
# 561 "parser.ml"
               : 'bexp))
; (fun __caml_parser_env ->
    Obj.repr(
# 72 "parser.mly"
                                   ( False )
# 567 "parser.ml"
               : 'bexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 73 "parser.mly"
                           ( Eq(_1, _3) )
# 575 "parser.ml"
               : 'bexp))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 74 "parser.mly"
                                   ( Isunset(_3) )
# 582 "parser.ml"
               : 'bexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 76 "parser.mly"
                                   ( Var _1)
# 589 "parser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 77 "parser.mly"
                                   ( Constant(_1) )
# 596 "parser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 78 "parser.mly"
               ( Loc(_1) )
# 603 "parser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 79 "parser.mly"
                          ( Plus(_1, _3) )
# 611 "parser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 80 "parser.mly"
                   ( Loc _1)
# 618 "parser.ml"
               : 'loc))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.program)
