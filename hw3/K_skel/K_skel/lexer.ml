# 6 "lexer.mll"
 
 open Parser
 exception Eof
 exception LexicalError
 let verbose1 s =  (* (print_string s; print_newline(); s) *) s
 let verbose2 s =  (* (print_string s; print_newline()) *) ()
 let comment_depth = ref 0
 let keyword_tbl = Hashtbl.create 31
 let _ = List.iter (fun (keyword, tok) -> Hashtbl.add keyword_tbl keyword tok)
                   [("unit", UNIT);
				    ("true", TRUE);
                    ("false", FALSE);
                    ("not", NOT);
                    ("if", IF);
                    ("then",THEN);
                    ("else",ELSE);
                    ("let", LET);
                    ("in", IN);
                    ("end", END);
	    	        ("proc", PROC);
                    ("while", WHILE);
                    ("do"   , DO);
                    ("read" , READ);
                    ("write", WRITE)
                  ] 

# 29 "lexer.ml"
let __ocaml_lex_tables = {
  Lexing.lex_base = 
   "\000\000\233\255\234\255\235\255\236\255\237\255\239\255\240\255\
    \241\255\002\000\243\255\244\255\245\255\246\255\247\255\248\255\
    \249\255\250\255\251\255\085\000\160\000\022\000\002\000\254\255\
    \242\255\052\000\252\255\253\255\054\000\054\000\255\255\254\255\
    ";
  Lexing.lex_backtrk = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\022\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\003\000\002\000\017\000\000\000\255\255\
    \255\255\255\255\255\255\255\255\003\000\003\000\255\255\255\255\
    ";
  Lexing.lex_default = 
   "\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\255\255\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\255\255\255\255\255\255\255\255\000\000\
    \000\000\026\000\000\000\000\000\255\255\255\255\000\000\000\000\
    ";
  Lexing.lex_trans = 
   "\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\022\000\022\000\022\000\022\000\022\000\000\000\022\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \022\000\000\000\022\000\000\000\000\000\000\000\000\000\000\000\
    \021\000\005\000\016\000\018\000\007\000\017\000\006\000\015\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\009\000\008\000\013\000\014\000\012\000\024\000\
    \023\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\010\000\029\000\011\000\028\000\031\000\
    \030\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\004\000\019\000\003\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \000\000\000\000\000\000\000\000\019\000\000\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \002\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000";
  Lexing.lex_check = 
   "\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\000\000\000\000\022\000\022\000\000\000\255\255\022\000\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\022\000\255\255\255\255\255\255\255\255\255\255\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\009\000\
    \021\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\025\000\000\000\025\000\028\000\
    \029\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
    \000\000\000\000\000\000\000\000\019\000\000\000\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \255\255\255\255\255\255\255\255\019\000\255\255\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \019\000\019\000\019\000\019\000\019\000\019\000\019\000\019\000\
    \020\000\020\000\020\000\020\000\020\000\020\000\020\000\020\000\
    \020\000\020\000\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \000\000\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\025\000\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
    \255\255";
  Lexing.lex_base_code = 
   "";
  Lexing.lex_backtrk_code = 
   "";
  Lexing.lex_default_code = 
   "";
  Lexing.lex_trans_code = 
   "";
  Lexing.lex_check_code = 
   "";
  Lexing.lex_code = 
   "";
}

let rec start lexbuf =
    __ocaml_lex_start_rec lexbuf 0
and __ocaml_lex_start_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 38 "lexer.mll"
             ( start lexbuf )
# 178 "lexer.ml"

  | 1 ->
# 39 "lexer.mll"
            ( comment_depth :=1;
              comment lexbuf;
              start lexbuf )
# 185 "lexer.ml"

  | 2 ->
# 42 "lexer.mll"
              ( NUM (int_of_string (verbose1 (Lexing.lexeme lexbuf))) )
# 190 "lexer.ml"

  | 3 ->
# 43 "lexer.mll"
          ( let id = verbose1 (Lexing.lexeme lexbuf)
            in try Hashtbl.find keyword_tbl id
               with _ -> ID id
            )
# 198 "lexer.ml"

  | 4 ->
# 47 "lexer.mll"
           (verbose2 "+"; PLUS)
# 203 "lexer.ml"

  | 5 ->
# 48 "lexer.mll"
           (verbose2 "-";MINUS)
# 208 "lexer.ml"

  | 6 ->
# 49 "lexer.mll"
           ( verbose2 "*"; STAR)
# 213 "lexer.ml"

  | 7 ->
# 50 "lexer.mll"
           ( verbose2 "/"; SLASH)
# 218 "lexer.ml"

  | 8 ->
# 51 "lexer.mll"
           (verbose2 "="; EQUAL)
# 223 "lexer.ml"

  | 9 ->
# 52 "lexer.mll"
           ( verbose2 "<"; LB)
# 228 "lexer.ml"

  | 10 ->
# 53 "lexer.mll"
           ( verbose2 ">"; RB)
# 233 "lexer.ml"

  | 11 ->
# 54 "lexer.mll"
           ( verbose2 "]"; RBLOCK)
# 238 "lexer.ml"

  | 12 ->
# 55 "lexer.mll"
           ( verbose2 "["; LBLOCK)
# 243 "lexer.ml"

  | 13 ->
# 56 "lexer.mll"
            (verbose2 ":="; COLONEQ)
# 248 "lexer.ml"

  | 14 ->
# 57 "lexer.mll"
           ( verbose2 ";"; SEMICOLON)
# 253 "lexer.ml"

  | 15 ->
# 58 "lexer.mll"
        ( verbose2 ","; COMMA)
# 258 "lexer.ml"

  | 16 ->
# 59 "lexer.mll"
        ( verbose2 "."; PERIOD)
# 263 "lexer.ml"

  | 17 ->
# 60 "lexer.mll"
           ( verbose2 "("; LP)
# 268 "lexer.ml"

  | 18 ->
# 61 "lexer.mll"
           ( verbose2 ")"; RP)
# 273 "lexer.ml"

  | 19 ->
# 62 "lexer.mll"
        ( verbose2 "{"; LC)
# 278 "lexer.ml"

  | 20 ->
# 63 "lexer.mll"
        ( verbose2 "}"; RC)
# 283 "lexer.ml"

  | 21 ->
# 64 "lexer.mll"
           ( verbose2 "eof"; EOF)
# 288 "lexer.ml"

  | 22 ->
# 65 "lexer.mll"
         (raise LexicalError)
# 293 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_start_rec lexbuf __ocaml_lex_state

and comment lexbuf =
    __ocaml_lex_comment_rec lexbuf 25
and __ocaml_lex_comment_rec lexbuf __ocaml_lex_state =
  match Lexing.engine __ocaml_lex_tables __ocaml_lex_state lexbuf with
      | 0 ->
# 68 "lexer.mll"
          (comment_depth := !comment_depth+1; comment lexbuf)
# 304 "lexer.ml"

  | 1 ->
# 69 "lexer.mll"
          (comment_depth := !comment_depth-1;
           if !comment_depth > 0 then comment lexbuf )
# 310 "lexer.ml"

  | 2 ->
# 71 "lexer.mll"
         (raise Eof)
# 315 "lexer.ml"

  | 3 ->
# 72 "lexer.mll"
         (comment lexbuf)
# 320 "lexer.ml"

  | __ocaml_lex_state -> lexbuf.Lexing.refill_buff lexbuf; __ocaml_lex_comment_rec lexbuf __ocaml_lex_state

;;

