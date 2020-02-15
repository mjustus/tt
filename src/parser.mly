%{
open Raw
%}

%token UNIVERSE
%token BACKSLASH
%token DOT
%token LPAREN
%token RPAREN
%token SEMICOLON
%token COLON
%token COLON_COLON
%token COMMA
%token EQUALS
%token ARROW
%token IN
%token UNDERSCORE
%token LET

%token SUCCESS
%token <Failure_code.t> FAILURE

%token EOF
%token <string> IDENT
%token <int> INTEGER


%start file
%type <Raw.file> file

%start test
%type <Test.flag * Raw.file> test
%%
file :
    decls EOF { $1 }

test :
    test_flag file { ($1, $2) }
  | file { (Test.Success, $1) }

test_flag :
    SUCCESS { Test.Success }
  | FAILURE { Test.Failure $1 }

term_annot :
    term_annot COLON_COLON term_let { Chk ($3, $1) }
  | term_let { $1 }
      
decl :
    ident_opt COLON term_annot EQUALS term_annot { fun f -> Defn (f, $1, $3, $5) }

decls :
  | decl SEMICOLON decls { $1 $3 }
  | decl { $1 File.Done }
  | { File.Done }

term_let :
    LET ident_opt COLON term_let EQUALS term_let IN term_let
      { Let ($4, $6, Named.Opt.Bound ($2, $8)) }
  | term_pi { $1 }

term_pi :
    telescope ARROW term_let
      { Abs ($1 (Up $3)) }
  | term_spine ARROW term_let
      { Abs (Pi ($1, Named.Mult_opt.Bound (N_list.Last None, Up $3))) }
  | term_lam { $1 }

telescope :
    telescope_segment telescope { fun t -> $1 ($2 t) }
  | telescope_segment { $1 }
      
telescope_segment :
    LPAREN ident_comma_list COLON term_pi RPAREN
      { fun t -> Pi ($4, Named.Mult_opt.Bound ($2, t)) }

term_lam :
    BACKSLASH ident_list DOT term_let { Lam (Named.Mult_opt.Bound ($2, $4)) }
  | term_spine { $1 }

term_spine :
    term_spine term_atom { App ($1, $2) }
  | term_sum { $1 }

term_sum :
  | term_product { $1 }    

term_product :
  | term_atom { $1 }

term_atom :
    IDENT { Idt $1 }
  | UNIVERSE INTEGER { Unv ($2) }
  | LPAREN term_annot RPAREN { $2 }
    
ident_list :
    ident_opt ident_list { N_list.More ($1, $2) }
  | ident_opt { N_list.Last $1 }

ident_opt :
    UNDERSCORE { None }
  | IDENT {Some $1}


ident_comma_list :
    ident_opt COMMA ident_comma_list { N_list.More ($1, $3) }
  | ident_opt { N_list.Last $1 }

