
%{
  open Lambda;;
%}

%token LAMBDA
%token TRUE
%token FALSE
%token IF
%token THEN
%token ELSE
%token SUCC
%token PRED
%token ISZERO
%token LET
%token LETREC
%token FIX
%token IN
%token CONCAT
%token LENGTH
%token COMPARE
%token BOOL
%token NAT
%token STRING
%token AS
%token CASE
%token OF
%token LIST
%token NIL
%token CONS
%token ISNIL
%token HEAD
%token TAIL

%token LPAREN
%token RPAREN
%token DOT
%token EQ
%token COLON
%token ARROW
%token LBRACE
%token RBRACE
%token EOF
%token COMMA
%token LBRACKET
%token RBRACKET
%token GT
%token LT
%token OR


%token <string> ID
%token <int> INTV
%token <string> IDV
%token <string> IDV2
%token <string> STRINGV

%start s
%type <Lambda.command> s

%%
s :
    IDV EQ term EOF
      { Bind ($1, $3)}
  | IDV2 EQ ty EOF
      { TyBind ($1, $3)}
  | term EOF
      { Eval $1 }
  | IDV2 EOF
      { EvalTy $1 }


term :
    appTerm
      { $1 }
  | IF term THEN term ELSE term
      { TmIf ($2, $4, $6) }
  | LAMBDA IDV COLON ty DOT term
      { TmAbs ($2, $4, $6) }
  | LET IDV EQ term IN term
      { TmLetIn ($2, $4, $6) }
  | LETREC IDV COLON ty EQ term IN term
      { TmLetIn ($2, TmFix (TmAbs ($2, $4, $6)), $8) }
  | CASE term OF cases
      { TmCase ($2, $4) }

cases :
    LT IDV EQ IDV GT EQ GT term
    {[$2, $4, $8]}
  | LT IDV EQ IDV GT EQ GT term OR cases
    {($2, $4, $8)::$10}

appTerm :
    pathTerm
      { $1 }
  | SUCC pathTerm
      { TmSucc $2 }
  | PRED pathTerm
      { TmPred $2 }
  | ISZERO pathTerm
      { TmIsZero $2 }
  | FIX pathTerm
      { TmFix $2 }
  | CONCAT pathTerm pathTerm
      { TmConcat ($2, $3) }
  | LENGTH pathTerm
      { TmLength $2 }
  | COMPARE pathTerm pathTerm
      { TmCompare ($2, $3) }
  | CONS LBRACKET ty RBRACKET pathTerm pathTerm
      { TmCons ($3, $5, $6) }
  | ISNIL LBRACKET ty RBRACKET pathTerm
      { TmIsNil ($3, $5) }
  | HEAD LBRACKET ty RBRACKET pathTerm
      { TmHead ($3, $5) }
  | TAIL LBRACKET ty RBRACKET pathTerm
      { TmTail ($3, $5) }
  | appTerm pathTerm
      { TmApp ($1, $2) }


pathTerm :
     NIL LBRACKET ty RBRACKET
      { TmNil ($3) }
   | pathTerm DOT INTV
      { TmProjection ($1, (string_of_int $3))}
   | pathTerm DOT IDV
      { TmProjection ($1, $3)}
   | atomicTerm
      { $1 } 

atomicTerm :
    LPAREN term RPAREN
      { $2 }
  | TRUE
      { TmTrue }
  | FALSE
      { TmFalse }
  | IDV
      { TmVar $1 }
  | INTV
      { let rec f = function
            0 -> TmZero
          | n -> TmSucc (f (n-1))
        in f $1 }
  | STRINGV
      { TmString $1 }
  | LBRACE recordTm RBRACE
      { TmRecord $2 }
  | LBRACE tupleTm RBRACE
      { TmTuple $2 }
  | LT IDV EQ term GT AS ty
      { TmVariant ($7,($2, $4)) }


recordTm:
      { [] } 
   | noemptyrecordTm 
      { $1 }

noemptyrecordTm:
     IDV EQ term 
      { [$1, $3] }
   | IDV EQ term COMMA noemptyrecordTm 
      { ($1, $3)::$5 }


ty :
    atomicTy    
      { $1 }
  | atomicTy ARROW ty
      { TyArr ($1, $3) }

atomicTy :
    LPAREN ty RPAREN
      { $2 }
  | BOOL
      { TyBool }
  | IDV2 
      { TyName $1 }
  | NAT
      { TyNat }
  | STRING
      { TyString }
  | LBRACE recordTy RBRACE
      { TyRecord $2 }
  | LT variantTy GT
      { TyVariant $2 }
  | LBRACE tupleTy RBRACE
      { TyTuple $2 }
  | LIST LBRACKET ty RBRACKET 
      { TyList $3 }
   
recordTy:
      { [] }
  | noemptyrecordTy 
      { $1 }
  
noemptyrecordTy:
    IDV COLON ty 
      { [$1, $3] }
  | IDV COLON ty COMMA noemptyrecordTy 
      { ($1, $3)::$5 }

variantTy:
      { [] }
  | noemptyvariantTy 
      { $1 }
  
noemptyvariantTy:
    IDV COLON ty 
      { [$1, $3] }
  | IDV COLON ty COMMA noemptyvariantTy 
      { ($1, $3)::$5 }

tupleTm: 
    term 
      { [$1] }
  | term COMMA tupleTm 
      { $1::$3 }

tupleTy: 
    ty 
      { [$1] }
  | ty COMMA tupleTy 
      { $1::$3 }