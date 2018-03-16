(*
In this assignment, you will define the abstract syntax (data type exp) and a definitional interpreter eval for a simple arithmetic and boolean calculation language.



The expressions in the language are of the following forms

Integer constants, 
Unary arithmetic operations: abs, (and any other sensible ones you can think of),
Identifiers, represented as (alphanumeric) strings
binary operations: + (addition), - (subtraction), * (multiplication), div, mod, ^ (exponentiation)
Boolean constants: T and F
Unary boolean operation: not
binary boolean operations:  /\ (and), \/ (or), -> (implies)
Comparison operators: = (equal) , > (greater than), < (less than) , >= (greater or equal), <= (less or equal) on integer expressions
n-tuples for each n > 2
Projection operators proj(i,n) which project the ith element of an n-tuple.


Assume all inputs are of proper type (we will study type-checking later).  Define a suitable data type answer.



eval: exp -> answer.

Next, define a suitable set of opcodes for a stack-and-table machine to evaluate this language and define a compiler for this language to sequences of these opcodes.

compile: exp -> opcode list

Third, define the stack machine execution functions, which takes a sequence of opcodes and executes them starting from a given stack and table.

execute: stack * table * opcode list -> answer

Provide enough examples 
*)




open List;;

type exp = Const of int | T | F | Abs of exp | Addition of exp*exp | Subtraction of exp*exp | Multipiction of exp*exp | Div of exp*exp | Mod of exp*exp | Exponent of exp*exp| 
And of exp*exp | Or of exp*exp | Implies of exp*exp | Not of exp | Equal of exp*exp | Gt of exp*exp | Lt of exp*exp | Gte of exp*exp | Lte of exp*exp | Tup of exp list | 
Proj of int*exp | Var of string;;

type answer = C of int | True | False | TUPL of answer list;;

let absa e = match e with C(n)-> C(abs n);;

let add e1 e2 = match (e1,e2) with (C(n1),C(n2)) -> C(n1 + n2);; 

let sub e1 e2 = match (e1,e2) with (C(n1),C(n2)) -> C(n1 - n2);;

let mul e1 e2 = match (e1,e2) with (C(n1),C(n2)) -> C(n1*n2);;

let div e1 e2 = match (e1,e2) with (C(n1),C(n2)) -> C(n1/n2);;

let moda e1 e2 = match (e1,e2) with (C(n1),C(n2)) -> C(n1-n2*(n1/n2));;

let expa e1 e2 = match (e1,e2) with (C(n1),C(n2)) -> C(int_of_float ((float_of_int n1) ** (float_of_int n2)));;

let anda e1 e2 = match (e1,e2) with (True,True) -> True | (False,True) -> False | (True,False) -> False  | (False,False) -> False;;

let ora e1 e2 = match (e1,e2) with (True,True) -> True | (False,True) -> True | (True,False) -> True  | (False,False) -> False;;

let imp e1 e2 = match (e1,e2) with (True,True) -> True | (False,True) -> True | (True,False) -> False  | (False,False) -> True;;

let nota e = match e with True-> False | False -> True ;;

let equ e1 e2 = match (e1,e2) with (C(n),C(m)) -> if n=m then True else False ;;

let gt e1 e2 = match (e1,e2) with (C(n),C(m)) -> if n>m then True else False ;;

let lt e1 e2 = match (e1,e2) with (C(n),C(m)) -> if n<m then True else False ;;

let gte e1 e2 = match (e1,e2) with (C(n),C(m)) -> if n>=m then True else False ;;

let lte e1 e2 = match (e1,e2) with (C(n),C(m)) -> if n<=m then True else False ;;

exception ValueNotFound;;

let rho e = match e with "x" -> C(0) | "y" -> C(3) | "a" -> True | "b" -> False | _ -> raise ValueNotFound ;;

let rec eval e = match e with Const(n)->C(n) | T -> True | F -> False | Var(x) -> rho x | Abs(n) -> absa (eval n) | Addition(e1,e2) -> add (eval e1) (eval e2) |
 Subtraction(e1,e2) -> sub (eval e1) (eval e2) | Multipiction(e1,e2) -> mul (eval e1) (eval e2) | Mod(e1,e2) -> moda (eval e1) (eval e2) |Div(e1,e2) -> div (eval e1) (eval e2) |
 Exponent(e1,e2) -> expa (eval e1) (eval e2)| And(e1,e2) -> anda (eval e1) (eval e2) | Or(e1,e2) -> ora (eval e1) (eval e2) | Implies(e1,e2) -> imp (eval e1) (eval e2) | 
 Not(e1) -> nota (eval e1) | Equal(e1,e2) -> equ (eval e1) (eval e2) | Gt(e1,e2) -> gt (eval e1) (eval e2) | Lt(e1,e2) -> lt (eval e1) (eval e2) | 
 Lte(e1,e2) -> lte (eval e1) (eval e2) | Gte(e1,e2) -> gte (eval e1) (eval e2) |Proj(n,Tup(e1)) -> eval (nth e1 n);;

type opcode = CONST of int | Tr | Fl | ABS | ADD | SUB | MUL | DIV | MOD | EXP | AND | OR | IMP | NOT | EQUAL | GT | LT | GTE | LTE | TUP of opcode list | PROJ | VAR of string;;

let tup e = TUP(e);; 

let rec compile e = match e with Const(n)->[CONST(n)] | T -> [Tr] | F -> [Fl] | Var(x) -> [VAR(x)] |  Abs(n) -> (compile n)@[ABS] | Addition(e1,e2) -> (compile e1)@(compile e2)@[ADD] |
  Subtraction(e1,e2) -> (compile e1)@(compile e2)@[SUB] | Multipiction(e1,e2) -> (compile e1)@(compile e2)@[MUL]| Mod(e1,e2) -> (compile e1)@(compile e2)@[MOD] |
  Div(e1,e2) -> (compile e1)@(compile e2)@[DIV] |Exponent(e1,e2) -> (compile e1)@(compile e2)@[EXP] | And(e1,e2) -> (compile e1)@(compile e2)@[AND] | 
  Or(e1,e2) -> (compile e1)@(compile e2)@[OR] | Implies(e1,e2) -> (compile e1)@(compile e2)@[IMP] | Not(e1) -> (compile e1)@[NOT] | Equal(e1,e2) -> (compile e1)@(compile e2)@[EQUAL] | 
  Gt(e1,e2) -> (compile e1)@(compile e2)@[GT] | Lt(e1,e2) -> (compile e1)@(compile e2)@[LT]| Lte(e1,e2) -> (compile e1)@(compile e2)@[LTE] | Gte(e1,e2) -> (compile e1)@(compile e2)@[GTE] |
  Tup(e1) -> List.map tup (List.map compile e1)  | Proj(n,e1) -> [CONST(n)]@(compile e1)@[PROJ];;

let table e = match e with "x" -> C(0) | "y" -> C(3) | "a" -> True | "b" -> False | _ -> raise ValueNotFound ;;

let rec execute (s,table,o) = match (s,table,o) with (s,table,[]) -> hd s | (s,table,CONST(n)::o') -> execute(C(n)::s,table,o') | (s,table,Tr::o') -> execute(True::s,table,o') | 
(s,table,Fl::o') -> execute(False::s,table,o') | (s,table,VAR(x)::o') -> execute(table(x)::s,table,o') | (C(n)::s,table,ABS::o') -> execute((absa (C(n)))::s,table,o') | 
(C(n1)::C(n2)::s,table,ADD::o') -> execute((add (C(n1)) (C(n2)))::s,table,o') | (C(n1)::C(n2)::s,table,SUB::o') -> execute((sub (C(n2)) (C(n1)))::s,table,o') | 
(C(n1)::C(n2)::s,table,MUL::o') -> execute((mul (C(n1)) (C(n2)))::s,table,o') | (C(n1)::C(n2)::s,table,DIV::o') -> execute((div (C(n2)) (C(n1)))::s,table,o') |
(C(n1)::C(n2)::s,table,MOD::o') -> execute((moda (C(n2)) (C(n1)))::s,table,o') | (C(n1)::C(n2)::s,table,EXP::o') -> execute((expa (C(n2)) (C(n1)))::s,table,o') |
(True::True::s,table,AND::o') -> execute(True::s,table,o') | (True::False::s,table,AND::o') -> execute(False::s,table,o') | (False::True::s,table,AND::o') -> execute(False::s,table,o') |
(False::False::s,table,AND::o') -> execute(False::s,table,o') |(True::True::s,table,OR::o') -> execute(True::s,table,o') | (True::False::s,table,OR::o') -> execute(True::s,table,o') |
(False::True::s,table,OR::o') -> execute(True::s,table,o') |(False::False::s,table,OR::o') -> execute(False::s,table,o') | (True::True::s,table,IMP::o') -> execute(True::s,table,o') |
(True::False::s,table,IMP::o') -> execute(False::s,table,o') |(False::True::s,table,IMP::o') -> execute(True::s,table,o') |(False::False::s,table,IMP::o') -> execute(True::s,table,o') |
(True::s,table,NOT::o') -> execute(False::s,table,o') | (False::s,table,NOT::o') -> execute(True::s,table,o') | (C(n1)::C(n2)::s,table,EQUAL::o') -> execute((equ (C(n1)) (C(n2)))::s,table,o') |
(C(n1)::C(n2)::s,table,GT::o') -> execute((gt (C(n2)) (C(n1)))::s,table,o') | (C(n1)::C(n2)::s,table,LT::o') -> execute((lt (C(n2)) (C(n1)))::s,table,o') |
(C(n1)::C(n2)::s,table,GTE::o') -> execute((gte (C(n2)) (C(n1)))::s,table,o') |(C(n1)::C(n2)::s,table,LTE::o') -> execute((lte (C(n2)) (C(n1)))::s,table,o') | 
 (C(n)::s,table,TUP(e1)::TUP(e2)::o) -> execute(C(n)::TUPL([execute(s,table,e1)]@[execute(s,table,e2)])::s,table,o)  |
 (C(n)::TUPL(e)::s,table,TUP(e1)::o) -> execute(C(n)::TUPL(e@[execute(s,table,e1)])::s,table,o)  |
 (C(n)::TUPL(e)::s,table,PROJ::o') -> execute((nth e n)::s,table,o') ;;

(*            EXAMPLES of the definitional interpreter  *)

let a= Const(1);;
let b = Const(2);;
let c=Addition(a,b);;
eval c;;
let d= compile c;;
execute ([],table,d);;   (* The value returned from eval and execute are same and equal to C(3) *)

(*   Next *)
let y = Subtraction(b,a);;
eval y;;
let c = compile y;;
execute ([],table,c);;

(*   Next *)

let y =  Subtraction(Proj(2,Tup[Const(1);Const(1);Addition(Subtraction(Const(5),Const(4)),Addition(Const(3),Const(4)))]),Const(3));;
eval y;;
let c = compile y;;
execute([],table,c);;


(*   Next *)

let y =  Mod(Proj(2,Tup[Const(1);Const(1);Addition(Subtraction(Const(5),Const(4)),Addition(Const(3),Const(4)))]),Var("y"));;
eval y;;
let c = compile y;;
execute ([],table,c);;











