(**															Assignment 3 Programing Languages
Consider the representation of "pre-terms" using the following data type definition

type term = V of variable | Node of symbol * (term list);;

Choose suitable type representations for types variable and symbol.



1. Given a signature consisting of symbols and their arities (>= 0) in any suitable form -- either as a list of (symbol, arity) pairs, or as a function from symbols to arities, write a function check_sig that checks whether the signature is a valid signature (no repeated symbols, arities are non-negative etc.)
2. Given a valid signature (checked using check_sig), define a function wfterm that checks that a given preterm is well-formed according to the signature.
3. Define functions ht, size and vars that given a well-formed term, return its height (leaves are at height 0) , its size (number of nodes) and the set of variables appearing in it respectively.  Use map, foldl and other such functions as far as possible wherever you use lists.  
4. Define a suitable representation for substitutions.  
5. Come up with an efficient representation of composition of substitutions. 
6. Define the function subst that given a term t and a substitution s, applies the (Unique Homomorphic Extension of) substitution s to t.  Ensure that subst is efficiently implemented. 
7. Define the function mgu that given two terms t1 and t2, returns their most general unifier, if it exists and otherwise raises an exception NOT_UNIFIABLE.
For each of your programs provide adequate suitable test cases and comment your programs.


**)

open List;;

type variable = string;; (**)

type symbol = string;;

(*The type of both the string and variables is string *)

type term = V of variable | Node of symbol * (term list);;

(** Assuming that the signature is given as a list of pairs of Symbols and arity all the functions are implimented bellow. **)

type signature = (string*int) list;;

let check_positive p = if p>=0 then true else false;;

let get_first (a,b) = a;; 

let get_second (a,b) = b;;

let rec give_symbols l = match l with [] -> [] | x::xs ->  [get_first x]@(give_symbols xs);;  (*Function to give the list a symbols from a signature*)

let rec give_arity l = match l with [] -> [] | x::xs ->  [get_second x]@(give_arity xs);; (*Function to give the list a arities from a signature*)

let rec check_unique l = match l with [] -> true | x::xs -> (not (List.mem x xs)) && (check_unique xs);; (*Function to check the uniqueness of symbol in a signature *)

let rec check_arity l = match l with [] -> true | x::xs -> (check_positive x) && (check_arity xs );;  (*Function to check that all the arities of a given signatutre are non-negative *)

let rec check_sig l = (check_unique (give_symbols l))&& (check_arity (give_arity l)) ;;


(* Examples for check_sig*)
let x1 = [("a",2);("b",3);("c",4);("c",3);("d",11)];;
let x2 = [("a",2);("b",3);("c",4);("e",3);("d",11)];;
let x3 = [("a",2);("b",3);("c",4);("f",-3);("d",11)];;

check_sig x1;;
(*Answer:  - : bool = false*)
check_sig x2;;
(*Answer:  - : bool = true*)
check_sig x3;;
(*Answer:  - : bool = false*)


(** Part 1 Done **)
exception SymbolNotInSignature;;

let rec get_arity_symbol s l = match (s,l) with (s,[]) -> raise SymbolNotInSignature | (s,x::xs) -> match x with (a,b) -> if s=a then b else (get_arity_symbol s xs);; 
(*Function to get arity of a symbol in a signature otherwise it raises an exception *)

let rec wfterm t s = match (t,s) with (V(x),s)-> true | (Node(sym,l),s) -> (List.length l = get_arity_symbol sym s) && (match l with [] -> true | x::xs -> wfterm x s);;



(*Examples for wfterm *)
let sign = [("a1",0);("a2",0);("a3",0);("f3",3);("f1",1);("b1",1);("f2",2) ];;
let ter = Node("f3",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
wfterm ter sign;;
(*Answer: true *)

let ter = Node("f",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
wfterm ter sign;;
(*Answer: Exception: SymbolNotInSignature. *)

let ter = Node("f3",[Node("a1",[]);Node("a2",[]);Node("f3",[Node("a1",[]);Node("a2",[]);Node("a3",[])])]);;
wfterm ter sign;;
(*Answer: true *)

let ter3 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[])]);;
wfterm ter3 sign;;
(*Answer: true *)

let ter4 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[]);V("e") ]);;
wfterm ter4 sign;;
(*Answer: false *)

(** Part 2 Done **)

let rec max_list l = match l with [] -> 0 |[a] -> a | x::xs -> if (x > max_list xs) then x else max_list xs;; (*To get the max element of a list *)

let rec sum_list l = match l with [] -> 0 | x::xs -> x + sum_list xs;; (*To get the sum of elements of a list *)

let rec ht t = match t with V(x) -> 0 | Node(s,[]) -> 0 | Node(s,l) -> (max_list(List.map ht l)) + 1;;

let rec size t = match t with V(x) -> 1 | Node(s,[])-> 1 | Node(s,l) ->(sum_list(List.map size l)) + 1;;

let rec list_concat l = match l with [] -> [] | x::xs -> x@(list_concat xs);; (*To concatinate list of list i.e 'a list list -> 'a list = <fun> *)
 
let rec vars t = match t with V(x) -> [x] | Node(s,[]) -> [] | 
				 Node(s,l) -> list_concat (List.map vars l);;


(*Examples for size,ht,vars *)
let sign = [("a1",0);("a2",0);("a3",0);("f3",3);("f1",1);("b1",1);("f2",2) ];;
let ter = Node("f3",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
ht ter;; size ter;; vars ter;;
(*Answer:
- : int = 1
- : int = 4
- : variable list = [] *)

let ter1 = Node("f",[Node("a1",[]);Node("a2",[]);Node("a3",[])]);;
ht ter1;; size ter1;; vars ter1;;
(*Answer:
- : int = 1
- : int = 4
- : variable list = []
  *)

let ter2 = Node("f3",[V("d");Node("a2",[]);Node("f3",[Node("a1",[]);V("ss");Node("a3",[])])]);;
ht ter2;; size ter2;; vars ter2;;
(*Answer:
- : int = 2
- : int = 5
- : variable list = ["d"; "ss"]
 *)

let ter3 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[])]);;
ht ter3;; size ter3;; vars ter3;;
(*Answer:
- : int = 1
- : int = 3
- : variable list = ["d"]
*)

let ter4 =  Node("f3",[V("d");Node("a2",[]);Node("a3",[]);V("e") ]);;
ht ter4;; size ter4;; vars ter4;;
(*Answer:
- : int = 1
- : int = 3
- : variable list = ["d"; "e"]
*)


let ter5 = Node(("Abs"),[Node((("Mult"),[V("a1"); Node(("Add"),[V("b1");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
ht ter5;; size ter5;; vars ter5;;
(*Answer :
- : int = 6
- : int = 6
- : variable list = ["a1"; "b1"; "x"; "y"; "z"]
*)


				
(** Part 3 Done **)	


type substitution = S of (term*term)list | Composition of substitution list;;	
(** Substitution is a type containg pairs of substitutions and composition is list of substitutions carried out in increasing order of list indices **) 

(** Part 4&5 Done **)

let rec list_replace l e v = match l with []-> [] | x::xs -> if x=e then [v]@(list_replace xs e v) else [x]@(list_replace xs e v);; (*To replace an element e with v in a list l*)

let rec uncurry f a b c = match a with [] -> [] | x::xs -> [f x b c]@(uncurry f xs b c);; 

let rec replace t v w  = if v=w then t else match t with Node(s,[]) -> Node(s,[])
| Node(s,l) -> Node(s,uncurry replace (list_replace l v w) v w) | V(x) -> V(x);; (*To do a single substitution of v with w in a term t*)

let rec subst term s = match s with S [] -> term | 
S(x::xs) -> subst (replace term (get_first x) (get_second x)) (S(xs)) 
| Composition(x::xs) -> (subst (subst (term) (x)) (Composition(xs))) 
| Composition([]) ->term;;

(*Examples for subst *)

let s1 = Composition[S[(V("x"),V("y"))];S[(V("z"),V("t"))];S[(V("s"),V("q"))];S[(V("d"),V("r"))]];;
let s2 = S[(V("a"),V("b"))];;
let t = Node("add",[V("a");Node("add",[V("z");V("b")])]);;
subst t s1;;
(*Answer: - : term = Node ("add", [V "a"; Node ("add", [V "t"; V "b"])]) *)
subst t s2;;
(*Answer: - : term = Node ("add", [V "b"; Node ("add", [V "z"; V "b"])])*)
let t = Node("f3",[V("d");Node("a2",[]);Node("a3",[Node("add",[V("a");Node("add",[V("g");V("b")])])])]);;
subst t s1;;
(*Answer:  - : term = Node ("f3",[V "r"; Node ("a2", []);Node ("a3", [Node ("add", [V "a"; Node ("add", [V "g"; V "b"])])])])*)


(** Part 6 Done  **)

exception NOT_UNIFIABLE;;




let rec mgu t1 t2 = match (t1,t2) with (V(x),V(y)) ->if x=y then S([]) else S([(V(x),V(y))])
| (V(x),Node(s,[])) -> S([(V(x),Node(s,[]))]) 
| (V(x),Node(s,l)) -> if (List.mem x (vars (Node(s,l)))) then raise NOT_UNIFIABLE else S([(V(x),Node(s,l))])
| (Node(s,l),V(x)) -> if (List.mem x (vars (Node(s,l)))) then raise NOT_UNIFIABLE else S([(V(x),Node(s,l))])
| (Node(s,[]),Node(d,[])) -> if s=d then S([]) else raise NOT_UNIFIABLE
| (Node(s,[]),Node(d,l)) -> raise NOT_UNIFIABLE
| (Node(s,l1),Node(d,l2)) -> if s<>d then raise NOT_UNIFIABLE else
							 let unifier=ref (S([])) in
  							 for i=0 to ((List.length l1)-1) do 
  							   unifier:= Composition([!unifier]@[mgu (List.nth l1 i) (List.nth l2 i)])
  							  done;
  							!unifier;;


(**Examples for the Code **)
let e1=Node(("Abs"),[Node((("Mult"),[V("a1"); Node(("Add"),[V("b1");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
let e2=Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
let x = mgu e1 e2;;
(*Answer: val y : substitution =
  Composition
   [S [];
    Composition
     [Composition [S []; S [(V "a1", V "x")]];
      Composition
       [Composition [S []; S [(V "b1", V "y")]];
        Composition
         [S [];
          Composition
           [Composition [S []; S []];
            Composition [Composition [S []; S []]; S []]]]]]]  *)
subst e1 x = subst e2 x;;  (* Answer bool=true *)	

let ex1=Node(("Negate"),[Node((("Mult"),[V("a1"); Node(("Add"),[V("b1");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("x");V("x")])  ]))])])  ]))]) ;;
let ex2=Node(("Negate"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");Node(("Abs"),[Node((("Mult"),[V("x"); Node(("Add"),[V("y");V("z")])  ]))])])  ]))]) ;;
let x= mgu ex1 ex2;;						

(*Answer: val x1 : substitution =
  Composition
   [S [];
    Composition
     [Composition [S []; S [(V "a1", V "x")]];
      Composition
       [Composition [S []; S [(V "b1", V "y")]];
        Composition
         [S [];
          Composition
           [Composition [S []; S []];
            Composition
             [Composition [S []; S [(V "x", V "y")]]; S [(V "x", V "z")]]]]]]]*)

subst ex1 x = subst ex2 x;;  (* Answer bool=true *)	


let t1 = Node("x",[]);;
let t2 = Node("y",[]);;
let x = mgu t1 t2;;
(*Answer: Exception: NOT_UNIFIABLE.*)

let t1 = V("f");;
let t2 = Node("a",[]);;
let x = mgu t1 t2;;
(*Answer: val x : substitution = S [(V "f", Node ("a", []))]*)
subst t1 x = subst t2 x;;  (* Answer bool=true *)	


let t1 = Node("add",[V("a");Node("add",[V("a");V("b")])]);;
let t2 = Node("add",[V("x");Node("add",[V("y");V("z")])]);;
let x = mgu t1 t2;;
(*Answer: val x : substitution =
  Composition
   [Composition [S []; S [(V "a", V "x")]];
    Composition [Composition [S []; S [(V "a", V "y")]]; S [(V "b", V "z")]]]*)
subst t1 x = subst t2 x;;  (* Answer bool=true *)	










