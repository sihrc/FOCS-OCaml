(*
Chris Lee
christopher.lee@students.olin.edu

Assignment 1

To Instructor:
  Simply run ./run to see test cases, or recompile lee_chris_hw0.ml
  Solutions are listed below before section: "PRINT CASES"
*)



type 'a dfa = {
	states	:	'a list;
	alphabet:	char list;
	start	:	'a;
	delta	:	('a * char * 'a) list;
	final 	:	'a list
}

let explode (str) = 
  let rec acc (index,result) = 
  if (index<0) then
	result
	else
 	acc(index-1, (String.get str index)::result)
	in
	acc(String.length(str)-1, [])

let implode (cs) = 
  let str = String.create(List.length(cs)) in
  let rec loop (cs,index) = 
  match cs with
  [] -> str
  | c::cs -> (String.set str index c; loop(cs,index+1))
in
loop(cs,0)

exception DFAError of string

exception Unimplemented of string

let transitionError (input) = 
  raise (DFAError("Cannot transition on input "^(implode [input])))

let isolatedBs =              
{alphabet = ['a'; 'b'];       
states = ["start"; "readb"; "sink"];
start = "start";
delta = [("start", 'a', "start");
("start", 'b', "readb");
("readb", 'a', "start");
("readb", 'b', "sink"); 
("sink", 'a', "sink");
("sink", 'b', "sink")];
final = ["start";"readb"]}


let asThenBs =                (* language: strings of a's followed by b's *)
{states = ["eata"; "eatb"; "sink"];
alphabet = ['a'; 'b'];
start = "eata";
delta = [("eata", 'a', "eata");
("eata", 'b', "eatb");
("eatb", 'a', "sink");
("eatb", 'b', "eatb");
("sink", 'a', "sink");
("sink", 'b', "sink")];
final = ["eata"; "eatb"]}


let aStar =                    (* language: all strings of a's *)
{alphabet= ['a'; 'b'];
states= ["ok"; "sink"];
start= "ok";
delta = [("ok",   'a', "ok");
("ok",   'b', "sink");
("sink", 'a', "sink");
("sink", 'b', "sink")];
final = ["ok"]}


let bPlus =                     (* language: all nonempty strings of b's *)
{alphabet= ['a'; 'b'];
states= ["start"; "ok"; "sink"];
start= "start";
delta = [("start", 'b', "ok");
("start", 'a', "sink");
("ok",    'b', "ok");
("ok",    'a', "sink");
("sink",  'b', "sink");
("sink",  'a', "sink")];
final = ["ok"]}

let abaStar =              (* language: any number of ab's followed by a's *)
{alphabet= ['a'; 'b'];
states= ["astate"; "bstate"; "aonly"; "sink"];
start= "astate";
delta = [("astate", 'a', "bstate");
("astate", 'b', "sink");
("bstate", 'a', "aonly");
("bstate", 'b', "astate");
("aonly",  'a', "aonly");
("aonly",  'b', "sink");
("sink",   'a', "sink");
("sink",   'b', "sink")];
final = ["astate"; "bstate"; "aonly"]}

let strings (alphabet, n) = 
  let rec mapCons (c, ls) = 
  match ls with
  [] -> []
  | l::ls' -> (c::l)::mapCons(c,ls')  in
  let rec mapConsSet (alphabet, l) = 
  match alphabet with
  [] -> []
  | c::cs -> mapCons(c,l) @ mapConsSet(cs,l)  in
  let rec mapImplode (css) = 
  match css with
  [] -> []
  | (cs::css) -> (implode cs)::mapImplode(css)  in
  let rec strings' (n) = 
  if (n<=0) then
  [[]]
else let s = strings'(n-1) in
[] :: mapConsSet(alphabet,s)
in 
mapImplode(strings'(n))

(**************************************************************************)
(**************************************************************************)
(************************		SOLUTIONS 		***************************)
(************************		  BEGIN			***************************)
(************************		   ERE			***************************)
(**************************************************************************)
(**************************************************************************)

(*************************************************************)
(*						Question 2							 *)
(*************************************************************)

(*
 *  isFinal : 'a dfa * 'a -> bool
 *
 *    isFinal(dfa,q) should return true if and only if 'q' is a final state
 *    in the DFA 'dfa'
 *
*)
let rec checkElement = function
	[],_ -> false
	|hd::tl, s -> if hd = s then true else checkElement(tl,s)

let rec isFinal (dfa, state) = 
	checkElement(dfa.final,state);;
(* 
 *  transition : 'a dfa * 'a * char -> 'a
 *
 *    transition(dfa,q,a) should return the state obtained by reading input
 *    symbol 'a' in state 'q' in the DFA 'dfa'
 *
 *  PROVIDE CODE FOR THIS FUNCTION FOR QUESTION (2) 
 *
*)
let rec checktrans = function
	((a,b,c)::tl,d,e) -> if (a = d && b = e) then c else checktrans(tl,d,e)


let transition (dfa,state,input) = 
	checktrans(dfa.delta,state,input);;
 
(*
 *  extendedTransition : 'a dfa * 'a * char list -> 'a
 *
 *    extendedTransition(dfa,q,cs) should return the state obtained by
 *    reading the list of input symbols in 'cs' from state 'q' in the DFA
 *    'dfa'
 *
 *  PROVIDE CODE FOR THIS FUNCTION FOR QUESTION (2) 
 *
*)

let rec extendedTransition = function
	|dfa,state,hd::tl -> extendedTransition(dfa,transition(dfa,state,hd),tl)
	|dfa,state,[] -> state

(*
 *  accept : 'a dfa * string -> bool
 *
 *    accept(dfa,input) should return true if and only the input string
 *    'input' is accepted by the DFA 'dfa'
 *
 *  PROVIDE CODE FOR THIS FUNCTION FOR QUESTION (2) 
 *
*)

let accept (dfa,s) = 
	isFinal(dfa,extendedTransition(dfa,dfa.start,explode(s)));;
 

(* 
 *  Compute the language of a DFA, restricted to inputs of length <= n
 *   language(dfa,n) returns a list of strings accepted by dfa
 *   printLanguage(dfa,n) prints the strings accepted by dfa
 *
*)

let language (dfa, n) = 
  let candidates = strings(dfa.alphabet, n) in
  let rec tryAll (l) = 
  match l with
  [] -> []
  | s::ss -> if (accept(dfa,s)) then
  s::(tryAll ss)
else
 tryAll ss
in
tryAll(candidates)


let printLanguage (dfa,n) = 
  let rec printList (l) = 
  match l with 
  [] -> ()
  | s::ss -> (print_string "   ";
    if (s="") then
    print_string "<empty>"
  else
  print_string s; 
  print_newline(); 
printList ss)
in
printList(language(dfa,n))


(*************************************************************)
(*						Question 3							 *)
(*************************************************************)

(*Question 3 part a *)
let rec member = function
	_, [] -> false
	|s, hd::tl-> if hd = s then true else member(s,tl)

(*Question 3 part b *)

let rec difference = function
	|[],[] -> []
	|[], l -> []
	|l,[] -> l
	|hd::tl, l2 -> if member(hd,l2) then difference(tl,l2) else hd::difference(tl,l2)

(*Question 3 part c *)
let rec append_list = function 
	[],l2 -> l2
	|h::l1, l2 -> h::(append_list(l1,l2));;	

let rec tuple_map = function
	|a,[] -> []
	|a, hd::tl -> (a,hd)::tuple_map(a,tl)

let rec cross = function
	[],l -> []
	|l,[] -> []
	|hd::tl, l -> append_list(tuple_map(hd,l),cross(tl,l))
	

(*Question 3 part d *)

let compl dfa =              
	{alphabet = dfa.alphabet;       
	states = dfa.states;
	start = dfa.start;
	delta = dfa.delta;
	final = difference(dfa.states,dfa.final)};;

(*Question 3 part e *)
let rec same = function
	|[],[] -> []
	|[],l -> []
	|l,[] -> l
	|hd::tl, l -> if member(hd,l) then hd::same(tl,l) else same(tl,l)

let rec crossdelta = function
	|[] -> []
	|((a,b,c),(d,e,f))::tl -> if b = e then ((a,d),b,(c,f))::crossdelta(tl) else crossdelta(tl)

let inter (dfa1, dfa2) = 
	{alphabet = same(dfa1.alphabet,dfa2.alphabet);
	states = cross(dfa1.states,dfa2.states);
	start = (dfa1.start,dfa2.start);
	delta = crossdelta(cross(dfa1.delta,dfa2.delta));
	final = cross(dfa1.final, dfa2.final);
	}

(*Question 3 part f *)

let union (dfa1, dfa2) =
	compl(inter(compl(dfa1),compl(dfa2)));;

(* PRINT FUNCTIONS *)
let print_bool a = 
	if a = true then print_string "true" else print_string "false";;

let rec print_int_list = function 
	[] -> ()
	| e::l -> print_int e ; print_string " " ; print_int_list l;;
 
let rec print_intint_list = function 
	[] -> ()
	| (a,b)::l -> print_string "("; print_int a; print_string ",";print_int b; print_string ")"; print_string " " ; print_intint_list l;;
 
let rec print_stringint_list = function 
	[] -> ()
	| (a,b)::l -> print_string "("; print_string a; print_string ",";print_int b; print_string ")"; print_string " " ; print_stringint_list l;;
 
let rec print_intchar_list = function 
	[] -> ()
	| (a,b)::l -> print_string "("; print_int a; print_string ",";print_char b; print_string ")"; print_string " " ; print_intchar_list l;;



(* PRINT CASES *)

 (* Number 2 Part a *)
print_string("\n===================\nNumber 2 :: Part a\n===================\n");;

 let case1 = isFinal(isolatedBs,"start");;
print_string("Case 1:\n\t bool = ");;print_bool(case1);;print_string("\n");;

 let case2 = isFinal(isolatedBs,"readb");;
print_string("Case 2:\n\t bool = ");;print_bool(case2);;print_string("\n");;

let case3 = isFinal(isolatedBs,"sink");;
print_string("Case 3:\n\t bool = ");;print_bool(case3);;print_string("\n");;

(* Number 2 Part b *)
print_string("\n===================\nNumber 2 :: Part b\n===================\n");;

let case1 = transition(isolatedBs,"start",'a');;
print_string("Case 1:\n\t string = ");;print_string(case1);;print_string("\n");;

let case2 = transition(isolatedBs,"start",'b');;
print_string("Case 2:\n\t string = ");;print_string(case2);;print_string("\n");;

let case3 = transition(isolatedBs,"readb",'a');;
print_string("Case 3:\n\t string = ");;print_string(case3);;print_string("\n");;

let case4 = transition(isolatedBs,"readb",'b');;
print_string("Case 4:\n\t string = ");;print_string(case4);;print_string("\n");;

(* Number 2 Part c *)
print_string("\n===================\nNumber 2 :: Part c\n===================\n");;

let case1 = extendedTransition(isolatedBs,"start",[]);;
print_string("Case 1:\n\t string = ");;print_string(case1);;print_string("\n");;

let case2 = extendedTransition(isolatedBs,"start",['b']);;
print_string("Case 2:\n\t string = ");;print_string(case2);;print_string("\n");;

let case3 = extendedTransition(isolatedBs,"start",['a';'a';'b';'a']);;
print_string("Case 3:\n\t string = ");;print_string(case3);;print_string("\n");;

let case4 = extendedTransition(isolatedBs,"start",['a';'a';'b';'b';'a']);;
print_string("Case 4:\n\t string = ");;print_string(case4);;print_string("\n");;

(* Number 2 Part d *)
print_string("\n===================\nNumber 2 :: Part d\n===================\n");;

let case1 = accept(isolatedBs,"aaaaaa");;
print_string("Case 1:\n\t bool = ");;print_bool(case1);;print_string("\n");;

let case2 = accept(isolatedBs,"aaaaab");;
print_string("Case 2:\n\t bool = ");;print_bool(case2);;print_string("\n");;

let case3 = accept(isolatedBs,"aaabab");;
print_string("Case 3:\n\t bool = ");;print_bool(case3);;print_string("\n");;

let case4 = accept(isolatedBs,"aaabbb");;
print_string("Case 3:\n\t bool = ");;print_bool(case4);;print_string("\n");;

(*printLanguage(isolatedBs,6);;*)
(*printLanguage(asThenBs,6);;*)

(* Number 3 Part a *)
print_string("\n===================\nNumber 3 :: Part a\n===================\n");;

let case1 = member(3,[]);;
print_string("Case 1:\n\t bool = ");;print_bool(case1);;print_string("\n");;

let case2 = member(3,[2;1]);;
print_string("Case 2:\n\t bool = ");;print_bool(case2);;print_string("\n");;

let case3 = member(3,[2;3;1]);;
print_string("Case 3:\n\t bool = ");;print_bool(case3);;print_string("\n");;

(* Number 3 Part a *)
print_string("\n===================\nNumber 3 :: Part b\n===================\n");;

let case = difference([],[3;4;5]);;
print_string("Case 1:\n\tint list = [ ");;print_int_list(case);;print_string("]\n");;

let case = difference([1],[3;4;5]);;
print_string("Case 2:\n\tint list = [ ");;print_int_list(case);;print_string("]\n");;

let case = difference([1;2;3;4],[3;4;5]);;
print_string("Case 3:\n\tint list = [ ");;print_int_list(case);;print_string("]\n");;

let case = difference([3;4],[3;4;5]);;
print_string("Case 4:\n\tint list = [ ");;print_int_list(case);;print_string("]\n");;
	

(* Number 3 Part c *)
print_string("\n===================\nNumber 3 :: Part c\n===================\n");;

let case = cross([],[]);;
print_string("Case 1:\n\t(int * int) list = \n\t\t[ ");;print_intint_list(case);;print_string("]\n");;

let case = cross([1],[10;20]);;
print_string("Case 2:\n\t(int * int) list = \n\t\t[ ");;print_intint_list(case);;print_string("]\n");;

let case = cross([1;2;3],[10;20]);;
print_string("Case 3:\n\t(int * int) list = \n\t\t[ ");;print_intint_list(case);;print_string("]\n");;

let case = cross(["hello"],[10;20]);;
print_string("Case 4:\n\t(string * int) list = \n\t\t[ ");;print_stringint_list(case);;print_string("]\n");;

let case = cross(["hello";"world"],[10;20;30]);;
print_string("Case 5:\n\t(string * int) list = \n\t\t[ ");;print_stringint_list(case);;print_string("]\n");;

let case = cross([1;2;3;4;5],['a';'b';'c';'d';'e']);;
print_string("Case 6:\n\t(int * char) list = \n\t\t[ ");;print_intchar_list(case);;print_string("]\n");;

(* Number 3 Part d *)
print_string("\n===================\nNumber 3 :: Part d\n===================\n");;

let case = compl(isolatedBs);;
print_string("\n\tPolymorphic print please? printLanguage commented out\n");;
(* printLanguage(case,6);; *)

(* Number 3 Part e *)
print_string("\n===================\nNumber 3 :: Part e\n===================\n");;
print_string("Case 1: \n");;

printLanguage(inter(isolatedBs,compl(isolatedBs)),10);;
print_string("Case 2: \n");
printLanguage(inter(isolatedBs,asThenBs),10);;

(* Number 3 Part f *)
print_string("\n===================\nNumber 3 :: Part f\n===================\n");;
print_string("Case 1: \n");;

printLanguage(union(isolatedBs,compl(isolatedBs)),4);;
