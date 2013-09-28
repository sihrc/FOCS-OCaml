(*
Chris Lee
christopher.lee@students.olin.edu

Assignment 2

To Instructor:
  Simply run ./run to see test cases, or recompile lee_chris_hw0.ml
  Solutions are listed below before section: "PRINT CASES"
*)


(* 
 * Type for regular expressions 
 *
 *)

type regexp = 
    One
  | Zero
  | Char of char
  | Plus of regexp * regexp
  | Concat of regexp * regexp
  | Star of regexp


(*
 * Hook into the OCaml shell to print regular expressions nicely
 *
 *)

let print_regexp rexp = 
  let rec parConcat (rexp) = 
    match rexp with
    | Plus (_,_) -> "("^(to_string rexp)^")"
    | _ -> to_string (rexp)
  and parStar (rexp) = 
    match rexp with
    | Plus (_,_) -> "("^(to_string rexp)^")"
    | Concat (_,_) -> "("^(to_string rexp)^")"
    | _ -> to_string (rexp)
  and to_string (rexp) = 
    match (rexp) with
      One -> "1"
    | Zero -> "0"
    | Char (c) -> Char.escaped c
    | Plus (rexp1, rexp2) -> (to_string rexp1)^"+"^(to_string rexp2)
    | Concat (rexp1,rexp2) -> (parConcat rexp1)^(parConcat rexp2)
    | Star (rexp1) -> (parStar rexp1)^"*"
  in print_string (to_string rexp)
;;


(* 
 * Some sample regular expressions
 *
 *)

let re1 = 
  Concat (Star (Char 'b'), Star (Concat (Char 'a', Star (Char 'b'))))

let re2 = 
  Concat (Star (Char 'a'), 
          Star (Concat (Char 'b', Concat(Char 'a',Star (Char 'a')))))

let re3 = Concat (Star (Char 'b'),
                  Concat (Plus (Char 'a', Char 'b'),
                          Star (Char 'b')))



(*
 * Massive massive ugliness hidden away in a module
 *  (you can pretty much ignore everything between 'module' and 
 *   'end' below)
 *
 * This is all a bunch of helper functions to help simplify a
 * regular expression so that we can reasonably compare two
 * regular expressions for equivalence.
 *
 * Did I mention it was ugly? It is.
 *
 * You don't need to understand this code.
 *
 * It's perfectly fine to simply assume that function 'simplify'
 * given below uses magic, per Arthur C. Clarke's definition.
 *
 *)

module SimplifyHelp : sig val simplify : regexp -> regexp end = 
  struct

    type regexp_alt = 
        A_One
      | A_Zero
      | A_Char of char
      | A_Plus of regexp_alt list
      | A_Concat of regexp_alt * regexp_alt
      | A_Star of regexp_alt

    let rec 
      regexp_to_alt (rexp) = 
        match rexp with
	  One -> A_One
	| Zero -> A_Zero
	| Char c -> A_Char c
	| Plus (rexp1, rexp2) -> A_Plus ((smash rexp1) @ (smash rexp2))
	| Concat (rexp1, rexp2) -> A_Concat (regexp_to_alt rexp1,
  					     regexp_to_alt rexp2)
	| Star rexp1 -> A_Star (regexp_to_alt rexp1)
    and 
      smash (rexp) = 
        match rexp with
	  Plus (rexp1, rexp2) -> (smash rexp1) @ (smash rexp2)
	| r -> [regexp_to_alt r]

    let rec collapseAPlus (l) = 
      match l with
	[] -> raise (Failure "trying to collapse A_Plus []")
      | [_] -> raise (Failure "trying to collapse A_Plus [_]")
      | [r1;r2] -> Plus (alt_to_regexp r1, alt_to_regexp r2)
      | r::rs -> Plus (alt_to_regexp r, collapseAPlus rs)

    and alt_to_regexp (rexp_alt) = 
      match rexp_alt with
	A_One -> One
      | A_Zero -> Zero
      | A_Char c -> Char c
      | A_Plus l -> collapseAPlus l
      | A_Concat (r1, r2) -> Concat (alt_to_regexp r1, alt_to_regexp r2)
      | A_Star (r1) -> Star (alt_to_regexp r1)

    let rec simplifyAlt (rexp_alt) =       
      let rec removeDup (l) = 
	match l with
	  [] -> []
	| r::rs -> if (List.mem r rs) 
        then removeDup rs
        else r::(removeDup rs)  in
      let rec simpAPlus l = 
	match l with
	  [] -> []
	| A_Zero::rs -> simpAPlus rs
	| (A_Plus subl)::rs -> simpAPlus(subl@rs)
	| r::rs -> (simp r)::simpAPlus rs 
      and simp (rexp_alt) = 
	match rexp_alt with
	  A_One -> A_One
	| A_Zero -> A_Zero
	| A_Char (c) -> A_Char (c)
	| A_Plus [] -> A_Zero
	| A_Plus [rexp] -> simp rexp
	| A_Plus l -> A_Plus (List.sort compare (removeDup (simpAPlus l)))
	| A_Concat (A_Zero, rexp2) -> A_Zero
	| A_Concat (rexp1, A_Zero) -> A_Zero
	| A_Concat (A_One, rexp2) -> simp rexp2
	| A_Concat (rexp1, A_One) -> simp rexp1
	| A_Concat (rexp1, rexp2) -> A_Concat (simp rexp1, simp rexp2)
	| A_Star (rexp1) -> A_Star (simp rexp1) in
      let rec loop (rexp) = 
	let s = simp (rexp) 
	in if (s = rexp) 
        then s
	else loop s
      in loop (rexp_alt)

    let simplify rexp = alt_to_regexp (simplifyAlt (regexp_to_alt rexp))

  end




(*
 * Simplify a regular expression
 * (gets rid of +0, and *0, *1, and r + r when r's are equivalent)
 *
 *   regexp -> regexp
 *)

let simplify (rexp) = SimplifyHelp.simplify rexp


(*
 * Check whether two regular expressions are equivalent 
 *
 *  regexp * regexp -> bool
 *)

let equivRE (r1, r2) = (simplify r1 = simplify r2)



(* 
 * Check if a regexp appears in a list using equivalence instead of =
 *
 *  regexp * regexp list -> bool
 *)

let rec memberRE (rexp, l) = 
  match l with
    [] -> false
  | r::rs -> equivRE (rexp,r) || memberRE (rexp,rs)


(* 
 * Append two lists of regexps in such a way as to not produce duplicates
 * if an equivalent regexp appears in both lists
 *
 *  regexp list * regexp list -> regexp list
 *)

let rec unionRE (rs, ss) = 
  match rs with
    [] -> ss
  | r::rs' -> if memberRE (r, ss)
                then unionRE (rs', ss)
              else r::(unionRE (rs', ss))


(*
 * Check if every regexp in the first list is equivalent to a regexp in the
 * second list 
 *
 *  regexp list * regexp list -> bool
 *)

let rec subsetRE (rs, ss) =    
  match rs with
    [] -> true
  | r::rs' -> memberRE (r,ss) && subsetRE (rs',ss)


(* 
 * Compute the empty function of a regular expression
 *
 *  regexp -> regexp
 *)

let rec empty (rexp) =     
  match rexp with
    Zero -> Zero
  | One -> One
  | Char a -> Zero
  | Plus (r1,r2) -> simplify (Plus (empty r1,empty r2))
  | Concat (r1,r2) -> simplify (Concat (empty r1, empty r2))
  | Star _ -> One



(*
 * Compute the derivative of a regular expression
 *
 *  regexp * char -> regexp
 *)

let rec derivative (rexp, a) = 
  match rexp with
    One -> Zero
  | Zero -> Zero
  | Char c -> if (c=a) then One else Zero
  | Plus (r1,r2) -> simplify (Plus (derivative (r1,a), derivative (r2,a)))
  | Concat (r1,r2) -> simplify (Plus (Concat (derivative (r1,a), r2), 
                                      Concat(empty(r1), derivative (r2,a))))
  | Star (r) -> simplify (Concat (derivative (r,a),Star r))



let rec print_regexp_list = function
  |hd::tl -> print_regexp(hd); print_string(","); print_regexp_list(tl)
  |[] -> print_string("")

let rec print_regexp_tuple = function
  |(reg,a,reg2)::tl -> print_string("(");print_regexp(reg); print_string(","); print_char(a); print_string(",");print_regexp(reg2);print_string("), ");print_regexp_tuple(tl)
  |[] -> print_string "";;

let rec append_list = function 
  [],l2 -> l2
  |h::l1, l2 -> h::(append_list(l1,l2));; 


(*  PROVIDE CODE FOR THESE FUNCTIONS FOR QUESTION (3) *)

let rec allDerivativesSym = function
  |hd::tl, c-> unionRE([derivative(hd,c)],allDerivativesSym(tl,c))
  |[],_ -> [];;
  

let rec allDerivatives = function
  |l, hd::tl -> unionRE(allDerivativesSym(l,hd),allDerivatives(l,tl))
  |_, [] -> [];;

let rec recStates = function
    |l1, l2 -> if subsetRE(allDerivatives(l1,l2),l1) then l1 else unionRE(l1,recStates(allDerivatives(l1,l2),l2))

let makeStates (re, l) =
  recStates([re],l);;  
  
let rec makeDeltaSym = function
  |hd::tl, a, l-> if memberRE(derivative(hd,a),l) then (hd,a,derivative(hd,a))::makeDeltaSym(tl,a,l) else makeDeltaSym(tl,a,l)
  |_,_, [] -> []
  |[],_,_ -> []

let rec makeDelta = function
  |l, hd::tl -> append_list(makeDeltaSym(l,hd,l),makeDelta(l,tl))
  |_,[] -> []

let rec makeFinalStates = function
  |[] -> []
  |hd::tl -> if (empty(hd) = One) then hd::makeFinalStates(tl) else makeFinalStates(tl);;
  
type 'a dfa = {
  states  : 'a list;
  alphabet: char list;
  start : 'a;
  delta : ('a * char * 'a) list;
  final   : 'a list
}

let makeDFA (regx, alpha) = 
  {alphabet = alpha;
  states = makeStates(regx,alpha);
  start = regx;
  delta = makeDelta(makeStates(regx,alpha), alpha);
  final = makeFinalStates(makeStates(regx,alpha));
  }

  

(******************** FROM HOMEWORK 1 ***********************)
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
printList(language(dfa,n));;


(************************** TEST CASES *****************************)(*
(* Number 3 Part a *)
print_string("\n===================\nNumber 3 :: Part a\n===================\n");;

let case = allDerivativesSym([re1;re2],'a');;
print_string("Case 1:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = allDerivativesSym([re1;re2],'b');;
print_string("Case 2:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = allDerivativesSym([re1;re2;re1],'b');;
print_string("Case 3:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = allDerivativesSym([re1;re2;re3],'a');;
print_string("Case 4:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = allDerivativesSym([re1;re2;re3],'b');;
print_string("Case 5:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

(* Number 3 Part b *)
print_string("\n===================\nNumber 3 :: Part b\n===================\n");;

let case = allDerivatives([re1],['a';'b']);;
print_string("Case 1:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = allDerivatives([re1;re2],['a';'b']);;
print_string("Case 2:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = allDerivatives([re1;re2;re1],['a';'b']);;
print_string("Case 3:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = allDerivatives([re1;re2;re3],['a';'b']);;
print_string("Case 4:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;


(* Number 3 Part c *)
print_string("\n===================\nNumber 3 :: Part c\n===================\n");;

let case = makeStates(re1,['a';'b']);;
print_string("Case 1:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = makeStates(re2,['a';'b']);;
print_string("Case 2:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = makeStates(re3,['a';'b']);;
print_string("Case 3:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

(* Number 3 Part d *)
print_string("\n===================\nNumber 3 :: Part d\n===================\n");;

let case = makeDelta(makeStates(re1,['a';'b']),['a';'b']);;
print_string("Case 1:\n\tregexp list = [ ");;print_regexp_tuple(case);;print_string("]\n");;

let case = makeDelta(makeStates(re2,['a';'b']),['a';'b']);;
print_string("Case 2:\n\tregexp list = [ ");;print_regexp_tuple(case);;print_string("]\n");;

let case = makeDelta(makeStates(re3,['a';'b']),['a';'b']);;
print_string("Case 3:\n\tregexp list = [ ");;print_regexp_tuple(case);;print_string("]\n");;


(* Number 3 Part e *)
print_string("\n===================\nNumber 3 :: Part e\n===================\n");;

let case = makeFinalStates(makeStates(re1,['a';'b']));;
print_string("Case 1:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = makeFinalStates(makeStates(re2,['a';'b']));;
print_string("Case 2:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;

let case = makeFinalStates(makeStates(re3,['a';'b']));;
print_string("Case 3:\n\tregexp list = [ ");;print_regexp_list(case);;print_string("]\n");;


(* Number 3 Part f *)
print_string("\n===================\nNumber 3 :: Part f\n===================\n");;

let case = makeDFA(re1,['a';'b']);;
print_string("Case 1:\n\t ");;printLanguage(case,5);;print_string("\n");;

let case = makeDFA(re2,['a';'b']);;
print_string("Case 2:\n\t ");;printLanguage(case,5);;print_string("\n");;

let case = makeDFA(re3,['a';'b']);;
print_string("Case 3:\n\t ");;printLanguage(case,5);;print_string("\n");;

*)