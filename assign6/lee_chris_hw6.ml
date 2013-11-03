	(* 
Chris Lee
christopher.lee@students.olin.edu

Assignment 5

#use "lee_chris_hw6.ml";;
 run (binary_sum ()) ""
 *)


let fail s = raise (Failure s)

(* 
 * String to Characters utility functions:
 *   explode : string -> char list
 *      returns the list of characters making up a string
 *   implode : char list -> string
 *      concatenates the list of characters into a string
 *
 *)

let explode str = 
  let rec loop index result = 
    if (index<0) then result
    else loop (index-1) ((String.get str index)::result)  in
  loop (String.length str - 1) []

let implode (cs) = 
  let str = String.create(List.length(cs))  in
  (List.iteri (String.set str) cs; str)

(*
 * Type for deterministic Turing machines
 *
 * Parameterized by type for states
 *)

type direction = Left | Right

type 'a turing = { states : 'a list;
		   input_alph : char list;
		   tape_alph : char list;
		   leftmost : char;
		   blank : char;
		   delta : ('a * char) -> ('a * char * direction);
		   start : 'a;
		   accept : 'a;
		   reject : 'a }


(*
 * Print a configuration (including newline) to standard output
 * 
 *)

let print_config m (u,q,v) = 
  let string cs =
    let str = String.make (List.length(cs) * 2) ' '  in
    let put i = String.set str (i*2)  in
    (List.iteri put cs; str)  in
  Printf.printf "  %s(%s) %s\n" (string u) q (string v)

(*
 * IMPLEMENT THE FOLLOWING FUNCTIONS FOR QUESTION 2
 *
 *)

let starting_config m w = ([], m.start, '>'::(explode w));;

let accepting_config m c = match c with (_,q,_) -> q = m.accept;;

let rejecting_config m c = match c with (_,q,_) -> q = m.reject;;

let halting_config m c = accepting_config m c || rejecting_config m c;;

let step_config m c = 
	match c with (p,q1,s) ->
		match m.delta (q1,List.hd s) with
			(q2, c, Right) -> let next = if (List.length s) = 1 then [m.blank] else (List.tl s) in
							(p@[c], q2, next)
			|(q2, c, Left) -> let before = List.rev p in
							(List.rev (List.tl before), q2, (List.hd before)::c::(List.tl s));;

let rec step_through m c = 
	print_config m c;
	if not (halting_config m c)
		then step_through m (step_config m c)
	else
		c;;

let run m w = 
	let res = accepting_config m (step_through m (starting_config m w)) in
	if res then
		Printf.printf "Accepting %s\n" w
	else
		Printf.printf "Rejecting %s\n" w; 
	res;;
	

(* 
if accepting_config m res
		then Printf.printf "Accepting %s\n" w
else
		Printf.printf "Rejecting %s\n" w *)



(* 
 * Some sample deterministic Turing machines
 *
 * asbs is the regular language {a^m b^n | m,n >= 0}
 * anbn is the context-free language {a^n b^n | n >= 0}
 * anbncn is the non-context-free language {a^n b^n c^n | n >= 0}
 *
 *)

let asbs = { states = ["start"; "q1"; "acc"; "rej"];
	     input_alph = ['a';'b'];
	     tape_alph = ['a';'b';'_';'>'];
	     blank = '_';
	     leftmost = '>';
	     start = "start";
	     accept = "acc";
	     reject = "rej";
	     delta = fun (q,a) -> 
                       match (q,a) with
                       | ("start", 'a') -> ("start", 'a', Right)
     	               | ("start", 'b') -> ("q1", 'b', Right)
		       | ("start", '>') -> ("start", '>', Right)
		       | ("start", '_') -> ("acc", '_', Right)
		       | ("q1", 'a') -> ("rej", 'a', Right)
		       | ("q1", 'b') -> ("q1", 'b', Right)
		       | ("q1", '>') -> ("rej", '>', Right)
		       | ("q1", '_') -> ("acc", '_', Right)
		       | ("acc", sym) -> ("acc", sym, Right)
		       | ("rej", sym) -> ("rej", sym, Right)
		       | _ -> fail "Undefined transition" }

let anbn = { states = ["start"; "q1"; "q2"; "q3"; "q4"; "acc"; "rej"];
	     input_alph = ['a';'b'];
	     tape_alph = ['a';'b';'X';'_';'>'];
	     blank = '_';
	     leftmost = '>';
	     start = "start";
	     accept = "acc";
	     reject = "rej";
	     delta = fun (q,a) -> 
	               match (q,a) with
		       | ("start", 'a') -> ("start", 'a', Right)
     	       | ("start", 'b') -> ("q1", 'b', Right)
		       | ("start", '>') -> ("start", '>', Right)
		       | ("start", '_') -> ("q2", '_', Right)
		       | ("start", 'X') -> ("rej", 'X', Right)
		       | ("q1", 'b') -> ("q1", 'b', Right)
		       | ("q1", '_') -> ("q2", '_', Right)
		       | ("q1", sym) -> ("rej", sym, Right)
		       | ("q2", '>') -> ("q3", '>', Right)
		       | ("q2", sym) -> ("q2", sym, Left)
		       | ("q3", 'X') -> ("q3", 'X', Right)
		       | ("q3", '_') -> ("acc", '_', Right)
		       | ("q3", 'a') -> ("q4", 'X', Right)
		       | ("q3", sym) -> ("rej", sym, Right)
		       | ("q4", 'a') -> ("q4", 'a', Right)
		       | ("q4", 'X') -> ("q4", 'X', Right)
		       | ("q4", 'b') -> ("q2", 'X', Right)
		       | ("q4", sym) -> ("rej", sym, Right)
		       | ("acc", sym) -> ("acc", sym, Right)
		       | ("rej", sym) -> ("rej", sym, Right)
		       | _ -> fail "Undefined transition" }

let anbncn = { states = ["start";"q1";"q2";"q3";"q4";"q5";"q6";"acc";"rej"];
	       input_alph = ['a';'b';'c'];
	       tape_alph = ['a';'b';'c';'X';'_';'>'];
	       blank = '_';
	       leftmost = '>';
	       start = "start";
	       accept = "acc";
	       reject = "rej";
	       delta = fun (q,a) -> 
	         match (q,a) with
		 | ("start", 'a') -> ("start", 'a', Right)
     	         | ("start", 'b') -> ("q1", 'b', Right)
		 | ("start", 'c') -> ("q6", 'c', Right)
		 | ("start", '>') -> ("start", '>', Right)
		 | ("start", '_') -> ("q2", '_', Right)
		 | ("start", 'X') -> ("rej", 'X', Right)
		 | ("q1", 'b') -> ("q1", 'b', Right)
		 | ("q1", 'c') -> ("q6", 'c', Right)
		 | ("q1", '_') -> ("q2", '_', Right)
		 | ("q1", sym) -> ("rej", sym, Right)
		 | ("q2", '>') -> ("q3", '>', Right)
		 | ("q2", sym) -> ("q2", sym, Left)
		 | ("q3", 'X') -> ("q3", 'X', Right)
		 | ("q3", '_') -> ("acc", '_', Right)
		 | ("q3", 'a') -> ("q4", 'X', Right)
		 | ("q3", sym) -> ("rej", sym, Right)
		 | ("q4", 'a') -> ("q4", 'a', Right)
		 | ("q4", 'X') -> ("q4", 'X', Right)
		 | ("q4", 'b') -> ("q5", 'X', Right)
		 | ("q4", sym) -> ("rej", sym, Right)
		 | ("q5", 'b') -> ("q5", 'b', Right)
		 | ("q5", 'X') -> ("q5", 'X', Right)
		 | ("q5", 'c') -> ("q2", 'X', Right)
		 | ("q5", sym) -> ("rej", sym, Right)
		 | ("q6", 'c') -> ("q6", 'c', Right)
		 | ("q6", '_') -> ("q2", '_', Right)
		 | ("q6", sym) -> ("rej", sym, Right)
		 | ("acc", sym) -> ("acc", sym, Right)
		 | ("rej", sym) -> ("rej", sym, Right)
		 | _ -> fail "Undefined transition" }



(* 
 * The type for a DFA, parameterized by the type for the states 
 *
 *)

type 'a dfa = {states_d :   'a list;
    	       alphabet_d : char list;
	       start_d :    'a;
   	       delta_d :    ('a * char * 'a) list;
	       final_d :    'a list}



(*
 * Some sample DFAs
 *
 * isolatedBs: all strings where every b is bracketed by a's
 * asThenBs: strings of a's followed by b's
 *
 *)

let isolatedBs =    
  {alphabet_d = ['a'; 'b'];   
   states_d = ["start"; "readb"; "sink"];
   start_d = "start";
   delta_d = [("start", 'a', "start");
            ("start", 'b', "readb");
            ("readb", 'a', "start");
            ("readb", 'b', "sink"); 
            ("sink", 'a', "sink");
            ("sink", 'b', "sink")];
   final_d = ["start";"readb"]}

let asThenBs =              
    {states_d = ["start"; "matchb"; "sink"];
     alphabet_d = ['a'; 'b'];
     start_d = "start";
     delta_d = [("start", 'a', "start");
              ("start", 'b', "matchb");
              ("matchb", 'a', "sink");
              ("matchb", 'b', "matchb");
              ("sink", 'a', "sink");
              ("sink", 'b', "sink")];
     final_d = ["start"; "matchb"]}


(* 
 * IMPLEMENT THE FOLLOWING FUNCTIONS FOR QUESTION 3
 *
 *)

let reject_state dfa = 
	let deltas = List.filter (fun delta -> match delta with (s,_,s') -> s = s') dfa.delta_d in
	let all = List.flatten (List.map (fun alpha -> List.fold_right (fun x xs -> match x with (q,s,_) -> if s = alpha then q::xs else xs) deltas []) dfa.alphabet_d) in
	List.filter (fun x -> List.length (List.filter (fun a -> a = x) all) = List.length dfa.alphabet_d) dfa.states_d;;

let add_epsilon dfa =
	let rejs = reject_state dfa in
	dfa.delta_d
	@(List.map (fun x -> (x,'_',"acc")) dfa.final_d)
	@(List.map (fun x -> ("acc",x,"acc")) dfa.alphabet_d)
	@(List.map (fun x -> (x, '_', "rej")) rejs);;
	


let rec turing_delta deltas (state,symbol) = 
	match deltas with 
	[] -> (state,symbol,Right)
	|(q1,s,q2)::tl -> if (q1 = state && s = symbol) then (q2,symbol,Right) else turing_delta tl (state,symbol);;



 let turing_DFA dfa = 
	{	
		states = "acc"::"rej"::dfa.states_d;
		input_alph = dfa.alphabet_d;
		tape_alph = '_'::'>'::dfa.alphabet_d;
		leftmost = '>';
		blank = '_';
		delta = turing_delta (add_epsilon dfa);
		start = dfa.start_d;
		accept = "acc";
		reject = "rej";
	};;

let binary_sum () = 
	{
		states = ["11w3"; "cback"; "01n3"; "00wc3"; "11n3"; "11wc3"; "00n3"; "q1"; "1c2"; "q3"; "q2"; "q5"; "q4"; "0c2"; "10c3"; "01wc3"; "10wc3"; "rej"; "start"; "00w3"; "11c3"; "01w3"; "0w2"; "1n2"; "0n2"; "10n3"; "nback"; "1wc2"; "1w2"; "acc"; "c"; "10w3"; "n"; "0wc2"; "01c3"; "00c3"];
		input_alph = ['0';'1';'#'];
		tape_alph = ['0';'1';'#';'>';'_'];
		leftmost = '>';	
		blank = '_';
		start = "start";
		accept = "acc";
		reject = "rej";
		delta = fun (q,a) -> match (q,a) with 
		| ("start", '>') -> ("start",'<',Right)
		| ("start", '0') -> ("q1",'0',Right)
		| ("start", '1') -> ("q1",'1',Right)
		| ("start", sym) -> ("rej",sym,Right)
		| ("q1", '0') -> ("q1",'0',Right)
		| ("q1", '1') -> ("q1",'1',Right)
		| ("q1", '#') -> ("q2",'#',Right)
		| ("q1", sym) -> ("rej",sym,Right)
		| ("q2", '0') -> ("q3",'0',Right)
		| ("q2", '1') -> ("q3",'1',Right)
		| ("q2", sym) -> ("rej",sym,Right)
		| ("q3", '0') -> ("q3",'0',Right)
		| ("q3", '1') -> ("q3",'1',Right)
		| ("q3", '#') -> ("q4",'#',Right)
		| ("q3", sym) -> ("rej",sym,Right)
		| ("q4", '0') -> ("q5",'0',Right)
		| ("q4", '1') -> ("q5",'1',Right)
		| ("q4", sym) -> ("rej",sym,Right)
		| ("q5", '0') -> ("q5",'0',Right)
		| ("q5", '1') -> ("q5",'1',Right)
		| ("q5", '_') -> ("n",'_',Left)
		| ("q5", sym) -> ("rej",sym,Right)
		| ("n", '0') -> ("0w2",'_', Left) 
		| ("n", '1') -> ("1w2",'_', Left)
		| ("n", '#') -> ("acc",'#', Left)
		| ("n", '_') -> ("n",'_', Left)
		| ("n", sym) -> ("rej",sym, Right)
		| ("0w2", '0') -> ("0w2",'0', Left) 
		| ("0w2", '1') -> ("0w2",'1', Left)
		| ("0w2", '#') -> ("0n2",'#', Left)
		| ("0w2", sym) -> ("rej",sym, Right)
		| ("1w2", '0') -> ("1w2",'0', Left) 
		| ("1w2", '1') -> ("1w2",'1', Left)
		| ("1w2", '#') -> ("1n2",'#', Left)
		| ("1w2", sym) -> ("rej",sym, Right)
		| ("0n2", '0') -> ("00w3",'#',Left)
		| ("0n2", '1') -> ("01w3",'#',Left)
		| ("0n2", '#') -> ("0n2",'#',Left)
		| ("0n2", sym) -> ("rej",sym, Right)
		| ("1n2", '0') -> ("10w3",'#',Left)
		| ("1n2", '1') -> ("11w3",'#',Left)
		| ("1n2", '#') -> ("1n2",'#',Left)
		| ("1n2", sym) -> ("rej",sym, Right)
		| ("00w3", '0') -> ("00w3",'0', Left) 
		| ("00w3", '1') -> ("00w3",'1', Left)
		| ("00w3", '#') -> ("00n3",'#', Left)
		| ("00w3", sym) -> ("rej",sym, Right)
		| ("01w3", '0') -> ("01w3",'0', Left) 
		| ("01w3", '1') -> ("01w3",'1', Left)
		| ("01w3", '#') -> ("01n3",'#', Left)
		| ("01w3", sym) -> ("rej",sym, Right)
		| ("10w3", '0') -> ("10w3",'0', Left) 
		| ("10w3", '1') -> ("10w3",'1', Left)
		| ("10w3", '#') -> ("10n3",'#', Left)
		| ("10w3", sym) -> ("rej",sym, Right)
		| ("11w3", '0') -> ("11w3",'0', Left) 
		| ("11w3", '1') -> ("11w3",'1', Left)
		| ("11w3", '#') -> ("11n3",'#', Left)
		| ("11w3", sym) -> ("rej",sym, Right)
		| ("00n3", '0') -> ("nback",'#',Left)
		| ("00n3", '#') -> ("00n3",'#',Left)
		| ("00n3", '>') -> ("nback",'>',Right)
		| ("00n3", sym) -> ("rej",sym, Right)
		| ("01n3", '1') -> ("cback",'#',Left)
		| ("01n3", '#') -> ("01n3",'#',Left)
		| ("01n3", '>') -> ("nback",'>',Right)
		| ("01n3", sym) -> ("rej",sym, Right)
		| ("10n3", '1') -> ("nback",'#',Left)
		| ("10n3", '#') -> ("10n3",'#',Left)
		| ("10n3", '>') -> ("nback",'>',Right)
		| ("10n3", sym) -> ("rej",sym, Right)
		| ("11n3", '0') -> ("nback",'#',Left)
		| ("11n3", '#') -> ("11n3",'#',Left)
		| ("11n3", '>') -> ("nback",'>',Right)
		| ("11n3", sym) -> ("rej",sym, Right)
		| ("c", '0') -> ("0wc2",'_', Left) 
		| ("c", '1') -> ("1wc2",'_', Left)
		| ("c", '#') -> ("acc",'#', Left)
		| ("c", '_') -> ("c",'_', Left)
		| ("c", sym) -> ("rej",sym, Right)
		| ("0wc2", '0') -> ("0wc2",'0', Left) 
		| ("0wc2", '1') -> ("0wc2",'1', Left)
		| ("0wc2", '#') -> ("0c2",'#', Left)
		| ("0wc2", sym) -> ("rej",sym, Right)
		| ("1wc2", '0') -> ("1wc2",'0', Left) 
		| ("1wc2", '1') -> ("1wc2",'1', Left)
		| ("1wc2", '#') -> ("1c2",'#', Left)
		| ("1wc2", sym) -> ("rej",sym, Right)
		| ("0c2", '0') -> ("00wc3",'#',Left)
		| ("0c2", '1') -> ("01wc3",'#',Left)
		| ("0c2", '#') -> ("0c2",'#',Left)
		| ("0c2", sym) -> ("rej",sym, Right)
		| ("1c2", '0') -> ("10wc3",'#',Left)
		| ("1c2", '1') -> ("11wc3",'#',Left)
		| ("1c2", '#') -> ("1c2",'#',Left)
		| ("1c2", sym) -> ("rej",sym, Right)
		| ("00wc3", '0') -> ("00wc3",'0', Left) 
		| ("00wc3", '1') -> ("00wc3",'1', Left)
		| ("00wc3", '#') -> ("00c3",'#', Left)
		| ("00wc3", sym) -> ("rej",sym, Right)
		| ("01wc3", '0') -> ("01wc3",'0', Left) 
		| ("01wc3", '1') -> ("01wc3",'1', Left)
		| ("01wc3", '#') -> ("01c3",'#', Left)
		| ("01wc3", sym) -> ("rej",sym, Right)
		| ("10wc3", '0') -> ("10wc3",'0', Left) 
		| ("10wc3", '1') -> ("10wc3",'1', Left)
		| ("10wc3", '#') -> ("10c3",'#', Left)
		| ("10wc3", sym) -> ("rej",sym, Right)
		| ("11wc3", '0') -> ("11wc3",'0', Left) 
		| ("11wc3", '1') -> ("11wc3",'1', Left)
		| ("11wc3", '#') -> ("11c3",'#', Left)
		| ("11wc3", sym) -> ("rej",sym, Right)
		| ("00c3", '1') -> ("cback",'#',Left)
		| ("00c3", '>') -> ("nback",'>',Right)
		| ("00c3", '#') -> ("00c3",'#',Left)
		| ("00c3", sym) -> ("rej",sym, Right)
		| ("01c3", '0') -> ("nback",'#',Left)
		| ("01c3", '>') -> ("nback",'>',Right)
		| ("01c3", '#') -> ("01c3",'#',Left)
		| ("01c3", sym) -> ("rej",sym, Right)
		| ("10c3", '0') -> ("nback",'#',Left)
		| ("10c3", '>') -> ("nback",'>',Right)
		| ("10c3", '#') -> ("10c3",'#',Left)
		| ("10c3", sym) -> ("rej",sym, Right)
		| ("11c3", '1') -> ("cback",'#',Left)
		| ("11c3", '>') -> ("nback",'>',Right)
		| ("11c3", '#') -> ("11c3",'#',Left)
		| ("11c3", sym) -> ("rej",sym, Right)
		| ("nback", '_') -> ("n",'_',Left)
		| ("nback", sym) -> ("nback",sym,Right)
		| ("cback", '_') -> ("c",'_',Left)
		| ("cback", '<') -> ("rej",'<',Right)
		| ("cback", sym) -> ("cback",sym,Right)
		| ("rej", sym) -> ("rej",sym, Right)
		| ("acc", sym) -> ("acc",sym, Right)
		| _ -> fail "Undefined transition"}

(* 
type 'a turing = { states : 'a list;
		   input_alph : char list;
		   tape_alph : char list;
		   leftmost : char;
		   blank : char;
		   delta : ('a * char) -> ('a * char * direction);
		   start : 'a;
		   accept : 'a;
		   reject : 'a }

type 'a dfa = {states_d :   'a list;
   alphabet_d : char list;
	start_d :    'a;
   delta_d :    ('a * char * 'a) list;
	final_d :    'a list} *)


