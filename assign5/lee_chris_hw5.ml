(* 
Chris Lee
christopher.lee@students.olin.edu

Assignment 5

#use "lee_chris_hw5.ml";;
step anbn [N "start"; T 'a'];;
eliminate_epsilon_rules anbnbmamcp;;
 *)


let explode str = 
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

let fail s = raise (Failure s)



(*
 * A function to perform depth first search in a tree
 * created from a transition relation.
 *
 * dfs quit trans init goal   
 *       returns true if there is a node N in the 
 *       tree created by the transition relation 'trans' starting
 *       at the initial node 'init' such that 'goal N' is true.
 *
 *       Quit search the current branch when 'quit N' is true 
 *
 * The 'quit' function is used to control the depth of the search. 
 * When 'quit N' returns true, it means that we have gone deep enough
 * and that we're acknowledging that we won't find the solution on
 * that branch.   
 *
 *)

let dfs quit trans init goal = 
  let rec loop seen stack = 
    match stack with
      [] -> false
    | curr :: stack' when not (List.mem curr seen) -> 
           if (goal curr) then true
	   else if (quit curr) then loop (curr::seen) stack'
	   else loop (curr::seen) ((trans curr)@stack')
    | _:: stack' -> loop seen stack'
  in loop [] [init]



(*
 * Some types to help us define CFGs (without epsilon production rules)
 *
 * symbol is either a terminal 'T char' or a nonterminal 'N string'
 *    (I'm using strings to describe nonterminals for added flexibility
 *
 * rule is the type of a non-epsilon production rule
 *    A rule can only be constructed with mk_rule that takes the 
 *    the nonterminal name 'A' and the list of symbols to produce 'w',
 *    and creates the rule 'A -> w', and it can only be used using
 *    get_rule that returns the components 'A' and 'w' of 'A -> w'
 *
 *)

type symbol = 
    T of char 
  | N of string


(* this module is simply to hide the implementation of the rule type 
 * so that the only way to create a rule is to use mk_rule below *)

module Rule : sig 
  type t
  val mk: string -> symbol list -> t
  val get: t -> string * symbol list 
  val strSymL : symbol list -> string
  val print_rule: Format.formatter -> t -> unit
end = struct
  type t = string * symbol list
  let mk s sl =
    match sl with
    | [] -> fail "Trying to create epsilon rule!"
    | _ -> (s,sl)
  let get r = r
  let strS (s) = "\""^s^"\""
  let strSym = function 
    | (T c) -> "T \'"^(Char.escaped c)^"\'"
    | (N s) -> "N "^(strS s)  
  let strSymL sl = "["^(String.concat "; " (List.map strSym sl))^"]"
  let print_rule ppf (s,sl) = 
    Format.fprintf ppf "(%s,%s)" (strS s) (strSymL sl)
end
;; #install_printer Rule.print_rule


type rule = Rule.t

(* this is used to create a non-epsilon production rule 
 * it fails if the symbol list is empty
 *)

let mk_rule : string -> symbol list -> rule = Rule.mk

(* this extracts the components of a production rule
 *)

let get_rule : rule -> string * symbol list = Rule.get




(*
 * The type for CFGs with no epsilon production rules
 *
 *)

type cfgNE = { nonterms_ne     : string list;
                terms_ne        : char list;
                rules_ne       : rule list;
                gen_empty_ne   : bool;
		start_ne       : string }



(* function to test if a symbol list is the sequence of terminals we seek *)

let found w = 
  let w' = List.map (fun c -> T c) (explode w)  in
  fun str -> str = w'


(* PROVIDE CODE FOR THIS FUNCTION FOR QUESTION 2 *)

let rec miniStep f xs before = 
  match xs with
  [] -> []
  |hd::tl -> (before@(f hd)@tl)::(miniStep f tl (before@[hd]));;

let rec remDup xs =
  match xs with
  [] -> []
  |hd::tl -> if (List.exists (fun x -> x = hd) tl) then remDup tl else hd::(remDup tl);;

let step cfgNE syms = 
  (* list of results*)
  remDup  (List.filter (fun x -> not (x = syms)) (List.flatten
  (*list of list of results*)
  (List.map (fun sym1 -> 
    (* list of results*)
    match sym1 with T a -> []|N nonterm ->
    List.fold_right (fun x y -> (miniStep (fun sym2 -> match sym2 with T a -> [T a]|N nonterm2 -> 
      if nonterm = nonterm2 then x else [N nonterm2]) syms [])@y) 
    (* list of list of steps*)
    (List.fold_right (fun x y -> match get_rule x with (prev,next) -> if prev = nonterm then next::y else y) cfgNE.rules_ne []) []
    ) syms)));;




(* Function to search the derivation tree for a sequence of terminals
 * matching the provided string 
 * It searches until the sequence of symbols grows larger than the
 * string looked for.
 *)

let generate cfgNE w = 
  if (w = "") then cfgNE.gen_empty_ne
  else dfs (fun syms -> List.length syms > String.length w)
           (step cfgNE)
           [N cfgNE.start_ne]
           (found w)



(* 
 *  Compute the language of a CFG, restricted to inputs of length <= n
 *   language(cfg,n) returns a list of strings generated by cfg
 *   printLanguage(cfg,n) prints the strings generated by cfg
 *
 *)

let language cfgNE n = 
  let strings alphabet n = 
    let rec mapCons c = List.map (fun y -> c::y)  in
    let rec mapConsSet alphabet l = 
      List.fold_right (fun c -> List.append (mapCons c l)) alphabet []  in
    let rec strings' n =
      if (n<=0) then [[]]
      else [] :: mapConsSet alphabet (strings' (n-1))
    in List.map implode (strings' n)  in
  List.filter (generate cfgNE) (strings cfgNE.terms_ne n)

let printLanguage cfgNE n = 
  List.iter (fun s -> Printf.printf "  %s\n" (if (s="") then "<empty>" else s))
              (language cfgNE n)




(* 
 *  Some sample CFGs without any epsilon production rules
 *
 *)


(* The language {a^nb^n | n>=0}   *)

let anbn = { nonterms_ne = ["start"];
             terms_ne = ['a';'b'];
             rules_ne = [mk_rule "start" [T 'a'; T 'b'];
                         mk_rule "start" [T 'a'; N "start"; T 'b']];
             gen_empty_ne = true;
             start_ne = "start" }

(* The language {a^nb^nc^m | m>=0}   *)

let anbncm = { nonterms_ne = ["start"; "A"; "B"];
               terms_ne = ['a'; 'b'; 'c'];
	       rules_ne = [ mk_rule "start" [N "A"];
			    mk_rule "start" [N "B"];
			    mk_rule "start" [N "A"; N "B"];
			    mk_rule "A" [T 'a'; T 'b'];
			    mk_rule "A" [T 'a'; N "A"; T 'b'];
			    mk_rule "B" [T 'c'];
			    mk_rule "B" [T 'c'; N "B"]];
	       gen_empty_ne = true;
	       start_ne = "start" }




(*
 * The type for general CFGs 
 *
 *)

type cfg = { nonterms : string list;
	     terms    : char list;
	     rules    : (string * symbol list) list;
	     start    : string }



(* A sample grammar with language {a^nb^nb^ma^mc^p | m,n,p>=0}  *)

let anbnbmamcp = { nonterms = ["Start"; "A"; "B"; "C"];
		   terms = ['a';'b';'c'];
		   rules = [ ("Start", [N "A"; N "B"; N "C"]);
			     ("A", [T 'a'; N "A"; T 'b']);
			     ("A", []);
			     ("B", [T 'b'; N "B"; T 'a']);
			     ("B", []);
			     ("C", [T 'c'; N "C"]);
			     ("C", [])];
		   start = "Start" }
		           

(* PROVIDE CODE FOR THIS FUNCTION FOR QUESTION 5 *)
let share l1 l2 = List.fold_right (fun x y -> (List.exists (fun z -> z = x) l2)||y) l1 false;;

let eliminate_epsilon_rules cfg = 
  let new_rules = 
  match (List.partition (fun rule -> match rule with (str, syml) -> syml = []) cfg.rules) with 
    (eprod, prod) ->  let stre = (List.map (fun e -> match e with (stre, _) -> N stre) eprod) in
    List.fold_right (fun p ps -> match p with (strp, symlp) -> if (share symlp stre) then (strp, List.filter (fun x -> not (share [x] stre)) symlp)::p::ps else p::ps) prod []
  in 
  {nonterms_ne = cfg.nonterms;
  terms_ne = cfg.terms;
  gen_empty_ne = List.exists (fun x -> match x with (s,l) -> s = (cfg.start) && (l = [])) new_rules;
  rules_ne = List.map (fun x -> match x with (s, l) -> mk_rule s l) (List.filter (fun x -> match x with (s,l) -> l != []) new_rules);
  start_ne = cfg.start
  };;