(* 
Chris Lee
christopher.lee@students.olin.edu

Assignment 8

#use "lee_chris_hw8.ml";;
 *)



let fail s = raise (Failure s)

(************************************************************* 
 * LAMBDA CALCULUS
 *
 *)



(*
 * type for lambda-terms
 *
 *)

type term = 
  | Var of string
  | Lam of string * term
  | App of term * term



(*
 * Pretty-printing lambda-terms
 *
 *)

let string_of_term t = 
  let rec term t = 
    match t with
    | Var x -> x
    | Lam (x,t) -> "\\"^x^"."^(term t)
    | App (t,u) -> app t u 
  and arg u = 
    match u with
    | Var x -> x
    | _ -> "("^(term u)^")" 
  and app t u = 
    match t with
    | App (t1,t2) -> (app t1 t2)^" "^(arg u)
    | Var x -> x^" "^(arg u)
    | _ -> "("^(term t)^") "^(arg u) in
  term t

let show_term t = Printf.printf "%s\n" (string_of_term t)

let print_term ppf t = 
  Format.fprintf ppf "%s" (string_of_term t)
(* Hack to add a prettyprinter to the OCaml shell to print lambda terms *)
;; #install_printer print_term



(*
 * Free variables of a lambda-term
 *
 *)

let setunion s t = 
  List.fold_right (fun x xs -> if List.mem x xs then xs else x::xs) s t

let setdiff s t = 
  List.filter (fun x -> not (List.mem x t)) s

let rec fv t = 
  match t with
  | Var x -> [x]
  | Lam (x,t) -> setdiff (fv t) [x]
  | App (t,u) -> setunion (fv t) (fv u)

(*
 * Some helper functions to help construct lambda-terms
 *
 * apps [t1;t2;t3;t4] --> App (App (App (t1,t2), t3), t4)
 * lams [x1;x2;x3;x4] t --> Lam (x1, Lam (x2, Lam (x3, Lam (x4, t))))
 *)

let rec apps ts = 
  match ts with
  | [] -> Lam ("x",Var "x")
  | [t] -> t
  | [t1;t2] -> App (t1,t2)
  | t1::t2::ts -> apps (App (t1,t2)::ts)

let rec lams xs t = 
  match xs with
  | [] -> t
  | x::xs' -> Lam (x,lams xs' t)



(* 
 *  IMPLEMENT THE FOLLOWING FUNCTIONS FOR QUESTION 2
 *
 *)

let rec subst t1 v t2 = 
  match t1 with
    |Var a ->  if a = v then t2 else Var a
    |Lam (b1, b2) -> if List.exists(fun x -> x = b1) (fv t2) or b1 = v then Lam (b1, b2) else Lam (b1, subst b2 v t2)
    |App (c1, c2) -> App (subst c1 v t2, subst c2 v t2)

let rec has_redex t = 
  match t with 
    |Var _ -> false
    |Lam (_,b) -> false or has_redex b
    |App (Lam (_,_), _) -> true 
    |App (a,b) -> false or has_redex a or has_redex b
    
let rec find_reduction t =
  match t with 
    |Var a -> Var a
    |Lam (b1, b2) -> Lam(b1,find_reduction b2)
    |App (Lam (a,b), c) -> subst b a c
    |App (a,b) -> match (find_reduction a) with 
                    |Var _ -> App(a,find_reduction b)
                    | _ -> App(find_reduction a,b)

let reduce_once t = 
  if (not (has_redex t)) then t else (find_reduction t)

let rec reduce t = 
  let post_t = reduce_once t in
  if t = post_t then t else reduce post_t




(*
 * Some sample lambda terms for testing and experimenting
 *
 * See lecture notes for details
 *
 *)

(* Booleans *)

let true_L = lams ["x";"y"] (Var "x")
let false_L = lams ["x";"y"] (Var "y")

let and_L = lams ["m";"n"] (apps [Var "m"; Var "n"; Var "m"])
let or_L = lams ["m";"n"] (apps [Var "m"; Var "m"; Var "n"])
let not_L = lams ["m";"x";"y"] (apps [Var "m"; Var "y"; Var "x"])

(* Pairs *)

let pair_L = lams ["x";"y";"z"] (apps [Var "z"; Var "x"; Var "y"])
let first_L = Lam ("p", App (Var "p", true_L))
let second_L = Lam ("p", App (Var "p", false_L))

(* Natural numbers *)

let zero_L = lams ["f";"x"] (Var "x")

let succ_L = 
  lams ["n";"f";"x"] (App (App (Var "n", Var "f"), App (Var "f", Var "x")))

let one_L = App (succ_L, zero_L)
let two_L = App (succ_L, one_L)
let three_L = App (succ_L, two_L)

let plus_L = lams ["m";"n";"f";"x"] (App (App (Var "m", Var "f"),
					  App (App (Var "n", Var "f"), 
					       Var "x")))

let times_L = lams ["m";"n";"f";"x"] (App (App (Var "m",
						App (Var "n", Var "f")),
					   Var "x"))

let iszero_L = Lam ("n", apps [Var "n"; Lam ("x",false_L); true_L])

let pred_L = lams ["n";"f";"x"] (apps [ Var "n";
					lams ["g";"h"] (App (Var "h",
							     App (Var "g",
								  Var "f")));
					Lam ("u", Var "x");
					Lam ("u", Var "u")])

(* Recursion *)

let y_L = Lam ("f", App (Lam ("x", App (Var "f", App (Var "x", Var "x"))),
			 Lam ("x", App (Var "f", App (Var "x", Var "x")))))

(* Factorial (using recursion) *)

let f_fact_L = lams ["f";"n"] (apps [ App (iszero_L, Var "n");
				      one_L;
				      apps [ times_L;
					     Var "n";
					     App (Var "f",
						  App (pred_L, Var "n"))]])
    
let fact_L = App (y_L, f_fact_L)





(*************************************************************
 *
 * Modular Turing Machines
 *
 *)


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



type direction = Left | Right | Stay

type symbol = string

type 'a tm_desc = { states : 'a list;
		    input_alph : symbol list;
  		    tape_alph : symbol list;
		    leftmost : symbol;
		    blank : symbol;
		    delta : (('a * symbol) -> ('a * symbol * direction));
		    start : 'a;
		    accept : 'a;
		    reject : 'a }

	
module TM : sig

  type 'a machine

  (* Build Turing machines *)

  val build : ('a -> string) -> 'a tm_desc -> 'a machine
	  
  val build' : string tm_desc -> string machine

  (* Execute Turing machines *)

  val run : 'a machine -> string -> bool

  val run_trace_all : 'a machine -> string -> bool

  val run_trace_some : 'a machine -> 'a list -> string -> bool 

  (* Functions to work with transition functions/tables *)

  val machine_trans_table : 'a machine -> 
                              (('a * symbol) * ('a * symbol * direction)) list

  val make_trans_table : 'a list -> symbol list -> 
                           (('a * symbol) -> ('a * symbol * 'c)) -> 
                             (('a * symbol) * ('a * symbol * 'c)) list

  val make_delta : (('a * symbol) * ('a * symbol * 'c)) list -> 
                        (('a * symbol) -> ('a * symbol * 'c))

  val print_machine : Format.formatter -> 'a machine -> unit

end  = struct
	
  type 'a machine = M of 'a tm_desc * ('a -> string)

  type 'a config = C of (symbol list * 'a * symbol list)

  let errorTM s = raise (Failure ("TM ERROR: "^s))

  let checkTrue b s = if b then () else errorTM s

  let check_delta string_of_state md = 
    let trans st sym = 
      Printf.sprintf "delta(%s,%s)" (string_of_state st) sym in
    let tried_delta (st,sym) = 
      try 
	md.delta (st,sym) 
      with _ -> errorTM (Printf.sprintf "%s undefined" (trans st sym)) in
    let checkState st = 
      let checkSym sym = 
	let (q,s,d) = tried_delta (st,sym) in
	let _ = checkTrue (List.mem q md.states) 
	           (Printf.sprintf "%s yields state %s not in states list"
                      (trans st sym) (string_of_state q))  in
	let _ = checkTrue (List.mem sym md.tape_alph)
	           (Printf.sprintf "%s yields symbol %s not in tape alphabet"
		      (trans st sym) s)  in
	()  in
      List.iter checkSym md.tape_alph  in
    let checkLeftmost st = 
      checkTrue (match md.delta(st,md.leftmost) with
                 | (_,_,Left) -> false | _ -> true)
	(Printf.sprintf "%s moves left" (trans st md.leftmost))  in
    let checkLoop st sym = 
      checkTrue (match md.delta(st,sym) with (st',_,_) -> st=st')
	(Printf.sprintf "%s does not loop" (trans st sym))  in
    let _ = List.iter checkState md.states  in
    let _ = List.iter checkLeftmost md.states in
    let _ = List.iter (checkLoop md.accept) md.tape_alph  in
    let _ = List.iter (checkLoop md.reject) md.tape_alph  in
    ()


  let check_alphabet md = 
    let _ = checkTrue (List.for_all (fun x -> List.mem x md.tape_alph) 
                                       md.input_alph)
                 "input alphabet not included in tape alphabet" in
    let _ = checkTrue (List.mem md.leftmost md.tape_alph)
	         "leftmost symbol not in tape alphabet"  in
    let _ = checkTrue (List.mem md.blank md.tape_alph)
	         "blank symbol not in tape alphabet"  in
    let _ = checkTrue (List.for_all (fun x -> String.length x = 1) 
			                md.input_alph)
	         "input symbols not all of length 1"  in
    let _ = checkTrue (List.for_all (fun x -> not (x="")) md.tape_alph)
	         "tape symbols not nonempty"  in
    ()

  let check_states md = 
    let _ = checkTrue (List.mem md.start md.states)
              "start state not in states list"  in
    let _ = checkTrue (List.mem md.accept md.states)
	      "accept state not in states list"  in
    let _ = checkTrue (List.mem md.reject md.states)
	      "reject state not in states list"  in
    ()

  let build string_of_state md = 
    let _ = check_alphabet md  in
    let _ = check_states md  in
    let _ = check_delta string_of_state md  in
    M (md, string_of_state)


  (* add elements of xs not already present in ys to ys *)
  let add xs ys = 
    List.fold_right (fun x r -> if (List.mem x r) then r else x::r) xs ys
      
  let build' = build (fun s -> s)

  let print_config string_of_state (C (u,q,v)) = 
    let print_syms = List.iter (Printf.printf "%s ")  in
    let _ = print_string "  "  in
    let _ = print_syms u  in
    let _ = Printf.printf "(%s) " (string_of_state q)  in
    let _ = print_syms v  in
    print_newline ()
	
  let next md (C (u,q,v) as c) = 
    let rec split_last u = 
      match List.rev u with
      |	[] -> fail "Moving Left from leftmost tape position"
      |	x :: xs -> (List.rev xs, x)  in
    let (a,v') = match v with
                 | [] -> (md.blank,[])
		 | a::v' -> (a,v')  in
    match md.delta (q,a) with
    | (q',b,Left) -> let (u',c) = split_last u in C (u',q',c::b::v')
    | (q',b,Right) -> C (u@[b],q',v')
    | (q',b,Stay) -> C (u,q',b::v')

  let run' f (M (md,ss)) w = 
    let input = List.map Char.escaped (explode w) in
    let _ = checkTrue (List.for_all (fun s -> List.mem s md.input_alph) input)
	        "Input string uses symbols not in input alphabet"  in
    let init_tape = md.leftmost::input  in
    let rec loop (C (u,q,v) as c) = 
      let _ = f ss c in 
      if (q = md.accept) then true
      else if (q = md.reject) then false
      else loop (next md c)  in
    loop (C ([], md.start, init_tape))

  let run m w = run' (fun _ _ -> ()) m w

  let run_trace_all m w = run' print_config m w	       

  let run_trace_some m states w = 
    let select_print_config string_of_state (C (u,q,v) as c) = 
      if (List.mem q states) 
      then print_config string_of_state c
      else ()  in
    run' select_print_config m w

  let make_trans_table states symbols delta = 
    let get_trans st = 
      List.fold_right (fun sym r -> ((st,sym),delta(st,sym))::r) 
	                 symbols []  in
    List.fold_right (fun st r -> (get_trans st)@r) states []

  let machine_trans_table (M (md,_)) = 
    make_trans_table md.states md.tape_alph md.delta 

  let make_delta table x = List.assoc x table

  let print_machine ppf (M (md,_)) = 
    Format.fprintf ppf "<TM over {%s} %d states>" 
      (String.concat "," md.input_alph)
      (List.length md.states)
end

(* Hack to add a printer to the OCaml shell to "see" Turing machines *)
;; #install_printer TM.print_machine





(*
 * Type for Modular Turing Machines
 *
 *)

type 'a tm_module = { states_M : 'a list;
		      delta_M : (('a * symbol) -> ('a * symbol * direction));
		      start_M : 'a;
		      accept_M : 'a;
		      reject_M : 'a }

type target = ToStart of string | ToAccept | ToReject

type 'a tm_desc_M = { input_alph_M : symbol list;
		      tape_alph_M : symbol list;
		      leftmost_M : symbol;
		      blank_M : symbol;
		      modules : (string * 'a tm_module * 
				   (target * target)) list; 
		      start_module : string ;
		    }
		     
type 'a mod_state = Accept | Reject | Rewind of string | State of string * 'a



(* 
 *  IMPLEMENT THE FOLLOWING FUNCTIONS FOR QUESTION 3
 *
 *)

let make_states m = 
  Accept::Reject::List.flatten (List.map (fun x -> 
    match x with
    |(a,b,_) -> (Rewind a)::List.map (fun state -> State (a,state)) b.states_M
  ) m.modules)
  
let find_module name m = 
  let res = List.filter (fun x -> match x with (a,b,c) -> a = name) m.modules in
  if List.length res < 1 then fail ("Cannot find module "^name)
    else match (List.hd res) with 
      (a,b,c) -> b

let make_delta m =
  let mod_info name = 
    let res = List.filter (fun x -> match x with (a,b,c) -> a = name) m.modules in
    if List.length res < 1 then fail ("Cannot find module "^name) else
      (List.hd res) in
  let get_rej_acc t s = 
    match t with 
      |ToStart x -> (Rewind x, s, Stay)
      |ToAccept -> (Accept, s, Stay)
      |ToReject -> (Reject, s, Stay) in
  let delta_func (q,s) = 
    match q with 
      |State (a,b) -> (let (name, cur_mod, (acc,rej)) = (mod_info a) in
                      match cur_mod.delta_M (b,s) with
                        |(acc',b,c) when acc' = cur_mod.accept_M -> (get_rej_acc acc b)
                        |(rej',b',c') when rej' = cur_mod.reject_M -> (get_rej_acc rej b')
                        |(a',b',c') -> (State(a, a'), b', c'))
      |Rewind b when s = m.leftmost_M -> (State (b, (find_module b m).start_M), s, Right)
      |Rewind b -> (Rewind b, s, Left)
      |sym -> (sym,s,Stay)
  in delta_func

let build_M string_of_state m = 
  let stringify st = match st with 
    |State (a, b) -> (string_of_state a)^":"^(string_of_state b)
    |Rewind b -> "Rewind"^":"^(string_of_state b)
    |Reject -> "Reject"
    |Accept -> "Accept"
  in
  TM.build stringify { 
    states = make_states m;
    input_alph = m.input_alph_M;
    tape_alph = m.tape_alph_M;
    leftmost = m.leftmost_M;
    blank = m.blank_M;
    delta = make_delta m;
    start = State (m.start_module, (find_module m.start_module m).start_M);
    accept = Accept;
    reject = Reject};;

 
(*
 * Sample modular Turing machine accepting {a^nb^n | n>=0}
 *
 *)

let mod_as_bs_desc = 
  let delta (q,a) = match q,a with
        | "start", "a" -> ("start", "a", Right)
		    | "start", "b" -> ("q1", "b", Right)
		    | "start", ">" -> ("start", ">", Right)
		    | "start", "_" -> ("acc", "_", Right)
		    | "q1", "b" -> ("q1", "b", Right)
		    | "q1", "_" -> ("acc", "_", Right)
		    | "acc", sym -> ("acc", sym, Right)
		    | _, sym -> ("rej", sym, Right)  in
  { states_M = ["start"; "q1"; "acc"; "rej"];
    delta_M = delta;
    start_M = "start";
    accept_M = "acc";
    reject_M = "rej" }


let mod_match_a_b_desc = 
  let delta (q,a) = 
    match q,a with
    | "q1", ">" -> ("q1", ">", Right)
    | "q1", "X" -> ("q1", "X", Right)
    | "q1", "_" -> ("acc", "_", Right)
    | "q1", "a" -> ("q2", "X", Right)
    | "q2", "a" -> ("q2", "a", Right)
    | "q2", "X" -> ("q2", "X", Right)
    | "q2", "b" -> ("acc", "X", Right)
    | "acc", sym -> ("acc", sym, Right)
    | _, sym -> ("rej", sym, Right)  in
  { states_M = ["q1"; "q2"; "acc"; "rej"];
    delta_M = delta;
    start_M = "q1";
    accept_M = "acc";
    reject_M = "rej" }


let mod_done_desc = 
  let delta (q,a) = 
    match q,a with
    | "q1", ">" -> ("q1", ">", Right)
    | "q1", "X" -> ("q1", "X", Right)
    | "q1", "_" -> ("acc", "_", Right)
    | "acc", sym -> ("acc", sym, Right)
    | _, sym -> ("rej", sym, Right)  in
  { states_M = ["q1"; "acc"; "rej"];
    delta_M = delta;
    start_M = "q1";
    accept_M = "acc";
    reject_M = "rej" }


let mod_anbn_desc = 
  { modules = 
      [ ("asbs", mod_as_bs_desc, (ToStart "done?", ToReject));
	("done?", mod_done_desc, (ToAccept, ToStart "match_a_b"));
	("match_a_b", mod_match_a_b_desc, (ToStart "done?", ToReject))];
    input_alph_M = ["a";"b"];
    tape_alph_M = ["a"; "b"; "X"; "_"; ">"];
    leftmost_M = ">";
    blank_M = "_";
    start_module = "asbs" }
