(*
Chris Lee
christopher.lee@students.olin.edu

Assignment 0

To Instructor:
	Simply run ./run to see test cases, or recompile lee_chris_hw0.ml
	Solutions are listed below before section: "PRINT CASES"
 *)

(* =========
Number 1 
========== *)

(* == Part a == *)

let rec append_list = function 
	[],l2 -> l2
	|h::l1, l2 -> h::(append_list(l1,l2));;	

(* == Part b == *) 

let rec flatten = function
	[] -> []
	|h::t -> append_list(h,flatten(t));;

(* == Part c == *)
let rec double = function
	[] -> []
	|h::t -> 2*h::double(t);;

(* == Part d == *)
let rec last = function
	[] -> None
	|[a] -> Some a
	|h::t -> last(t);;
	

(* =========
Number 2
========== *)
(* == Part a == *)
type rational = {num: int; den: int}

let half = {num = 1; den = 2};;
let third = {num = 1; den = 3};;
let fourth = {num = 1; den = 4};;

let simplify r = 
	let rec gcf = function
	|a, 0 -> a
	|0, a -> a
	|a,b -> gcf(b, (a mod b)) in
	let x = gcf(r.den, r.num) in
	{num = r.num/x; den = r.den/x};;

(* == Part b == *)
let addR (a,b) = 
	simplify {num = (a.num * b.den + b.num * a.den); den = (a.den * b.den)};;

let multR (a,b) =
	simplify {num = a.num * b.num; den = a.den * b.den};;

(* == Part c == *)
type number = I of int
			| R of rational
			| F of float

let floatR r =
	float(r.num) /. float(r.den);;

let add = function
	|(I x, I y) -> I (x + y)
	|(F x, F y) -> F (x +. y)
	|(R x, R y) -> R (addR(x,y))
	|(R x, F y) | (F y, R x) -> F (floatR(x) +. y)
	|(I x, F y) | (F y, I x) -> F (float(x) +. y)
	|(I x, R y) | (R y, I x) -> R (addR(y, {num = x; den = 1}));;


(* =========
Number 5
========== *)

type bConst = One | Zero

type bExpr = Const of bConst
			| Var of string
			| And of bExpr * bExpr
			| Or of bExpr * bExpr
			| Not of bExpr

let sample1 = And(Not(Var "a"), Not(Var "b"))
let sample2 = Or(Not(Var "a"), And(Var "b", Const(One)))
let sample3 = And(Var "a", Not(Var "a"))

(* == Part a == *)

let rec vars = function
	|Const a -> []
	|Var a -> 	[a]
	|And(a,b) -> if vars(a) = vars(b) then vars(a) else append_list(vars(a),vars(b))
	|Or(a,b) -> append_list(vars(a),vars(b))
	|Not a -> vars(a);;

(* == Part b ==*)

let rec subst = function
	|Const a, b, c -> Const a
	|Var a, b, c -> if a = b then c else Var a
	|And(a,d), b, c -> And(subst(a,b,c),subst(d,b,c))
	|Or(a,d), b, c ->  Or(subst(a,b,c),subst(d,b,c))
	|Not a, b, c -> Not(subst(a,b,c))

(* == Part c ==*)

let rec eval = function
	|Const a -> Some a
	|Var a -> None
	|And(a,b) -> if eval(a) = Some One && eval(b) = Some One then Some One else if eval(a) = None or eval(b) = None then None else Some Zero
	|Or(a,b) -> if eval(a) = Some One or eval(b) = Some One then Some One else if eval(a) = None or eval(b) = None then None else Some Zero
	|Not a -> if eval(a) = Some One then Some Zero else if eval(a) = None then None else Some One;;



(* PRINT FUNCTIONS *)
let rec print_int_list = function 
	[] -> ()
	| e::l -> print_int e ; print_string " " ; print_int_list l;;

let rec print_string_list = function 
	[] -> ()
	| e::l -> print_string e ; print_string " " ; print_string_list l;;	

let rec print_float_list = function 
	[] -> ()
	| e::l -> print_float e ; print_string " " ; print_float_list l;;

let rec print_option_string = function
	|None -> print_string("None")
	|Some a -> print_string("Some "	);print_string(a);;

let rec print_option_int = function
	|None -> print_string("None")
	|Some a -> print_string("Some ");print_int(a);;

let print_rational r =
	print_string("Num = "); print_int(r.num); print_string(" Den = "); print_int(r.den);;

let print_number = function
	|I a ->print_string("Number of Integer: "); print_int(a)
	|F a ->print_string("Number of Float: "); print_float(a)
	|R a ->print_string("Number of Rational: "); print_rational(a);;

let rec print_bexpr = function
	|Const a -> print_string("Const "); if a = One then print_string("One") else print_string("Zero")
	|Var a -> print_string("Var "); print_string(a)
	|And(a,b) -> print_string("And(");print_bexpr(a);print_string(", ");print_bexpr(b);print_string(")")
	|Or(a,b) -> print_string("Or(");print_bexpr(a);print_string(", ");print_bexpr(b);print_string(")")
	|Not a -> print_string("Not("); print_bexpr(a); print_string(")");;

let print_bOption = function
	|None -> print_string("bConst option = None")
	|Some a -> print_string("bConst option = Some "); if a = One then print_string("One") else print_string("Zero");;

(* PRINT CASES *)

(* Number 1 Part a *)
print_string("\n===================\nNumber 1 :: Part a\n===================\n");;

let case1 = append_list([],[]);;
print_string("Case 1:\n\t[ ");;print_int_list(case1);;print_string("]\n");;

let case2 = append_list([1;2;3],[3;4;5]);;
print_string("Case 2:\n\t[ ");;print_int_list(case2);;print_string("]\n");;

let case3 = append_list(["a";"b";"c"],[]);;
print_string("Case 3:\n\t[ ");;print_string_list(case3);; print_string("]\n");;(* Couldn't figure out why I can't print string lists*)	

let case4 = append_list([],[1.0;2.0;3.0]);;
print_string("Case 4:\n\t[ ");;print_float_list(case4);; print_string("]\n");;


(* Number 1 Part b *)

print_string("\n===================\nNumber 1 :: Part b\n===================\n");;

let case = flatten([]);;
print_string("Case 1:\n\t[ ");;print_int_list(case);;print_string("]\n");;

let case = flatten([[1;2;3]]);;
print_string("Case 2:\n\t[ ");;print_int_list(case);;print_string("]\n");;

let case = flatten([[1;2;3];[4;5;6]]);;
print_string("Case 3:\n\t[ ");;print_int_list(case);;print_string("]\n");;

let case = flatten([["a"];["b";"c"];[];["d";"e";"f"]]);;
print_string("Case 4:\n\t[ ");;print_string_list(case);;print_string("]\n");;
	

(* Number 1 Part c *)

print_string("\n===================\nNumber 1 :: Part c\n===================\n");;

let case = double([]);;
print_string("Case 1:\n\t[ ");;print_int_list(case);;print_string("]\n");;

let case = double([1]);;
print_string("Case 2:\n\t[ ");;print_int_list(case);;print_string("]\n");;

let case = double([1;2;3]);;
print_string("Case 3:\n\t[ ");;print_int_list(case);;print_string("]\n");;

let case = double([10;20;30;40;50]);;
print_string("Case 4:\n\t[ ");;print_int_list(case);;print_string("]\n");;

(* Number 1 Part d *)

print_string("\n===================\nNumber 1 :: Part c\n===================\n");;

let case = last([]);;
print_string("Case 1:\n\t[ ");;print_option_string(case);;print_string("]\n");;

let case = last([1]);;
print_string("Case 1:\n\t[ ");;print_option_int(case);;print_string("]\n");;

let case = last([1;2;3;4]);;
print_string("Case 1:\n\t[ ");;print_option_int(case);;print_string("]\n");;

let case = last(["a";"b";"c"]);;
print_string("Case 1:\n\t[ ");;print_option_string(case);;print_string("]\n");;


(* Number 2 Part a *)

print_string("\n===================\nNumber 2 :: Part a\n===================\n");;

let case = simplify {num = 10; den = 20};;
print_string("Case 1:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = simplify {num = 30; den = 35};;
print_string("Case 2:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = simplify {num = 6; den = 4};;
print_string("Case 3:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = simplify {num = 1; den = 2};;
print_string("Case 4:\n\t[ ");;print_rational(case);;print_string("]\n");;

(* Number 2 Part b *)

print_string("\n===================\nNumber 2 :: Part b\n===================\n");;

let case = addR(half,half);;
print_string("Case 1:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = addR(half,third);;
print_string("Case 2:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = addR(half,fourth);;
print_string("Case 3:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = addR(fourth,addR(fourth,fourth));;
print_string("Case 4:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = addR(fourth,addR(fourth,addR(fourth,fourth)));;
print_string("Case 5:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = multR(half,half);;
print_string("Case 6:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = multR(half,fourth);;
print_string("Case 7:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = multR(third, {num = 3;den = 1});;
print_string("Case 8:\n\t[ ");;print_rational(case);;print_string("]\n");;

let case = multR({num = 2; den = 3},{num = 6; den = 4});;
print_string("Case 9:\n\t[ ");;print_rational(case);;print_string("]\n");;

(* Number 2 part c *)

print_string("\n===================\nNumber 2 :: Part c\n===================\n");;

let case = add(I 1, I 4);;
print_string("Case 1:\n\t[ ");;print_number(case);;print_string("]\n");;

let case = add(I 1, R half);;
print_string("Case 2:\n\t[ ");;print_number(case);;print_string("]\n");;

let case = add(F 3.0, R third);;
print_string("Case 3:\n\t[ ");;print_number(case);;print_string("]\n");;

let case = add(I 1, F 3.5);;
print_string("Case 4:\n\t[ ");;print_number(case);;print_string("]\n");;

(* Number 5 part a *)

print_string("\n===================\nNumber 5 :: Part a\n===================\n");;

let case = vars(Const One);;
print_string("Case 1:\n\t[ ");;print_string_list(case);;print_string("]\n");;

let case = vars(And(Const One, Const Zero));;
print_string("Case 2:\n\t[ ");;print_string_list(case);;print_string("]\n");;

let case = vars(sample1);;
print_string("Case 3:\n\t[ ");;print_string_list(case);;print_string("]\n");;
	
let case = vars(sample2);;
print_string("Case 4:\n\t[ ");;print_string_list(case);;print_string("]\n");;

let case = vars(sample3);;
print_string("Case 5:\n\t[ ");;print_string_list(case);;print_string("]\n");;

(* Number 5 part b *)

print_string("\n===================\nNumber 5 :: Part b\n===================\n");;

let case = subst(sample1, "a", Const Zero);;
print_string("Case 1:\n\t");;print_bexpr(case);;print_string("\n");;

let case = subst(sample1, "b", Var "c");;
print_string("Case 2:\n\t");;print_bexpr(case);;print_string("\n");;

let case = subst(sample2, "a", Not(Var "a"));;
print_string("Case 3:\n\t");;print_bexpr(case);;print_string("\n");;
	
let case = subst(sample3, "a", Const One);;
print_string("Case 4:\n\t");;print_bexpr(case);;print_string("\n");;

(* Number 5 part b *)

print_string("\n===================\nNumber 5 :: Part c\n===================\n");;

let case = eval(sample1);;
print_string("Case 1:\n\t");;print_bOption(case);;print_string("\n");;

let sample1' = subst(sample1, "a", Const One);;
let case = eval(sample1');;
print_string("Case 2:\n\t");;print_bOption(case);;print_string("\n");;

let sample1'' = subst(sample1', "b", Const Zero);;
let case = eval(sample1'');;
print_string("Case 3:\n\t");;print_bOption(case);;print_string("\n");;
	
let case = eval(sample3);;
print_string("Case 4:\n\t");;print_bOption(case);;print_string("\n");;

let case = eval(subst(sample3, "a", Const Zero));;
print_string("Case 5:\n\t");;print_bOption(case);;print_string("\n");;

let case = eval(subst(sample3, "a", Const One));;
print_string("Case 6:\n\t");;print_bOption(case);;print_string("\n");;
