(* Untyped Language *)

type expression =
  | N of numeral
  | S of expression * expression
  | P of expression * expression

and numeral =
  | Z
  | O
  | NZ of numeral
  | NO of numeral

let e = S (N O, P (N (NZ O), N (NO O)))

let rec estr (e : expression) : string =
  match e with
  | N n ->
      nstr n
  | S (e1, e2) ->
      "(" ^ estr e1 ^ "+" ^ estr e2 ^ ")"
  | P (e1, e2) ->
      "(" ^ estr e1 ^ "*" ^ estr e2 ^ ")"


and nstr (n : numeral) : string =
  match n with
  | Z ->
      "0"
  | O ->
      "1"
  | NZ n ->
      nstr n ^ "0"
  | NO n ->
      nstr n ^ "1"


let rec eval (e : expression) : int =
  match e with
  | N n ->
      nval n
  | S (e1, e2) ->
      eval e1 + eval e2
  | P (e1, e2) ->
      eval e1 * eval e2


and nval (n : numeral) : int =
  match n with Z -> 0 | O -> 1 | NZ n -> nval n * 2 | NO n -> (nval n * 2) + 1


let rec map f l = match l with [] -> [] | h :: t -> f h :: map f t;;

Printf.printf "%s\n" (estr e);;

Printf.printf "%d\n" (eval e)

(* Typed Languag *)

type tag =
  | None
  | Aexp
  | Bexp

type texp = Texp of tag ref * exp

and exp =
  | One
  | Plus of texp * texp
  | Equals of texp * texp
  | And of texp * texp
  | If of texp * texp * texp

let uexp (e : exp) : texp = Texp (ref None, e)

let e2 =
  uexp
    (Equals
       ( uexp (Plus (uexp One, uexp One))
       , uexp
           (If
              ( uexp (Equals (uexp One, uexp One))
              , uexp (Plus (uexp One, uexp One))
              , uexp One ) ) ) )


let rec tstr (t : tag ref) : string =
  match !t with None -> "" | Aexp -> ":aexp" | Bexp -> ":bexp"


let rec str (e : texp) : string =
  match e with
  | Texp (t, One) ->
      "1" ^ tstr t
  | Texp (t, Plus (e1, e2)) ->
      "(" ^ str e1 ^ "+" ^ str e2 ^ ")" ^ tstr t
  | Texp (t, Equals (e1, e2)) ->
      "(" ^ str e1 ^ "=" ^ str e2 ^ ")" ^ tstr t
  | Texp (t, And (e1, e2)) ->
      "(" ^ str e1 ^ "&" ^ str e2 ^ ")" ^ tstr t
  | Texp (t, If (e1, e2, e3)) ->
      "(if " ^ str e1 ^ " then " ^ str e2 ^ " else " ^ str e3 ^ ")" ^ tstr t

;;

Printf.printf "%s\n" (str e2)

let check (e : texp) (t : tag) : unit =
  match e with
  | Texp (t0, _) ->
      if !t0 <> t then raise (Failure "type error") else ()


let rec tset (e : texp) : unit =
  match e with
  | Texp (t, One) ->
      t := Aexp
  | Texp (t, Plus (e1, e2)) ->
      tset e1 ;
      check e1 Aexp ;
      tset e2 ;
      check e2 Aexp ;
      t := Aexp
  | Texp (t, Equals (e1, e2)) ->
      tset e1 ;
      check e1 Aexp ;
      tset e2 ;
      check e2 Aexp ;
      t := Bexp
  | Texp (t, And (e1, e2)) ->
      tset e1 ;
      check e1 Bexp ;
      tset e2 ;
      check e2 Bexp ;
      t := Bexp
  | Texp (t, If (e1, e2, e3)) ->
      tset e1 ;
      check e1 Bexp ;
      tset e2 ;
      check e2 Aexp ;
      tset e3 ;
      check e3 Aexp ;
      t := Aexp

;;

tset e2;;

Printf.printf "%s\n" (str e2)
