type expression =
  | N of numeral
  | S of expression * expression
  | P of expression * expression

and numeral =
  | Z
  | O
  | NZ of numeral
  | NO of numeral

let rec map f l = match l with [] -> [] | h :: t -> f h :: map f t
