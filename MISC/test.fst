module Test

let incr (x:int) : int = x + 1

let incr1 (x:int) : y: int{y > x} = x + 1

let incr2 (x:int) : y: int{y = x + 1} = x + 2 - 1

let incr7 (x:int) : y:int{if x%2 = 0 then y%2 = 1 else y%2 = 0} = x + 1

val max (x:int) (y:int) : int

let max x y = if x > y then x else y

val max1 (x:int) (y:int)
  : z:int{ z >= x && z >= y && (z = x || z = y)}

let max1 x y = if x >= y then x else y

open FStar.Mul

let rec factorial (n:nat)
  : nat
  = if n = 0
    then 1
    else n * factorial (n - 1)
    
val fibonacci_1 : x:int -> y:int{y >= 1 /\ y >= x /\ (if x>=3 then y >= 2 else true)}
let rec fibonacci_1 n =
  if n <= 1 then 1 else fibonacci_1 (n - 1) + fibonacci_1 (n - 2)

let max2 x:nat = x

val apply (a b:Type) (f:a -> b) : a -> b

let apply (a b: Type) (f: a->b) x : b = f x

val compose (a b c:Type) (f: b -> c) (g : a -> b) : a -> c

let compose (a b c: Type) (f: b -> c) (g: a -> b) x : c = f (g x)

val twice (a:Type) (f: a -> a) : a -> a

let twice a f x = compose a a a f f x

let id (a:Type) (x:a) : a = x

let _ : bool = id _ true

// implicit arg

let id' (#a: Type) (x: a) : a = x

let _ : nat = id' 0

let _ = id' #nat 0

let _ = id' #(x: int{x <> 0})

let p = forall (x:nat) (y:nat{y<>0}). x % y = 0 ==> (exists (z:nat). x = z * y)

let fact1 = forall (n:nat). factorial n > 0

let sqr_is_nat (x:int) : unit = assert (x * x >= 0)

// let sqr_is_pos (x:int) : unit = assert (x * x >= 1)

let _ = assert (max 0 1 = 1)
let _ = assert (forall x y. max x y >= x /\
                            max x y >= y /\
                            (max x y = x \/ max x y = y))

type three =
  | One_of_three : three
  | Two_of_three : three
  | Three_of_three : three

let distinct = assert (One_of_three <> Two_of_three /\
                       Two_of_three <> Three_of_three /\
                       Three_of_three <> One_of_three)

let exhaustive (x:three) = assert (x = One_of_three \/
                                   x = Two_of_three \/
                                   x = Three_of_three)

let is_one (x:three)
  : bool
  = match x with
    | One_of_three -> true
    | _ -> false

let is_two (x:three)
  : bool
  = match x with
    | Two_of_three -> true
    | _ -> false

let is_three (x:three)
  : bool
  = match x with
    | Three_of_three -> true
    | _ -> false


let three_as_int (x:three)
  : int
  = if is_one x then 1
    else if is_two x then 2
    else 3

let three_as_int' (x:three)
  : int
  = if One_of_three? x then 1
    else if Two_of_three? x then 2
    else 3

let rec length #a (l:list a)
  : nat
  = match l with
    | [] -> 0
    | _ :: tl -> 1 + length tl

val append (#a:Type) (l1 l2:list a)
  : l:list a { length l = length l1 + length l2 }

let rec append l1 l2
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

let append_same_length = assert (forall (t: Type) (l1 l2: list t). (length l1) + (length l2) = length (append l1 l2))

let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

let rec fib (a b n:nat) 
  : Tot nat (decreases n)
  = match n with
   | 0 -> a
   | _ -> fib b (a+b) (n-1)

let fibonacci' (n:nat) : nat = fib 1 1 n

let rec factorial_is_positive (x:nat)
  : u:unit{factorial x > 0}
  = if x = 0 then ()
    else factorial_is_positive (x - 1)

let rec factorial_is_pos (x:int)
  : Lemma (requires x >= 0)
          (ensures factorial x > 0)
  = if x = 0 then ()
    else factorial_is_pos (x - 1)

let rec factorial_is_greater_than_arg (x:int)
  : Lemma (requires x > 2)
          (ensures factorial x > x)
   = if x = 3 then ()
     else factorial_is_greater_than_arg (x - 1)

val fibonacci_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
  
let rec fibonacci_greater_than_arg (n: nat{n >= 2})
  : Lemma (requires n >= 2 )
          (ensures fibonacci n >= n)
  = if n <= 3 then ()
    else (fibonacci_greater_than_arg (n - 1);
          fibonacci_greater_than_arg (n - 2))

let rec app #a (l1 l2:list a)
  : list a
  = match l1 with
    | [] -> l2
    | hd :: tl -> hd :: app tl l2
    
val app_length (#a:Type) (l1 l2:list a)
  : Lemma (length (app l1 l2) = length l1 + length l2)

let rec app_length_sums #a (l1 l2: list a)
  : Lemma (length (app l1 l2) = length l1 + length l2)
  = match l1 with
    | [] -> ()
    | hd :: tl -> app_length_sums tl l2

let rec reverse #a (l:list a)
  : list a
  = match l with
    | [] -> []
    | hd :: tl -> append (reverse tl) [hd]

let snoc l h = append l [h]

let rec snoc_cons #a (l:list a) (h:a)
  : Lemma (reverse (snoc l h) == h :: reverse l)
  = match l with
    | [] -> ()
    | hd :: tl -> snoc_cons tl h

let rec rev_involutive #a (l:list a)
  : Lemma (reverse (reverse l) == l)
  = match l with
    | [] -> ()
    | hd :: tl ->
      // (1) [reverse (reverse tl) == tl]
      rev_involutive tl;
      // (2) [reverse (append (reverse tl) [hd]) == h :: reverse (reverse tl)]
      snoc_cons (reverse tl) hd
      // These two facts are enough for Z3 to prove the lemma:
      //   reverse (reverse (hd :: tl))
      //   =def= reverse (append (reverse tl) [hd])
      //   =(2)= hd :: reverse (reverse tl)
      //   =(1)= hd :: tl
      //   =def= l

val rev_injective (#a:Type) (l1 l2:list a)
  : Lemma (requires reverse l1 == reverse l2)
          (ensures  l1 == l2)

