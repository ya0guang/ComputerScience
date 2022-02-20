(* --------------------------------------------------------------------------
 * 
 * models.thy
 * Writing Definitions in Isabelle/HOL.
 *
 * (c) 2015, Wolfgang Schreiner: Thinking Programs.
 *
 * -------------------------------------------------------------------------- *)
theory models
imports Main
begin

(* --------------------------------------------------------------------------
 * Part 1: function and predicate definitions
 * -------------------------------------------------------------------------- *)

(* the type of infinite sequences *)
type_synonym 'a seq = "nat \<Rightarrow> 'a"

(* a predicate: s is a sequence that holds c everywhere *)
definition isconst :: "'a \<Rightarrow> 'a seq \<Rightarrow> bool" where
"isconst c s = (\<forall>i::nat. s i = c)"

(* a function: the sequence that holds c everywhere *)
definition cseq :: "'a \<Rightarrow> 'a seq" where
"cseq c = (\<lambda>i::nat. c)"

(* the relationship between these notions *)
lemma S1: "\<forall>(c::'a) (s::'a seq). isconst c (cseq c)"
by (simp add: cseq_def isconst_def)

(* an implicitly defined function with a precondition: a position of c in s *)
definition vpos :: "'a \<Rightarrow> 'a seq \<Rightarrow> nat" where
"vpos c s = (SOME n::nat. (\<exists>i::nat. s i = c) \<longrightarrow> s n = c)"

(* some knowledge about this function *)
lemma S2 : "\<forall>(c::'a)(s::'a seq). \<not>(\<forall>i::nat. s i \<noteq> c) \<longrightarrow> s(vpos c s) = c"
by (metis (mono_tags, lifting) someI_ex vpos_def)

(* another implicitly defined function *)
definition const :: "'a seq \<Rightarrow> 'a" where
"const s = (SOME c::'a. isconst c s)"

(* some knowledge about this function *)
lemma S3: "\<forall>c::'a. const (cseq c) = c"
by (metis S1 const_def isconst_def someI_ex)

(* s is a sequence that holds the same value everywhere *)
definition iscseq :: "'a seq \<Rightarrow> bool" where
"iscseq s = (\<exists>c::'a. isconst c s)"

(* some more knowledge about const *)
lemma S4: "\<forall>s::'a seq. iscseq s \<longrightarrow> (\<forall>i::nat. s i = const s)"
by (metis const_def isconst_def iscseq_def someI_ex)

(* the sum of two sequences *)
definition addseq :: "('a::ring) seq \<Rightarrow> 'a seq \<Rightarrow> 'a seq" where
"addseq s1 s2 = (\<lambda>i::nat. (s1 i) + (s2 i))"

(* adding two constant sequences yields a constant sequence *)
lemma S5: "\<forall>(c1::'a::ring)(c2::'a::ring). iscseq(addseq (cseq c1) (cseq c2))"
by (simp add: addseq_def cseq_def isconst_def iscseq_def)

(* --------------------------------------------------------------------------
 * Part 2: the theory of sets
 * -------------------------------------------------------------------------- *)

(* sets of integers *)
type_synonym iset = "int set"

(* some basic properties *)
lemma U1: "\<forall>(a::iset)(b::iset)(c::iset). a \<union> (b \<inter> c) = (a \<union> b) \<inter> (a \<union> c)"
by auto
lemma U2: "\<forall>(a::iset)(b::iset). a \<subseteq> b \<longrightarrow> a \<union> b = b"
by auto
lemma U3: "\<forall>(a::iset)(b::iset). a \<inter> b \<noteq> {} \<longrightarrow> a - b \<subset> a"
by blast

(* the "is not empty" predicate *)
definition notempty :: "iset \<Rightarrow> bool" where
"notempty s = (\<exists>x::int. x \<in> s)"

(* the integers from n to m *)
definition ints :: "int \<Rightarrow> int \<Rightarrow> iset" where
"ints n m = { i::int. n \<le> i \<and> i \<le> m }"

(* a first lemma *)
lemma L1: "\<forall>(n::int)(m::int). n \<le> m \<longleftrightarrow> notempty (ints n m)"
using notempty_def ints_def by auto

(* adding an integer to a set *)
definition add :: "int \<Rightarrow> iset \<Rightarrow> iset" where
"add i s = { (i+x) | (x::int). x \<in> s }"

(* some lemmas about adding an integer to a set *)
lemma L2: "\<forall>(i::int). add 0 s = s" 
by (simp add: add_def)
lemma L3: "\<forall>(s::iset)(i::int)(x::int). x \<in> (add i s) \<longleftrightarrow> x-i \<in> s"
using add_def by force
lemma L4: "\<forall>(s::iset)(i::int)(j::int). add i (add j s) = add (i+j) s"
by (smt Collect_cong L3 add_def mem_Collect_eq)

(* integer m is the maximum of integer set s *)
definition ismax :: "int \<Rightarrow> iset \<Rightarrow> bool" where
"ismax m s = (m \<in> s \<and> (\<forall>x::int. x \<in> s \<longrightarrow> x \<le> m))"

(* integer set s has a maximum *)
definition hasmax :: "iset \<Rightarrow> bool" where
"hasmax s = (\<exists>m::int. ismax m s)"

(* the maximum of an integer set (if it exists) *)
definition max :: "iset \<Rightarrow> int" where
"max s = (SOME (m::int). ismax m s)"

(* some properties of the maximum *)
lemma M1: "\<forall>(s::iset). hasmax s \<longrightarrow> 
  max s \<in> s \<and> (\<forall>x::int. x \<in> s \<longrightarrow> x \<le> max s)"
by (metis hasmax_def ismax_def models.max_def someI_ex)
lemma M2: "\<forall>(s::iset). hasmax s \<longrightarrow>
  (\<forall>x::int. x \<in> s \<and> x \<noteq> max s \<longrightarrow> x < max s)"
using M1 by fastforce
lemma M3: "\<forall>(s::iset). hasmax s \<and> hasmax(s - { max s }) \<longrightarrow> 
  max s > max (s - { max s })"
using M1 M2 by blast

end
(* --------------------------------------------------------------------------
 * end of file
 * -------------------------------------------------------------------------- *)