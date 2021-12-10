-- Jumi Hall
-- jah5py
import data.set algebra.algebra.basic tactic.ring

/-
Complete this file in your Lean IDE and submit it 
through Collab under the assignment tab for Final Exam.
-/

/-
#1A [5 points]. formally state the proposition that
"logical or is commutative". You will need to quantify
over arbitrary propositions, P and Q, and please use
the iff (↔) operator to express the idea that the two
different propositions in your answer are equivalent. 
-/

def or_commutes : Prop :=
  ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P 

/-
#1B [5 points]. Give a formal proof of or_commutes.
-/

example : or_commutes :=
begin
unfold or_commutes,
assume p q,
apply iff.intro,
assume porq,
cases porq,
apply or.intro_right,
exact porq,
apply or.intro_left,
exact porq,
assume qorp,
cases qorp,
apply or.intro_right,
exact qorp,
apply or.intro_left,
exact qorp,
end

/-
#1C [5 points]. Write a concise (not verbose) and 
precise English-language proof of this conjecture. 
-/

/-
ANSWER HERE: To prove that logical or is commutative, first we must
assume that P and Q are arbitrary but specific propositions. Then we may
split the "if and only if" proposition into two seperate pathways. For the 
first pathway, we may assume that we have a proof of P ∨ Q. With this, we can 
perform case analysis through or elimination, leaving us to show that, when given
either P or Q, we can give back a proof of P ∨ Q. Then, going down the second
pathway we do much the same thing; first we assume that we have a proof of Q ∨ P,
and then through case analysis using or elimination we can use the or introduction
rules to create or statements from the P or Q that we are given. 

-/


/-
#2A [5 points]. Write a formal definition of the 
proposition that if P and Q are arbitrary properties
of natural numbers, and if m and n are arbitrary 
natural numbers, then if ∀ n, P n → Q n, then if 
m = n, the if P n then Q m.
-/

def eq_elim : Prop := 
  ∀ (nat : ℕ )
    (P Q: ℕ → Prop)
    (m n : ℕ )
    (h : ∀ n, P n → Q n)
    (i : m = n),
  P n → Q m


/-
#2B [5 points]. Write a formal proof of this conjecture.
Remember that you can rewrite in either direction "at"
a given assumption in the context.
-/

def eq_elim_pf : eq_elim :=
begin
  unfold eq_elim,
  assume nat,
  assume p_prop q_prop,
  assume m n,
  assume h,
  assume i,
  assume pn,
  have hm := h m,
  apply hm,
  rw i at hm,
  



end


/-
#3A [5 points]. Formally express the proposition
that if Ball is an arbitrary type of object, and 
Red and Blue are properties of balls, then if there 
is a ball that is Red and Blue then there is a ball
that is Blue. You might want to use parentheses to
avoid any problems with the parsing of in your
expression.
-/

axioms
(Ball : Type)
(Red : Ball → Prop)
(Blue : Ball → Prop)

def red_blue : Prop := 
  (∃ (b: Ball), Red b ∧ Blue b) → (∃ (b: Ball), Blue b)

/-
#3B [5 points]. Give a concise English language
proof of this conjecture, being careful to state
the principles that you're using at each step in
your proof.
-/

/-
ANSWER: First we may assume that there exists an object of type
Ball. We can assume that this Ball has the properties of being 
Red and Blue. We can then perform case analysis on this existential
assumption to derive a name for the ball and a proof of its properties. We can
then apply the exists introduction law by using b as a witness to the proposition
to be proved. What is left to be proven is simple through and elimination. 

-/

/-
#3C [5 points]. Give a formal proof.
-/

example : red_blue :=
begin
  assume h,
  cases h with b red_and_blue,
  apply exists.intro b _,
  exact and.elim_right red_and_blue,
end

/-
#4A [5 points]. Complete the following formal 
definition of what it means for a set X to be 
a subset of a set Y.
-/

def subset_def : Prop := 
  ∀ (α : Type) 
  (X Y : set α),
  ∀ (a : α), a ∈ X → a ∈ Y


/-
#4B [5 points]. Give a formal definition of what 
it means for a set X to be a strict subset of a 
set Y.
-/

def subset_strict : Prop := 
  ∀ (α : Type) 
  (X Y : set α),
  ∀ (a : α), (a ∈ X → a ∈ Y) ∧ ∃ (b : α), (b ∈ Y) ∧ ¬ (b ∈ X)

/-
#5A [5 points]. Briefly explain what it means for 
a function, f : X → X (where X is a type) to be 
injective.
-/

/-
ANSWER: For a function to be injective, it must be "one-to-one". In other
words, it must pass the horizontal line test. The same first value may not relate
to multiple, different values. If two values relate to the same
value, then the two values must be equal to each other. 

-/

/-
#5B [5 points]. Does every injective function have 
an inverse that is also a function? Give a brief, 
compelling explanation of your answer (in English).
-/

/-
ANSWER: No. Even if an injective function passes the horizontal line test, 
that does not necessarily mean that it will pass the horizontal line test when it is 
inversed. An injective function, although it cannot be one-to-many, it can be many-to-one. 
This means that it is fully plausible for the function of its inverse to have multiple
y values for one x value.

-/

/-
#6 [5 points].

Suppose f : ℤ → ℕ is a function with the integers as 
its domain and the natural numbers as its codomain, and 
that it associates each integer, x, with its absolute 
value, |x|, of type nat. In other words, f x = |x|.

Which of the following properties of functions does 
the function f have? Answer Y or N (for yes or no) 
for each entry and give a very brief explanation of
your answer.

- Is it total? Y, it is defined for every value in its domain
- Is it surjective? Y, it will cover all of the natural numbers because it is infinite
- Is it injective? Y, there will not be any values of x that lead to multiple values of y
- Is it invertible? N, there are repeated y-values, meaning that if inverted the function would no
                        longer be a valid function, there would be many-to-one values. 
-/

/-
#7A [5 points]. Is the following relation transitive?
Briefly explain your answer.

{ (1,2), (2, 3), (3, 4), (1, 3), (2, 4) }

This relation is not transitive. Since the relation has the pairs (1,3) and (3,4),
the relation must also have the pair (1,4) in order to be transitive, and it does not. 
-/

/-
#7B [5 points]. Is the following relation on the 
natural numbers reflexive? Explain. Be careful.
{ (0,0), (1,1), (2,2) } 

Upon first glance, yes. This relation is reflexive because it reltes every value to itself.
They all equal themselves. 

-/

/-
#7C [5 points]. Give an example of a familiar 
arithmetic relation with each of the following 
properties and give a very short explanation 
for your answer. 

- symmetric: y = x when y is related to x, x is also related to y.
- partial order: y ≤ 5 every element is NOT related to every other element; the relation is not strongly connected
- asymmetric: y < x  when y is related to x, that means that x is not related to y
- antisymmetric: y ≤ x  if x is related to y when y is related to x, that can only mean that they are equal
- equivalence: y = x it is reflexive, symmetric, and transitive
-/

/-
#8A [5 points]. Give a natural language proof by 
induction for the proposition that for any natural
number, n, six times the sum of the squares of the 
numbers from 0 to n is equal to n(n + 1)(2n + 1). 

To prove by induction that for any natural number n, six times the sum
of the squares of the numbers from 0 to n is equal to n(n + 1)(2n + 1), first
we must start with our base case. The base case will be for when our natural 
number is 0. When it is 0, the sum of the squares from 0 to 0, when plugged into the
"n(n + 1)(2n + 1)" equation, gives us 0, as required. Then for the induction step, we
need to assume the inductive hypothesis 6(0^2+1^2+2^2+…𝑛^2)=𝑛(1+𝑛)(1+2𝑛). We need to show
that this same claim holds when n is replaced by n + 1. This will look like:

6(0^2+1^2+2^2+…(𝑛+1)^2)= (𝑛+1)(1+(𝑛+1))(1+2(𝑛+1))

The left hand side is equivalent to the sum of all the squares of the predecessor
of n+1, plus (n + 1)^2. This means that we can replace the left hand side with the right
hand side of our inductive hypothesis:

n(1+n)(1+2n) + 6(n+1)^2 = (n+1)(1+(n+1))(1+2n+2)

From here it is simple algebra to show that the claim holds. Thus, we have the base case
and induction step needed to build a proof by induction. 

-/


/-
#8B [15 points]. Give a formal proof of this
proposition. 

A. Formally define P as the property that the
six times the sum of the squares of the numbers 
from 0 to a  given natural number n is equal to 
n( n + 1 )( 2n + 1 ). To do this you will have
to define a function, call it sum_sq, that
computes the sum of the squares of the natural
numbers from zero to any given natural number,
n.
-/

def sum_sq : ℕ → ℕ 
| (nat.zero) := nat.zero
| (nat.succ n') := (sum_sq n') + (nat.succ n') * (nat.succ n')

def P : ℕ → Prop :=
  λ n, (6 * sum_sq n) = (n*((n + 1) * ((2 * n) + 1)))

/-
B. Formally define conjecture to be the proposition
that every natural number has this property, P.
-/

def conjecture := ∀ n, P n

/-
C. Use example to assert that this universal 
generalization is true (has a proof), and give
a formal proof.
-/
example : conjecture :=
begin
  unfold conjecture,
  assume n,
  unfold P,
  induction n with ih n',
  apply eq.refl,
  unfold sum_sq,
  rw mul_add,
  rw n',
  rw ih.succ_eq_add_one,
  ring,
end

/-
Extra credit. You have seen that addition (m + n)
is increment iteratively applied to n m times; that 
multiplication (m * n) is addition of m iterated
n times; and that exponentiation, (m^n), is the 
multiplication of m iterated n times. It's clear
that this process of defining new functions can
keep going. Implement the function, f, that we get
by iterating the exponentiation of m n times and
give a few test cases that show that (1) you can
figure out what the correct answer should be, and
(2) that your function computes the right asnwers
for your test cases.
-/

def f : ℕ → ℕ → ℕ 
| (nat.zero)(m) := nat.succ(nat.zero)
| (nat.succ n') (m) := exp (m) (f n' ^ m)

