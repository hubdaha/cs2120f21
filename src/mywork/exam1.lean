/-
Jumi Hall
jah5py 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
---------------------------------- elim
     pf (Q)
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q,
  assume p2q,
  exact p2q,
end

-- Extra credit [2 points]. Who invented this principle?

--Aristotle
---------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- The introduction rule for true is a proof of true. Thus it is invariably logically true. 

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- Given an arbitrary proposition P proved true and an arbitrary proposition Q proved true, 
-- we can state that the proposition of P ∧ Q is also true. 

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.
-/
/-
--------------------------------------------------------------
inference rule notation:

(P Q : Prop) (pq : P ∧ Q)
---------------------------- elim_left
        pf (P)

(P Q : Prop) (pq : P ∧ Q)
---------------------------- elim_right
        pf (Q)
-----------------------------------------------------------------
english language:

The left ∧ elimination rule allows us to deduce a proof of P from a 
proof of P ∧ Q.

The right ∧ elimination rule allows us to deduce a proof of Q from a 
proof of P ∧ Q.
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q : Prop), Q ∧ P → P := 
begin
  assume P Q,
  assume qp,
  exact and.elim_right qp,
end




-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- Show that you have an arbitrary t of type T. Because t is arbitrary,
-- the property Q is true for all t. The introduction rule for ∀ is to assume.

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                (Q)

-- Where T is a type and Q is an arbitrary proposition, given a proof of
where all t of type T implies the arbitrary proposition Q, we can derive
a proof of Q from a proof of t. 

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- To derive a proof of Q from pf, one must apply pf to the value t of 
Type T. 
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, give answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalize the following assumptions here
  -- (1) Lynn is a person
  -- (2) Lynn knows logic
  -- (1) (Lynn : Person)
  -- (2) (Lynn : Person), KnowsLogic Lynn

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/

example : ∀ (p : Person) (Lynn : Person), (KnowsLogic Lynn) → (BetterComputerScientist Lynn) := 
begin
assume p,
assume Lynn,
assume knowslogic,
apply LogicMakesYouBetterAtCS,
exact knowslogic,
end


-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

-- To prove the proposition ¬P, first you must assume P to be true. 
-- Then, you must derive a contradiction, proving P to be false. 
-- With a proof of P → false, by definition you can derive a proof of ¬P. 

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬P and show that ¬P → false.
From this derivation you can conclude ¬¬P.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is intuitively valid, and that accepting the axiom
of the excluded middle suffices to establish negation
elimination (better called double false elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (A B : Prop), (A ↔ B) → ((A → B) → (B → A)) :=
begin
  assume A B,
  assume aiffb,
  have ab : A → B := iff.elim_left aiffb,
  have ba : B → A := iff.elim_right aiffb,
  assume ab,
  assume b,
  apply ba b,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    
-- English rendition: For any Person p, if that Person is nice and talented,
-- then any Person q will like that Person p. If we are given that JohnLennon is
-- a person, and that he is Nice and Talented, then we can conclude that any person p
-- likes JohnLennon. 
example : ELJL :=
begin
  unfold ELJL,
  intros,
  apply elantp,
  exact and.elim_left JLNT,
    exact and.elim_right JLNT, 
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    -- heavy and red, heavy and blue, light and red, light and blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀ (A : Prop), ¬A ∨ A ↔ ¬A

example : negelim_equiv_exmid :=
begin
  unfold negelim_equiv_exmid,
  intros,
  apply iff.intro _ _,
  assume notaora,
  cases notaora,
  exact notaora,
  
end



/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
there is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∀ p q : Person, Loves p q ) → ∃ p q: Person, Loves q p :=
begin
  assume personeveryoneloves,
  have f := classical.em (∃ (p : Person), ¬ Loves p q),
end

