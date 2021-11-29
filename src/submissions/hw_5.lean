-- Jumi Hall
-- github: hubdaha
/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition/informal proof here: If there exists a function f for which
every type α value implies a type β value, then, for every arbitrary a of type α, 
if the predicate p is true for a, then this implies an a, which having been applied 
to the function f, for which the predicate q will be true. If there exists an a of type
alpha for which the predicate p is true, then there exists a b of type beta for which
the predicate q is true. 
-/


-- Give your formal proof here
begin
 intros e h,
 apply exists.elim e,
 apply exists.elim h,
 intros alpha palpha ab f,
 apply exists.intro _ _,
 exact ab alpha,
 apply f alpha,
 exact palpha,
end

-- informal proof: 
-- We can prove this propostion through the performance of case analysis on the assumptions.
-- Then we may prove there exists a beta value by providing an alpha value to the alpha → beta function,
-- leaving us to apply our main function to the alpha value, leaving us to prove that our alpha
-- value applied to the predicate p is true, which was already one of our assumptions. 