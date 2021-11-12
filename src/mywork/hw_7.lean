-- Jumi Hall, jah5py, github: hubdaha
-- Partnered with: Connor McCaffrey, cam7qe, github: camccaffrey
                -- Jakob Kauffmann, jgk2qq, github: jakekauff


import data.set
import tactic.ring

namespace relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  
-- Strangely Lean's library does define asymmetric, so here it is.
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x


/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (x y : β), r x y) → asymmetric r → ¬reflexive r :=
begin
  -- a relation is asymmetric if you know that if a is related to b b is not related a. 
  -- a relation is reflexive if every value is related to itself.
  -- a relationis not reflexive if there is at least one value x for which the pair (x,x) does
  -- not exist. 
  unfold asymmetric reflexive,
  assume ex,
  assume asymm,
  assume refl,
  cases ex with b pf,
  have rbb : r b b := refl b,
  have contra := asymm rbb,
  apply contra,
  exact rbb,
end

/-
Proof: Supposing that β is inhabited and r is asymmetric, we can show
that r is not reflexive. We can do this through proof by negation where we
will assume that r is reflexive and show that this leads to a contradiction.
First we expand the definitions. Then we can use case analysis through exists 
elimination. By applying the existing beta value to our asymmetry definition,
we can assume that b is related to itself. With "r b b", we can apply this to 
the ¬ r b b, giving us a contradiction. QED.

The proposition is not still true if you remove the first condition that β is inhabited. 
If beta is not necessarily inhabited, that means that we could have an empty set for which
would not apply to the proposition, providing a counterexample. 
-/

/-
Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. Is it actually true?
If not, what condition needs to be added to make it true? See
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html
-/

example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric,
  assume b,
  assume trans,
  assume refl,
  assume asymm,
  cases b with b tru,
  have rbb := refl b,
  have nrbb := asymm rbb,
  contradiction,
end

-- It is not true, we needed to add the condition that there exists a beta value in order
-- for it to become true. 

/-
State and prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and then give
an informal proof, of this proposition. You may use the following
formal definition of the powerset of a given set, s. 
-/

def powerset (s : set β) := { s' | s' ⊆ s}

example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1ins s2ins,
  assume s1s2 s2s1,
  apply set.ext,
  assume b,
  apply iff.intro,
  assume bs1,
  apply s1s2 bs1,
  assume bs2,
  apply s2s1 bs2,
end

/- 
Proof: We may suppose that s is a set of type β and that s1 and s2 are one of the subsets 
in the powerset of s. We may prove that s1 is equal to s2 from the propositions that s1 is a subset of
s2 and that s2 is also a subset of s1. To do so, first we can equate the equals sign to an if and
only if through set extentionality. If and only if creates two pathways for which we may show by 
application of our propositions and assumptions that our goals are true. QED.
-/

/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/

def divides (m n : ℕ) := ∃ k, n = k * m

/- 
#3: Formally and informally state and prove each of the following propositions.
Remember that the ring tactic is useful for producing proofs of
algebraic equalities involving + and *. You can use the phrase,
"by basic algebra" when translating the use of this tactic into
English.
-/

-- 3a: For any n, 1 divides n.

example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end

/- 
Proof: We can prove that for any n, 1 divides n. First we may assume that there exists an n of
type ℕ. Then we can unfold the definition of divides, leaving us to conclude through exists introduction
the value of n should fill in for k, leavins us with an arbitrary n = n*1. QED.
-/

-- 3b. For any n, n divides n

example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end

/- 
Proof: We may provide a proof for which any n divides n. To do so we may assume we have an
n of type ℕ. Then we can unfold the definition of divides, leaving us to show that 1 should be the
value in place of k in order for this to be true. QED.
-/

-- #3c. divides is reflexive (use our reflexive predicate)

example : reflexive divides :=
begin
  unfold reflexive,
  unfold divides,
  intros,
  apply exists.intro 1,
  ring,
end 

/- 
Proof: To show that divides is reflexive, first we expand the definitions of 
reflexive and divides. Then we may assume we have an n of type ℕ. After this we are prepared 
to show that for this function to be true the k vale must be 1, leaving us with an arbitrary 
n = 1 * n. QED.
-/

-- #3d. divides is transitive

example : transitive divides :=
begin
  assume h n k,
  unfold divides transitive,
  assume a b,
  apply exists.intro 1,
  ring,
  cases a with nat l,
  cases b with nat2 e,
  rw e,
  rw l,
  ring,
  have nat1: nat = 1 := sorry,
  rw nat1,
  have nat21: nat2 =1 := sorry,
  rw nat21,
  ring,
end 

/- 
Proof: To provide a proof that divides is transitive, we can expand on the definitions
of transitive and divides. Then we may show that k must equal 1. We can then perform case 
analyses on our exists statements. We may rewrite the outputs of these cases so that our final 
goal can be reached by assuming that the natural missing numbers are equal to 1. QED. 
-/

/- 
#3d. is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/- 
Divides is not symmetric because, if we were to have the values of 2 and 1, 1 divided by 2 
would not result in a natural number. 
-/

/- 
#3e. Prove that divides is antisymmetric. Use the
anti_symmetric predicate to state the proposition
formally.
-/

example : anti_symmetric divides := 
begin
  unfold anti_symmetric divides,
  assume x y kx ky,
  cases kx with kxv kxpf,
  cases ky with kyv kypf,
  rw kxpf at kypf,
  rw kxpf,
  have kxv1 : kxv = 1 := sorry,
  rw kxv1,
  ring,
end

/- 
Proof: To prove that divides is antisymmetric, first we can expand the definitions of antisymmetric
and divides. Then we can perform case analyses on our assumed exists statements, leaving us to 
rewrite the cases. It is obvious that the value of kxv must be 1, leaving us again to simply 
rewrite our goal and then solve simple algebra. QED.
-/ 



example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume h x k,
  have nk := h k,
  contradiction,
end

/- 
Proof: To prove that if we have a relation that is asymmetric then that relation must be
irreflexive, first we expand on those definitions. Then we make our assumptions and with these 
we can use proof by negation. We may apply our assumptions together to show that we have 
the relation  ¬ r x x, which directly contradicts the assumed relation of r x x. QED.
-/

example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive,
  assume h k,
  assume x y,
  assume rxy,
  assume nryx,
  have f := k rxy nryx,
  have nrxx := h x,
  contradiction,
end

/- 
Proof: To prove that if we have a relation that is both irreflexive and
transitive then it must be asymmetric, we can first unfold those definitions before we
make our assumptions. After the assumptions of transitivity and irreflexivity are made,
we can start our proof by negation. This proof by negation is completed by applying transitivity
to r x y and r x z together to show that we derive an r x x. Then to show ¬ r x x, we can apply
irreflexivity to x, giving us a contradiction. QED.
-/

example : (∃ (b : β), true) → transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume b trans symm irrefl,


end

/- We do not think that this proposition is provable as is. We added a beta value in the beginning
so that an empty set would not be a counterexample. However, we were still unable to prove this
proposition. 
-/
end relation
