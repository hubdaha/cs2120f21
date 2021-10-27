-- Jumi Hall
-- computing ID: jah5py
-- github: hubdaha

import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example : ∀ {α : Type} (L : set α), L ∩ L = L := 
begin
  intros,
  apply set.ext,
  intros,
  apply iff.intro _ _,
  assume lnl,
  cases lnl,
  exact lnl_left,
  assume l,
  exact and.intro l l,
end


/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
example : ∀ {α : Type} (L M : set α), L ∪ M = M ∪ L :=
begin
  intros,
  apply set.ext,
  intros,
  apply iff.intro _ _,
  assume lum,
  cases lum,
  apply or.intro_right,
  exact lum,
  apply or.intro_left,
  exact lum,
  assume mul,
  cases mul,
  apply or.intro_right,
  exact mul,
  apply or.intro_left,
  exact mul,
end
/-
English Language Proof
- To prove that, for some sets L and M of alpha values, the union of L and M is equal to the union
of M and L, after introductions we may equate the equals sign to "if and only if". From here,
for the forwards proposition we may perform case analysis, giving us the proposition that an alpha 
value wil exist in the set L. With this, we can introduce an or statement for which the x will exist in
the M or L set. Then, for the backwards proposition we may perform case analysis again, giving us the 
proposition that an x value will exist in the set M. This allows us to introduce an or statement
for which the x will exist in the L or M set. We can also introduce an or statement for which the x
will exist in the L or M set using the other proposed case in which x will exist in the L set. QED.
-/
/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
example : ∀ {α : Type} (L : set α), (L ⊆ L) ∧ ∀ {α : Type} (L M N : set α ), (L ⊆ M → M ⊆ N → L ⊆ N) :=
begin
  intros,
  apply and.intro _ _,
  assume alpha,
  assume alphaL,
  exact alphaL,
  assume type,
  assume L,
  assume M,
  assume N,
  assume lsm,
  assume msn,
  assume alpha,
  assume alphaL,
  have alphaM : alpha ∈ M := lsm alphaL,
  exact msn alphaM,
end
/-
English Language Proof
- To prove that, for sets L M and N of alpha type values, that L is a subset of itself and that if L is a subset of M,
and M is a subset of N, then L is a subset of N, first we may split the function in two. We can assume that L is a subset of L
because all of its values will be in itself. Then, for the other proposition that we must prove, after assumptions
we may use the application of our proposition that L is a subset of M to the proposition that there is an alpha value
in L to prove that there is an alpha value in M. This allows us to prove that there is also an alpha value in N by applying the
proposition that M is a subset of N to the proposition that we just found. QED.
-/
/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
example : ∀ {α : Type} (L M N: set α), (L ∪ M ∪ N = L ∪ (M ∪ N)) ∧ (L ∩ M ∩ N = L ∩ (M ∩ N)) :=
begin
  intros,
  apply and.intro _ _,
  apply set.ext,
  assume alpha,
  apply iff.intro _ _,
  assume h,
  cases h,
  cases h with ail aim,
  apply or.intro_left,
  exact ail,
  apply or.intro_right,
  apply or.intro_left,
  exact aim,
  apply or.intro_right,
  apply or.intro_right,
  exact h,
  assume f,
  cases f with ail aimn,
  apply or.intro_left,
  apply or.intro_left,
  exact ail,
  cases aimn,
  apply or.intro_left,
  apply or.intro_right,
  exact aimn,
  apply or.intro_right,
  exact aimn,
  ----------
  apply set.ext,
  intros,
  apply iff.intro _ _,
  assume xlmn,
  cases xlmn,
  apply and.intro _ _,
  exact and.elim_left xlmn_left,
  have xim : x ∈ M := and.elim_right xlmn_left,
  exact and.intro xim xlmn_right,
  assume xlnm,
  cases xlnm,
  apply and.intro _ _,
  have xim : x ∈ M := and.elim_left xlnm_right,
  exact and.intro xlnm_left xim,
  exact and.elim_right xlnm_right,  
end
/-
English Language Proof
- To prove that, where L M and N are sets of alpha values that whether we are finding the union or intersections, 
when grouped differently, are still equal, we may simplify the process by dividing the proposition into two 
and statements and equating the equals sign to "if and only if", thus giving us a forwards and backwards direction.
For the forwards direction, we can use case analysis and introduce or statements to prove the forwards proposition. For
the backwards direction, we may again equate the equals sign to "if and only if", giving us another set of forward
and backwards propostions. For the forward direction, we can use case analysis and simplify the goals by seperating them
into two and statements. We can then use the elimination rules to simplify our assumptions. We can introduce and statements,
finishing the proof of the forwards direction. For the backwards direction, we can use case analysis again
and then simplify the problem by dividing the proposition into two and statements. To get the first part of the and statement
we may use an elimination ruke for and on one of our assumptions and then introduce two together into
their own and statement. Then we may get the other part of the and statement using the and elimination rule again. QED.
-/

/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/
example : ∀ {α : Type} (L M N: set α ), L ∩ (M ∩ N) = (L ∩ M) ∩ (L ∩ N):= 
begin
  intros,
  apply set.ext,
  intros,
  apply iff.intro _ _,
  assume xlmn,
  apply and.intro _ _,
  apply and.elim xlmn,
  assume xil,
  assume ximn,
  exact and.intro xil (and.elim_left ximn),
  cases xlmn,
  cases xlmn_right,
  exact and.intro xlmn_left xlmn_right_right,
  assume xlmln,
  cases xlmln,
  cases xlmln_left,
  cases xlmln_right,
  apply and.intro _ _,
  exact xlmln_right_left,
  exact and.intro xlmln_left_right xlmln_right_right,
end
/-
English Language Proof
- To prove that ∩ is left-distributive over ∩, we may say that for all L M N sets of alpha type 
values, L ∩ (M ∩ N) = (L ∩ M) ∩ (L ∩ N). With this proposition, we may equate the equals sign to "if
and only if", thus giving us a forwards and backwards direction. For the forwards direction we can 
simplify by dividing the probem into two parts of an and statement, Then we can use the and elimination rule
to find needed assumptions, and apply them together into an and statement using the introduction rule. 
Then we may perform case analyses leaving us only to introduce our assumptions into an and statement. 
Then for the backwards direction we may use case analyses and the introduction rule for and to apply everything 
together into one statement. QED.
-/
/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/
-- 
example : ∀ {α : Type} (L M N: set α ), L ∪ (M ∩ N) = (L ∪ M) ∩ (L ∪ N):= 
begin
  intros,
  apply set.ext,
  intros,
  apply iff.intro _ _,
  assume xlmn,
  apply and.intro _ _,
  cases xlmn,
  apply or.intro_left,
  exact xlmn,
  apply or.intro_right,
  exact and.elim_left xlmn,
  cases xlmn,
  apply or.intro_left,
  exact xlmn,
  apply or.intro_right,
  exact and.elim_right xlmn,
  -------------------
  assume xlmln,
  cases xlmln,
  cases xlmln_left,
  cases xlmln_right,
  apply or.intro_left,
  exact xlmln_left,
  apply or.intro_left,
  exact xlmln_left,
  cases xlmln_right,
  apply or.intro_left,
  exact xlmln_right,
  apply or.intro_right,
  exact and.intro xlmln_left xlmln_right, 
end
/-
English Language Proof
- To prove that ∪ is left-distributive over ∩, we may say that for sets L M and N of type alpha values,
L ∪ (M ∩ N) = (L ∪ M) ∩ (L ∪ N). With this, we can equate the equals sign to "if and only if",
giving us two directions of propositions to prove. For the forwards direction, we can perform case analysis
and introduce or statements using our assumptions. Then, through case analyses we can simplify our assumptions 
and introduce them together into and statements (because we can read ∩ as and) and prove this propostion. For the 
backwards proposition, we can use case analyses on our assumptions and the use introduction rules for or to produce
or statements that we need. then we can use case analysis again and introduce our various statements into a 
bigger "and" statement. QED. 
-/

