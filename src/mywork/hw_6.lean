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
- 
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
- 
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
- 
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
- 𝑅∪(𝑆∩𝑇)=(𝑅∪𝑆)∩(𝑅∪𝑇)
- 𝑅∩(𝑆∪𝑇)=(𝑅∩𝑆)∪(𝑅∩𝑇)
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
  cases xlmn,
  apply and.intro _ _,
  apply or.intro_left,
  exact xlmn,
  apply or.intro_left,
  exact xlmn,
  cases xlmn,
  apply and.intro _ _,
  apply or.intro_right,
  exact xlmn_left,
  apply or.intro_right,
  exact xlmn_right,
  -------------------
  assume xlmln,
  cases xlmln,
  apply or.intro_left,
  apply or.elim xlmln_left,
  assume xil,
  exact xil,
  assume xim,
  apply or.elim xlmln_right,
  assume xil,
  exact xil,
  assume xin,
  
  /-
  assume xlmn,
  apply and.intro _ _,
  cases xlmn,
  apply or.intro_left,
  exact xlmn,
  cases xlmn,
  apply or.intro_right,
  exact xlmn_left,
  cases xlmn,
  apply or.intro_left,
  exact xlmn,
  cases xlmn,
  apply or.intro_right,
  exact xlmn_right,
  assume xlmln,
  have xlm : x ∈ (L ∪ M) := and.elim_left xlmln,
   -/

  
end
/-
English Language Proof
- 
-/

