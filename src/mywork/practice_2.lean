/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro
/-
We can apply the introduction rule for true. QED. 
-/

example : false := _    -- trick question? why?
                        -- Yes, this is a trick question.
                        -- There is no proof for false. False means that there is
                        -- a lack of proofs.

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
      assume p,
      exact p,
      assume p1,
      exact p1,
  --backwards
    assume P,
    apply or.intro_left,
    exact P,
end
/-
We assume P ∨ P is true. Seperate this theorum into 2 routes, where P ∨ P implies P, and P
implies P ∨ P. For the first route, we can assume P ∨ P and apply the elimation rule for or. 
In both cases of or, we find that we are able to derive P. Then we continue onto our 
second route, where we assume P and apply the introduction rule for or. After doing so,
we are left with P, which has already been assumed to be true. QED.
-/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume pandp,
      apply and.elim pandp,
      assume p,
      assume p,
      exact p,
    assume P,
      apply and.intro P P,
end
/- 

-/
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume porq,
      apply or.elim porq,
        assume P,
        apply or.intro_right,
        exact P,
      apply or.intro_left,
    assume qorp,
      apply or.elim qorp,
        assume Q,
        apply or.intro_right,
        exact Q,
      apply or.intro_left,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume pandq,
      have p : P := and.elim_left pandq,
      have q : Q := and.elim_right pandq,
      have qp : Q ∧ P := and.intro q p,
      exact qp,
    assume qandp,
      have q : Q := and.elim_left qandp,
      have p : P := and.elim_right qandp,
      have pq : P ∧ Q := and.intro p q,
      exact pq,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    assume pqr,
      have p : P := and.elim_left pqr,
      have qr : Q ∨ R := and.elim_right pqr,
      apply or.elim qr,
        assume Q,
        apply or.intro_left,
        apply and.intro p Q,
          assume R,
          apply or.intro_right,
          apply and.intro p R,
    assume pqpr,
      apply or.elim pqpr,
        assume pq,
        have p : P := and.elim_left pq,
        apply and.intro p _,
          apply or.intro_left,
          exact and.elim_right pq,
      assume pr,
        have p : P := and.elim_left pr,
        apply and.intro p _,
          apply or.intro_right,
          exact and.elim_right pr,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
    assume pqr,
    apply or.elim pqr,
      assume P,
      apply and.intro _ _,
        apply or.intro_left,
        exact P,
          apply or.intro_left,
          exact P,
      assume qr,
        apply and.intro _ _,
          apply or.intro_right,
          exact and.elim_left qr,
          apply or.intro_right,
          exact and.elim_right qr,
      assume pqpr,
      apply or.intro_left,
      cases pqpr,
      apply or.elim pqpr_left _ _,
        assume p,
        exact p,
        assume q,
      
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume pandporq,
      exact and.elim_left pandporq,
    assume P,
    apply and.intro P _,
      apply or.intro_left,
      exact P,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume ppq,
    apply or.elim ppq,
    assume P,
    exact P,
    assume pq,
    exact and.elim_left pq,
    assume P,
    apply or.intro_left,
    exact P,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,
    assume h,
    apply true.intro,
    assume h,
    apply or.intro_right,
    apply true.intro,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume h,
    apply or.elim h,
    assume p,
    exact p,
    assume f,
    cases f,
    assume P,
    apply or.intro_left,
    exact P,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
    assume ptrue,
    exact and.elim_left ptrue,
    assume P,
    apply and.intro P true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
    assume pfalse,
    exact and.elim_right pfalse,
    assume f,
    apply and.intro _ f,
    cases f,
end


