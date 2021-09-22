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
We can assume P is true. We then seperate the theorum into 2 routes, where P ∧ P
implies P, and P implies P ∧ P. For the first route, we can assume P ∧ P and apply the
elimination rule for and, which allows us now state that P → P → P. Assuming P, we can
then say that P does imply P, which in turn implies P. Then we move onto the second
route, where we start with assuming an arbitrary P. With this, we use the introduction
rule for and and fill in the sides with P. QED.
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
/-
We can assume that P and Q are true. We then seperate the theorum into 2 routes using the 
introduction rule for if and only if, where
P ∨ Q implies Q ∨ P, and Q ∨ P implies P ∨ Q. For the first route, we can assume P ∨ Q. 
With this, we apply the elimiation rule for or. We now have 3 paths to take. We can then assume
P, and apply the introduction rule for or to the right side of P ∨ Q, leaving us with P. Then to 
complete the second goal where Q implies Q ∧ P, we can apply the introduction rule for or to the
left of this proposition. Now with this route completed we can move to the 2nd route, where
we are trying to prove that Q ∨ P implies P ∨ Q. We this we can assume Q ∨ P. Then we can 
apply the elimination rule for or to Q ∨ P, giving us 2 routes to go down. We then assume Q and 
apply the introduction rule for or to the right side, giving us Q, which we have. Then we apply
the introduction rule for or to the left side. QED.
-/

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
/- 
For this proposition, we must assume P and Q. Then we apply the introduction rule for if
and only if. This gives us 2 propositions to prove, where P ∧ Q implies Q ∧ P, and Q ∧ 
P implies P ∧ Q. Going down the first route we assume P ∧ Q. Then, using the elimination rule
for and, we can isolate P and Q with the left and right elimination rules, respectively. We can
also create the proposition Q ∧ P with the introduction rule for and, giving us Q ∧ P. For the
second route, where Q ∧ P implies P ∧ Q, we assume Q ∧ P. Then we isolate Q and P respectively through
the elimation rules for and on the left and the right. Then we create P ∧ Q with the introduction rule 
for and. QED.
-/

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
/- 
First we assume that we have P Q and R. Then we must apply the introduciton rule for if and
only if, giving us two paths that consist of P ∧ (Q ∨ R) implying (P ∧ Q) ∨ (P ∧ R), and
(P ∧ Q) ∨ (P ∧ R) implying P ∧ (Q ∨ R). For the first proposition, we assume that we have
P ∧ (Q ∨ R). With this, we isolate P and Q ∧ R using the left and right elimination rules for and,
respectively. Then we can apply the elimination rule for or to Q ∧ R, seperating the cases for
this or statement. When we assume Q for Q → ∧ Q ∨ P ∧ R, we can then apply the 
introduction rule for or to the left side of the if statement, leaving us with P ∧ Q for our goal.
This goal can be completed by applying the introduction rule for and to P and Q. Now we must assume
R and this time apply the introduction rule for or to the right side of the if statement, leaving us
with P ∧ R for our goal. We can complete this goal using the introduction rule for and and applying
it to P and R. Now we must go down the opposite route, where (P ∧ Q) ∨ (P ∧ R) implies P ∧ (Q ∨ R).
To start, we assume (P ∧ Q) ∨ (P ∧ R). Now we apply the elimination rule for or, giving us
the possible routes to go down with this or statement. On the left side of the or statement is P ∧ Q,
which we assume to be true. Then we can apply the introduction rule for and to P, which we can isolate
through the elimination rule for and to the left side of P ∧ Q. The other side of this introduction rule for 
and will be applied to Q ∨ R, which can be derived from applying the introduction rule for or 
to the left side of Q ∨ R, leaving us with Q. We can derive Q through the elimination rule for and 
to the right side of P ∧ Q. Now we have one goal left. First we can isolate p through the elimination rule
for and to the left side of P ∧ R. Then we can apply the introduction rule for or to the right side
of Q ∨ R, leaving us with R, which we can derive from using the elimination rule for and and applying it
to the right side of P ∧ R. This allows us to apply the introduction rule for and to P and R. 
-/

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


