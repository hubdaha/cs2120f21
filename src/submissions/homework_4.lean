/-
Group: Earth, Wind, and Fire
Jumi Hall, jah5py@virginia.edu, https://github.com/hubdaha/cs2120f21.git
Connor McCaffrey, cam7qp@virginia.edu, https://github.com/camccaffrey/cs2120.git
Jakob Kauffmann, jgk2qq@virginia.edu, https://github.com/jakekauff/CS2120F21.git
-/

-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  cases h,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have f : false := h (eq.refl 0),
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
  apply iff.intro _ _,
    assume notpq,
      have pornp : P ∨ ¬P := classical.em P,
      have qornq : Q ∨ ¬Q := classical.em Q,
      cases pornp,
      cases qornq,
      have pq : P ∧ Q := and.intro pornp qornq,
      have f : false := notpq pq,
      exact false.elim f,
      apply or.intro_right,
      exact qornq,
      apply or.intro_left,
      exact pornp,
    assume npornq,
      apply not.intro,
      cases npornq,
      assume pq,
      have p : P := and.elim_left pq,
      apply npornq p,
      assume pq,
      have q : Q := and.elim_right pq,
      apply npornq q,  
end


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → ¬P ∧ ¬Q :=
begin
  assume P Q,
  assume notpq,
  have pornp := classical.em P,
  have qornq := classical.em Q,
  cases pornp with p np,
  have f : false := notpq (or.intro_left _ p),
  exact false.elim f,
  cases qornq with q nq,
  have f : false := notpq (or.intro_right _ q),
  exact false.elim f,
  exact and.intro np nq,
end


-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro _ _,
    assume p_or_npandq, 
    apply or.elim p_or_npandq,
    assume p,
    apply or.intro_left,
    exact p,
     assume npandq,
      have q := and.elim_right npandq,
      apply or.intro_right,
      exact q,
    assume porq,
      apply or.elim porq,
      assume p,

    apply or.intro_left,
      exact p,
      assume q,
      have pornp := classical.em P,
      apply or.elim pornp,
      assume p,
      apply or.intro_left,
      exact p,
      assume np,
      apply or.intro_right,
      apply and.intro np q,
end


-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro _ _,
    assume porqandporr,
      have porq: P ∨ Q := and.elim_left porqandporr,
      have porr: P ∨ R := and.elim_right porqandporr,
      cases porq with p q,
      apply or.intro_left,
      exact p,
      cases porr with p r,
      apply or.intro_left,
      exact p,
      have qr : Q ∧ R := and.intro q r,
      apply or.intro_right,
      exact qr,

      assume porqandr,
      cases porqandr with p qandr,
      apply and.intro _ _,
        apply or.intro_left,
        exact p,
        apply or.intro_left,
        exact p,
      apply and.intro _ _,
        apply or.intro_right,
        exact and.elim_left qandr,
        apply or.intro_right,
        exact and.elim_right qandr,
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro _ _,
  assume poqaros,
  have porq: P ∨ Q := and.elim_left poqaros,
  have rors: R ∨ S := and.elim_right poqaros,
    cases porq with p q,
    cases rors with r s,
    have pr : P ∧ R := and.intro p r,
    apply or.intro_left,
    exact pr,
    have ps : P ∧ S := and.intro p s,
    apply or.intro_right _ _,
    apply or.intro_left _ ps,
    cases rors with r s,
    have qr: Q ∧ R := and.intro q r,
    apply or.intro_right _ _,
    apply or.intro_right _ _,
    apply or.intro_left _ qr,
    have qs: Q ∧ S := and.intro q s,
    apply or.intro_right _ _,
    apply or.intro_right _ _,
    apply or.intro_right _ qs,
      assume prpsqrqs,
      cases prpsqrqs with pr psqrqs,
      have p: P := and.elim_left pr,
      have r: R := and.elim_right pr,
      have porq: P ∨ Q := or.intro_left _ p,
      have rors: R ∨ S := or.intro_left _ r,
      exact and.intro porq rors,
        cases psqrqs with ps qrqs,
        have p: P := and.elim_left ps,
        have s: S := and.elim_right ps,
        have porq: P ∨ Q := or.intro_left _ p,
        have rors: R ∨ S := or.intro_right _ s,
        exact and.intro porq rors,
          cases qrqs with qr qs,
          have q: Q := and.elim_left qr,
          have r: R := and.elim_right qr,
          have porq: P ∨ Q := or.intro_right _ q,
          have rors: R ∨ S := or.intro_left _ r,
          exact and.intro porq rors,
            have q: Q := and.elim_left qs,
            have s: S := and.elim_right qs,
            have porq: P ∨ Q := or.intro_right _ q,
            have rors: R ∨ S := or.intro_right _ s,
            exact and.intro porq rors,
end


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∀ (n : ℕ), (n = 0) ∨ (n ≠ 0) :=
begin
  assume n,
  apply classical.em,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro _ _,
    assume pq,
    cases classical.em P with p np,
    have q: Q := pq p,
    apply or.intro_right,
    exact q,
      exact or.intro_left _ np,
      assume nporq,
      assume p,
      cases nporq with np q,
      have f: false := np p,
      exact false.elim f,
      exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpq,
  assume notq,
  apply not.intro,
  assume p,
  have q: Q := pimpq p,
  contradiction, 
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume npimpnq,
  assume q,
  cases classical.em P with p np,
  exact p,
    have nq: ¬Q := npimpnq np,
    contradiction,
end

