axioms
  (Person : Type) -- person is a type of thing
  (Likes : Person → Person → Prop) -- 2 place predicate to represent a binary relation
                                   -- set of pairs. person 1 likes person 2 and person 2 likes person 1?

example :
  ¬ (∀ p : Person, Likes p p) ↔ 
  ∃ p : Person, ¬ Likes p p :=
begin
  apply iff.intro _ _,
  assume noteveryplikesp,
  have f := classical.em (∃ (p : Person), ¬ Likes p p),
  cases f,
  exact f,
    have contra : ∀ (p : Person), Likes p p := _,
    contradiction,
      assume p,
      have g := classical.em (Likes p p),
      cases g,
      exact g,
        have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
        contradiction,
          assume existspnotlikep,
          
end
