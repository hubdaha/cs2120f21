axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop := P → Q

axiom p : P
-- assume P is true
-- assume we have a proof of P (p)

axiom pq : if_P_is_true_then_so_is_Q
-- assume that we have a proof, pq, of P → Q

-- intro for implies: assume premise, show conclusion
-- elimination rule for implies (how to use): just apply it <3 

#check P → Q
#check pq
#check p
#check (pq p)

/- 
Suppose P and Q are propositions and you know that P → Q
and that P are both true. Show that Q is true.add_key_equivalence

Proof: Apply the truth of P → Q to the truth of P 
to derive the truth of Q.

Proof: By the elimination rule for → with pq applied to p.

Proof: By "modus ponens". QED
-/

/- 
FORALL
-/

axioms 
  (T : Type)
  (propertyT : T → Prop)
  (t : T)
  (a : ∀ (x : T), propertyT x ) -- proof that every object of type T has propertyT


-- Does t have property (propertyT)?

example: propertyT t := a t

#check a t

/- 
AND & →
-/

axioms (P Q : Prop)

/- 
Want a proof of P ∧ Q. 
-/


