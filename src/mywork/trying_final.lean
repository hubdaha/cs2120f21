import algebra.algebra.basic
import tactic.ring
/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
-/
def sum_to_of_squares : ℕ → ℕ 
| (nat.zero) := nat.zero
| (nat.succ n') := (sum_to_of_squares n') + (nat.succ n') * (nat.succ n')

def P : ℕ → Prop :=
  λ n, 6 * sum_to_of_squares n
  = (n * (1+n) * (1+2*n))

def conjecture := ∀ n, P n

theorem sum_to_opt : conjecture :=
begin
  unfold conjecture,
  assume n,
  unfold P,
  induction n with n' ih_n',
  apply rfl,
  unfold sum_to_of_squares,
  rw mul_add,
  rw ih_n',
  rw nat.succ_eq_add_one,
  ring,
end



/-
#2: Formal or detailed informal proofs 10-13
#3 (Extra Credit): #5 or #9
-/

/-
#10 Give an informal but detailed proof that for every natural number 
𝑛, 1⋅𝑛=𝑛, using a proof by induction, the definition of multiplication, 
and the theorems proved in Section 17.4.
-/

def



/-
Show that multiplication distributes over addition. In other words, prove that for natural numbers 𝑚, 𝑛, and 𝑘, 𝑚(𝑛+𝑘)=𝑚𝑛+𝑚𝑘. You should use the definitions of addition and multiplication and facts proved in Section 17.4 (but nothing more).

Prove the multiplication is associative, in the same way. You can use any of the facts proved in Section 17.4 and the previous exercise.

Prove that multiplication is commutative.
-/
