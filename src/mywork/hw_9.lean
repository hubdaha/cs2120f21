--Jumi Hall
--jah5py
--github : hubdaha
/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter. 

#1. Solve probem #1, first sentence only.
Write the principle of complete induction using the notation of symbolic logic.
"Let P be any property that satisfies the following: for any natural number n, 
whenever P holds of every number less than n it also holds of n. Then P holds
of every natural number."
-/

-- P (ℕ → Prop): ∀ (a b : ℕ) a < b, P(a) → P(b) →  ∀ (n : ℕ), P(n)

/-
#2. Solve at least one of #2 and #3. Give
    detailed but informal proofs. 

#2 Show that for every 𝑛, 0^2+1^2+2^2+…𝑛^2=(1/6)𝑛(1+𝑛)(1+2𝑛).
We prove this by induction on n. In the base case, when n = 0, we have 0^2 = (1/6)(0)(1+0)(1+2*0) = 0, as required. 
For the induction step, fix n, and assume the inductive hypothesis
0^2+1^2+2^2+…𝑛^2=(1/6)𝑛(1+𝑛)(1+2𝑛)
We need to show that this same claim holds with n replaced by n +1;
0^2+1^2+2^2+…(𝑛+1)^2= (1/6)(𝑛+1)(1+(𝑛+1))(1+2(𝑛+1))
(1/6)𝑛(1+𝑛)(1+2𝑛) + (n+1)^2 = (1/6)(𝑛+1)(1+(𝑛+1))(1+2(𝑛+1))
n(1+n)(1+2n) + 6(n+1)^2 = (n+1)(1+(n+1))(1+2n+2)
n(1+n)(1+2n) + 6(n+1)(n+1)) = (n+1)(n+2)(2n+3)
n(1+2n) + 6(n+1) = (n+2)(2n+3)
2n^2+n = 2n^2 + 7n + 6 - 6n - 6
2n^2 + n = 2n^2 + n

The claim holds and therefore we have proved this by induction on n. 


-/

