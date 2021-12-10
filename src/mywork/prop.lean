example : ∀ (n : ℕ), 2⁰ + 2¹ + ... + 2ⁿ = 2ⁿ⁺¹ - 1 :=
begin
  
end


/-
To prove that ∀ (n : ℕ), 2⁰ + 2¹ + ... + 2ⁿ = 2ⁿ⁺¹ - 1 :
first we must assume the base case where P 0  =0. 
Then from there we may assume that we have a proof for n'. 
With this, we can prove that the successor of n', or n' + 1 is 
equal to 1 + 2 + ... + 2^n' = 2^((n' + 1) + 1) - 1 by expanding P. 

-/