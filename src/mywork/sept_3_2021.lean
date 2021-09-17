theorem eq_symm : 
  ∀ (T : Type)(x y : T), x = y → y = x := 
  begin
    assume (T : Type),
    assume (x y : T),
    assume (e : x = y),
    rw e,
  end


/-
Theorem: Equality is symmetic.
∀ (T : Type)(x y : T), x = y → y = x.

Proof: What we really need to show is that 
∀ (T : Type)(x y : T), x = y → y = x.
First we will assume that T is any type, and we 
have objects x and y of this type. 
What remains to be shown is that if x = y,
then y = x. To prove this, we will assume the 
premise that x = y, but by the xiom of substitutability
of equals and using the assumed fact that x = y, we
can rewrite x in the goal as y, yielding y = y as our new 
proof goal. But this is true by the adiom of reflexitivity 
of equality. QED.

-/

/- 
Prove that equality is transitive.
-/

theorem eq_trans :
  ∀ (T : Type)(x y z : T), x = y → y = z → x = z :=
  begin
    assume (T : Type),
    assume (x y z : T),
    assume (e1 : x = y),
    assume (e2 : y = z),
    rw e1,
    exact e2,
  end

theorem eq_symm_and_trans :
  ∀ (T : Type)(x y z : T), x = y → z = y → z = x :=
  begin
    assume (T: Type),
    assume (x y z : T),
    assume (e1 : x = y),
    assume (e2 : z = y),
    rw e1,
    rw e2,
  end
