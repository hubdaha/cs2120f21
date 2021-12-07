import algebra.algebra.basic tactic.noncomm_ring

namespace hidden

inductive nat : Type
| zero : nat
| succ (n' : nat ) : nat  -- recursive self referential conductor

def z := nat.zero
#check z
#reduce z

def o := nat.succ z
#check o
#reduce o

def t := nat.succ o
#check t
#reduce t

def f : nat :=
begin
  exact nat.succ (nat.succ t)
end
#check f
#reduce f

def inc' : nat → nat :=
begin
  assume n,
  exact nat.succ n,
end
#reduce inc' f

def inc : nat → nat
| n := nat.succ n

#reduce inc f

def dec : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := n'

def add : nat → nat → nat
| (nat.zero) (m) := m
| (nat.succ n') (m) := nat.succ (add n' m)
-- tbh still dont know what n' is
#reduce add f t

def mul : nat → nat → nat
| (nat.zero) (m) := nat.zero
| (nat.succ n') (m) := add (m) (mul n' m)
#reduce mul f t
#reduce mul t t 

def sum_to : nat → nat
| (nat.zero) := nat.zero
| (nat.succ n') := add (sum_to n') (inc n')
#reduce sum_to f


def exp : nat → nat → nat 
| 
end hidden

def P : nat → Prop
| n := hidden.sum to n )
