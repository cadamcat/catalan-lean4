import Mathlib

/-! Smoke test: the environment resolves Mathlib names used by the Catalan interface. -/

#check @Nat.Prime
#check @IsCyclotomicExtension
#check @NumberField.RingOfIntegers
#check @MonoidAlgebra

example : Nat.Prime 3 := by norm_num
