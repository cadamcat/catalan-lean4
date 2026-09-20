/- Independent core-only specifications; placeholders occur only in this challenge. -/
set_option autoImplicit false
namespace StrictCatalan

def ProperPower (n : Nat) : Prop :=
  ∃ m k : Nat, Nat.le 2 m ∧ Nat.le 2 k ∧ Nat.pow m k = n

def Prime (p : Nat) : Prop :=
  Nat.le 2 p ∧ ∀ d : Nat, (∃ k : Nat, p = Nat.mul d k) → d = 1 ∨ d = p

theorem jsp :
    (ProperPower 8 ∧ ProperPower 9) ∧
    ∀ n : Nat, Nat.lt 0 n → ProperPower n → ProperPower (Nat.add n 1) → n = 8 := sorry

theorem natural :
    ∀ (a b x y : Nat),
    Nat.lt 1 a → Nat.lt 1 b → Nat.lt 0 x → Nat.lt 0 y →
    Nat.sub (Nat.pow x a) (Nat.pow y b) = 1 →
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := sorry

theorem positive_int :
    ∀ (x y : Int) (a b : Nat),
    Nat.lt 1 a → Nat.lt 1 b → Int.lt 1 x → Int.lt 1 y →
    Int.pow x a = Int.add (Int.pow y b) 1 →
    a = 2 ∧ b = 3 ∧ x = 3 ∧ y = 2 := sorry

theorem signed_int :
    ∀ (x y : Int) (p q : Nat),
    Nat.le 2 p → Nat.le 2 q → x ≠ 0 → y ≠ 0 →
    Int.sub (Int.pow x p) (Int.pow y q) = 1 →
    p = 2 ∧ q = 3 ∧ (x = 3 ∨ x = Int.neg 3) ∧ y = 2 := sorry

theorem odd_primes :
    ∀ (p q : Nat),
    Prime p → Prime q → p ≠ 2 → q ≠ 2 →
    ∀ (x y : Int), x ≠ 0 → y ≠ 0 →
    Int.pow x p ≠ Int.add (Int.pow y q) 1 := sorry

end StrictCatalan
