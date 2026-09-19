import Catalan

set_option autoImplicit false
namespace CatalanVerification

theorem natural_statement :
    ∀ (a b x y : _root_.Nat),
      _root_.Nat.lt (nat_lit 1) a → _root_.Nat.lt (nat_lit 1) b →
      _root_.Nat.lt (nat_lit 0) x → _root_.Nat.lt (nat_lit 0) y →
      @_root_.Eq _root_.Nat (_root_.Nat.sub (_root_.Nat.pow x a) (_root_.Nat.pow y b)) (nat_lit 1) →
      _root_.And (@_root_.Eq _root_.Nat a (nat_lit 2))
        (_root_.And (@_root_.Eq _root_.Nat b (nat_lit 3))
          (_root_.And (@_root_.Eq _root_.Nat x (nat_lit 3)) (@_root_.Eq _root_.Nat y (nat_lit 2)))) :=
  fun a b x y ha hb hx hy h => Catalan.catalans_conjecture a b x y ha hb hx hy h

theorem signed_statement :
    ∀ (x y : _root_.Int) (p q : _root_.Nat),
      _root_.Nat.le (nat_lit 2) p → _root_.Nat.le (nat_lit 2) q →
      _root_.Not (@_root_.Eq _root_.Int x (_root_.Int.ofNat (nat_lit 0))) →
      _root_.Not (@_root_.Eq _root_.Int y (_root_.Int.ofNat (nat_lit 0))) →
      @_root_.Eq _root_.Int
        (_root_.Int.sub (_root_.Int.pow x p) (_root_.Int.pow y q))
        (_root_.Int.ofNat (nat_lit 1)) →
      _root_.And (@_root_.Eq _root_.Nat p (nat_lit 2))
        (_root_.And (@_root_.Eq _root_.Nat q (nat_lit 3))
          (_root_.And
            (_root_.Or (@_root_.Eq _root_.Int x (_root_.Int.ofNat (nat_lit 3)))
              (@_root_.Eq _root_.Int x (_root_.Int.neg (_root_.Int.ofNat (nat_lit 3)))))
            (@_root_.Eq _root_.Int y (_root_.Int.ofNat (nat_lit 2))))) :=
  fun x y p q hp hq hx hy h => Catalan.catalan_int_signed x y p q hp hq hx hy h

def IntendedPower (n : Nat) : Prop :=
  ∃ m k : Nat, Nat.le 2 m ∧ Nat.le 2 k ∧ Nat.pow m k = n

theorem consecutive_powers :
    (IntendedPower 8 ∧ IntendedPower 9) ∧
      ∀ n : Nat, Nat.lt 0 n → IntendedPower n → IntendedPower (Nat.add n 1) → n = 8 :=
  Catalan.JSP.statement

#print axioms CatalanVerification.natural_statement
#print axioms CatalanVerification.signed_statement
#print axioms CatalanVerification.consecutive_powers

end CatalanVerification
