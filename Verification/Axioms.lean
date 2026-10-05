module

public import Catalan

/-!
# `Verification.Axioms`

Checks the public Catalan theorem declarations and their axioms.
-/

@[expose] public section

#check @Catalan.catalans_conjecture
#print axioms Catalan.catalans_conjecture

#check @Catalan.catalan_int
#print axioms Catalan.catalan_int

#check @Catalan.catalan_int_signed
#print axioms Catalan.catalan_int_signed

#check @Catalan.mihailescu_odd_primes
#print axioms Catalan.mihailescu_odd_primes

#check @Catalan.JSP.statement
#print axioms Catalan.JSP.statement
