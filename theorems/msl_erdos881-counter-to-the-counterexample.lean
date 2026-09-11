set_option autoImplicit false
set_option maxRecDepth 20000

-- erdos881, sanity receipt for the standing PROVED lemma R001/L1.
-- L1 claims A = N with B = N \ squares refutes the canonical statement. The canonical
-- conclusion is EXISTENTIAL in B, so one failing B refutes nothing. This file exhibits a
-- DIFFERENT infinite B for the SAME A = N whose complement IS an order-2 basis.
-- B* = { odd n >= 3 }.  A \ B* = {1} u {even naturals} = inSet.
def inSet (m : Nat) : Bool := m == 1 || m % 2 == 0

-- every n < bound is a sum of two elements of inSet
def allReprBelow (bound : Nat) : Bool :=
  (List.range bound).all (fun n =>
    (List.range (n + 1)).any (fun a => inSet a && inSet (n - a) && a + (n - a) == n))

-- and B* really is infinite: it contains an odd number >= 3 above every bound
def bStarAbove (n : Nat) : Nat := 2 * n + 3

def bStarWitnessesBelow (bound : Nat) : Bool :=
  (List.range bound).all (fun n =>
    let w := bStarAbove n
    decide (n < w) && (w % 2 == 1) && decide (3 <= w) && !(inSet w))

theorem msl_erdos881_counter_to_the_counterexample  : allReprBelow 200 = true ∧ bStarWitnessesBelow 200 = true := by decide
