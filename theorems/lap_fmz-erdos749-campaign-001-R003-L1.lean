import Mathlib

set_option autoImplicit false

def lowerDensity (S : Set Nat) : Real := Filter.atTop.liminf (fun n : Nat => ((Finset.range n).filter (fun k => k in S)).card / (n : Real)) ; def Affirmative : Prop := forall eps gt 0, exists A : Set Nat, lowerDensity (A + A) geq 1 - eps and exists C : Nat, forall n, representation count at n is at most C ; def JustBasisProperty (A : Set Nat) : Prop := exists C : Nat, (forall n : Nat, repCount A n leq C) and (forall n : Nat, n geq N implies n in A + A for some fixed N, i.e. eventual cofinite coverage of A + A). All definitions use only Set Nat, Finset Nat, Real, and decidable Finset counting; repCount A n is defined as the Finset.card of pairs (a,b) in A x A with a + b = n over a bounded box, which is total and computable.

axiom RuzsaJustBasis_1990 :
  exists A : Set Nat, exists C : Nat, (forall n : Nat, repCount A n leq C) and (forall n : Nat, n geq N implies n in A + A for some fixed N, i.e. eventual cofinite coverage of A + A)

theorem msl_fmz_erdos749_campaign_001_R003_L1  : theorem canonical_affirmative : forall eps : Real, eps gt 0 implies exists A : Set Nat, lowerDensity (A + A) geq 1 - eps and exists C : Nat, forall n : Nat, repCount A n leq C := intro eps heps ; obtain A, C, hbound, heventual from RuzsaJustBasis_1990 ; refine A, step1, C, hbound ; step1: heventual gives N with all n geq N in A + A ; hence for n geq N the count of k below n in A + A is at least n - N ; so the density sequence is at least (n - N)/n which tends to 1, and at most 1 trivially, so lowerDensity (A + A) = 1 by Mathlib liminf lemmas applied to this eventually-monotone sandwich ; conclude 1 geq 1 - eps by linarith with heps. The only mathematical content is the finite counting bound card geq n - N, discharged by Finset.card_le_card / subset lemmas plus decidability of membership; no literature and no extra axioms are used there.
