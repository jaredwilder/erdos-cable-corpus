# TheoremOS 0.9 — Recovered Formal Declaration Index

**Public release:** 2026-09-10  
**Source archive SHA-256:** `62471bce01f9da61239d1c0acc24325c2e9ea424642a346e74552335b19359bd`

> Authority boundary: this is a source-bound declaration index recovered from the estate atlas. The TheoremOS 0.9 checkpoint itself recorded 100/100 exact source bindings but **0 strict frontier closures** and **no qualified Lean ecosystem on that host**. `LEAN_THEOREM` below is the atlas/source declaration class, not a new kernel-verification claim from TheoremOS.

| declaration | atlas class | source | recovered signature excerpt |
|---|---|---|---|
| `convexUnitDistanceCounts_bddAbove` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/96.lean` | `(n : ℕ) : BddAbove <\| convexUnitDistanceCounts n` |
| `erdos124.converse` | `LEAN_LEMMA` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/124.lean` | `{D : Finset ℕ} (hD₃ : ∀ d ∈ D, 3 ≤ d)` |
| `erdos_1` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/1.lean` | `: ∃ C > (0 : ℝ), ∀ (N : ℕ) (A : Finset ℕ) (_ : IsSumDistinctSet A N),` |
| `erdos_1097.variants.lower_bound` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/1097.lean` | `: ∃ c > (0 : ℝ), ∀ᶠ n in Filter.atTop, ∃ (A : Finset ℤ),` |
| `erdos_11.variants.granville_soundararajan` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/11.lean` | `(H : type_of% erdos_11) :` |
| `erdos_1142.test_not_106` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/1142.lean` | `: ¬ Erdos1142Prop 106` |
| `erdos_12.parts.i` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/12.lean` | `: answer(True) ↔ ∃ (A : Set ℕ), IsGood A ∧` |
| `erdos_12.parts.ii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/12.lean` | `: answer(False) ↔ ∃ c > (0 : ℝ), ∀ (A : Set ℕ), IsGood A →` |
| `erdos_12.variants.erdos_sarkozy` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/12.lean` | `(f : ℕ → ℕ) (hf : atTop.Tendsto f atTop) :` |
| `erdos_12.variants.erdos_sarkozy_density_0` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/12.lean` | `(A : Set ℕ) (hA : IsGood A) : A.HasDensity 0` |
| `erdos_12.variants.schoen` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/12.lean` | `(A : Set ℕ) (hA : IsGood A) (hA' : A.Pairwise Nat.Coprime) :` |
| `erdos_120.variants.finite_set` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/120.lean` | `{A : Set ℝ} (h : A.Finite) : ¬ Erdos120For A` |
| `erdos_208.parts.ii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/208.lean` | `: answer(sorry) ↔ ∃ (c : ℕ → ℝ), (c =o[atTop] (1 : ℕ → ℝ)) ∧ ∀ᶠ n in atTop,` |
| `erdos_218.variants.ge` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/218.lean` | `: {n \| primeGap (n + 1) ≤ primeGap n}.HasDensity <\| 1 / 2` |
| `erdos_218.variants.infinite_equal_prime_gap` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/218.lean` | `: {n \| primeGap n = primeGap (n + 1)}.Infinite` |
| `erdos_218.variants.le` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/218.lean` | `: {n \| primeGap n ≤ primeGap (n + 1)}.HasDensity <\| 1 / 2` |
| `erdos_241.variants.generalization` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/241.lean` | `(r : ℕ) (hr : r ≥ 2) : BoseChowlaConjecture r` |
| `erdos_267` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/267.lean` | `: answer(sorry) ↔ ∀ᵉ (n : ℕ → ℕ) (c > (1 : ℚ)), StrictMono n → (∀ k, c ≤ n (k+1) / n k) →` |
| `erdos_267.variants.generalisation_ratio_limit_to_infinity` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/267.lean` | `: answer(sorry) ↔ ∀ (n : ℕ → ℕ),` |
| `erdos_274.variants.abelian` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/274.lean` | `{G : Type*} [Fintype G] [CommGroup G]` |
| `erdos_313.variants.solution_42_2_3_7` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/313.lean` | `: (42, {2, 3, 7}) ∈ erdos313Solutions` |
| `erdos_313.variants.solution_6_2_3` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/313.lean` | `: (6, {2, 3}) ∈ erdos313Solutions` |
| `erdos_346.variants.example` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/346.lean` | `: ∃ A : ℕ → ℕ, IsAddStronglyCompleteNatSeq A ∧` |
| `erdos_346.variants.f_isAddStronglyCompleteNatSeq` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/346.lean` | `: IsAddStronglyCompleteNatSeq f` |
| `erdos_346.variants.f_not_isAddComplete` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/346.lean` | `{B : Set ℕ} (h : B ⊆ range f) (hB : B.Infinite) :` |
| `erdos_359.parts.i` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/359.lean` | `(A : ℕ → ℕ) (hA : IsGoodFor A 1) :` |
| `erdos_359.parts.ii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/359.lean` | `(A : ℕ → ℕ) (hA : IsGoodFor A 1) (c : ℝ) (hc : 0 < c):` |
| `erdos_41.variants.pairwise` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/41.lean` | `(A : Set ℕ) (hA₂ : NtupleCondition A 2) (hA : A.Infinite) :` |
| `erdos_445.test.small_example` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/445.lean` | `: Erdos445Prop 1 5 1` |
| `erdos_517.variants.fejer` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/517.lean` | `{f : ℂ → ℂ} {n : ℕ → ℕ} (hn : HasFejerGaps n) {a : ℕ → ℂ}` |
| `erdos_567.parts.i` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/567.lean` | `: answer(sorry) ↔ IsRamseySizeLinear Q3` |
| `erdos_567.parts.ii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/567.lean` | `: answer(sorry) ↔ IsRamseySizeLinear K33` |
| `erdos_567.parts.iii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/567.lean` | `: answer(sorry) ↔ IsRamseySizeLinear H5` |
| `erdos_593.variants.implications_combine` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/593.lean` | `(h₁ : ∀ (W : Type) [Fintype W] (F : ThreeUniformHypergraph W),` |
| `erdos_593.variants.obligatory_monotone` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/593.lean` | `{W₁ W₂ : Type} [Fintype W₁] [Fintype W₂] [DecidableEq W₂]` |
| `erdos_593.variants.uncountable_vertices_if_large_chromatic` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/593.lean` | `{V : Type} (H : ThreeUniformHypergraph V) (hχ : ℵ₀ < H.chromaticCardinal) :` |
| `erdos_602.variants.single_set` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/602.lean` | `{α : Type*} (A : Set α) (hA : A.Infinite) :` |
| `erdos_602.variants.unique_index` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/602.lean` | `{α : Type*} (I : Type*) [Unique I]` |
| `erdos_680.parts.ii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/680.lean` | `: answer(sorry) ↔ ∀ ε > 0, ∃ C > 0,` |
| `erdos_770.parts.i` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/770.lean` | `: answer(sorry) ↔ ∀ p : ℕ, p.Prime → ∃ a, HasDensity {n \| h n = p} a` |
| `erdos_770.parts.ii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/770.lean` | `: answer(sorry) ↔ liminf h atTop = ⊤` |
| `erdos_770.parts.iii` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/770.lean` | `: answer(sorry) ↔ ∀ ε > 0, ∀ᶠ n in atTop,` |
| `erdos_770.variants.odd_h_unbounded` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/770.lean` | `: Unbounded (· ≤ ·) (ENat.toNat '' (h '' Odd))` |
| `erdos_770.variants.three` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/770.lean` | `: {n \| h n = 3}.Infinite` |
| `erdos_828.variants.lehmer_conjecture` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/828.lean` | `: answer(sorry) ↔ ∀ n > 1, φ n ∣ n - 1 ↔ Prime n` |
| `erdos_944.variants.large_k_for_any_r` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/944.lean` | `(r : ℕ) (hr : 1 ≤ r) : ∀ᶠ k in Filter.atTop,` |
| `erdos_945.variants.constant` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/945.lean` | `: answer(sorry) ↔ Erdos945Constant` |
| `erdos_945.variants.equivalence` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/945.lean` | `: Erdos945Prop ↔ Erdos945Constant` |
| `erdos_961.sylvester_schur` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/961.lean` | `(k : ℕ) (hk : 0 < k) : Erdos961Prop k k` |
| `erdos_961.variants.well_defined` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/961.lean` | `(k : ℕ) (hk : 0 < k): ∃ n, Erdos961Prop k n` |
| `evens_infinite` | `LEAN_LEMMA` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/602.lean` | `: Set.Infinite {n : ℕ \| Even n}` |
| `exists_three_consecutive_primes_in_ap` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/141.lean` | `: ∃ (s : Set ℕ), s.IsAPAndPrimeProgressionOfLength 3` |
| `first_three_odd_primes` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/141.lean` | `: ({3, 5, 7} : Set ℕ).IsPrimeProgressionOfLength 3` |
| `greedyUnitFractionRem_one` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/282.lean` | `(n : ℕ) : greedyUnitFractionRem .univ (1 / n) 1 = 0` |
| `greedyUnitFractionRem_sq_one` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/282.lean` | `: greedyUnitFractionRem { n \| IsSquare n } 1 0 = 0` |
| `greedyUnitFractionRem_zero` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/282.lean` | `(n : ℕ) : greedyUnitFractionRem .univ (1 / n) 0 = 0` |
| `herzog_schonheim` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/274.lean` | `{G : Type*} [Group G] (hG : 1 < ENat.card G) {ι : Type*} [Fintype ι]` |
| `horizontal_leg_valid` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/1212.lean` | `{a b c : ℕ} (hc : c.Composite) (ha2 : 2 ≤ a)` |
| `isClusterPrime_97_isLeast_non_cluster` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/17.lean` | `: IsLeast {p : ℕ \| p.Prime ∧ ¬ IsClusterPrime p} 97` |
| `odds_infinite` | `LEAN_LEMMA` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/602.lean` | `: Set.Infinite {n : ℕ \| Odd n}` |
| `right_neighbor_witness_free` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/1212.lean` | `{P : Finset ℕ} {x y : ℕ} (hP : ∀ p ∈ P, p.Prime)` |
| `vertical_leg_valid` | `LEAN_THEOREM` | `ORACLE-THEOREMOS-0.9.0/frontier100/source_snapshot/statements/1212.lean` | `{a b c : ℕ} (ha : a.Composite) (hb : 2 ≤ b)` |
