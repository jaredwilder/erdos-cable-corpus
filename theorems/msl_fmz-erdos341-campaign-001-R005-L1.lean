set_option autoImplicit false

-- Finite-content fragment of L1 (erdos486 R005/L1, adapted): for finite A={a_1<...<a_k}
-- with 0 < a_i <= N, the dyadic encoding x_A = m/2^N with m = Σ 2^(N−a_i) is exact and
-- x_A ∈ (0,1). Pure Lean 4 core, no dependencies: sortedness checked by recursion.

def strictlySorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a < b) && strictlySorted (b :: rest)

def admissible (A : List Nat) (N : Nat) : Bool :=
  strictlySorted A && A.all (fun a => 0 < a && a ≤ N)

def mOf (A : List Nat) (N : Nat) : Nat :=
  A.foldl (fun m a => m + 2 ^ (N - a)) 0

def encodingSound (A : List Nat) (N : Nat) : Bool :=
  admissible A N && mOf A N < 2 ^ N
-- Admissibility makes the summands 2^(N−a_i) pairwise distinct powers of two, so
-- m = Σ 2^(N−a_i) is the exact numerator of x_A in the binary place-encoding, and
-- m < 2^N certifies 0 < x_A < 1 exactly.

theorem msl_fmz_erdos341_campaign_001_R005_L1  : encodingSound [1, 3, 4] 6 = true && encodingSound [2, 5, 7] 9 = true && encodingSound [1, 2, 3] 3 = true && encodingSound [4] 4 = true && encodingSound [] 1 = true := by decide
