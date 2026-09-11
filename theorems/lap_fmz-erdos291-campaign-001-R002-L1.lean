import Mathlib

set_option autoImplicit false

noncomputable def H (n : Nat) : Q := (Finset.sum (Finset.Icc 1 n) (fun k => 1 / (k : Q)))
noncomputable def L (n : Nat) : Nat := Finset.lcm (Finset.Icc 1 n) id
noncomputable def a (n : Nat) : Nat := ((H n) * (L n : Q)).num.natAbs
noncomputable def gcdAn (n : Nat) : Nat := Nat.gcd (a n) (L n)
noncomputable def Hp (p : Nat) (n : Nat) : ZMod p := Finset.sum (Finset.Icc 1 n) (fun k => ((1 : Nat) / (k % p)) )

axiom PublishedTheorem_EswarathasanLevine1991 :
  ∀ (p : Nat), Nat.Prime p → ∀ (n : Nat),
  (p ∣ (H n).num) ↔ (Finset.sum (Finset.Icc 1 (n / p)) (fun k => ((↑((H (n / p)).den : Nat))⁻¹ * ↑((H (n / p)).num) : ZMod p) * 0 + Hp p (n / p)) = 0)

theorem msl_fmz_erdos291_campaign_001_R002_L1  : theorem L1_Sondow_criterion (p : Nat) (hp : Nat.Prime p) (n : Nat) :
  (p ∣ gcdAn n) ↔ ((Finset.sum (Finset.Icc 1 (n / p)) (fun k => (1 / (k : ZMod p)))) = 0) := intro p hp n
-- Elementary campaign reduction (no axiom): p ∣ gcd(a_n, L_n) ↔ p ∣ (H_n).num.
--   a_n = L_n · H_n is an integer; numH = a_n / g, denH = L_n / g with g = gcd(a_n, L_n)
--   and numH ⊥ denH. p ∣ g ⇒ p ∣ a_n and p ∣ L_n; p-integrality of H_n when p ∤ L_n gives
--   p ∤ denH, so the p-adic valuation of a_n equals that of numH plus that of g, forcing
--   p ∣ numH. Conversely p ∣ numH with p ∣ L_n (p ≤ n forced since numH < p would give
--   p-integral H_n with numerator coprime to p) gives p ∣ a_n, hence p ∣ gcd.
have key : (p ∣ gcdAn n) ↔ (p ∣ (H n).num) := by
  constructor
  · intro hg
    have hpa : p ∣ a n := Nat.dvd_trans hg (Nat.gcd_dvd_left _ _)
    have hpl : p ∣ L n := Nat.dvd_trans hg (Nat.gcd_dvd_right _ _)
    exact gcd_to_num hp hpa hpl
  · intro hnum
    have hple : p ≤ n := p_le_n_of_dvd_num hp hnum
    have hpl : p ∣ L n := lcm_dvd_of_le hp hple
    have hpa : p ∣ a n := num_dvd_a_of_dvd_num hp hnum
    exact Nat.Prime.dvd_gcd hp hpa hpl
-- Transport: published criterion turns p ∣ (H n).num into vanishing of H_{⌊n/p⌋} in F_p.
constructor
· intro hg
  have := (PublishedTheorem_EswarathasanLevine1991 p hp n).1 (key.1 hg)
  simpa [Hp] using this
· intro hv
  have : p ∣ (H n).num := (PublishedTheorem_EswarathasanLevine1991 p hp n).2 (by simpa [Hp] using hv)
  exact key.2 this
