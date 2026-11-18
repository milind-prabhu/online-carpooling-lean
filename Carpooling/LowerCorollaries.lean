import Carpooling.FinalLower

namespace Carpooling
open Finset
open scoped Classical

/-- Explicit vanishing-error modulus for the paper's 1-o(1) probability.
For each fixed a and k, n≥2^(2ak) makes the failure probability at most 1/k.
The rate constant remains (64a)^(-1/3), independent of n and k. -/
theorem theorem_1_3_with_error (n d a k : ℕ) (hd : 2 ≤ d) (hn : d < n)
    (heven : (n*d)%2 = 0) (ha48 : 48 ≤ a) (hscale : 6*Nat.log 2 n ≤ a*(d+1))
    (hk : 0 < k) (hlarge : 2^(2*a*k) ≤ n) :
    ∃ (G : FiniteCarpoolGraph) (h : ℕ), StochasticLowerGuarantee n d a h G ∧
      ∀ R : UnitOnlineRule G.graph (Fintype.card G.Vertex),
        uniformProb (univ \ integerDiscrepancyEvent R.run h) ≤ 1/(k:ℝ) := by
  obtain ⟨G,h,hG⟩ := theorem_1_3 n d a hd hn heven ha48 hscale
  refine ⟨G,h,hG,?_⟩
  intro R
  have hb := hG.2.2.2.2 R
  have hl : 2*a*k ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide : 1 < 2) hlarge
  have hap : 0 < a := by omega
  have hN : 10*k ≤ d+1 := by
    have hm : a*(10*k) ≤ a*(d+1) := by nlinarith
    by_contra hbad
    have hgt := Nat.mul_lt_mul_of_pos_left (show d+1 < 10*k by omega) hap
    omega
  have hNR : (0:ℝ) < (d+1:ℕ) := by positivity
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  apply hb.trans
  apply (div_le_div_iff₀ hNR hkR).mpr
  simp only [one_mul]
  exact_mod_cast hN

/-- The lower bound remains valid after any finite, nonuniform distribution
over independent random seeds. Each seed can choose a different causal rule. -/
theorem randomized_lower_bound {n d a h : ℕ} {G : FiniteCarpoolGraph}
    (hG : StochasticLowerGuarantee n d a h G)
    {S : Type*} [Fintype S] (w : S → ℝ) (hw : ∀ s, 0 ≤ w s) (hsum : ∑ s, w s = 1)
    (R : S → UnitOnlineRule G.graph (Fintype.card G.Vertex)) :
    (∑ s, w s*uniformProb (univ \ integerDiscrepancyEvent (R s).run h)) ≤
      10/((d+1:ℕ):ℝ) := by
  calc
    _ ≤ ∑ s, w s*(10/((d+1:ℕ):ℝ)) :=
      sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hG.2.2.2.2 (R s)) (hw s))
    _ = _ := by rw [←sum_mul,hsum,one_mul]

end Carpooling
