import Carpooling.Deterministic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Carpooling
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma le_four_cuberoot {a p : ℝ} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (h : a^3 ≤ 64*p) : a ≤ 4 * p^((1:ℝ)/3) := by
  have hroot : (p^((1:ℝ)/3))^3 = p := by
    simpa using Real.rpow_inv_natCast_pow hp (by decide : (3:ℕ) ≠ 0)
  have hnonneg : 0 ≤ p^((1:ℝ)/3) := Real.rpow_nonneg hp _
  apply (pow_le_pow_iff_left₀ ha (by positivity) (by decide : (3:ℕ) ≠ 0)).mp
  nlinarith [hroot]

/-- Lemma 3.1, with the exact constant 4 and the n cutoff. -/
theorem lemma_3_1 {T : ℕ} (R : Run V T)
    (hinit : ∀ k, R.d 0 k ≤ 0) (i : V) :
    R.d T i ≤ min (4 * (expandingCount R T : ℝ)^((1:ℝ)/3)) (Fintype.card V) := by
  apply le_min
  · exact le_trans (le_max_left _ _) (le_four_cuberoot (le_max_right _ _)
      (Nat.cast_nonneg _) (positive_cube_bound R hinit i))
  · exact position_le_card R hinit i

/-- Theorem 1.1, explicit pointwise version of the maximum-over-prefixes bound. -/
theorem theorem_1_1 {T : ℕ} (R : Run V T)
    (hinit : ∀ k, R.d 0 k = 0) {t : ℕ} (ht : t ≤ T) (i : V) :
    |R.d t i| ≤ min (4 * (t : ℝ)^((1:ℝ)/3)) (Fintype.card V) := by
  obtain ⟨hc, hn⟩ := deterministic_upper_bound R hinit ht i
  exact le_min (le_four_cuberoot (abs_nonneg _) (Nat.cast_nonneg _) hc) hn

end Carpooling
