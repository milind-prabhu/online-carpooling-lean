import Carpooling.Spreadness
import Carpooling.Potential
import Mathlib.Data.Real.Archimedean

namespace Carpooling
open scoped Classical
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma topSum_sq_le {x : V → ℝ} {r : ℕ} (hr : r ≤ Fintype.card V)
    (hs : 0 ≤ topSum x r) : (topSum x r)^2 ≤ (r : ℝ) * potential x := by
  let A := topSet x r
  have hc : A.card = r := (topSet_spec x hr).1
  have hsum : topSum x r ≤ ∑ k ∈ A, max (x k) 0 :=
    sum_le_sum fun k _ => le_max_left _ _
  have hcs := sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) (fun k => max (x k) 0)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one, hc] at hcs
  have hsub : (∑ k ∈ A, (max (x k) 0)^2) ≤ potential x := by
    apply sum_le_sum_of_subset_of_nonneg (subset_univ A)
    intro k _ _; exact sq_nonneg _
  have hsq : (topSum x r)^2 ≤ (∑ k ∈ A, max (x k) 0)^2 :=
    pow_le_pow_left₀ hs hsum 2
  exact hsq.trans (hcs.trans (mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg r)))

lemma Run.total_nonpos {T : ℕ} (R : Run V T) (hinit : ∀ k, R.d 0 k ≤ 0)
    {t : ℕ} (ht : t ≤ T) : (∑ k, R.d t k) ≤ 0 := by
  induction t with
  | zero => exact sum_nonpos fun k _ => hinit k
  | succ t ih => rw [(R.step t (by omega)).sum_preserved]; exact ih (by omega)

/-- The n part of Lemma 3.1. -/
theorem position_le_card {T : ℕ} (R : Run V T) (hinit : ∀ k, R.d 0 k ≤ 0)
    (i : V) : R.d T i ≤ Fintype.card V := by
  by_contra hn
  have hnD : (Fintype.card V : ℝ) < R.d T i := lt_of_not_ge hn
  have hnpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨t, ht, hspread⟩ := spreadness R hinit (le_refl (R.d T i)) hnpos
    (le_refl (Fintype.card V)) (le_of_lt hnD)
  rw [topSum_all] at hspread
  have hsum := R.total_nonpos hinit ht
  have hcast : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hprod : 0 < (Fintype.card V : ℝ) * (R.d T i - Fintype.card V + 1) :=
    mul_pos hcast (by linarith)
  linarith

lemma expandingCount_mono {T : ℕ} (R : Run V T) {s t : ℕ} (hst : s ≤ t) :
    expandingCount R s ≤ expandingCount R t := by
  classical
  apply card_le_card
  exact filter_subset_filter _ (range_mono hst)

/-- Lemma 3.1 in polynomial form: equivalent to the stated cube-root bound.
The exact count of expanding moves, rather than T, appears on the right. -/
theorem positive_cube_bound {T : ℕ} (R : Run V T)
    (hinit : ∀ k, R.d 0 k ≤ 0) (i : V) :
    (max (R.d T i) 0)^3 ≤ 64 * (expandingCount R T : ℝ) := by
  let D := R.d T i
  let p := expandingCount R T
  change (max D 0)^3 ≤ 64 * (p : ℝ)
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  by_cases hD : D ≤ 0
  · simp only [max_eq_right hD, zero_pow (by decide : 3 ≠ 0)]
    positivity
  rw [max_eq_left (le_of_lt (lt_of_not_ge hD))]
  have hDpos : 0 < D := lt_of_not_ge hD
  have hpot := potential_bound R hinit (le_refl T)
  have hone : posSq D ≤ potential (R.d T) :=
    single_le_sum (f := fun k => posSq (R.d T k)) (fun k _ => posSq_nonneg _) (mem_univ i)
  have hp_pos : 0 < p := by
    by_contra hn
    have hpzero : p = 0 := by omega
    have hs : posSq D = D^2 := by simp [posSq, max_eq_left (le_of_lt hDpos)]
    change potential (R.d T) ≤ 2 * (p : ℝ) at hpot
    rw [hpzero, Nat.cast_zero, mul_zero] at hpot
    nlinarith
  have hp_one : (1 : ℝ) ≤ p := by exact_mod_cast hp_pos
  by_cases hsmall : D < 2
  · have hDsq : D^2 < 4 := by nlinarith
    have hmul : D^2 * D < 4 * 2 :=
      mul_lt_mul hDsq hsmall.le hDpos (by norm_num)
    nlinarith
  have hDtwo : 2 ≤ D := le_of_not_gt hsmall
  let r := ⌊D/2⌋₊ + 1
  have hr : 1 ≤ r := by omega
  have hfloor := Nat.floor_le (by linarith : (0 : ℝ) ≤ D/2)
  have hfloorlt := Nat.lt_floor_add_one (D/2)
  have hrlo : D/2 ≤ (r : ℝ) := by exact le_of_lt (by simpa [r] using hfloorlt)
  have hrhi : (r : ℝ) ≤ D/2+1 := by dsimp [r]; push_cast; linarith
  have hrD : (r : ℝ) ≤ D := by linarith
  have hDn : D ≤ Fintype.card V := position_le_card R hinit i
  have hrn : r ≤ Fintype.card V := by exact_mod_cast (le_trans hrD hDn)
  obtain ⟨t, ht, hspread⟩ := spreadness R hinit (le_refl D) hr hrn hrD
  have hB : D/2 ≤ D - (r : ℝ) + 1 := by linarith
  have hSpos : 0 ≤ topSum (R.d t) r := by
    have : 0 ≤ (r : ℝ) * (D-r+1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  have hcs := topSum_sq_le hrn hSpos
  have henergy := potential_bound R hinit ht
  have hcount : (expandingCount R t : ℝ) ≤ p := by
    exact_mod_cast expandingCount_mono R ht
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hSsq := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg r) (by linarith : 0 ≤ D-r+1)) hspread 2
  have hcancel : (r : ℝ) * (D-r+1)^2 ≤ 2*(p : ℝ) := by
    apply (mul_le_mul_iff_right₀ hrpos).mp
    nlinarith
  have hBsq : (D/2)^2 ≤ (D-(r : ℝ)+1)^2 :=
    pow_le_pow_left₀ (by linarith) hB 2
  have hlower : (D/2)*(D/2)^2 ≤ (r : ℝ)*(D-r+1)^2 :=
    mul_le_mul hrlo hBsq (sq_nonneg _) (Nat.cast_nonneg _)
  nlinarith

/-- Two-sided expanding-move version, from a zero initial state. -/
theorem abs_cube_bound_expanding {T : ℕ} (R : Run V T)
    (hinit : ∀ k, R.d 0 k = 0) (i : V) :
    |R.d T i|^3 ≤ 64 * (expandingCount R T : ℝ) := by
  by_cases h : 0 ≤ R.d T i
  · have hp := positive_cube_bound R (fun k => le_of_eq (hinit k)) i
    simpa [abs_of_nonneg h, max_eq_left h] using hp
  · have hn := positive_cube_bound R.neg (by intro k; simp [Run.neg, hinit]) i
    rw [expandingCount_neg] at hn
    simpa [Run.neg, abs_of_neg (lt_of_not_ge h), max_eq_left (by linarith : 0 ≤ -R.d T i)] using hn

/-- Theorem 1.1, polynomial form, at every prefix and for every vertex. -/
theorem deterministic_upper_bound {T : ℕ} (R : Run V T)
    (hinit : ∀ k, R.d 0 k = 0) {t : ℕ} (ht : t ≤ T) (i : V) :
    |R.d t i|^3 ≤ 64 * (t : ℝ) ∧ |R.d t i| ≤ Fintype.card V := by
  let P := R.prefix t ht
  have hi : ∀ k, P.d 0 k = 0 := hinit
  constructor
  · have hc := abs_cube_bound_expanding P hi i
    have hcount : (expandingCount P t : ℝ) ≤ t := by exact_mod_cast expandingCount_le P t
    change |R.d t i|^3 ≤ 64 * (expandingCount P t : ℝ) at hc
    linarith
  · have hp := position_le_card P (fun k => le_of_eq (hi k)) i
    have hn := position_le_card P.neg (by intro k; simp [Run.neg, hi]) i
    exact abs_le.mpr ⟨by simpa [P, Run.neg, Run.prefix] using neg_le_neg hn, hp⟩

end Carpooling
