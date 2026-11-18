import Carpooling.UpperBounds

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma topSum_mono {x y : V → ℝ} (h : ∀ k, x k ≤ y k) {r : ℕ}
    (hr : r ≤ Fintype.card V) : topSum x r ≤ topSum y r := by
  exact (sum_le_sum fun k _ => h k).trans
    ((topSet_spec y hr).2 _ (topSet_spec x hr).1)

lemma potential_mono {x y : V → ℝ} (h : ∀ k, x k ≤ y k) :
    potential x ≤ potential y := by
  apply sum_le_sum
  intro k _
  exact pow_le_pow_left₀ (le_max_right _ _) (max_le_max (h k) le_rfl) 2

/-- Spreadness survives arbitrary coordinate decreases after a legal move. -/
lemma Move.topSum_dominated_step {x z y : V → ℝ} (e : Move x z)
    (hy : ∀ k, y k ≤ z k) {r : ℕ} (hrn : r < Fintype.card V)
    (hinc : topSum x r < topSum y r) :
    2 * topSum y r - topSum y (r-1) - 2 ≤ topSum x (r+1) := by
  let A := topSet y r
  have hc : A.card = r := (topSet_spec y (Nat.le_of_lt hrn)).1
  have hs : (∑ k ∈ A, y k) = topSum y r := rfl
  have hbefore : (∑ k ∈ A, x k) ≤ topSum x r := by
    simpa [hc] using sum_le_topSum x A
  have hdom : (∑ k ∈ A, y k) ≤ ∑ k ∈ A, z k := sum_le_sum fun k _ => hy k
  have hchange := e.sum_update A
  have hu : e.u ∈ A := by
    by_contra h
    by_cases hv : e.v ∈ A
    · simp only [if_neg h, if_pos hv] at hchange
      linarith [e.weight_nonneg]
    · simp only [if_neg h, if_neg hv] at hchange
      linarith
  have hv : e.v ∉ A := by
    intro h
    simp only [if_pos hu, if_pos h] at hchange
    linarith
  have hrem : (A.erase e.u).card = r-1 := by simp [card_erase_of_mem hu, hc]
  have hsmall := sum_le_topSum y (A.erase e.u)
  rw [hrem, sum_erase_eq_sub hu] at hsmall
  have hgap : y e.u - z e.v ≤ 2 := by
    have h := hy e.u
    rw [e.at_u] at h
    rw [e.at_v]
    linarith [e.ordered, e.weight_le_one]
  have hcard : (insert e.v A).card = r+1 := by simp [hv, hc]
  have hlarge := sum_le_topSum x (insert e.v A)
  rw [hcard] at hlarge
  have hsame : (∑ k ∈ insert e.v A, z k) = ∑ k ∈ insert e.v A, x k := by
    simpa [hu] using e.sum_update (insert e.v A)
  rw [sum_insert hv] at hsame
  linarith

/-- A chip move followed by coordinate decreases, or decreases alone.
The boolean records a charged move; every expanding move must be charged. -/
inductive DStep (x y : V → ℝ) (charged : Bool) : Prop
  | drop (h : ∀ k, y k ≤ x k)
  | move {z : V → ℝ} (e : Move x z) (h : ∀ k, y k ≤ z k)
      (charge : e.Expanding → charged = true)

lemma DStep.potential_le {x y : V → ℝ} {c : Bool} (h : DStep x y c) :
    potential y ≤ potential x + (if c then 2 else 0) := by
  cases h with
  | drop h => have hh := potential_mono h; cases c <;> simp_all <;> linarith
  | move e h hc =>
    have hmono := potential_mono h
    have he := e.potential_le
    by_cases hex : e.Expanding
    · rw [hc hex]; simpa [hex] using hmono.trans he
    · cases c <;> simp_all <;> linarith

lemma DStep.total_le {x y : V → ℝ} {c : Bool} (h : DStep x y c) :
    (∑ k, y k) ≤ ∑ k, x k := by
  cases h with
  | drop h => exact sum_le_sum fun k _ => h k
  | move e h hc => exact (sum_le_sum fun k _ => h k).trans_eq e.sum_preserved

lemma DStep.topSum_step {x y : V → ℝ} {c : Bool} (h : DStep x y c)
    {r : ℕ} (hrn : r < Fintype.card V) (hinc : topSum x r < topSum y r) :
    2 * topSum y r - topSum y (r-1) - 2 ≤ topSum x (r+1) := by
  cases h with
  | drop h => exact False.elim ((not_lt_of_ge (topSum_mono h (Nat.le_of_lt hrn))) hinc)
  | move e h hc => exact e.topSum_dominated_step h hrn hinc

structure DRun (V : Type*) [Fintype V] [DecidableEq V] (T : ℕ) where
  d : ℕ → V → ℝ
  charge : ℕ → Bool
  step : ∀ t, t < T → DStep (d t) (d (t+1)) (charge t)

def DRun.count {T : ℕ} (R : DRun V T) (t : ℕ) : ℕ :=
  ((range t).filter fun s => R.charge s = true).card

lemma DRun.count_mono {T : ℕ} (R : DRun V T) {s t : ℕ} (h : s ≤ t) :
    R.count s ≤ R.count t := card_le_card (filter_subset_filter _ (range_mono h))

lemma DRun.count_succ {T : ℕ} (R : DRun V T) (t : ℕ) :
    R.count (t+1) = R.count t + if R.charge t then 1 else 0 := by
  simp only [DRun.count, range_add_one, filter_insert]
  cases hc : R.charge t <;> simp [hc]

lemma DRun.potential_bound {T : ℕ} (R : DRun V T) (hi : ∀ k, R.d 0 k ≤ 0)
    {t : ℕ} (ht : t ≤ T) : potential (R.d t) ≤ 2 * (R.count t : ℝ) := by
  induction t with
  | zero =>
    have hz : potential (R.d 0) = 0 := by
      apply sum_eq_zero
      intro k _; simp [posSq, max_eq_right (hi k)]
    simp [hz, DRun.count]
  | succ t ih =>
    have hs := (R.step t (by omega)).potential_le
    have hp := ih (by omega)
    rw [R.count_succ, Nat.cast_add]
    cases hc : R.charge t <;> simp_all <;> linarith

lemma DRun.total_nonpos {T : ℕ} (R : DRun V T) (hi : ∀ k, R.d 0 k ≤ 0)
    {t : ℕ} (ht : t ≤ T) : (∑ k, R.d t k) ≤ 0 := by
  induction t with
  | zero => exact sum_nonpos fun k _ => hi k
  | succ t ih => exact (R.step t (by omega)).total_le.trans (ih (by omega))

lemma DRun.spreadness {T : ℕ} (R : DRun V T) (hi : ∀ k, R.d 0 k ≤ 0)
    {D : ℝ} {i : V} (hD : D ≤ R.d T i) {r : ℕ} (hr : 1 ≤ r)
    (hrn : r ≤ Fintype.card V) (hrD : (r : ℝ) ≤ D) :
    ∃ t ≤ T, (r : ℝ) * (D-r+1) ≤ topSum (R.d t) r := by
  apply threshold_crossing (S := fun t r => topSum (R.d t) r) hr hrD
  · intro t; exact topSum_zero _
  · intro s; exact topSum_nonpos hi s
  · intro t ht s hs hsr hinc
    exact (R.step t ht).topSum_step (lt_of_lt_of_le hsr hrn) hinc
  · exact hD.trans (le_topSum_one _ i)

lemma DRun.position_le_card {T : ℕ} (R : DRun V T) (hi : ∀ k, R.d 0 k ≤ 0)
    (i : V) : R.d T i ≤ Fintype.card V := by
  by_contra hn
  have hnD : (Fintype.card V : ℝ) < R.d T i := lt_of_not_ge hn
  have hnpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨i⟩
  obtain ⟨t, ht, hs⟩ := R.spreadness hi (le_refl (R.d T i)) hnpos le_rfl hnD.le
  rw [topSum_all] at hs
  have hsum := R.total_nonpos hi ht
  have hcast : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hprod : 0 < (Fintype.card V : ℝ) * (R.d T i - Fintype.card V + 1) :=
    mul_pos hcast (by linarith)
  linarith

theorem DRun.positive_cube_bound {T : ℕ} (R : DRun V T)
    (hinit : ∀ k, R.d 0 k ≤ 0) (i : V) :
    (max (R.d T i) 0)^3 ≤ 64 * (R.count T : ℝ) := by
  let D := R.d T i
  let p := R.count T
  change (max D 0)^3 ≤ 64 * (p : ℝ)
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  by_cases hD : D ≤ 0
  · simp only [max_eq_right hD, zero_pow (by decide : 3 ≠ 0)]
    positivity
  rw [max_eq_left (le_of_lt (lt_of_not_ge hD))]
  have hDpos : 0 < D := lt_of_not_ge hD
  have hpot := R.potential_bound hinit (le_refl T)
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
  have hDn : D ≤ Fintype.card V := R.position_le_card hinit i
  have hrn : r ≤ Fintype.card V := by exact_mod_cast (le_trans hrD hDn)
  obtain ⟨t, ht, hspread⟩ := R.spreadness hinit (le_refl D) hr hrn hrD
  have hB : D/2 ≤ D - (r : ℝ) + 1 := by linarith
  have hSpos : 0 ≤ topSum (R.d t) r := by
    have : 0 ≤ (r : ℝ) * (D-r+1) := mul_nonneg (Nat.cast_nonneg _) (by linarith)
    linarith
  have hcs := topSum_sq_le hrn hSpos
  have henergy := R.potential_bound hinit ht
  have hcount : (R.count t : ℝ) ≤ p := by
    exact_mod_cast R.count_mono ht
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


theorem DRun.position_bound {T : ℕ} (R : DRun V T) (hi : ∀ k, R.d 0 k ≤ 0)
    (i : V) : R.d T i ≤ 4 * (R.count T : ℝ)^((1:ℝ)/3) :=
  (le_max_left _ _).trans (le_four_cuberoot (le_max_right _ _)
    (Nat.cast_nonneg _) (R.positive_cube_bound hi i))

end Carpooling
