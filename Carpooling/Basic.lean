import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Weighted Greedy chip game from Section 2 of arXiv:2609.21348v1.
The relation includes both legal tie choices. -/
namespace Carpooling
open scoped Classical
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

structure Move (x y : V → ℝ) where
  u : V
  v : V
  distinct : u ≠ v
  weight : ℝ
  weight_nonneg : 0 ≤ weight
  weight_le_one : weight ≤ 1
  ordered : x u ≤ x v
  update : ∀ k, y k = x k + (if k = u then weight else 0) -
    (if k = v then weight else 0)

def Move.Expanding {x y : V → ℝ} (e : Move x y) : Prop :=
  x e.v < x e.u + e.weight

omit [Fintype V] in
lemma Move.at_u {x y : V → ℝ} (e : Move x y) :
    y e.u = x e.u + e.weight := by
  simpa [e.distinct] using e.update e.u

omit [Fintype V] in
lemma Move.at_v {x y : V → ℝ} (e : Move x y) :
    y e.v = x e.v - e.weight := by
  simpa [Ne.symm e.distinct] using e.update e.v

omit [Fintype V] in
lemma Move.sum_update {x y : V → ℝ} (e : Move x y) (R : Finset V) :
    ∑ k ∈ R, y k = (∑ k ∈ R, x k) +
      (if e.u ∈ R then e.weight else 0) -
      (if e.v ∈ R then e.weight else 0) := by
  simp_rw [e.update, sum_sub_distrib, sum_add_distrib]
  simp

lemma Move.sum_preserved {x y : V → ℝ} (e : Move x y) :
    ∑ k, y k = ∑ k, x k := by
  simpa using e.sum_update univ

/-- A finite legal run. No assumption about an adversary or future edges is needed. -/
structure Run (V : Type*) [Fintype V] [DecidableEq V] (T : ℕ) where
  d : ℕ → V → ℝ
  step : ∀ t, t < T → Move (d t) (d (t+1))

noncomputable def expandingCount {T : ℕ} (R : Run V T) (t : ℕ) : ℕ :=
  by
    classical
    exact ((range t).filter fun s => ∃ h : s < T, (R.step s h).Expanding).card

def Move.neg {x y : V → ℝ} (e : Move x y) : Move (fun k => -x k) (fun k => -y k) where
  u := e.v
  v := e.u
  distinct := Ne.symm e.distinct
  weight := e.weight
  weight_nonneg := e.weight_nonneg
  weight_le_one := e.weight_le_one
  ordered := neg_le_neg e.ordered
  update := by
    intro k
    rw [e.update]
    by_cases hu : k = e.u <;> by_cases hv : k = e.v <;> simp [hu, hv] <;> ring

def Run.neg {T : ℕ} (R : Run V T) : Run V T where
  d := fun t k => -R.d t k
  step := fun t ht => (R.step t ht).neg

def Run.prefix {T : ℕ} (R : Run V T) (t : ℕ) (ht : t ≤ T) : Run V t where
  d := R.d
  step := fun s hs => R.step s (lt_of_lt_of_le hs ht)

lemma expandingCount_le {T : ℕ} (R : Run V T) (t : ℕ) : expandingCount R t ≤ t := by
  exact le_trans (card_filter_le _ _) (by simp)

lemma expandingCount_neg {T : ℕ} (R : Run V T) (t : ℕ) :
    expandingCount R.neg t = expandingCount R t := by
  unfold expandingCount
  congr 1
  apply filter_congr
  intro s _
  apply exists_congr
  intro hs
  change (-R.d s (R.step s hs).u < -R.d s (R.step s hs).v + (R.step s hs).weight) ↔
    R.d s (R.step s hs).v < R.d s (R.step s hs).u + (R.step s hs).weight
  constructor <;> intro h <;> linarith

end Carpooling
