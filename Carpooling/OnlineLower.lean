import Carpooling.PaddedThresholds

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A causal unit-weight online orientation rule; the fields specify the
model, not any discrepancy or probability bound. -/
structure UnitOnlineRule (G : SimpleGraph V) (T : ℕ) where
  run : (Fin T → G.edgeSet) → IntegerRun V T
  initial : ∀ x v, (run x).d 0 v = 0
  request : ∀ x (t : Fin T),
    s(((run x).step t.val t.isLt).u,((run x).step t.val t.isLt).v) = (x t).val
  causal : ∀ (t : Fin T) x y,
    (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ = y ⟨i.val,lt_trans i.isLt t.isLt⟩) →
      (run x).d t.val = (run y).d t.val

lemma IntegerRun.first_discrepancy {T : ℕ} (hT : 0 < T) (R : IntegerRun V T)
    (hi : ∀ v, R.d 0 v = 0) : ∃ t ≤ T, ∃ v, (1:ℤ) ≤ |R.d t v| := by
  let e := R.step 0 hT
  refine ⟨1,hT,e.u,?_⟩
  have he := e.update e.u
  have hu : R.d 1 e.u = 1 := by simpa [hi,e.distinct] using he
  simp [hu]

lemma first_discrepancy_probability {E : Type*} [Fintype E] [DecidableEq E]
    {T : ℕ} (hT : 0 < T) (R : (Fin T → E) → IntegerRun V T)
    (hi : ∀ x v, (R x).d 0 v = 0) :
    uniformProb (univ \ integerDiscrepancyEvent R 1) = 0 := by
  have he : univ \ integerDiscrepancyEvent R 1 = ∅ := by
    ext x
    have hx : x ∈ integerDiscrepancyEvent R 1 := by
      simp only [integerDiscrepancyEvent,mem_filter,mem_univ,true_and]
      exact (R x).first_discrepancy hT (hi x)
    simp [hx]
  simp [he,uniformProb]

structure FiniteCarpoolGraph where
  Vertex : Type
  finite : Fintype Vertex
  decideEq : DecidableEq Vertex
  graph : SimpleGraph Vertex

instance (G : FiniteCarpoolGraph) : Fintype G.Vertex := G.finite
instance (G : FiniteCarpoolGraph) : DecidableEq G.Vertex := G.decideEq

lemma cubic_log_rate {n d a h : ℕ} (hd : 2 ≤ d) (hn : d < n) (ha : 0 < a) (hh : 0 < h)
    (hcert : Nat.log (d+1) n ≤ 16*a*h^3) :
    (Real.log (n:ℝ)/Real.log (d:ℝ))^((1:ℝ)/3) ≤ (64*(a:ℝ))^((1:ℝ)/3)*(h:ℝ) := by
  have hnp : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdp : (1:ℝ) < d := by exact_mod_cast (by omega : 1 < d)
  have hlogd : 0 < Real.log (d:ℝ) := Real.log_pos hdp
  have hN : (0:ℝ) < (d+1:ℕ) := by positivity
  have hpow := Nat.lt_pow_succ_log_self (show 1 < d+1 by omega) n
  have hpowR : (n:ℝ) ≤ ((d+1:ℕ):ℝ)^(Nat.log (d+1) n+1) := by exact_mod_cast le_of_lt hpow
  have hl := Real.log_le_log hnp hpowR
  rw [Real.log_pow] at hl
  have hpowh : 1 ≤ h^3 := Nat.one_le_pow _ _ hh
  have hq : Nat.log (d+1) n+1 ≤ 17*a*h^3 := by nlinarith
  have hqR : ((Nat.log (d+1) n+1:ℕ):ℝ) ≤ 17*(a:ℝ)*(h:ℝ)^3 := by exact_mod_cast hq
  have hlogN : 0 ≤ Real.log ((d+1:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d+1))
  have hNd : ((d+1:ℕ):ℝ) ≤ (d:ℝ)^2 := by exact_mod_cast (by nlinarith : d+1 ≤ d^2)
  have hld := Real.log_le_log hN hNd
  rw [Real.log_pow] at hld
  have hc : Real.log (n:ℝ) ≤ 64*(a:ℝ)*(h:ℝ)^3*Real.log (d:ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right hqR hlogN
    have h2 := mul_le_mul_of_nonneg_left hld (show 0 ≤ 17*(a:ℝ)*(h:ℝ)^3 by positivity)
    calc
      _ ≤ 17*(a:ℝ)*(h:ℝ)^3*Real.log ((d+1:ℕ):ℝ) := hl.trans h1
      _ ≤ 17*(a:ℝ)*(h:ℝ)^3*(2*Real.log (d:ℝ)) := by simpa only [Nat.cast_ofNat] using h2
      _ = 34*(a:ℝ)*(h:ℝ)^3*Real.log (d:ℝ) := by ring
      _ ≤ _ := by nlinarith [show 0 ≤ (a:ℝ)*(h:ℝ)^3*Real.log (d:ℝ) by positivity]
  have hr : Real.log (n:ℝ)/Real.log (d:ℝ) ≤ 64*(a:ℝ)*(h:ℝ)^3 :=
    (div_le_iff₀ hlogd).mpr hc
  have hnonneg : 0 ≤ Real.log (n:ℝ)/Real.log (d:ℝ) := by
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    · exact le_of_lt hlogd
  have hp := Real.rpow_le_rpow hnonneg hr (by norm_num : (0:ℝ) ≤ 1/3)
  have he : (64*(a:ℝ)*(h:ℝ)^3)^((1:ℝ)/3) = (64*(a:ℝ))^((1:ℝ)/3)*(h:ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    simpa only [one_div] using Real.pow_rpow_inv_natCast (Nat.cast_nonneg h) (by decide : (3:ℕ) ≠ 0)
  exact hp.trans_eq he

def StochasticLowerGuarantee (n d a h : ℕ) (G : FiniteCarpoolGraph) : Prop :=
  Fintype.card G.Vertex = n ∧ G.graph.IsRegularOfDegree d ∧ 0 < h ∧
    (Real.log (n:ℝ)/Real.log (d:ℝ))^((1:ℝ)/3) ≤ (64*(a:ℝ))^((1:ℝ)/3)*(h:ℝ) ∧
    ∀ R : UnitOnlineRule G.graph (Fintype.card G.Vertex),
      uniformProb (univ \ integerDiscrepancyEvent R.run h) ≤ 10/((d+1:ℕ):ℝ)

end Carpooling
