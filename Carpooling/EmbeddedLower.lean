import Carpooling.LocalStochasticLower

/-! A forced small vertex set inside an arbitrarily larger ambient graph. -/
namespace Carpooling
open Finset
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

def UnitMove.pullback {x y : V → ℤ} (e : UnitMove x y) (f : W ↪ V)
    (a b : W) (ha : f a = e.u) (hb : f b = e.v) :
    UnitMove (fun i => x (f i)) (fun i => y (f i)) where
  u := a
  v := b
  distinct := fun hab => e.distinct (ha.symm.trans ((congrArg f hab).trans hb))
  update := by
    intro k
    rw [e.update]
    simp only [←ha,←hb,f.injective.eq_iff]

noncomputable def IntegerRun.pullback {T : ℕ} (R : IntegerRun V T) (f : W ↪ V)
    (hends : ∀ t (ht : t < T), ∃ a b, f a = (R.step t ht).u ∧ f b = (R.step t ht).v) :
    IntegerRun W T where
  d := fun t i => R.d t (f i)
  step := fun t ht =>
    let a := (hends t ht).choose
    let b := (hends t ht).choose_spec.choose
    (R.step t ht).pullback f a b
      (hends t ht).choose_spec.choose_spec.1 (hends t ht).choose_spec.choose_spec.2

lemma IntegerRun.pullback_u {T : ℕ} (R : IntegerRun V T) (f : W ↪ V)
    (hends : ∀ t (ht : t < T), ∃ a b, f a = (R.step t ht).u ∧ f b = (R.step t ht).v)
    (t : ℕ) (ht : t < T) : f ((R.pullback f hends).step t ht).u = (R.step t ht).u :=
  (hends t ht).choose_spec.choose_spec.1

lemma IntegerRun.pullback_v {T : ℕ} (R : IntegerRun V T) (f : W ↪ V)
    (hends : ∀ t (ht : t < T), ∃ a b, f a = (R.step t ht).u ∧ f b = (R.step t ht).v)
    (t : ℕ) (ht : t < T) : f ((R.pullback f hends).step t ht).v = (R.step t ht).v :=
  (hends t ht).choose_spec.choose_spec.2

theorem embedded_equal_endpoint_lower_bound {T h : ℕ} (R : IntegerRun V T)
    (f : Fin (2*h+2) ↪ V)
    (hends : ∀ t (ht : t < T), ∃ a b, f a = (R.step t ht).u ∧ f b = (R.step t ht).v)
    (hi : ∀ v, R.d 0 v = 0)
    (hequal : ∀ t (ht : t < T), (∀ i, |R.d t (f i)| < (h:ℤ)) →
      R.d t (R.step t ht).u = R.d t (R.step t ht).v)
    (hT : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(T:ℤ)) :
    ∃ t ≤ T, ∃ v, (h:ℤ) ≤ |R.d t v| := by
  obtain ⟨t,ht,i,hi'⟩ := equal_endpoint_lower_bound (R.pullback f hends)
    (fun i => hi (f i)) (fun t ht hb => by
      change R.d t (f _) = R.d t (f _)
      rw [R.pullback_u f hends t ht,R.pullback_v f hends t ht]
      exact hequal t ht hb) (by simpa using hT)
  exact ⟨t,ht,f i,hi'⟩

section Probability
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- Force only 2h+2 chosen vertices, while sampling uniformly from an arbitrary
larger edge alphabet. The probability cost uses the ambient alphabet size;
the cubic horizon depends only on the small forced set. -/
theorem embedded_local_lower_probability (h : ℕ) (f : Fin (2*h+2) ↪ V)
    (g : E → Sym2 V)
    (encode : (a b : Fin (2*h+2)) → a ≠ b → E)
    (hencode : ∀ a b hab, g (encode a b hab) = s(f a,f b))
    (T : ℕ) (hT : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(T:ℤ))
    (R : (Fin T → E) → IntegerRun V T)
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x t (ht : t < T),
      s(((R x).step t ht).u,((R x).step t ht).v) = g (x ⟨t,ht⟩))
    (hcausal : ∀ (t : Fin T) (x y : Fin T → E),
      (∀ s : Fin t.val, x ⟨s.val,lt_trans s.isLt t.isLt⟩ =
        y ⟨s.val,lt_trans s.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    1/(Fintype.card E:ℝ)^T ≤ uniformProb (integerDiscrepancyEvent R h) := by
  classical
  let P : (t : Fin T) → (Fin t.val → E) → E := fun t z =>
    let pos := fun i => (R (extendSamplePrefix t z)).d t.val (f i)
    encode (lowerPair h pos).1 (lowerPair h pos).2 (lowerPair_distinct h pos)
  rw [←adaptive_matching_probability P]
  apply uniformProb_mono
  intro x hx
  have hm := (mem_filter.mp hx).2
  have hedge : ∀ t (ht : t < T),
      s(((R x).step t ht).u,((R x).step t ht).v) =
        s(f (lowerPair h (fun i => (R x).d t (f i))).1,
          f (lowerPair h (fun i => (R x).d t (f i))).2) := by
    intro t ht
    let ti : Fin T := ⟨t,ht⟩
    let z : Fin ti.val → E := fun s => x ⟨s.val,lt_trans s.isLt ti.isLt⟩
    have hstate : (R (extendSamplePrefix ti z)).d t = (R x).d t := by
      apply hcausal ti
      intro s
      simp [extendSamplePrefix,z,s.isLt]
    rw [hrequest x t ht,hm ti]
    change g (encode _ _ _) = _
    rw [hencode]
    change s(f (lowerPair h (fun i => (R (extendSamplePrefix ti z)).d t (f i))).1,
      f (lowerPair h (fun i => (R (extendSamplePrefix ti z)).d t (f i))).2) = _
    rw [hstate]
  have hends : ∀ t (ht : t < T), ∃ a b,
      f a = ((R x).step t ht).u ∧ f b = ((R x).step t ht).v := by
    intro t ht
    rcases Sym2.eq_iff.mp (hedge t ht) with ⟨hu,hv⟩ | ⟨hu,hv⟩
    · exact ⟨_,_,hu.symm,hv.symm⟩
    · exact ⟨_,_,hu.symm,hv.symm⟩
  simp only [integerDiscrepancyEvent,mem_filter,mem_univ,true_and]
  apply embedded_equal_endpoint_lower_bound (R x) f hends (hi x) _ hT
  intro t ht hb
  have hp := lowerPair_equal h (fun i => (R x).d t (f i)) hb
  rcases Sym2.eq_iff.mp (hedge t ht) with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]; exact hp
  · rw [hu,hv]; exact hp.symm

end Probability
end Carpooling
