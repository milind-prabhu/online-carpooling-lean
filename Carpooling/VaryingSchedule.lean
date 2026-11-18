import Carpooling.ScheduledLower
namespace Carpooling
open Finset
open scoped Classical
variable {J U E K : Type*} [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]
 [Fintype E] [DecidableEq E] [Nonempty E] [Fintype K] [DecidableEq K]

theorem scheduled_varying_targets_lower_probability {T L h : ℕ}
    (hK : 0 < Fintype.card K) (target : K ↪ J) (f : Fin (2*h+2) ↪ U)
    (schedule : Fin T → J) (g : Fin T → E → Sym2 U)
    (encode : J → (a b : Fin (2*h+2)) → a ≠ b → E)
    (hencode : ∀ t k a b hab, schedule t = target k →
      g t (encode (target k) a b hab) = s(f a,f b)) (cut : K → ℕ) (hcut : ∀ j, cut j ≤ T)
    (hsize : ∀ j, (targetTimes schedule target cut j).card = L)
    (hL : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(L:ℤ))
    (R : (Fin T → E) → IntegerRun (J × U) T)
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x (t : Fin T),
      s(((R x).step t.val t.isLt).u,((R x).step t.val t.isLt).v) =
        (g t (x t)).map (fun u => (schedule t,u)))
    (hcausal : ∀ (t : Fin T) (x y : Fin T → E),
      (∀ s : Fin t.val, x ⟨s.val,lt_trans s.isLt t.isLt⟩ =
        y ⟨s.val,lt_trans s.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    uniformProb (univ \ integerDiscrepancyEvent R h) ≤
      (Fintype.card E:ℝ)^L/(Fintype.card K:ℝ) := by
  classical
  let I := targetTimes schedule target cut
  let P : (t : Fin T) → (Fin t.val → E) → E := fun t z =>
    let pos := fun i => (R (extendSamplePrefix t z)).d t.val (schedule t,f i)
    encode (schedule t) (lowerPair h pos).1 (lowerPair h pos).2 (lowerPair_distinct h pos)
  have hforce : ∀ j, selectedMatchingEvent (I j) P ⊆ integerDiscrepancyEvent R h := by
    intro j x hx
    have hm := (mem_filter.mp hx).2
    let d : ℕ → Fin (2*h+2) → ℤ := fun t i => (R x).d (min t (cut j)) (target j,f i)
    have hchange : ∀ t : Fin T, (∀ i, |d t.val i| < (h:ℤ)) →
        integerPotential (d (t.val+1))-integerPotential (d t.val) = if t ∈ I j then 2 else 0 := by
      intro t hb
      by_cases hbefore : t.val < cut j
      · have hmin : min t.val (cut j) = t.val := min_eq_left (le_of_lt hbefore)
        have hmin' : min (t.val+1) (cut j) = t.val+1 := min_eq_left (by omega)
        simp only [d,hmin] at hb
        simp only [d,hmin,hmin']
        by_cases hj : schedule t = target j
        · have htI : t ∈ I j := mem_filter.mpr ⟨mem_univ _,hj,hbefore⟩
          rw [if_pos htI]
          let z : Fin t.val → E := fun s => x ⟨s.val,lt_trans s.isLt t.isLt⟩
          have hstate : (R (extendSamplePrefix t z)).d t.val = (R x).d t.val := by
            apply hcausal t
            intro s
            simp [extendSamplePrefix,z,s.isLt]
          have hedge : s(((R x).step t.val t.isLt).u,((R x).step t.val t.isLt).v) =
              s((target j,f (lowerPair h (fun i => (R x).d t.val (target j,f i))).1),
                (target j,f (lowerPair h (fun i => (R x).d t.val (target j,f i))).2)) := by
            rw [hrequest x t,hm t htI]
            change (g t (encode (schedule t) _ _ _)).map _ = _
            rw [hj,hencode t j _ _ _ hj,Sym2.map_pair_eq]
            change s((target j,f (lowerPair h (fun i =>
              (R (extendSamplePrefix t z)).d t.val (target j,f i))).1),
              (target j,f (lowerPair h (fun i =>
              (R (extendSamplePrefix t z)).d t.val (target j,f i))).2)) = _
            rw [hstate]
          let fj : Fin (2*h+2) ↪ J × U := {
            toFun := fun i => (target j,f i)
            inj' := fun a b he => f.injective (congrArg Prod.snd he) }
          exact ((R x).step t.val t.isLt).embedded_potential_change fj _ _ hedge
            (lowerPair_equal h (fun i => (R x).d t.val (target j,f i)) hb)
        · have htI : t ∉ I j := by simp [I,targetTimes,hj]
          rw [if_neg htI]
          have hidle : (fun i => (R x).d (t.val+1) (target j,f i)) =
              (fun i => (R x).d t.val (target j,f i)) := by
            funext i
            exact ((R x).step t.val t.isLt).other_component_unchanged
              (g t (x t)) (schedule t) (target j) hj (hrequest x t) (f i)
          rw [hidle,sub_self]
      · have hmin : min t.val (cut j) = cut j := min_eq_right (by omega)
        have hmin' : min (t.val+1) (cut j) = cut j := min_eq_right (by omega)
        have htI : t ∉ I j := by simp [I,targetTimes,hbefore]
        simp [d,hmin,hmin',htI]
    obtain ⟨t,ht,i,hlarge⟩ := charged_potential_lower_bound d (I j)
      (fun i => by simp [d,hi]) hchange (by simpa [I,hsize] using hL)
    simp only [integerDiscrepancyEvent,mem_filter,mem_univ,true_and]
    exact ⟨min t (cut j),(min_le_left _ _).trans ht,(target j,f i),hlarge⟩
  have hdisjoint : ∀ j k, j ≠ k → Disjoint (I j) (I k) := by
    intro j k hjk
    apply disjoint_left.mpr
    intro t htj htk
    exact hjk (target.injective ((mem_filter.mp htj).2.1.symm.trans (mem_filter.mp htk).2.1))
  have hb := adaptive_prescription_amplification I hK hdisjoint hsize P
  apply le_trans _ hb
  apply uniformProb_mono
  intro x hx
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro j hj
  exact (mem_sdiff.mp hx).2 (hforce j hj)


theorem scheduled_varying_targets_of_counts {T L h : ℕ}
    (hK : 0 < Fintype.card K) (target : K ↪ J) (f : Fin (2*h+2) ↪ U)
    (schedule : Fin T → J) (g : Fin T → E → Sym2 U)
    (encode : J → (a b : Fin (2*h+2)) → a ≠ b → E)
    (hencode : ∀ t k a b hab, schedule t = target k →
      g t (encode (target k) a b hab) = s(f a,f b))
    (hcount : ∀ k, L ≤ (univ.filter fun t => schedule t = target k).card)
    (hL : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(L:ℤ))
    (R : (Fin T → E) → IntegerRun (J × U) T)
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x (t : Fin T),
      s(((R x).step t.val t.isLt).u,((R x).step t.val t.isLt).v) =
        (g t (x t)).map (fun u => (schedule t,u)))
    (hcausal : ∀ (t : Fin T) (x y : Fin T → E),
      (∀ s : Fin t.val, x ⟨s.val,lt_trans s.isLt t.isLt⟩ =
        y ⟨s.val,lt_trans s.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    uniformProb (univ \ integerDiscrepancyEvent R h) ≤
      (Fintype.card E:ℝ)^L/(Fintype.card K:ℝ) := by
  have hex : ∀ k, ∃ c ≤ T,
      ((univ.filter fun t => schedule t = target k).filter fun t => t.val < c).card = L :=
    fun k => exists_prefix_cut _ (hcount k)
  let cut : K → ℕ := fun k => (hex k).choose
  apply scheduled_varying_targets_lower_probability hK target f schedule g encode hencode cut
    (fun k => (hex k).choose_spec.1) _ hL R hi hrequest hcausal
  intro k
  have hset : targetTimes schedule target cut k =
      ((univ.filter fun t => schedule t = target k).filter fun t => t.val < cut k) := by
    ext t
    simp [targetTimes]
  rw [hset]
  exact (hex k).choose_spec.2

end Carpooling
