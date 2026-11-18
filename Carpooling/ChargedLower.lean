import Carpooling.EmbeddedLower

namespace Carpooling
open Finset
open scoped Classical

/-- The lower-bound potential argument with idle times between the forced
requests. Only the cardinality of I enters the horizon condition. -/
theorem charged_potential_lower_bound {T h : ℕ}
    (d : ℕ → Fin (2*h+2) → ℤ) (I : Finset (Fin T))
    (hi : ∀ v, d 0 v = 0)
    (hchange : ∀ t : Fin T, (∀ v, |d t.val v| < (h:ℤ)) →
      integerPotential (d (t.val+1)) - integerPotential (d t.val) =
        if t ∈ I then 2 else 0)
    (hT : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(I.card:ℤ)) :
    ∃ t ≤ T, ∃ v, (h:ℤ) ≤ |d t v| := by
  by_contra hn
  have hb : ∀ t, t ≤ T → ∀ v, |d t v| < (h:ℤ) := by
    intro t ht v
    by_contra hv
    exact hn ⟨t,ht,v,le_of_not_gt hv⟩
  have hsum := sum_congr (s₁ := (univ : Finset (Fin T))) rfl
    (fun t _ => hchange t (hb t.val (le_of_lt t.isLt)))
  have htel : (∑ t : Fin T, (integerPotential (d (t.val+1))-integerPotential (d t.val))) =
      integerPotential (d T) - integerPotential (d 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun t => integerPotential (d (t+1))-integerPotential (d t)) T]
    exact sum_range_sub (fun t => integerPotential (d t)) T
  have hpot : integerPotential (d T) = 2*(I.card:ℤ) := by
    rw [htel] at hsum
    simpa [integerPotential,hi,mul_comm] using hsum
  have hsq : ∀ v, d T v ^ 2 ≤ (h:ℤ)^2 := by
    intro v
    have hv := le_of_lt (hb T (le_refl T) v)
    nlinarith [sq_abs (d T v),abs_nonneg (d T v)]
  have hbound := sum_le_sum (s := (univ : Finset (Fin (2*h+2)))) (fun v _ => hsq v)
  have hbound' : integerPotential (d T) ≤ ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 := by
    simpa [integerPotential] using hbound
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma UnitMove.embedded_potential_change {h : ℕ} {x y : V → ℤ}
    (e : UnitMove x y) (f : Fin (2*h+2) ↪ V) (a b : Fin (2*h+2))
    (hedge : s(e.u,e.v) = s(f a,f b)) (hequal : x (f a) = x (f b)) :
    integerPotential (fun i => y (f i)) - integerPotential (fun i => x (f i)) = 2 := by
  rcases Sym2.eq_iff.mp hedge with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · have he := (e.pullback f a b hu.symm hv.symm).potential_change
    change integerPotential (fun i => y (f i)) = integerPotential (fun i => x (f i)) +
      2*(x (f a)-x (f b))+2 at he
    rw [hequal] at he
    omega
  · have he := (e.pullback f b a hu.symm hv.symm).potential_change
    change integerPotential (fun i => y (f i)) = integerPotential (fun i => x (f i)) +
      2*(x (f b)-x (f a))+2 at he
    rw [hequal] at he
    omega

end Carpooling
