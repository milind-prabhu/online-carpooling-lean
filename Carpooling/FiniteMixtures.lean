import Carpooling.Amplification

namespace Carpooling
open Finset
open scoped Classical
variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
  [Fintype Γ] [DecidableEq Γ] [Nonempty Γ]

lemma uniformProb_equiv_preimage (e : Ω ≃ Γ) (A : Finset Γ) :
    uniformProb (univ.filter fun x => e x ∈ A) = uniformProb A := by
  have he : (univ.filter fun x => e x ∈ A).map e.toEmbedding = A := by
    ext y
    simp
  have hc := congrArg Finset.card he
  rw [card_map] at hc
  simp only [uniformProb,hc,Fintype.card_congr e]

lemma uniformProb_nonneg (A : Finset Ω) : 0 ≤ uniformProb A := by
  unfold uniformProb
  positivity

lemma uniformProb_le_one (A : Finset Ω) : uniformProb A ≤ 1 := by
  unfold uniformProb
  apply (div_le_one (by exact_mod_cast Fintype.card_pos : (0:ℝ) < Fintype.card Ω)).mpr
  exact_mod_cast card_le_univ A

lemma uniformMean_prod (f : Ω → Γ → ℝ) :
    uniformMean (fun x : Ω × Γ => f x.1 x.2) =
      uniformMean (fun x : Ω => uniformMean (f x)) := by
  simp only [uniformMean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul]
  rw [←sum_div,div_div,mul_comm (Fintype.card Γ:ℝ) (Fintype.card Ω:ℝ)]

noncomputable def eventFiber (A : Finset (Ω × Γ)) (x : Ω) : Finset Γ :=
  univ.filter fun y => (x,y) ∈ A

lemma uniformProb_prod_fibers (A : Finset (Ω × Γ)) :
    uniformProb A = uniformMean (fun x => uniformProb (eventFiber A x)) := by
  rw [←uniformMean_indicator]
  change uniformMean (fun x : Ω × Γ => eventIndicator A (x.1,x.2)) = _
  rw [uniformMean_prod (fun x y => eventIndicator A (x,y))]
  congr 1
  funext x
  have he : (fun y => eventIndicator A (x,y)) = eventIndicator (eventFiber A x) := by
    funext y
    simp [eventIndicator,eventFiber]
  rw [he,uniformMean_indicator]

/-- Average a conditional estimate over a finite product sample space. -/
theorem uniformProb_mixture_bound (A : Finset (Ω × Γ)) (B : Finset Ω) {a : ℝ}
    (ha : 0 ≤ a) (hgood : ∀ x, x ∉ B → uniformProb (eventFiber A x) ≤ a) :
    uniformProb A ≤ uniformProb B+a := by
  rw [uniformProb_prod_fibers]
  have hpoint : ∀ x, uniformProb (eventFiber A x) ≤ eventIndicator B x+a := by
    intro x
    by_cases hx : x ∈ B
    · simp only [eventIndicator,if_pos hx]
      exact (uniformProb_le_one _).trans (by linarith)
    · simpa [eventIndicator,hx] using hgood x hx
  have hb := uniformMean_mono hpoint
  simpa only [uniformMean_add,uniformMean_indicator,uniformMean_const] using hb

end Carpooling
