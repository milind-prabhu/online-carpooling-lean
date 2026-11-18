import Carpooling.FiniteSampling

namespace Carpooling
open Finset
open scoped Classical
variable {A J : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype J] [DecidableEq J] [Nonempty J]

noncomputable def classCount {T : ℕ} (cls : A → Option J) (x : Fin T → A) (j : J) : ℕ :=
  (univ.filter fun t => cls (x t) = some j).card

theorem classCount_variance (cls : A → Option J) (N : ℕ)
    (hfiber : ∀ j, (univ.filter fun a => cls a = some j).card = N) (j : J) :
    uniformMean (fun x : Fin (Fintype.card A) → A => ((classCount cls x j:ℝ)-N)^2) ≤ (N:ℝ) := by
  let S := univ.filter fun a => cls a = some j
  let B : Fin (Fintype.card A) → Finset (Fin (Fintype.card A) → A) := evaluationEvent S
  let p : ℝ := (N:ℝ)/(Fintype.card A:ℝ)
  have hA : (Fintype.card A:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfirst : ∀ t, uniformProb (B t) = p := by
    intro t
    rw [evaluation_probability]
    simp only [uniformProb,S,hfiber,p]
  have hsecond : ∀ s t, s ≠ t → uniformProb (B s ∩ B t) = p^2 := by
    intro s t hst
    rw [evaluation_pair_probability S S s t hst]
    have hs : uniformProb S = p := by simp only [uniformProb,S,hfiber,p]
    rw [hs,pow_two]
  have hcount : ∀ x : Fin (Fintype.card A) → A,
      (classCount cls x j:ℝ)-N = ∑ t, (eventIndicator (B t) x-p) := by
    intro x
    have he : (∑ t, eventIndicator (B t) x) = (classCount cls x j:ℝ) := by
      simp [B,S,eventIndicator,evaluationEvent,classCount]
    rw [sum_sub_distrib,he]
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    dsimp [p]
    field_simp
  simp_rw [hcount]
  rw [indicator_sum_variance B p hfirst hsecond]
  simp only [Fintype.card_fin]
  have hmul : (Fintype.card A:ℝ)*p = (N:ℝ) := by dsimp [p]; field_simp
  rw [hmul]
  have hp : 0 ≤ p := by dsimp [p]; positivity
  nlinarith [show (0:ℝ) ≤ N from Nat.cast_nonneg N]

end Carpooling
