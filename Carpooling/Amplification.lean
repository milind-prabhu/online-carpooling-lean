import Carpooling.AdaptiveProbability
import Carpooling.StochasticTheorem
import Mathlib.Tactic.FieldSimp

/-! Finite second-moment amplification, followed by adaptive-prescription
events on disjoint sets of sampling times. -/
namespace Carpooling
open Finset
open scoped Classical
variable {Ω J : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
  [Fintype J] [DecidableEq J]

noncomputable def uniformMean (f : Ω → ℝ) : ℝ := (∑ x, f x)/(Fintype.card Ω:ℝ)
noncomputable def eventIndicator (A : Finset Ω) (x : Ω) : ℝ := if x ∈ A then 1 else 0

lemma uniformMean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g :=
  div_le_div_of_nonneg_right (sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

@[simp] lemma uniformMean_const (c : ℝ) : uniformMean (fun _ : Ω => c) = c := by
  have hn : (Fintype.card Ω:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [uniformMean,hn]

@[simp] lemma uniformMean_add (f g : Ω → ℝ) :
    uniformMean (fun x => f x+g x) = uniformMean f+uniformMean g := by
  simp only [uniformMean,sum_add_distrib,add_div]

@[simp] lemma uniformMean_sub (f g : Ω → ℝ) :
    uniformMean (fun x => f x-g x) = uniformMean f-uniformMean g := by
  simp only [uniformMean,sum_sub_distrib,sub_div]

@[simp] lemma uniformMean_const_mul (c : ℝ) (f : Ω → ℝ) :
    uniformMean (fun x => c*f x) = c*uniformMean f := by
  simp only [uniformMean,←mul_sum,mul_div_assoc]

@[simp] lemma uniformMean_mul_const (f : Ω → ℝ) (c : ℝ) :
    uniformMean (fun x => f x*c) = uniformMean f*c := by
  simp only [uniformMean,←sum_mul,div_mul_eq_mul_div]

@[simp] lemma uniformMean_sum (f : J → Ω → ℝ) :
    uniformMean (fun x => ∑ j, f j x) = ∑ j, uniformMean (f j) := by
  simp only [uniformMean,←sum_div]
  rw [sum_comm]

@[simp] lemma uniformMean_indicator (A : Finset Ω) :
    uniformMean (eventIndicator A) = uniformProb A := by
  simp [uniformMean,eventIndicator,uniformProb]

lemma eventIndicator_mul (A B : Finset Ω) :
    (fun x => eventIndicator A x*eventIndicator B x) = eventIndicator (A ∩ B) := by
  funext x
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [eventIndicator,ha,hb]

noncomputable def noHitEvent (A : J → Finset Ω) : Finset Ω :=
  univ.filter fun x => ∀ j, x ∉ A j

/-- Pairwise intersection probabilities suffice; mutual independence is not
assumed. This is useful when each prescription uses the full global history. -/
theorem pairwise_event_amplification (A : J → Finset Ω) {p : ℝ}
    (hp : 0 < p) (hJ : 0 < Fintype.card J)
    (hfirst : ∀ j, uniformProb (A j) = p)
    (hsecond : ∀ j k, j ≠ k → uniformProb (A j ∩ A k) = p^2) :
    uniformProb (noHitEvent A) ≤ 1/((Fintype.card J:ℝ)*p) := by
  let μ : ℝ := (Fintype.card J:ℝ)*p
  have hμ : 0 < μ := mul_pos (by exact_mod_cast hJ) hp
  have hmoment : ∀ j k,
      uniformMean (fun x => (eventIndicator (A j) x-p)*(eventIndicator (A k) x-p)) =
        if j = k then p*(1-p) else 0 := by
    intro j k
    have hexpand : (fun x => (eventIndicator (A j) x-p)*(eventIndicator (A k) x-p)) =
        (fun x => eventIndicator (A j) x*eventIndicator (A k) x -
          p*eventIndicator (A j) x - p*eventIndicator (A k) x + p*p) := by
      funext x; ring
    rw [hexpand]
    simp only [uniformMean_add,uniformMean_sub,uniformMean_const_mul,
      eventIndicator_mul,uniformMean_indicator,uniformMean_const,hfirst]
    by_cases hjk : j = k
    · subst k
      simp [hfirst]
      <;> ring
    · rw [if_neg hjk,hsecond j k hjk]
      ring
  let Z : Ω → ℝ := fun x => ∑ j, (eventIndicator (A j) x-p)
  have hvariance : uniformMean (fun x => (Z x)^2) = μ*(1-p) := by
    have he : (fun x => (Z x)^2) =
        (fun x => ∑ j, ∑ k, (eventIndicator (A j) x-p)*(eventIndicator (A k) x-p)) := by
      funext x
      simp only [Z,pow_two,sum_mul_sum]
    rw [he,uniformMean_sum]
    simp_rw [uniformMean_sum,hmoment]
    simp [μ,mul_assoc]
  have hpoint : ∀ x, eventIndicator (noHitEvent A) x*μ^2 ≤ (Z x)^2 := by
    intro x
    by_cases hx : ∀ j, x ∉ A j
    · have hz : Z x = -μ := by simp [Z,eventIndicator,hx,μ] <;> ring
      simp [eventIndicator,noHitEvent,hx,hz]
    · simp [eventIndicator,noHitEvent,hx,sq_nonneg]
  have hbound := uniformMean_mono hpoint
  rw [uniformMean_mul_const,uniformMean_indicator,hvariance] at hbound
  have hbound' : uniformProb (noHitEvent A)*μ^2 ≤ μ := by
    nlinarith [mul_pos hμ hp]
  apply (le_div_iff₀ hμ).mpr
  apply (mul_le_mul_iff_left₀ hμ).mp
  nlinarith [hbound']

section Adaptive
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

lemma selectedMatchingEvent_union {T : ℕ} (I H : Finset (Fin T))
    (P : (t : Fin T) → (Fin t.val → E) → E) :
    selectedMatchingEvent (I ∪ H) P = selectedMatchingEvent I P ∩ selectedMatchingEvent H P := by
  ext x
  simp only [selectedMatchingEvent,mem_filter,mem_univ,true_and,mem_inter]
  constructor
  · intro hx
    exact ⟨fun t ht => hx t (mem_union_left _ ht),fun t ht => hx t (mem_union_right _ ht)⟩
  · rintro ⟨hI,hH⟩ t ht
    rcases mem_union.mp ht with ht | ht
    · exact hI t ht
    · exact hH t ht

/-- Amplification of adaptive edge prescriptions on disjoint sets of times.
P may use every earlier sample, including samples assigned to other cliques.
The probability that all K prescriptions fail is at most |E|^L/K. -/
theorem adaptive_prescription_amplification {T L : ℕ}
    (I : J → Finset (Fin T)) (hJ : 0 < Fintype.card J)
    (hdisjoint : ∀ j k, j ≠ k → Disjoint (I j) (I k))
    (hsize : ∀ j, (I j).card = L)
    (P : (t : Fin T) → (Fin t.val → E) → E) :
    uniformProb (noHitEvent (fun j => selectedMatchingEvent (I j) P)) ≤
      (Fintype.card E:ℝ)^L/(Fintype.card J:ℝ) := by
  let p : ℝ := 1/(Fintype.card E:ℝ)^L
  have hE : (0:ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hp : 0 < p := by dsimp [p]; positivity
  have hfirst : ∀ j, uniformProb (selectedMatchingEvent (I j) P) = p := by
    intro j
    rw [selected_matching_probability,hsize j]
  have hsecond : ∀ j k, j ≠ k →
      uniformProb (selectedMatchingEvent (I j) P ∩ selectedMatchingEvent (I k) P) = p^2 := by
    intro j k hjk
    rw [←selectedMatchingEvent_union,selected_matching_probability,
      card_union_of_disjoint (hdisjoint j k hjk),hsize j,hsize k,pow_add]
    dsimp [p]
    ring
  have hb := pairwise_event_amplification (fun j => selectedMatchingEvent (I j) P)
    hp hJ hfirst hsecond
  have hJe : (Fintype.card J:ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hJ
  have hEe : (Fintype.card E:ℝ) ≠ 0 := ne_of_gt hE
  have heq : 1/((Fintype.card J:ℝ)*p) = (Fintype.card E:ℝ)^L/(Fintype.card J:ℝ) := by
    dsimp [p]
    field_simp
  exact hb.trans_eq heq

end Adaptive
end Carpooling
