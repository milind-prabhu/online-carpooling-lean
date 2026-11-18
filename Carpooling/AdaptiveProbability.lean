import Carpooling.FiniteProbability

/-! Exact probability of matching adaptively prescribed edge identities.
Each prescription may depend on the entire preceding sample prefix. -/
namespace Carpooling
open Finset
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

def prescribedSample {T : ℕ} (P : (t : Fin T) → (Fin t.val → E) → E)
    (t : Fin T) : E :=
  P t (fun s => prescribedSample P ⟨s.val, lt_trans s.isLt t.isLt⟩)
termination_by t.val

noncomputable def adaptiveMatchingEvent {T : ℕ}
    (P : (t : Fin T) → (Fin t.val → E) → E) : Finset (Fin T → E) :=
  univ.filter fun x => ∀ t, x t = P t (fun s => x ⟨s.val,lt_trans s.isLt t.isLt⟩)

/-- Every causal prescription has exactly one matching sequence, despite
depending on previous observations. No independence assumption about P is needed. -/
theorem adaptiveMatchingEvent_eq_singleton {T : ℕ}
    (P : (t : Fin T) → (Fin t.val → E) → E) :
    adaptiveMatchingEvent P = {prescribedSample P} := by
  ext x
  simp only [adaptiveMatchingEvent,mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · intro hx
    have hi : ∀ n (hn : n < T), x ⟨n,hn⟩ = prescribedSample P ⟨n,hn⟩ := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro hn
        rw [hx ⟨n,hn⟩,prescribedSample]
        congr 1
        funext s
        exact ih s.val s.isLt (lt_trans s.isLt hn)
    funext t
    exact hi t.val t.isLt
  · intro hx
    subst x
    intro t
    exact prescribedSample.eq_1 P t

/-- Adaptive edge guessing has the same exact likelihood as guessing a fixed
word: |E|^(-T). This is the local likelihood ingredient in Section 4.2. -/
theorem adaptive_matching_probability {T : ℕ}
    (P : (t : Fin T) → (Fin t.val → E) → E) :
    uniformProb (adaptiveMatchingEvent P) = 1/(Fintype.card E:ℝ)^T := by
  rw [adaptiveMatchingEvent_eq_singleton]
  simp [uniformProb,Fintype.card_fun]

/-- Complete a partially free sample, prescribing just the times in I. -/
def completeSelected {T : ℕ} (I : Finset (Fin T))
    (P : (t : Fin T) → (Fin t.val → E) → E)
    (free : {t : Fin T // t ∉ I} → E) (t : Fin T) : E :=
  if ht : t ∈ I then
    P t (fun s => completeSelected I P free ⟨s.val,lt_trans s.isLt t.isLt⟩)
  else free ⟨t,ht⟩
termination_by t.val

noncomputable def selectedMatchingEvent {T : ℕ} (I : Finset (Fin T))
    (P : (t : Fin T) → (Fin t.val → E) → E) : Finset (Fin T → E) :=
  univ.filter fun x => ∀ t ∈ I, x t = P t (fun s => x ⟨s.val,lt_trans s.isLt t.isLt⟩)

lemma completeSelected_matches {T : ℕ} (I : Finset (Fin T))
    (P : (t : Fin T) → (Fin t.val → E) → E)
    (free : {t : Fin T // t ∉ I} → E) :
    completeSelected I P free ∈ selectedMatchingEvent I P := by
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_⟩
  intro t ht
  rw [completeSelected, dif_pos ht]

lemma completeSelected_unique {T : ℕ} (I : Finset (Fin T))
    (P : (t : Fin T) → (Fin t.val → E) → E) (x : Fin T → E)
    (hx : x ∈ selectedMatchingEvent I P) :
    completeSelected I P (fun t => x t.val) = x := by
  have hm := (mem_filter.mp hx).2
  have hi : ∀ n (hn : n < T),
      completeSelected I P (fun t => x t.val) ⟨n,hn⟩ = x ⟨n,hn⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      rw [completeSelected]
      split_ifs with ht
      · rw [hm ⟨n,hn⟩ ht]
        congr 1
        funext s
        exact ih s.val s.isLt (lt_trans s.isLt hn)
      · rfl
  funext t
  exact hi t.val t.isLt

/-- Even after leaving arbitrary sampling times unconstrained, causal guesses
cost exactly one factor |E| for each constrained time. In particular, separate
cliques' edge prescriptions need not be functions of their local histories alone. -/
theorem selectedMatchingEvent_card {T : ℕ} (I : Finset (Fin T))
    (P : (t : Fin T) → (Fin t.val → E) → E) :
    (selectedMatchingEvent I P).card = Fintype.card E ^ (T-I.card) := by
  let equiv : {x // x ∈ selectedMatchingEvent I P} ≃ ({t : Fin T // t ∉ I} → E) := {
    toFun := fun x t => x.val t.val
    invFun := fun free => ⟨completeSelected I P free,completeSelected_matches I P free⟩
    left_inv := fun x => Subtype.ext (completeSelected_unique I P x.val x.property)
    right_inv := by
      intro free
      funext t
      dsimp
      rw [completeSelected,dif_neg t.property] }
  have h := Fintype.card_congr equiv
  rw [Fintype.card_fun,Fintype.card_subtype_compl] at h
  simpa only [Fintype.card_coe,Fintype.card_fin] using h

theorem selected_matching_probability {T : ℕ} (I : Finset (Fin T))
    (P : (t : Fin T) → (Fin t.val → E) → E) :
    uniformProb (selectedMatchingEvent I P) = 1/(Fintype.card E:ℝ)^I.card := by
  have hI : I.card ≤ T := by simpa using card_le_univ I
  have hp : (Fintype.card E:ℝ)^T =
      (Fintype.card E:ℝ)^(T-I.card)*(Fintype.card E:ℝ)^I.card := by
    rw [←pow_add,Nat.sub_add_cancel hI]
  have he : (0:ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  unfold uniformProb
  rw [selectedMatchingEvent_card]
  push_cast
  rw [Fintype.card_fun,Fintype.card_fin]
  push_cast
  rw [hp]
  rw [div_mul_eq_div_div,div_self (ne_of_gt (pow_pos he _))]

end Carpooling
