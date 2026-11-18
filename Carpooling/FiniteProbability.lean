import Carpooling.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Fintype.EquivFin

namespace Carpooling
open Finset
open scoped Classical

/-- Uniform probability on a finite sample space, as an exact real ratio. -/
noncomputable def uniformProb {Ω : Type*} [Fintype Ω] (A : Finset Ω) : ℝ :=
  (A.card : ℝ) / Fintype.card Ω

lemma uniformProb_mono {Ω : Type*} [Fintype Ω] {A B : Finset Ω} (h : A ⊆ B) :
    uniformProb A ≤ uniformProb B := by
  unfold uniformProb
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_le_card h) (Nat.cast_nonneg _)

lemma uniformProb_biUnion_le {Ω W : Type*} [Fintype Ω] [DecidableEq Ω]
    (S : Finset W) (A : W → Finset Ω) :
    uniformProb (S.biUnion A) ≤ ∑ w ∈ S, uniformProb (A w) := by
  unfold uniformProb
  rw [← sum_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast card_biUnion_le

section Samples
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def fixedEvent {T : ℕ} (I : Finset (Fin T)) (b : Fin T → E) : Finset (Fin T → E) :=
  univ.filter fun x => ∀ i ∈ I, x i = b i

lemma fixedEvent_card {T : ℕ} (I : Finset (Fin T)) (b : Fin T → E) :
    (fixedEvent I b).card = Fintype.card E ^ (T-I.card) := by
  let equiv : {x : Fin T → E // ∀ i ∈ I, x i = b i} ≃ ({i : Fin T // i ∉ I} → E) := {
    toFun := fun x i => x.val i.val
    invFun := fun g => ⟨fun i => if h : i ∈ I then b i else g ⟨i,h⟩,
      by intro i hi; simp [hi]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ I
      · simp [hi, x.property i hi]
      · simp [hi]
    right_inv := by intro g; funext i; simp [i.property] }
  have h := Fintype.card_congr equiv
  rw [Fintype.card_fun] at h
  have hdom : Fintype.card {i : Fin T // i ∉ I} = T-I.card := by
    rw [Fintype.card_subtype_compl]
    simp
  rw [hdom] at h
  simpa [fixedEvent, Fintype.card_subtype] using h

noncomputable def prescribedEvent {T r : ℕ} (f : Fin r ↪ Fin T) (b : Fin r → E) :
    Finset (Fin T → E) := univ.filter fun x => ∀ j, x (f j) = b j

lemma prescribedEvent_card {T r : ℕ} (f : Fin r ↪ Fin T) (b : Fin r → E) :
    (prescribedEvent f b).card = Fintype.card E ^ (T-r) := by
  let I : Finset (Fin T) := univ.image f
  let ext : Fin T → E := fun i => if h : ∃ j, f j = i then b h.choose else Classical.choice ‹Nonempty E›
  have hext : ∀ j, ext (f j) = b j := by
    intro j
    have h : ∃ k, f k = f j := ⟨j,rfl⟩
    simp only [ext, dif_pos h]
    exact congrArg b (f.injective h.choose_spec)
  have heq : prescribedEvent f b = fixedEvent I ext := by
    ext x
    simp only [prescribedEvent, fixedEvent, mem_filter, mem_univ, true_and]
    constructor
    · intro hx i hi
      obtain ⟨j, _, rfl⟩ := mem_image.mp hi
      rw [hext, hx]
    · intro hx j
      rw [← hext]
      exact hx (f j) (mem_image.mpr ⟨j,mem_univ _,rfl⟩)
  rw [heq, fixedEvent_card]
  have hI : I.card = r := by simp [I, card_image_of_injective _ f.injective]
  rw [hI]

lemma prescribedEvent_probability {T r : ℕ} (f : Fin r ↪ Fin T) (b : Fin r → E) :
    uniformProb (prescribedEvent f b) = (1 / (Fintype.card E : ℝ))^r := by
  have hM : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hr : r ≤ T := by simpa using Fintype.card_le_of_injective f f.injective
  unfold uniformProb
  rw [prescribedEvent_card]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, one_div_pow]
  have hT : (Fintype.card E : ℝ)^T = (Fintype.card E : ℝ)^(T-r) * (Fintype.card E : ℝ)^r := by
    rw [← pow_add, Nat.sub_add_cancel hr]
  rw [hT, div_mul_eq_div_div, div_self (pow_ne_zero _ hM.ne')]

/-- A pattern must use distinct sampling times, even if its edge labels repeat. -/
noncomputable def occurrenceEvent {T r : ℕ} (b : Fin r → E) : Finset (Fin T → E) :=
  univ.biUnion fun f : Fin r ↪ Fin T => prescribedEvent f b

/-- Equation (7): the occurrence bound for any fixed edge multiset/order. -/
theorem occurrence_probability_bound {T r : ℕ} (b : Fin r → E) :
    uniformProb (occurrenceEvent (T := T) b) ≤ ((T : ℝ) / Fintype.card E)^r := by
  have hu := uniformProb_biUnion_le (univ : Finset (Fin r ↪ Fin T))
    (fun f => prescribedEvent f b)
  simp only [prescribedEvent_probability, sum_const, card_univ, nsmul_eq_mul] at hu
  have hcard : Fintype.card (Fin r ↪ Fin T) ≤ T^r := by
    have h := Fintype.card_le_of_injective (fun f : Fin r ↪ Fin T => (f : Fin r → Fin T))
      (by intro f g h; exact Function.Embedding.ext (congrFun h))
    simpa [Fintype.card_fun] using h
  have hc : (Fintype.card (Fin r ↪ Fin T) : ℝ) ≤ (T : ℝ)^r := by exact_mod_cast hcard
  calc
    uniformProb (occurrenceEvent (T := T) b) ≤
        (Fintype.card (Fin r ↪ Fin T) : ℝ) * (1/(Fintype.card E : ℝ))^r := hu
    _ ≤ (T : ℝ)^r * (1/(Fintype.card E : ℝ))^r :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = ((T : ℝ) / Fintype.card E)^r := by rw [← mul_pow]; congr 1; ring

end Samples

section MappedSamples
variable {E A : Type*} [Fintype E] [DecidableEq E] [Nonempty E] [DecidableEq A]

noncomputable def mappedOccurrenceEvent {T r : ℕ} (g : E → A) (b : Fin r → A) : Finset (Fin T → E) :=
  univ.filter fun x => ∃ f : Fin r ↪ Fin T, ∀ j, g (x (f j)) = b j

theorem mapped_occurrence_probability_bound {T r : ℕ} (g : E → A)
    (hg : Function.Injective g) (b : Fin r → A) :
    uniformProb (mappedOccurrenceEvent (T := T) g b) ≤ ((T : ℝ) / Fintype.card E)^r := by
  by_cases hn : (mappedOccurrenceEvent (T := T) g b).Nonempty
  · obtain ⟨x, hx⟩ := hn
    obtain ⟨f, hf⟩ := (mem_filter.mp hx).2
    let c : Fin r → E := fun j => x (f j)
    have heq : mappedOccurrenceEvent (T := T) g b = occurrenceEvent (T := T) c := by
      ext y
      simp only [mappedOccurrenceEvent, mem_filter, mem_univ, true_and,
        occurrenceEvent, mem_biUnion, prescribedEvent]
      constructor
      · rintro ⟨h, hh⟩
        refine ⟨h, ?_⟩
        intro j; exact hg ((hh j).trans (hf j).symm)
      · rintro ⟨h, hh⟩
        refine ⟨h, ?_⟩
        intro j
        rw [hh j]
        exact hf j
    rw [heq]
    exact occurrence_probability_bound c
  · have he : mappedOccurrenceEvent (T := T) g b = ∅ := not_nonempty_iff_eq_empty.mp hn
    rw [he]
    unfold uniformProb
    simp only [card_empty, Nat.cast_zero, zero_div]
    positivity

/-- Multiset containment gives distinct matching sample times, including for repeated labels. -/
theorem embedding_of_bag_le {T r : ℕ} (b : Fin r → A) (x : Fin T → A)
    (h : (univ : Finset (Fin r)).val.map b ≤ (univ : Finset (Fin T)).val.map x) :
    ∃ f : Fin r ↪ Fin T, ∀ j, x (f j) = b j := by
  have hcard : ∀ a, Fintype.card {j : Fin r // b j = a} ≤ Fintype.card {i : Fin T // x i = a} := by
    intro a
    have hc := Multiset.le_iff_count.mp h a
    simpa only [Multiset.count_map, ← Finset.filter_val, Fintype.card_subtype, eq_comm] using hc
  let fiber : ∀ a, {j : Fin r // b j = a} ↪ {i : Fin T // x i = a} :=
    fun a => (Function.Embedding.nonempty_of_card_le (hcard a)).some
  let f : Fin r ↪ Fin T := (Equiv.sigmaFiberEquiv b).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl A) fiber).trans
      (Equiv.sigmaFiberEquiv x).toEmbedding)
  refine ⟨f, ?_⟩
  intro j
  exact (fiber (b j) ⟨j,rfl⟩).property

end MappedSamples

section Evaluation
variable {Q : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]

noncomputable def evaluationEvent {K : ℕ} (S : Finset Q) (j : Fin K) : Finset (Fin K → Q) :=
  univ.filter fun x => x j ∈ S

lemma evaluationEvent_card {K : ℕ} (S : Finset Q) (j : Fin K) :
    (evaluationEvent S j).card = S.card * Fintype.card Q^(K-1) := by
  let e : {x : Fin K → Q // x j ∈ S} ≃ S × ({i : Fin K // i ≠ j} → Q) := {
    toFun := fun x => (⟨x.val j,x.property⟩, fun i => x.val i.val)
    invFun := fun p => ⟨fun i => if h : i = j then p.1.val else p.2 ⟨i,h⟩, by simp⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext i
      by_cases h : i = j <;> simp [h]
    right_inv := by
      rintro ⟨q,g⟩
      apply Prod.ext
      · apply Subtype.ext; simp
      · funext i; simp [i.property] }
  have h := Fintype.card_congr e
  rw [Fintype.card_prod, Fintype.card_fun] at h
  have hdom : Fintype.card {i : Fin K // i ≠ j} = K-1 := by
    rw [Fintype.card_subtype_compl]; simp
  rw [hdom] at h
  simpa [evaluationEvent, Fintype.card_subtype] using h

lemma evaluation_probability {K : ℕ} (S : Finset Q) (j : Fin K) :
    uniformProb (evaluationEvent S j) = uniformProb S := by
  have hQ : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have hK : K-1+1 = K := by have hj := j.isLt; omega
  unfold uniformProb
  rw [evaluationEvent_card]
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow]
  apply (div_eq_div_iff (pow_ne_zero _ hQ.ne') hQ.ne').mpr
  have hpow : (Fintype.card Q : ℝ)^K = (Fintype.card Q : ℝ)^(K-1) * Fintype.card Q := by
    calc
      _ = (Fintype.card Q : ℝ)^(K-1+1) := congrArg (fun n => (Fintype.card Q : ℝ)^n) hK.symm
      _ = _ := pow_succ _ _
  rw [hpow]
  ring

/-- A union bound over batches; independence between the bad events is unnecessary. -/
theorem batch_failure_bound {K : ℕ} (S : Finset Q) :
    uniformProb ((univ : Finset (Fin K)).biUnion fun j => evaluationEvent S j) ≤
      (K : ℝ) * uniformProb S := by
  have h := uniformProb_biUnion_le (univ : Finset (Fin K)) (fun j => evaluationEvent S j)
  simpa only [evaluation_probability, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] using h

end Evaluation
end Carpooling
