import Carpooling.Occupancy

namespace Carpooling
open Finset
open scoped Classical
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

lemma evaluation_pair_probability {T : ℕ} (S H : Finset A) (s t : Fin T) (hst : s ≠ t) :
    uniformProb (evaluationEvent S s ∩ evaluationEvent H t) = uniformProb S*uniformProb H := by
  let e : {x : Fin T → A // x s ∈ S ∧ x t ∈ H} ≃
      (S × H) × ({i : Fin T // i ∉ ({s,t} : Finset (Fin T))} → A) := {
    toFun := fun x => ((⟨x.val s,x.property.1⟩,⟨x.val t,x.property.2⟩),fun i => x.val i.val)
    invFun := fun p => ⟨fun i => if hs : i = s then p.1.1.val else
      if ht : i = t then p.1.2.val else p.2 ⟨i,by simp [hs,ht]⟩,
      by simp [hst,Ne.symm hst,p.1.1.property,p.1.2.property]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext i
      by_cases hs : i = s <;> by_cases ht : i = t <;> simp [hs,ht,hst,Ne.symm hst]
    right_inv := by
      rintro ⟨⟨a,b⟩,z⟩
      apply Prod.ext
      · apply Prod.ext <;> apply Subtype.ext <;> simp [hst,Ne.symm hst]
      · funext i
        have hi := i.property
        simp only [mem_insert,mem_singleton,not_or] at hi
        simp [hi.1,hi.2] }
  have hd : Fintype.card {i : Fin T // i ∉ ({s,t} : Finset (Fin T))} = T-2 := by
    rw [Fintype.card_subtype_compl]
    simp only [Fintype.card_fin,Fintype.card_subtype]
    have he : (univ.filter fun i : Fin T => i ∈ ({s,t} : Finset (Fin T))) = {s,t} := by
      ext i; simp
    rw [he]
    simp [hst,Ne.symm hst]
  have hc : (evaluationEvent S s ∩ evaluationEvent H t).card =
      S.card*H.card*Fintype.card A^(T-2) := by
    have hc := Fintype.card_congr e
    rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_fun,hd] at hc
    simpa [evaluationEvent,←filter_and,Fintype.card_subtype] using hc
  have hT : 2 ≤ T := by
    have hi := s.isLt
    have hj := t.isLt
    have hne : s.val ≠ t.val := fun he => hst (Fin.ext he)
    omega
  have hA : (Fintype.card A:ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp : (Fintype.card A:ℝ)^T = (Fintype.card A:ℝ)^(T-2)*(Fintype.card A:ℝ)^2 := by
    rw [←pow_add,Nat.sub_add_cancel hT]
  unfold uniformProb
  rw [hc]
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_mul,Nat.cast_pow]
  rw [hp]
  field_simp

end Carpooling
