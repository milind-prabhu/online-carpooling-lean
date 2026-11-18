import Carpooling.UniformMaps
import Carpooling.Pushforward

namespace Carpooling
open Finset
open scoped Classical
variable {J U W B C : Type*} [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]
 [Fintype W] [DecidableEq W] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

def mixedClass : (J × U) ⊕ W → Option J
  | Sum.inl p => some p.1
  | Sum.inr _ => none

def mixedFrame : ((J × U) ⊕ W) ↪ (Option J × (U ⊕ W)) where
  toFun
    | Sum.inl p => (some p.1,Sum.inl p.2)
    | Sum.inr w => (none,Sum.inr w)
  inj' := by
    rintro (⟨j,u⟩ | w) (⟨k,v⟩ | z) h <;> simp_all

def mixedPairDecoder : ((J × U) ⊕ W) × (B × C) → (J × B) ⊕ C
  | (Sum.inl p,e) => Sum.inl (p.1,e.1)
  | (Sum.inr _,e) => Sum.inr e.2

lemma mixedClass_fiber (j : J) :
    (univ.filter fun a : (J × U) ⊕ W => mixedClass a = some j).card = Fintype.card U := by
  have he : (univ.filter fun a : (J × U) ⊕ W => mixedClass a = some j).card =
      ∑ a : (J × U) ⊕ W, if mixedClass a = some j then 1 else 0 := by simp
  rw [he,Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type,mixedClass]
  simp

lemma mixedPairDecoder_fiber (z : (J × B) ⊕ C) :
    (univ.filter fun a : ((J × U) ⊕ W) × (B × C) => mixedPairDecoder a = z).card =
      match z with
      | Sum.inl _ => Fintype.card U*Fintype.card C
      | Sum.inr _ => Fintype.card W*Fintype.card B := by
  have he : (univ.filter fun a : ((J × U) ⊕ W) × (B × C) => mixedPairDecoder a = z).card =
      ∑ a : ((J × U) ⊕ W) × (B × C), if mixedPairDecoder a = z then 1 else 0 := by simp
  rw [he]
  cases z with
  | inl p =>
    rcases p with ⟨j,b⟩
    simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,mixedPairDecoder,Sum.inl.injEq,Sum.inr_ne_inl,ite_false,Prod.mk.injEq]
    simp [ite_and]
  | inr c =>
    simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,mixedPairDecoder,Sum.inr.injEq,Sum.inl_ne_inr,ite_false]
    simp

lemma mixedPairDecoder_constant_fiber
    (hbalance : Fintype.card U*Fintype.card C = Fintype.card W*Fintype.card B)
    (z : (J × B) ⊕ C) :
    (univ.filter fun a : ((J × U) ⊕ W) × (B × C) => mixedPairDecoder a = z).card =
      Fintype.card U*Fintype.card C := by
  rw [mixedPairDecoder_fiber]
  cases z <;> simp [hbalance]

noncomputable def pairWordEquiv (T : ℕ) {X Y : Type*} :
    ((Fin T → X) × (Fin T → Y)) ≃ (Fin T → X × Y) where
  toFun p t := (p.1 t,p.2 t)
  invFun x := (fun t => (x t).1,fun t => (x t).2)
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

end Carpooling
