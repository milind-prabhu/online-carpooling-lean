import Carpooling.FiniteMixtures

namespace Carpooling
open Finset
open scoped Classical
variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

lemma fiber_card_subtype (f : A → B) (b : B) :
    Fintype.card {a // f a = b} = (univ.filter fun a => f a = b).card := by
  simp [Fintype.card_subtype]

lemma constant_fiber_card (f : A → B) (k : ℕ)
    (hf : ∀ b, (univ.filter fun a => f a = b).card = k) :
    Fintype.card A = Fintype.card B*k := by
  let e : A ≃ (b : B) × {a : A // f a = b} := {
    toFun := fun a => ⟨f a,⟨a,rfl⟩⟩
    invFun := fun p => p.2.val
    left_inv := fun _ => rfl
    right_inv := by rintro ⟨b,a,ha⟩; subst b; rfl }
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_sigma,fiber_card_subtype,hf,sum_const,card_univ,nsmul_eq_mul] using hc

lemma constant_fiber_preimage_card (f : A → B) (k : ℕ)
    (hf : ∀ b, (univ.filter fun a => f a = b).card = k) (S : Finset B) :
    (univ.filter fun a => f a ∈ S).card = S.card*k := by
  let e : {a : A // f a ∈ S} ≃ (b : S) × {a : A // f a = b.val} := {
    toFun := fun a => ⟨⟨f a.val,a.property⟩,⟨a.val,rfl⟩⟩
    invFun := fun p => ⟨p.2.val,by rw [p.2.property]; exact p.1.property⟩
    left_inv := fun _ => rfl
    right_inv := by
      rintro ⟨⟨b,hb⟩,a,ha⟩
      change f a = b at ha
      subst b
      rfl }
  have hc := Fintype.card_congr e
  simpa [Fintype.card_subtype,Fintype.card_sigma,fiber_card_subtype,hf] using hc

theorem uniformProb_constant_fiber (f : A → B) {k : ℕ} (hk : 0 < k)
    (hf : ∀ b, (univ.filter fun a => f a = b).card = k) (S : Finset B) :
    uniformProb (univ.filter fun a => f a ∈ S) = uniformProb S := by
  unfold uniformProb
  rw [constant_fiber_preimage_card f k hf S,constant_fiber_card f k hf]
  push_cast
  exact mul_div_mul_right _ _ (by exact_mod_cast hk.ne' : (k:ℝ) ≠ 0)

lemma word_fiber_card (f : A → B) {k T : ℕ}
    (hf : ∀ b, (univ.filter fun a => f a = b).card = k) (y : Fin T → B) :
    (univ.filter fun x : Fin T → A => (fun t => f (x t)) = y).card = k^T := by
  let e : {x : Fin T → A // (fun t => f (x t)) = y} ≃
      ((t : Fin T) → {a : A // f a = y t}) := {
    toFun := fun x t => ⟨x.val t,congrFun x.property t⟩
    invFun := fun z => ⟨fun t => (z t).val,funext fun t => (z t).property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_subtype,Fintype.card_pi,fiber_card_subtype,hf,prod_const,
    card_univ,Fintype.card_fin] using hc

end Carpooling
