import Carpooling.VaryingSchedule
import Carpooling.CountBounds
import Carpooling.FiniteMixtures

namespace Carpooling
open Finset
open scoped Classical
variable {A J U E : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
 [Fintype J] [DecidableEq J] [Nonempty J] [Fintype U] [DecidableEq U]
 [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def splitFailure {T : ℕ} {V : Type*} [Fintype V] [DecidableEq V]
    (R : (Fin T → A) → (Fin T → E) → IntegerRun V T) (h : ℕ) :
    Finset ((Fin T → A) × (Fin T → E)) :=
  univ.filter fun p => p.2 ∉ integerDiscrepancyEvent (R p.1) h

/-- Component probabilities may be nonuniform. Each targeted clique has N
vertices among the uniform label alphabet A; the remaining labels can select
an arbitrary padding component, whose edges are allowed a different decoder. -/
theorem weighted_cliques_lower_probability {N L h : ℕ}
    (hN : 0 < N) (hNL : 2*L ≤ N) (cls : A → Option J)
    (hfiber : ∀ j, (univ.filter fun a => cls a = some j).card = N)
    (f : Fin (2*h+2) ↪ U)
    (g : (Fin (Fintype.card A) → A) → Fin (Fintype.card A) → E → Sym2 U)
    (encode : Option J → (a b : Fin (2*h+2)) → a ≠ b → E)
    (hencode : ∀ s t j a b hab, cls (s t) = some j →
      g s t (encode (some j) a b hab) = s(f a,f b))
    (hL : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(L:ℤ))
    (R : (Fin (Fintype.card A) → A) → (Fin (Fintype.card A) → E) →
      IntegerRun (Option J × U) (Fintype.card A))
    (hi : ∀ s x v, (R s x).d 0 v = 0)
    (hrequest : ∀ s x (t : Fin (Fintype.card A)),
      s(((R s x).step t.val t.isLt).u,((R s x).step t.val t.isLt).v) =
        (g s t (x t)).map (fun u => (cls (s t),u)))
    (hcausal : ∀ s (t : Fin (Fintype.card A)) x y,
      (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ =
        y ⟨i.val,lt_trans i.isLt t.isLt⟩) → (R s x).d t.val = (R s y).d t.val) :
    uniformProb (splitFailure R h) ≤
      8/(N:ℝ)+2*(Fintype.card E:ℝ)^L/(Fintype.card J:ℝ) := by
  classical
  let c : (Fin (Fintype.card A) → A) → J → ℕ := classCount cls
  let a : ℝ := 2*(Fintype.card E:ℝ)^L/(Fintype.card J:ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hgood : ∀ s, s ∉ fewPopulated c L →
      uniformProb (eventFiber (splitFailure R h) s) ≤ a := by
    intro s hs
    let K := {j : J // j ∈ populated c L s}
    have hcard : Fintype.card J ≤ 2*Fintype.card K := by
      have he : Fintype.card K = (populated c L s).card := Fintype.card_coe _
      rw [he]
      simpa [fewPopulated] using hs
    have hK : 0 < Fintype.card K := by have := Fintype.card_pos (α := J); omega
    let target : K ↪ Option J := ⟨fun k => some k.val,fun _ _ h => Subtype.ext (Option.some.inj h)⟩
    have hcount : ∀ k : K, L ≤ (univ.filter fun t => cls (s t) = target k).card := by
      intro k
      exact (mem_filter.mp k.property).2
    have hb := scheduled_varying_targets_of_counts hK target f (fun t => cls (s t))
      (g s) encode (fun t k a b hab ht => hencode s t k.val a b hab ht)
      hcount hL (R s) (hi s) (hrequest s) (hcausal s)
    have he : eventFiber (splitFailure R h) s = univ \ integerDiscrepancyEvent (R s) h := by
      ext x; simp [eventFiber,splitFailure]
    rw [he]
    apply hb.trans
    have hMR : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
    have hKR : (0:ℝ) < Fintype.card K := by exact_mod_cast hK
    have hcardR : (Fintype.card J:ℝ) ≤ 2*(Fintype.card K:ℝ) := by exact_mod_cast hcard
    dsimp [a]
    apply (div_le_div_iff₀ hKR hMR).mpr
    nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg (Fintype.card E)) L)
      (sub_nonneg.mpr hcardR)]
  have hb := uniformProb_mixture_bound (splitFailure R h) (fewPopulated c L) ha hgood
  have ho := fewPopulated_probability c hN hNL (fun j => classCount_variance cls N hfiber j)
  exact hb.trans (add_le_add_right ho a)

end Carpooling
