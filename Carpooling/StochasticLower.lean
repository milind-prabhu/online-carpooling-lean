import Carpooling.ScheduledLower
import Carpooling.Occupancy
import Carpooling.FiniteMixtures

/-! Unconditional stochastic lower bound in the product sampling model for
disjoint cliques. N is the mean local request count; the graph specialization
sets N to the number of vertices per clique. -/
namespace Carpooling
open Finset
open scoped Classical
variable {J U E : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
  [Fintype U] [DecidableEq U] [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def productLowerFailure {T : ℕ}
    (R : (Fin T → J) → (Fin T → E) → IntegerRun (J × U) T) (h : ℕ) :
    Finset ((Fin T → J) × (Fin T → E)) :=
  univ.filter fun x => x.2 ∉ integerDiscrepancyEvent (R x.1) h

/-- For MN iid uniform requests from M disjoint cliques, every causal
unit-weight orientation algorithm reaches discrepancy h except with
probability at most 8/N + 2q^L/M, where q is the local edge alphabet size.
No local count, schedule, or probability estimate is assumed. -/
theorem iid_cliques_lower_probability {N L h : ℕ} (hN : 0 < N) (hNL : 2*L ≤ N)
    (f : Fin (2*h+2) ↪ U) (g : E → Sym2 U)
    (encode : (a b : Fin (2*h+2)) → a ≠ b → E)
    (hencode : ∀ a b hab, g (encode a b hab) = s(f a,f b))
    (hL : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(L:ℤ))
    (R : (Fin (Fintype.card J*N) → J) → (Fin (Fintype.card J*N) → E) →
      IntegerRun (J × U) (Fintype.card J*N))
    (hi : ∀ s x v, (R s x).d 0 v = 0)
    (hrequest : ∀ s x (t : Fin (Fintype.card J*N)),
      s(((R s x).step t.val t.isLt).u,((R s x).step t.val t.isLt).v) =
        (g (x t)).map (fun u => (s t,u)))
    (hcausal : ∀ s (t : Fin (Fintype.card J*N)) (x y : Fin (Fintype.card J*N) → E),
      (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ =
        y ⟨i.val,lt_trans i.isLt t.isLt⟩) → (R s x).d t.val = (R s y).d t.val) :
    uniformProb (productLowerFailure R h) ≤
      8/(N:ℝ)+2*(Fintype.card E:ℝ)^L/(Fintype.card J:ℝ) := by
  classical
  let a : ℝ := 2*(Fintype.card E:ℝ)^L/(Fintype.card J:ℝ)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hgood : ∀ s, s ∉ fewGoodLabelsEvent (J := J) N L →
      uniformProb (eventFiber (productLowerFailure R h) s) ≤ a := by
    intro s hs
    let K := {j : J // j ∈ goodLabels s L}
    have hcard : Fintype.card J ≤ 2*Fintype.card K := by
      have he : Fintype.card K = (goodLabels s L).card := Fintype.card_coe _
      rw [he]
      simpa [fewGoodLabelsEvent] using hs
    have hK : 0 < Fintype.card K := by have := Fintype.card_pos (α := J); omega
    let target : K ↪ J := ⟨Subtype.val,Subtype.val_injective⟩
    have hcount : ∀ k : K, L ≤ (univ.filter fun t => s t = target k).card := by
      intro k
      exact (mem_filter.mp k.property).2
    have hb := scheduled_targets_lower_probability_of_counts hK target f g encode hencode
      s hcount hL (R s) (hi s) (hrequest s) (hcausal s)
    have hfiber : eventFiber (productLowerFailure R h) s =
        univ \ integerDiscrepancyEvent (R s) h := by
      ext x
      simp [eventFiber,productLowerFailure]
    rw [hfiber]
    apply hb.trans
    have hMR : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
    have hKR : (0:ℝ) < Fintype.card K := by exact_mod_cast hK
    have hcardR : (Fintype.card J:ℝ) ≤ 2*(Fintype.card K:ℝ) := by exact_mod_cast hcard
    dsimp [a]
    apply (div_le_div_iff₀ hKR hMR).mpr
    nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg (Fintype.card E)) L)
      (sub_nonneg.mpr hcardR)]
  have hb := uniformProb_mixture_bound (productLowerFailure R h) (fewGoodLabelsEvent N L) ha hgood
  have ho := few_good_labels_probability (J := J) hN hNL
  exact hb.trans (add_le_add_right ho a)

end Carpooling
