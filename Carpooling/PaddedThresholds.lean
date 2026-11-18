import Carpooling.PaddedLower
import Carpooling.PaddingParameters

namespace Carpooling
open Finset
open scoped Classical

lemma padded_failure_log_bound {M N P h : ℕ} (hM : 0 < M) (hN : 0 < N) (hh : 0 < h)
    (hP : P ≤ N^4) (hlog : 48*h^3 ≤ Nat.log N M) :
    8/(N:ℝ)+2*(P:ℝ)^(lowerRequestThreshold h)/(M:ℝ) ≤ 10/(N:ℝ) := by
  let L := lowerRequestThreshold h
  let b := N^(4*L)
  have hL : L ≤ 3*h^3 := lowerRequestThreshold_le hh
  have hLp : 0 < L := by dsimp [L,lowerRequestThreshold]; omega
  have hp : N^(8*L) ≤ M := (Nat.pow_le_pow_right hN (show 8*L ≤ Nat.log N M by omega)).trans
    (Nat.pow_log_le_self N hM.ne')
  have hbM : b^2 ≤ M := by simpa [b,←pow_mul,mul_comm,mul_left_comm,mul_assoc] using hp
  have hPb : P^L ≤ b := by simpa [b,←pow_mul] using Nat.pow_le_pow_left hP L
  have hNb : N ≤ b := by
    calc
      N = N^1 := (pow_one _).symm
      _ ≤ N^(4*L) := Nat.pow_le_pow_right hN (by omega)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hbR : (0:ℝ) < b := by exact_mod_cast pow_pos hN (4*L)
  have hPR : (P:ℝ)^L ≤ b := by exact_mod_cast hPb
  have hbMR : (b:ℝ)^2 ≤ M := by exact_mod_cast hbM
  have hNbR : (N:ℝ) ≤ b := by exact_mod_cast hNb
  have hr : (P:ℝ)^L/(M:ℝ) ≤ 1/(b:ℝ) := by
    apply (div_le_div_iff₀ hMR hbR).mpr
    nlinarith
  have hi := one_div_le_one_div_of_le hNR hNbR
  calc
    _ = 8/(N:ℝ)+2*((P:ℝ)^L/(M:ℝ)) := by ring
    _ ≤ 8/(N:ℝ)+2*(1/(N:ℝ)) := by linarith [hr.trans hi]
    _ = _ := by ring

variable {J U W : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
 [Fintype U] [DecidableEq U] [Nonempty (⊤ : SimpleGraph U).edgeSet]
 [Fintype W] [DecidableEq W]

theorem padded_graph_lower_logarithmic (H : SimpleGraph W) [DecidableRel H.Adj]
    [Nonempty H.edgeSet] (hH : H.IsRegularOfDegree (Fintype.card U-1))
    {h : ℕ} (hh : 0 < h) (hsize : 6*h^3 ≤ Fintype.card U)
    (hrem : Fintype.card W ≤ 2*Fintype.card U)
    (hlog : 48*h^3 ≤ Nat.log (Fintype.card U) (Fintype.card J))
    (R : (Fin (Fintype.card ((J × U) ⊕ W)) → (paddedGraph (J := J) (U := U) H).edgeSet) →
      IntegerRun ((J × U) ⊕ W) (Fintype.card ((J × U) ⊕ W)))
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x (t : Fin (Fintype.card ((J × U) ⊕ W))),
      s(((R x).step t.val t.isLt).u,((R x).step t.val t.isLt).v) = (x t).val)
    (hcausal : ∀ (t : Fin (Fintype.card ((J × U) ⊕ W))) x y,
      (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ =
        y ⟨i.val,lt_trans i.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    uniformProb (univ \ integerDiscrepancyEvent R h) ≤ 10/(Fintype.card U:ℝ) := by
  have hcube : h ≤ h^3 := by simpa using Nat.pow_le_pow_right hh (by decide : 1 ≤ 3)
  have hsmall : 2*h+2 ≤ Fintype.card U := by omega
  let f : Fin (2*h+2) ↪ U := {
    toFun := fun i => (Fintype.equivFin U).symm ⟨i.val,lt_of_lt_of_le i.isLt hsmall⟩
    inj' := by
      intro a b he
      have he' := (Fintype.equivFin U).symm.injective he
      exact Fin.ext (congrArg (fun v : Fin (Fintype.card U) => v.val) he') }
  have hN : 0 < Fintype.card U := by omega
  have hL := lowerRequestThreshold_le hh
  have hb := padded_graph_stochastic_lower H hH hh f
    (show 2*lowerRequestThreshold h ≤ Fintype.card U by omega)
    (lowerRequestThreshold_horizon h) R hi hrequest hcausal
  have hq : Fintype.card (⊤ : SimpleGraph U).edgeSet ≤ (Fintype.card U)^2 := by
    have he : Fintype.card (⊤ : SimpleGraph U).edgeSet = (Fintype.card U).choose 2 := by
      simpa only [SimpleGraph.edgeFinset_card] using SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := U)
    rw [he]; exact Nat.choose_le_pow _ _
  have hp : Fintype.card H.edgeSet ≤ (Fintype.card U)^2 := by
    have he := regular_edge_balance H hH
    have hd : Fintype.card U-1 ≤ Fintype.card U := Nat.sub_le _ _
    have hm := Nat.mul_le_mul hrem hd
    nlinarith
  have hP : Fintype.card (⊤ : SimpleGraph U).edgeSet*Fintype.card H.edgeSet ≤ (Fintype.card U)^4 := by
    have hm := Nat.mul_le_mul hq hp
    nlinarith
  apply hb.trans
  simpa only [Nat.cast_mul] using padded_failure_log_bound Fintype.card_pos hN hh hP hlog

end Carpooling
