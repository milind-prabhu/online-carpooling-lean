import Carpooling.RegularGraphLower
import Mathlib.Data.Nat.Choose.Bounds

namespace Carpooling
open Finset
open scoped Classical

/-- Number of locally forced requests used for discrepancy h. -/
def lowerRequestThreshold (h : ℕ) : ℕ := (h+1)*h^2+1

lemma lowerRequestThreshold_le {h : ℕ} (hh : 0 < h) : lowerRequestThreshold h ≤ 3*h^3 := by
  have h1 : 1 ≤ h^2 := Nat.one_le_pow _ _ hh
  unfold lowerRequestThreshold
  have hmul := Nat.mul_le_mul_right (h^2) (show h+1 ≤ 2*h by omega)
  nlinarith

lemma lowerRequestThreshold_horizon (h : ℕ) :
    ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(lowerRequestThreshold h:ℤ) := by
  unfold lowerRequestThreshold
  push_cast
  nlinarith

/-- Finite logarithmic tradeoff: h³ ≤ (log_N M)/12 yields discrepancy h,
provided N ≥ 6h³. The failure probability is at most 10/N. -/
lemma lower_failure_log_bound {M N h : ℕ} (hM : 0 < M) (hN : 0 < N) (hh : 0 < h)
    (hlog : 12*h^3 ≤ Nat.log N M) :
    8/(N:ℝ)+2*(N.choose 2:ℝ)^(lowerRequestThreshold h)/(M:ℝ) ≤ 10/(N:ℝ) := by
  let L := lowerRequestThreshold h
  let a := N^(2*L)
  have hL : L ≤ 3*h^3 := lowerRequestThreshold_le hh
  have hLp : 0 < L := by dsimp [L,lowerRequestThreshold]; omega
  have hpower : N^(4*L) ≤ M := by
    exact (Nat.pow_le_pow_right hN (show 4*L ≤ Nat.log N M by omega)).trans
      (Nat.pow_log_le_self N hM.ne')
  have haM : a^2 ≤ M := by simpa [a,←pow_mul,mul_comm,mul_left_comm,mul_assoc] using hpower
  have hq : (N.choose 2)^L ≤ a := by
    have he := Nat.pow_le_pow_left (Nat.choose_le_pow N 2) L
    simpa [a,←pow_mul,mul_comm] using he
  have hNa : N ≤ a := by
    calc
      N = N^1 := (pow_one _).symm
      _ ≤ N^(2*L) := Nat.pow_le_pow_right hN (by omega)
  have hMR : (0:ℝ) < M := by exact_mod_cast hM
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have haR : (0:ℝ) < a := by exact_mod_cast pow_pos hN (2*L)
  have hqR : (N.choose 2:ℝ)^L ≤ a := by exact_mod_cast hq
  have haMR : (a:ℝ)^2 ≤ M := by exact_mod_cast haM
  have hNaR : (N:ℝ) ≤ a := by exact_mod_cast hNa
  have hratio : (N.choose 2:ℝ)^L/(M:ℝ) ≤ 1/(a:ℝ) := by
    apply (div_le_div_iff₀ hMR haR).mpr
    nlinarith
  have hinv : 1/(a:ℝ) ≤ 1/(N:ℝ) := one_div_le_one_div_of_le hNR hNaR
  calc
    _ = 8/(N:ℝ)+2*((N.choose 2:ℝ)^L/(M:ℝ)) := by ring
    _ ≤ 8/(N:ℝ)+2*(1/(N:ℝ)) := by linarith [hratio.trans hinv]
    _ = _ := by ring

variable {J U : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
  [Fintype U] [DecidableEq U] [Nonempty (⊤ : SimpleGraph U).edgeSet]

/-- Explicit high-probability cube-root stochastic lower bound on a regular
disjoint-clique graph. Degree is N-1, vertices and iid arrivals both MN.
Every integer h with 6h³≤N and 12h³≤floor(log_N M) is attained with
probability at least 1-10/N by every causal orientation algorithm. -/
theorem regular_cliques_lower_logarithmic {h : ℕ} (hh : 0 < h)
    (hsize : 6*h^3 ≤ Fintype.card U)
    (hlog : 12*h^3 ≤ Nat.log (Fintype.card U) (Fintype.card J))
    (R : (Fin (Fintype.card J*Fintype.card U) →
      (disjointCliques (J := J) (U := U)).edgeSet) →
      IntegerRun (J × U) (Fintype.card J*Fintype.card U))
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x (t : Fin (Fintype.card J*Fintype.card U)),
      s(((R x).step t.val t.isLt).u,((R x).step t.val t.isLt).v) = (x t).val)
    (hcausal : ∀ (t : Fin (Fintype.card J*Fintype.card U)) x y,
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
  have hb := regular_cliques_stochastic_lower f (show 2*lowerRequestThreshold h ≤ Fintype.card U by omega)
    (lowerRequestThreshold_horizon h) R hi hrequest hcausal
  exact hb.trans (lower_failure_log_bound Fintype.card_pos hN hh hlog)

end Carpooling
