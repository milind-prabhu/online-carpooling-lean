import Carpooling.LowerBound
import Carpooling.AdaptiveProbability
import Mathlib.Data.Sym.Sym2
import Mathlib.Combinatorics.SimpleGraph.Finite

/-! Local stochastic lower bound on a complete graph, against every causal
online orientation rule. Global Poissonization is not assumed here. -/
namespace Carpooling
open Finset
open scoped Classical
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def extendSamplePrefix {T : ℕ} (t : Fin T)
    (past : Fin t.val → E) : Fin T → E :=
  fun s => if hs : s.val < t.val then past ⟨s.val,hs⟩ else Classical.choice ‹Nonempty E›

noncomputable def integerDiscrepancyEvent {V : Type*} [Fintype V] [DecidableEq V]
    {T : ℕ} (R : (Fin T → E) → IntegerRun V T) (h : ℕ) : Finset (Fin T → E) :=
  by
    classical
    exact univ.filter fun x => ∃ t ≤ T, ∃ v, (h:ℤ) ≤ |(R x).d t v|

/-- Local lower bound with explicit constants. The edge alphabet can be any
uniform finite encoding of all unordered pairs of 2h+2 vertices. The online
rule is arbitrary, subject only to unit-weight updates and prefix causality.
In particular its orientation is not required to be Greedy. -/
theorem complete_graph_local_lower_probability (h : ℕ)
    (g : E → Sym2 (Fin (2*h+2)))
    (encode : (u v : Fin (2*h+2)) → u ≠ v → E)
    (hencode : ∀ u v huv, g (encode u v huv) = s(u,v))
    (T : ℕ) (hT : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(T:ℤ))
    (R : (Fin T → E) → IntegerRun (Fin (2*h+2)) T)
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x t (ht : t < T),
      s(((R x).step t ht).u,((R x).step t ht).v) = g (x ⟨t,ht⟩))
    (hcausal : ∀ (t : Fin T) (x y : Fin T → E),
      (∀ s : Fin t.val, x ⟨s.val,lt_trans s.isLt t.isLt⟩ =
        y ⟨s.val,lt_trans s.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    1/(Fintype.card E:ℝ)^T ≤ uniformProb (integerDiscrepancyEvent R h) := by
  classical
  let P : (t : Fin T) → (Fin t.val → E) → E := fun t z =>
    let pos := (R (extendSamplePrefix t z)).d t.val
    encode (lowerPair h pos).1 (lowerPair h pos).2 (lowerPair_distinct h pos)
  rw [←adaptive_matching_probability P]
  apply uniformProb_mono
  intro x hx
  have hm := (mem_filter.mp hx).2
  simp only [integerDiscrepancyEvent,mem_filter,mem_univ,true_and]
  apply equal_endpoint_lower_bound (R x) (hi x) _ (by simpa using hT)
  intro t ht hb
  let ti : Fin T := ⟨t,ht⟩
  let z : Fin ti.val → E := fun s => x ⟨s.val,lt_trans s.isLt ti.isLt⟩
  have hstate : (R (extendSamplePrefix ti z)).d t = (R x).d t := by
    apply hcausal ti
    intro s
    simp [extendSamplePrefix,z,s.isLt]
  have heq : g (x ti) =
      s((lowerPair h ((R x).d t)).1,(lowerPair h ((R x).d t)).2) := by
    rw [hm ti]
    change g (encode _ _ _) = _
    rw [hencode]
    change s((lowerPair h ((R (extendSamplePrefix ti z)).d t)).1,
      (lowerPair h ((R (extendSamplePrefix ti z)).d t)).2) = _
    rw [hstate]
  have he := (hrequest x t ht).trans heq
  have hlower := lowerPair_equal h ((R x).d t) hb
  rcases Sym2.eq_iff.mp he with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · rw [hu,hv]; exact hlower
  · rw [hu,hv]; exact hlower.symm

/-- Uniform edge alphabet of an actual complete simple graph. -/
abbrev CliqueEdge (h : ℕ) := (⊤ : SimpleGraph (Fin (2*h+2))).edgeSet

def cliqueEncode (h : ℕ) (u v : Fin (2*h+2)) (huv : u ≠ v) : CliqueEdge h :=
  ⟨s(u,v),by simpa using huv⟩

instance cliqueEdge_nonempty (h : ℕ) : Nonempty (CliqueEdge h) := by
  refine ⟨cliqueEncode h ⟨0,by omega⟩ ⟨1,by omega⟩ ?_⟩
  intro heq
  have he := congrArg Fin.val heq
  simp only [Fin.mk.injEq] at heq
  contradiction

lemma cliqueEdge_card (h : ℕ) : Fintype.card (CliqueEdge h) = (2*h+2).choose 2 := by
  simpa only [SimpleGraph.edgeFinset_card,Fintype.card_fin] using
    (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin (2*h+2)))

/-- The local stochastic lower bound specialized to an actual complete graph:
at least (choose(2h+2,2))^(-T) chance of reaching discrepancy h. -/
theorem clique_local_lower_probability (h T : ℕ)
    (hT : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(T:ℤ))
    (R : (Fin T → CliqueEdge h) → IntegerRun (Fin (2*h+2)) T)
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x t (ht : t < T),
      s(((R x).step t ht).u,((R x).step t ht).v) = (x ⟨t,ht⟩).val)
    (hcausal : ∀ (t : Fin T) (x y : Fin T → CliqueEdge h),
      (∀ s : Fin t.val, x ⟨s.val,lt_trans s.isLt t.isLt⟩ =
        y ⟨s.val,lt_trans s.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    1/((2*h+2).choose 2:ℝ)^T ≤ uniformProb (integerDiscrepancyEvent R h) := by
  have hp := complete_graph_local_lower_probability h (fun e : CliqueEdge h => e.val)
    (cliqueEncode h) (fun _ _ _ => rfl) T hT R hi hrequest hcausal
  simpa only [cliqueEdge_card] using hp

end Carpooling
