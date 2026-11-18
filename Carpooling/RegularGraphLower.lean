import Carpooling.StochasticLower
import Carpooling.DisjointCliques

namespace Carpooling
open Finset
open scoped Classical
variable {J U : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
  [Fintype U] [DecidableEq U] [Nonempty (⊤ : SimpleGraph U).edgeSet]

/-- Unconditional finite stochastic lower bound on an actual regular graph.
The graph has M*N vertices and degree N-1, and exactly MN iid uniform graph
edges are sampled. Every causal algorithm is covered, with unit weights.
The explicit failure bound is 8/N + 2*choose(N,2)^L/M. -/
theorem regular_cliques_stochastic_lower {L h : ℕ}
    (f : Fin (2*h+2) ↪ U) (hNL : 2*L ≤ Fintype.card U)
    (hL : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(L:ℤ))
    (R : (Fin (Fintype.card J*Fintype.card U) →
      (disjointCliques (J := J) (U := U)).edgeSet) →
      IntegerRun (J × U) (Fintype.card J*Fintype.card U))
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x (t : Fin (Fintype.card J*Fintype.card U)),
      s(((R x).step t.val t.isLt).u,((R x).step t.val t.isLt).v) = (x t).val)
    (hcausal : ∀ (t : Fin (Fintype.card J*Fintype.card U)) x y,
      (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ =
        y ⟨i.val,lt_trans i.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    uniformProb (univ \ integerDiscrepancyEvent R h) ≤
      8/(Fintype.card U:ℝ)+2*((Fintype.card U).choose 2:ℝ)^L/(Fintype.card J:ℝ) := by
  classical
  let T := Fintype.card J*Fintype.card U
  let e := cliqueSampleEquiv (J := J) (U := U) T
  let Q := fun s x => R (e (s,x))
  letI : Nonempty U := ⟨f ⟨0,by omega⟩⟩
  letI : Nonempty (disjointCliques (J := J) (U := U)).edgeSet :=
    ⟨disjointCliqueEdgeEquiv (Classical.choice ‹Nonempty J›,
      Classical.choice ‹Nonempty (⊤ : SimpleGraph U).edgeSet›)⟩
  let encode : (a b : Fin (2*h+2)) → a ≠ b → (⊤ : SimpleGraph U).edgeSet :=
    fun a b hab => ⟨s(f a,f b),by simpa using f.injective.ne hab⟩
  have hreq : ∀ s x (t : Fin T),
      s(((Q s x).step t.val t.isLt).u,((Q s x).step t.val t.isLt).v) =
        ((x t).val).map (fun u => (s t,u)) := by
    intro s x t
    exact hrequest (e (s,x)) t
  have hcaus : ∀ s (t : Fin T) x y,
      (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ =
        y ⟨i.val,lt_trans i.isLt t.isLt⟩) → (Q s x).d t.val = (Q s y).d t.val := by
    intro s t x y hxy
    apply hcausal t
    intro i
    change disjointCliqueEdgeEquiv (s _,x _) = disjointCliqueEdgeEquiv (s _,y _)
    rw [hxy i]
  have hp := iid_cliques_lower_probability (J := J) (N := Fintype.card U)
    Fintype.card_pos hNL f (fun edge : (⊤ : SimpleGraph U).edgeSet => edge.val)
    encode (fun _ _ _ => rfl) hL Q (fun s x v => hi (e (s,x)) v) hreq hcaus
  let A := univ \ integerDiscrepancyEvent R h
  have hfailure : productLowerFailure Q h = univ.filter (fun p => e p ∈ A) := by
    ext p
    simp [productLowerFailure,A,integerDiscrepancyEvent,Q,T]
  rw [hfailure,uniformProb_equiv_preimage] at hp
  have hcard : Fintype.card (⊤ : SimpleGraph U).edgeSet = (Fintype.card U).choose 2 := by
    simpa only [SimpleGraph.edgeFinset_card] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := U))
  simpa only [hcard] using hp

end Carpooling
