import Carpooling.RegularGraphs
import Carpooling.FiniteMixtures

namespace Carpooling
open Finset
open scoped Classical
variable {J U : Type*} [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]

/-- A disjoint union of complete graphs, with one copy of U for each j. -/
def disjointCliques : SimpleGraph (J × U) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := fun _ _ h => ⟨h.1.symm,h.2.symm⟩
  loopless := fun _ h => h.2 rfl

instance disjointCliques_decidableAdj : DecidableRel (disjointCliques (J := J) (U := U)).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = _ ∧ _ ≠ _))

theorem disjointCliques_regular :
    (disjointCliques (J := J) (U := U)).IsRegularOfDegree (Fintype.card U-1) := by
  intro ⟨j,u⟩
  let e : (disjointCliques (J := J) (U := U)).neighborSet (j,u) ≃ {v : U // v ≠ u} := {
    toFun := fun v => ⟨v.val.2,Ne.symm v.property.2⟩
    invFun := fun v => ⟨(j,v.val),⟨rfl,Ne.symm v.property⟩⟩
    left_inv := fun v => Subtype.ext (Prod.ext v.property.1 rfl)
    right_inv := fun _ => rfl }
  rw [←SimpleGraph.card_neighborSet_eq_degree]
  calc
    _ = Fintype.card {v : U // v ≠ u} := Fintype.card_congr e
    _ = Fintype.card U-1 := by rw [Fintype.card_subtype_compl]; simp

noncomputable def disjointCliqueEdgeMap
    (p : J × (⊤ : SimpleGraph U).edgeSet) : (disjointCliques (J := J) (U := U)).edgeSet := by
  refine ⟨p.2.val.map (fun u => (p.1,u)),?_⟩
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective p.2.val
  have huv : u ≠ v := by simpa [←he] using p.2.property
  rw [←he,Sym2.map_pair_eq,SimpleGraph.mem_edgeSet]
  exact ⟨rfl,huv⟩

lemma disjointCliqueEdgeMap_injective :
    Function.Injective (disjointCliqueEdgeMap (J := J) (U := U)) := by
  rintro ⟨j,e⟩ ⟨k,f⟩ h
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
  obtain ⟨⟨w,z⟩,hf⟩ := Sym2.mk_surjective f.val
  have hh := congrArg Subtype.val h
  change e.val.map (fun u => (j,u)) = f.val.map (fun u => (k,u)) at hh
  rw [←he,←hf,Sym2.map_pair_eq,Sym2.map_pair_eq] at hh
  rcases Sym2.eq_iff.mp hh with ⟨hu,hv⟩ | ⟨hu,hv⟩
  · refine Prod.ext (show j = k from congrArg Prod.fst hu) ?_
    apply Subtype.ext
    rw [←he,←hf]
    exact Sym2.eq_iff.mpr (Or.inl ⟨congrArg Prod.snd hu,congrArg Prod.snd hv⟩)
  · refine Prod.ext (show j = k from congrArg Prod.fst hu) ?_
    apply Subtype.ext
    rw [←he,←hf]
    exact Sym2.eq_iff.mpr (Or.inr ⟨congrArg Prod.snd hu,congrArg Prod.snd hv⟩)

lemma disjointCliqueEdgeMap_surjective :
    Function.Surjective (disjointCliqueEdgeMap (J := J) (U := U)) := by
  intro e
  obtain ⟨⟨⟨j,u⟩,⟨k,v⟩⟩,he⟩ := Sym2.mk_surjective e.val
  have hadj : j = k ∧ u ≠ v := by
    have hm := e.property
    rw [←he,SimpleGraph.mem_edgeSet] at hm
    exact hm
  rcases hadj with ⟨hjk,huv⟩
  subst k
  refine ⟨(j,⟨s(u,v),by simpa using huv⟩),?_⟩
  apply Subtype.ext
  exact he

noncomputable def disjointCliqueEdgeEquiv :
    (J × (⊤ : SimpleGraph U).edgeSet) ≃ (disjointCliques (J := J) (U := U)).edgeSet :=
  Equiv.ofBijective disjointCliqueEdgeMap
    ⟨disjointCliqueEdgeMap_injective,disjointCliqueEdgeMap_surjective⟩

@[simp] lemma disjointCliqueEdgeEquiv_val (p : J × (⊤ : SimpleGraph U).edgeSet) :
    (disjointCliqueEdgeEquiv p).val = p.2.val.map (fun u => (p.1,u)) := rfl

theorem disjointCliques_edge_card :
    Fintype.card (disjointCliques (J := J) (U := U)).edgeSet =
      Fintype.card J*(Fintype.card U).choose 2 := by
  have hc := (Fintype.card_congr (disjointCliqueEdgeEquiv (J := J) (U := U))).symm
  rw [Fintype.card_prod] at hc
  have he : Fintype.card (⊤ : SimpleGraph U).edgeSet = (Fintype.card U).choose 2 := by
    simpa only [SimpleGraph.edgeFinset_card] using
      (SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := U))
  rwa [he] at hc

/-- Splitting a uniform graph-edge word into independent uniform clique labels
and independent uniform local edges is an exact finite sample-space bijection. -/
noncomputable def cliqueSampleEquiv (T : ℕ) :
    ((Fin T → J) × (Fin T → (⊤ : SimpleGraph U).edgeSet)) ≃
      (Fin T → (disjointCliques (J := J) (U := U)).edgeSet) where
  toFun x t := disjointCliqueEdgeEquiv (x.1 t,x.2 t)
  invFun y := (fun t => (disjointCliqueEdgeEquiv.symm (y t)).1,
    fun t => (disjointCliqueEdgeEquiv.symm (y t)).2)
  left_inv x := by
    apply Prod.ext <;> funext t <;> simp
  right_inv y := by
    funext t
    simp

end Carpooling
