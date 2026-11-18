import Carpooling.GraphSums
import Carpooling.MixedSampling
import Carpooling.WeightedLower

namespace Carpooling
open Finset
open scoped Classical
variable {J U W : Type*} [Fintype J] [DecidableEq J] [Fintype U] [DecidableEq U]
 [Fintype W] [DecidableEq W]

abbrev paddedGraph (H : SimpleGraph W) := (disjointCliques (J := J) (U := U)) ⊕g H

noncomputable def paddedEdgeEquiv (H : SimpleGraph W) :
    ((J × (⊤ : SimpleGraph U).edgeSet) ⊕ H.edgeSet) ≃ (paddedGraph (J := J) (U := U) H).edgeSet :=
  (Equiv.sumCongr disjointCliqueEdgeEquiv (Equiv.refl _)).trans (sumEdgeEquiv _ H)

noncomputable def paddedDecoder (H : SimpleGraph W) :
    (((J × U) ⊕ W) × ((⊤ : SimpleGraph U).edgeSet × H.edgeSet)) →
      (paddedGraph (J := J) (U := U) H).edgeSet :=
  fun a => paddedEdgeEquiv H (mixedPairDecoder a)

noncomputable def paddedLocalEdge (H : SimpleGraph W) :
    ((J × U) ⊕ W) → ((⊤ : SimpleGraph U).edgeSet × H.edgeSet) → Sym2 (U ⊕ W)
  | Sum.inl _,e => e.1.val.map Sum.inl
  | Sum.inr _,e => e.2.val.map Sum.inr

lemma paddedDecoder_frame (H : SimpleGraph W) (a : (J × U) ⊕ W)
    (e : (⊤ : SimpleGraph U).edgeSet × H.edgeSet) :
    (paddedDecoder H (a,e)).val.map mixedFrame =
      (paddedLocalEdge H a e).map (fun u => (mixedClass a,u)) := by
  cases a with
  | inl p =>
    rcases p with ⟨j,u⟩
    change ((e.1.val.map (fun u => (j,u))).map Sum.inl).map mixedFrame = _
    simp only [Sym2.map_map,paddedLocalEdge,mixedClass]
    rfl
  | inr w =>
    change (e.2.val.map Sum.inr).map mixedFrame = _
    simp only [Sym2.map_map,paddedLocalEdge,mixedClass]
    rfl

lemma paddedDecoder_constant_fiber (H : SimpleGraph W) [DecidableRel H.Adj]
    (hH : H.IsRegularOfDegree (Fintype.card U-1))
    (e : (paddedGraph (J := J) (U := U) H).edgeSet) :
    (univ.filter fun a => paddedDecoder H a = e).card = Fintype.card U*Fintype.card H.edgeSet := by
  have hbal : Fintype.card U*Fintype.card H.edgeSet =
      Fintype.card W*Fintype.card (⊤ : SimpleGraph U).edgeSet := by
    have h1 := regular_edge_balance H hH
    have h2 := regular_edge_balance (⊤ : SimpleGraph U) SimpleGraph.IsRegularOfDegree.top
    nlinarith [congrArg (Nat.mul (Fintype.card U)) h1,congrArg (Nat.mul (Fintype.card W)) h2]
  have hp : (fun a => paddedDecoder H a = e) =
      (fun a => mixedPairDecoder a = (paddedEdgeEquiv H).symm e) := by
    funext a
    apply propext
    constructor
    · intro ha
      have he := congrArg (paddedEdgeEquiv H).symm ha
      simpa only [paddedDecoder,Equiv.symm_apply_apply] using he
    · intro ha
      change paddedEdgeEquiv H (mixedPairDecoder a) = e
      rw [ha,Equiv.apply_symm_apply]
  have hset : (univ.filter fun a => paddedDecoder H a = e) =
      (univ.filter fun a => mixedPairDecoder a = (paddedEdgeEquiv H).symm e) := by
    ext a
    simp only [mem_filter,mem_univ,true_and]
    exact Iff.of_eq (congrFun hp a)
  rw [hset]
  exact mixedPairDecoder_constant_fiber hbal _

variable [Nonempty J] [Nonempty (⊤ : SimpleGraph U).edgeSet]

/-- Padding by any regular remainder preserves the stochastic lower bound.
The finite probability cost is intentionally loose: prescriptions include
an unused residual-edge coordinate. This keeps the sampler exactly uniform. -/
theorem padded_graph_stochastic_lower (H : SimpleGraph W) [DecidableRel H.Adj]
    [Nonempty H.edgeSet] (hH : H.IsRegularOfDegree (Fintype.card U-1))
    {L h : ℕ} (hh : 0 < h) (f : Fin (2*h+2) ↪ U)
    (hNL : 2*L ≤ Fintype.card U)
    (hL : ((2*h+2:ℕ):ℤ)*(h:ℤ)^2 < 2*(L:ℤ))
    (R : (Fin (Fintype.card ((J × U) ⊕ W)) → (paddedGraph (J := J) (U := U) H).edgeSet) →
      IntegerRun ((J × U) ⊕ W) (Fintype.card ((J × U) ⊕ W)))
    (hi : ∀ x v, (R x).d 0 v = 0)
    (hrequest : ∀ x (t : Fin (Fintype.card ((J × U) ⊕ W))),
      s(((R x).step t.val t.isLt).u,((R x).step t.val t.isLt).v) = (x t).val)
    (hcausal : ∀ (t : Fin (Fintype.card ((J × U) ⊕ W))) x y,
      (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ =
        y ⟨i.val,lt_trans i.isLt t.isLt⟩) → (R x).d t.val = (R y).d t.val) :
    uniformProb (univ \ integerDiscrepancyEvent R h) ≤
      8/(Fintype.card U:ℝ)+2*(Fintype.card (⊤ : SimpleGraph U).edgeSet*
        Fintype.card H.edgeSet:ℝ)^L/(Fintype.card J:ℝ) := by
  classical
  let A := (J × U) ⊕ W
  let E := (⊤ : SimpleGraph U).edgeSet × H.edgeSet
  let T := Fintype.card A
  let words : (Fin T → A) → (Fin T → E) → Fin T → (paddedGraph H).edgeSet :=
    fun s x t => paddedDecoder H (s t,x t)
  let Q := fun s x => (R (words s x)).pushforward (mixedFrame (J := J) (U := U) (W := W))
  letI : Nonempty U := ⟨f ⟨0,by omega⟩⟩
  letI : Nonempty A := ⟨Sum.inl (Classical.choice ‹Nonempty J›,Classical.choice ‹Nonempty U›)⟩
  letI : Nonempty (paddedGraph (J := J) (U := U) H).edgeSet :=
    ⟨paddedDecoder H (Classical.choice ‹Nonempty A›,(Classical.choice ‹Nonempty (⊤ : SimpleGraph U).edgeSet›,Classical.choice ‹Nonempty H.edgeSet›))⟩
  let f' : Fin (2*h+2) ↪ U ⊕ W := ⟨fun i => Sum.inl (f i),fun _ _ h => f.injective (Sum.inl.inj h)⟩
  let encode : Option J → (a b : Fin (2*h+2)) → a ≠ b → E :=
    fun _ a b hab => (⟨s(f a,f b),by simpa using f.injective.ne hab⟩,Classical.choice ‹Nonempty H.edgeSet›)
  have henc : ∀ (s : Fin T → A) (t : Fin T) j a b hab, mixedClass (s t) = some j →
      paddedLocalEdge H (s t) (encode (some j) a b hab) = s(f' a,f' b) := by
    intro s t j a b hab ht
    cases he : s t with
    | inl p => rfl
    | inr w => simp [he,mixedClass] at ht
  have hreq : ∀ s x (t : Fin T),
      s(((Q s x).step t.val t.isLt).u,((Q s x).step t.val t.isLt).v) =
        (paddedLocalEdge H (s t) (x t)).map (fun u => (mixedClass (s t),u)) := by
    intro s x t
    change s(mixedFrame _,mixedFrame _) = _
    rw [←Sym2.map_pair_eq,hrequest]
    exact paddedDecoder_frame H (s t) (x t)
  have hcaus : ∀ s (t : Fin T) x y,
      (∀ i : Fin t.val, x ⟨i.val,lt_trans i.isLt t.isLt⟩ =
        y ⟨i.val,lt_trans i.isLt t.isLt⟩) → (Q s x).d t.val = (Q s y).d t.val := by
    intro s t x y hxy
    apply congrArg (extendPosition mixedFrame)
    apply hcausal t
    intro i
    change paddedDecoder H (s _,x _) = paddedDecoder H (s _,y _)
    rw [hxy i]
  have hp := weighted_cliques_lower_probability (J := J) (U := U ⊕ W)
    (show 0 < Fintype.card U from Fintype.card_pos) hNL mixedClass
    (fun j => mixedClass_fiber j) f' (fun s t => paddedLocalEdge H (s t)) encode henc hL Q
    (fun s x => (R (words s x)).pushforward_initial mixedFrame (hi (words s x))) hreq hcaus
  let fail := univ \ integerDiscrepancyEvent R h
  have hsplit : splitFailure Q h = univ.filter (fun p => words p.1 p.2 ∈ fail) := by
    ext p
    simp only [splitFailure,fail,mem_filter,mem_univ,true_and,mem_sdiff]
    simp only [integerDiscrepancyEvent,mem_filter,mem_univ,true_and]
    simpa only [Q,T] using not_congr (pushforward_discrepancy_iff hh (R (words p.1 p.2)) mixedFrame)
  have hprob : uniformProb (splitFailure Q h) = uniformProb fail := by
    rw [hsplit]
    let D := fun x : Fin T → A × E => fun t => paddedDecoder H (x t)
    have hpre : (univ.filter fun p => words p.1 p.2 ∈ fail) =
        univ.filter (fun p => (pairWordEquiv T p |> D) ∈ fail) := rfl
    rw [hpre]
    calc
      _ = uniformProb (univ.filter fun x => D x ∈ fail) := by
        simpa only [mem_filter,mem_univ,true_and] using
          (uniformProb_equiv_preimage (pairWordEquiv T) (univ.filter fun x => D x ∈ fail))
      _ = uniformProb fail := by
        convert uniformProb_constant_fiber D
          (pow_pos (Nat.mul_pos (Fintype.card_pos (α := U)) (Fintype.card_pos (α := H.edgeSet))) T)
          (word_fiber_card (paddedDecoder H) (paddedDecoder_constant_fiber H hH)) fail using 1
        congr 1
        ext x
        simp only [mem_filter,mem_univ,true_and]
  rw [hprob] at hp
  simpa only [Fintype.card_prod,Nat.cast_mul] using hp

end Carpooling
