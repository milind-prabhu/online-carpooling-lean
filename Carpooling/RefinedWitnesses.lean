import Carpooling.StochasticBasic
import Carpooling.LocalTreeLike

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Witness
def nodeLabels : Tree V → List V
  | .nil => []
  | .node v L R => v :: (nodeLabels L ++ nodeLabels R)

def labels (root : V) (F : Tree V) : List V := root :: nodeLabels F

@[simp] lemma labels_length (root : V) (F : Tree V) : (labels root F).length = F.numNodes + 1 := by
  have h : (nodeLabels F).length = F.numNodes := by
    induction F with
    | nil => rfl
    | node v L R ihL ihR => simp [nodeLabels,Tree.numNodes,ihL,ihR]
  simp [labels,h]

lemma vertices_labels (root : V) (F : Tree V) : vertices root F = (labels root F).toFinset := by
  induction F generalizing root with
  | nil => simp [vertices,labels,nodeLabels]
  | node v L R ihL ihR =>
    rw [vertices,ihL,ihR]
    ext k
    simp [labels,nodeLabels,or_assoc,or_comm,or_left_comm]

noncomputable def labelAt (m : ℕ) (root : V) (F : Tree V) (i : Fin m) : V :=
  if h : i.val < (labels root F).length then (labels root F)[i.val] else root

lemma exists_labelAt {m : ℕ} {root v : V} {F : Tree V}
    (hm : F.numNodes + 1 = m) (hv : v ∈ vertices root F) :
    ∃ i : Fin m, labelAt m root F i = v := by
  rw [vertices_labels, List.mem_toFinset] at hv
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hv
  have hlen : (labels root F).length = m := (labels_length root F).trans hm
  let i : Fin m := ⟨j.val, by rw [← hlen]; exact j.isLt⟩
  refine ⟨i, ?_⟩
  change (if h : j.val < (labels root F).length then (labels root F)[j.val] else root) = v
  rw [dif_pos j.isLt]
  exact hj

noncomputable def extraBag {m p : ℕ} (root : V) (F : Tree V) (code : Fin p → Fin m × Fin m) : Multiset (Sym2 V) :=
  univ.val.map fun j => s(labelAt m root F (code j).1, labelAt m root F (code j).2)

@[simp] lemma extraBag_card {m p : ℕ} (root : V) (F : Tree V) (code : Fin p → Fin m × Fin m) :
    (extraBag root F code).card = p := by simp [extraBag]

lemma edges_support {root : V} {F : Tree V} {e : Sym2 V} (he : e ∈ edges root F)
    {v : V} (hv : v ∈ e) : v ∈ vertices root F := by
  induction F generalizing root e v with
  | nil => simp [edges] at he
  | node a L R ihL ihR =>
    simp only [edges,Multiset.mem_add,Multiset.mem_singleton] at he
    rcases he with (he | he) | he
    · subst e
      rcases Sym2.mem_iff.mp hv with hv | hv
      · rw [hv]; exact mem_union_right _ (root_mem root R)
      · rw [hv]; exact mem_union_left _ (root_mem a L)
    · exact mem_union_left _ (ihL he hv)
    · exact mem_union_right _ (ihR he hv)

/-- Encode p surplus edges using two indices among the m core-tree vertices. -/
theorem encode_extras {m p : ℕ} {root : V} {F : Tree V} (hm : F.numNodes + 1 = m)
    (Q : Multiset (Sym2 V)) (hp : Q.card = p)
    (hs : ∀ e ∈ Q, ∀ v ∈ e, v ∈ vertices root F) :
    ∃ code : Fin p → Fin m × Fin m, extraBag root F code = Q := by
  have hlen : Q.toList.length = p := (Multiset.length_toList Q).trans hp
  clear hp
  subst p
  have hmem : ∀ j : Fin Q.toList.length, bagEnumeration Q j ∈ Q := by
    intro j
    simpa only [bagEnumeration, Multiset.mem_toList] using (List.get_mem Q.toList j)
  have hex : ∀ j : Fin Q.toList.length, ∃ ij : Fin m × Fin m,
      s(labelAt m root F ij.1,labelAt m root F ij.2) = bagEnumeration Q j := by
    intro j
    let e := bagEnumeration Q j
    obtain ⟨a,ha⟩ := exists_labelAt hm (hs e (hmem j) e.out.1 (Sym2.out_fst_mem e))
    obtain ⟨b,hb⟩ := exists_labelAt hm (hs e (hmem j) e.out.2 (Sym2.out_snd_mem e))
    refine ⟨(a,b), ?_⟩
    rw [ha,hb]
    exact e.out_eq
  choose code hcode using hex
  refine ⟨code, ?_⟩
  unfold extraBag
  have hmap : (fun j => s(labelAt m root F (code j).1,labelAt m root F (code j).2)) = bagEnumeration Q := funext hcode
  rw [hmap,bagEnumeration_bag]

noncomputable def refinedPattern {m p : ℕ} (w : V × Tree V) (code : Fin p → Fin m × Fin m) : Multiset (Sym2 V) :=
  edges w.1 w.2 + extraBag w.1 w.2 code

lemma refinedPattern_card {N : V → Finset V} {m p : ℕ} {w : V × Tree V}
    (hw : w ∈ families N (m-1)) (code : Fin p → Fin m × Fin m) :
    (refinedPattern w code).card = m-1+p := by
  simp only [refinedPattern,Multiset.card_add,edges_card,extraBag_card,families_nodes hw]

lemma code_card (m p : ℕ) : Fintype.card (Fin p → Fin m × Fin m) = m^(2*p) := by
  simp only [Fintype.card_fun,Fintype.card_prod,Fintype.card_fin]
  rw [← pow_two,← pow_mul]

end Witness

section Probability
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def refinedWitnessEvent (N : V → Finset V) (g : E → Sym2 V) (T m p : ℕ) :
    Finset (Fin T → E) :=
  ((Witness.families N (m-1)) ×ˢ (univ : Finset (Fin p → Fin m × Fin m))).biUnion
    fun w => bagOccurrenceEvent g (Witness.refinedPattern w.1 w.2)

/-- The refined witness enumeration and occurrence estimate, before graph-specific simplification. -/
theorem refined_witness_probability (N : V → Finset V) {Δ : ℕ} (hΔ : ∀ v, (N v).card ≤ Δ)
    (g : E → Sym2 V) (hg : Function.Injective g) (T m p : ℕ) :
    uniformProb (refinedWitnessEvent N g T m p) ≤
      ((4:ℝ)^(m-1) * Fintype.card V * (Δ:ℝ)^(m-1) * (m:ℝ)^(2*p)) *
      ((T:ℝ)/Fintype.card E)^(m-1+p) := by
  let S := (Witness.families N (m-1)) ×ˢ (univ : Finset (Fin p → Fin m × Fin m))
  have hu := uniformProb_biUnion_le S (fun w => bagOccurrenceEvent (T := T) g (Witness.refinedPattern w.1 w.2))
  have hs : (∑ w ∈ S, uniformProb (bagOccurrenceEvent (T := T) g (Witness.refinedPattern w.1 w.2))) ≤
      (S.card : ℝ) * ((T:ℝ)/Fintype.card E)^(m-1+p) := by
    calc
      _ ≤ ∑ _w ∈ S, ((T:ℝ)/Fintype.card E)^(m-1+p) := by
        apply sum_le_sum
        intro w hw
        have hf := (mem_product.mp hw).1
        simpa only [Witness.refinedPattern_card hf] using bag_occurrence_probability (T := T) g hg (Witness.refinedPattern w.1 w.2)
      _ = _ := by simp
  have hcN : S.card ≤ 4^(m-1) * Fintype.card V * Δ^(m-1) * m^(2*p) := by
    rw [card_product,card_univ,Witness.code_card]
    exact Nat.mul_le_mul_right _ (Witness.families_card_bound N hΔ (m-1))
  have hc : (S.card : ℝ) ≤ (4:ℝ)^(m-1) * Fintype.card V * (Δ:ℝ)^(m-1) * (m:ℝ)^(2*p) := by exact_mod_cast hcN
  exact (hu.trans hs).trans (mul_le_mul_of_nonneg_right hc (by positivity))

end Probability
end Carpooling
