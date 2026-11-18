import Carpooling.Clusters
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Sym.Sym2

namespace Carpooling.Witness
open Finset
open scoped Classical
variable {V : Type*} [DecidableEq V]

def edges (root : V) : Tree V → Multiset (Sym2 V)
  | .nil => 0
  | .node v L R => {s(root,v)} + edges v L + edges root R

def vertices (root : V) : Tree V → Finset V
  | .nil => {root}
  | .node v L R => vertices v L ∪ vertices root R

def Valid (Adj : V → V → Prop) (root : V) : Tree V → Prop
  | .nil => True
  | .node v L R => Adj root v ∧ Valid Adj v L ∧ Valid Adj root R

@[simp] lemma root_mem (root : V) (F : Tree V) : root ∈ vertices root F := by
  induction F generalizing root with
  | nil => simp [vertices]
  | node v L R ihL ihR => exact mem_union_right _ (ihR root)

@[simp] lemma edges_card (root : V) (F : Tree V) : (edges root F).card = F.numNodes := by
  induction F generalizing root with
  | nil => simp [edges, Tree.numNodes]
  | node v L R ihL ihR => simp [edges, Tree.numNodes, ihL, ihR]

def append : Tree V → Tree V → Tree V
  | .nil, G => G
  | .node v L R, G => .node v L (append R G)

@[simp] lemma edges_append (root : V) (F G : Tree V) :
    edges root (append F G) = edges root F + edges root G := by
  induction F generalizing root with
  | nil => simp [append, edges]
  | node v L R ihL ihR => simp [append, edges, ihR, add_assoc]

@[simp] lemma vertices_append (root : V) (F G : Tree V) :
    vertices root (append F G) = vertices root F ∪ vertices root G := by
  induction F generalizing root with
  | nil => simp [append, vertices, insert_eq_of_mem (root_mem root G)]
  | node v L R ihL ihR => simp [append, vertices, ihR, union_assoc]

lemma valid_append {Adj : V → V → Prop} {root : V} {F G : Tree V}
    (hF : Valid Adj root F) (hG : Valid Adj root G) : Valid Adj root (append F G) := by
  induction F generalizing root with
  | nil => exact hG
  | node v L R ihL ihR => exact ⟨hF.1, hF.2.1, ihR hF.2.2 hG⟩

/-- Graft an arbitrary forest at any occurrence of its root label. -/
theorem graft {Adj : V → V → Prop} {root a : V} {F H : Tree V}
    (ha : a ∈ vertices root F) (hF : Valid Adj root F) (hH : Valid Adj a H) :
    ∃ G, Valid Adj root G ∧ edges root G = edges root F + edges a H ∧
      vertices root G = vertices root F ∪ vertices a H := by
  induction F generalizing root with
  | nil =>
    have har : a = root := mem_singleton.mp ha
    subst a
    exact ⟨H, hH, by simp [edges], by simp [vertices, insert_eq_of_mem (root_mem root H)]⟩
  | node v L R ihL ihR =>
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨G, hG, he, hv⟩ := ihL ha hF.2.1
      refine ⟨.node v G R, ⟨hF.1, hG, hF.2.2⟩, ?_, ?_⟩
      · simp only [edges, he]; ac_rfl
      · simp only [vertices, hv]; ac_rfl
    · obtain ⟨G, hG, he, hv⟩ := ihR ha hF.2.2
      refine ⟨.node v L G, ⟨hF.1, hF.2.1, hG⟩, ?_, ?_⟩
      · simp only [edges, he]; ac_rfl
      · simp only [vertices, hv]; ac_rfl

/-- Rerooting preserves the entire edge multiset, including repetitions. -/
theorem reroot {Adj : V → V → Prop}
    (hsymm : ∀ {u v}, Adj u v → Adj v u) {root a : V} {F : Tree V}
    (ha : a ∈ vertices root F) (hF : Valid Adj root F) :
    ∃ G, Valid Adj a G ∧ edges a G = edges root F ∧ vertices a G = vertices root F := by
  induction F generalizing root with
  | nil =>
    have : a = root := mem_singleton.mp ha
    subst a
    exact ⟨.nil, trivial, rfl, rfl⟩
  | node v L R ihL ihR =>
    rcases mem_union.mp ha with ha | ha
    · obtain ⟨G, hG, he, hv⟩ := ihL ha hF.2.1
      have hvmem : v ∈ vertices a G := by rw [hv]; exact root_mem v L
      have hbranch : Valid Adj v (.node root R .nil) := ⟨hsymm hF.1, hF.2.2, trivial⟩
      obtain ⟨K, hK, hKe, hKv⟩ := graft hvmem hG hbranch
      refine ⟨K, hK, ?_, ?_⟩
      · rw [hKe, he]
        simp only [edges, add_zero]
        rw [Sym2.eq_swap]
        ac_rfl
      · rw [hKv, hv]
        simp only [vertices]
        have : v ∈ vertices v L := root_mem v L
        ext k
        simp only [mem_union, mem_singleton]
        constructor
        · rintro (h | h | rfl)
          · exact Or.inl h
          · exact Or.inr h
          · exact Or.inl this
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
    · obtain ⟨G, hG, he, hv⟩ := ihR ha hF.2.2
      have hrmem : root ∈ vertices a G := by rw [hv]; exact root_mem root R
      have hbranch : Valid Adj root (.node v L .nil) := ⟨hF.1, hF.2.1, trivial⟩
      obtain ⟨K, hK, hKe, hKv⟩ := graft hrmem hG hbranch
      refine ⟨K, hK, ?_, ?_⟩
      · rw [hKe, he]
        simp only [edges, add_zero]
        ac_rfl
      · rw [hKv, hv]
        simp only [vertices]
        have : root ∈ vertices root R := root_mem root R
        ext k
        simp only [mem_union, mem_singleton]
        constructor
        · rintro (h | h | rfl)
          · exact Or.inr h
          · exact Or.inl h
          · exact Or.inr this
        · rintro (h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h

/-- Keep only edges that introduce a new vertex label. This constructs a spanning
tree inside a witness forest without assuming a separate graph traversal theorem. -/
theorem extend_spanning {Adj : V → V → Prop} {root base : V} {F H : Tree V}
    (hroot : root ∈ vertices base H) (hF : Valid Adj root F) (hH : Valid Adj base H) :
    ∃ G, Valid Adj base G ∧ edges base G ≤ edges base H + edges root F ∧
      vertices base G = vertices base H ∪ vertices root F ∧
      G.numNodes + (vertices base H).card = H.numNodes + (vertices base G).card := by
  induction F generalizing root H with
  | nil =>
    refine ⟨H, hH, by simp [edges], ?_, rfl⟩
    simp only [vertices]
    exact (union_eq_left.mpr (singleton_subset_iff.mpr hroot)).symm
  | node v L R ihL ihR =>
    have first : ∃ H1, Valid Adj base H1 ∧ edges base H1 ≤ edges base H + {s(root,v)} ∧
        vertices base H1 = insert v (vertices base H) ∧
        H1.numNodes + (vertices base H).card = H.numNodes + (vertices base H1).card := by
      by_cases hv : v ∈ vertices base H
      · refine ⟨H,hH,le_add_of_nonneg_right (by exact zero_le _),?_,rfl⟩
        exact (insert_eq_of_mem hv).symm
      · have hleaf : Valid Adj root (.node v .nil .nil) := ⟨hF.1,trivial,trivial⟩
        obtain ⟨H1,hH1,he,hv1⟩ := graft hroot hH hleaf
        have hverts : vertices base H1 = insert v (vertices base H) := by
          rw [hv1]
          simp only [vertices]
          ext k
          simp only [mem_union,mem_insert,mem_singleton]
          constructor
          · rintro (h | h | h)
            · exact Or.inr h
            · exact Or.inl h
            · subst k; exact Or.inr hroot
          · rintro (h | h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
        have hnum : H1.numNodes = H.numNodes+1 := by
          have hh := congrArg Multiset.card he
          simpa [edges] using hh
        refine ⟨H1,hH1,?_,hverts,?_⟩
        · rw [he]; simp [edges]
        · rw [hverts,card_insert_of_notMem hv,hnum]; omega
    obtain ⟨H1,hH1,he1,hv1,hn1⟩ := first
    have hv : v ∈ vertices base H1 := by rw [hv1]; exact mem_insert_self _ _
    obtain ⟨H2,hH2,he2,hv2,hn2⟩ := ihL hv hF.2.1 hH1
    have hr : root ∈ vertices base H2 := by
      rw [hv2,hv1]
      exact mem_union_left _ (mem_insert_of_mem hroot)
    obtain ⟨G,hG,heG,hvG,hnG⟩ := ihR hr hF.2.2 hH2
    refine ⟨G,hG,?_,?_,?_⟩
    · calc
        edges base G ≤ edges base H2 + edges root R := heG
        _ ≤ (edges base H1 + edges v L) + edges root R := add_le_add_right he2 _
        _ ≤ ((edges base H + {s(root,v)}) + edges v L) + edges root R :=
          add_le_add_right (add_le_add_right he1 _) _
        _ = edges base H + edges root (.node v L R) := by simp only [edges]; ac_rfl
    · rw [hvG,hv2,hv1]
      simp only [vertices]
      have hvL := root_mem v L
      ext k
      simp only [mem_union,mem_insert]
      constructor
      · rintro (((h | h) | h) | h)
        · subst k; exact Or.inr (Or.inl hvL)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    · omega

theorem spanning {Adj : V → V → Prop} {root : V} {F : Tree V} (hF : Valid Adj root F) :
    ∃ G, Valid Adj root G ∧ edges root G ≤ edges root F ∧
      vertices root G = vertices root F ∧ G.numNodes + 1 = (vertices root F).card := by
  obtain ⟨G,hG,he,hv,hn⟩ := extend_spanning (root_mem root .nil) hF (show Valid Adj root .nil from trivial)
  have hvG : vertices root G = vertices root F := by
    simpa [vertices,insert_eq_of_mem (root_mem root F)] using hv
  refine ⟨G,hG,by simpa [edges] using he,hvG,?_⟩
  simpa [vertices,Tree.numNodes,hvG] using hn

end Carpooling.Witness
