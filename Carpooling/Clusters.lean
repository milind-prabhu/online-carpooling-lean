import Carpooling.Basic
import Mathlib.Data.Nat.Log

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A partition represented by the block containing each vertex. -/
structure Clusters (V : Type*) [Fintype V] [DecidableEq V] where
  block : V → Finset V
  self_mem : ∀ k, k ∈ block k
  coherent : ∀ i j, j ∈ block i → block j = block i

lemma Clusters.ext {P Q : Clusters V} (h : P.block = Q.block) : P = Q := by
  cases P; cases Q; cases h; rfl

lemma Clusters.mem_iff {P : Clusters V} {i j : V} :
    j ∈ P.block i ↔ P.block j = P.block i := by
  constructor
  · exact P.coherent i j
  · intro h; rw [← h]; exact P.self_mem j

lemma Clusters.mem_symm {P : Clusters V} {i j : V} (h : j ∈ P.block i) :
    i ∈ P.block j := by rw [P.coherent i j h]; exact P.self_mem i

def Clusters.singletons : Clusters V where
  block := singleton
  self_mem := by simp
  coherent := by intro i j h; simpa using (mem_singleton.mp h)

lemma Clusters.outside {P : Clusters V} {u v i : V}
    (hi : i ∉ P.block u ∪ P.block v) {j : V} (hj : j ∈ P.block i) :
    j ∉ P.block u ∪ P.block v := by
  intro h
  rcases mem_union.mp h with h | h
  · have heq := (P.coherent u j h).symm.trans (P.coherent i j hj)
    exact hi (mem_union.mpr (Or.inl (by rw [heq]; exact P.self_mem i)))
  · have heq := (P.coherent v j h).symm.trans (P.coherent i j hj)
    exact hi (mem_union.mpr (Or.inr (by rw [heq]; exact P.self_mem i)))

noncomputable def Clusters.merge (P : Clusters V) (u v : V) : Clusters V where
  block := fun k => if k ∈ P.block u ∪ P.block v then P.block u ∪ P.block v else P.block k
  self_mem := by intro k; split_ifs with h; exact h; exact P.self_mem k
  coherent := by
    intro i j h
    by_cases hi : i ∈ P.block u ∪ P.block v
    · simp only [if_pos hi] at h
      simp [h, hi]
    · simp only [if_neg hi] at h
      have hj := P.outside hi h
      simp only [if_neg hi, if_neg hj]
      exact P.coherent i j h

lemma Clusters.merge_comm (P : Clusters V) (u v : V) : P.merge u v = P.merge v u := by
  apply Clusters.ext
  funext k
  simp only [Clusters.merge, union_comm]

lemma Clusters.subset_merge (P : Clusters V) (u v k : V) :
    P.block k ⊆ (P.merge u v).block k := by
  intro j hj
  by_cases hk : k ∈ P.block u ∪ P.block v
  · simp only [Clusters.merge, if_pos hk]
    rcases mem_union.mp hk with hk | hk
    · exact mem_union.mpr (Or.inl (by rwa [← P.coherent u k hk]))
    · exact mem_union.mpr (Or.inr (by rwa [← P.coherent v k hk]))
  · simpa only [Clusters.merge, if_neg hk] using hj

@[simp] lemma Clusters.merge_at_u (P : Clusters V) (u v : V) :
    (P.merge u v).block u = P.block u ∪ P.block v := by
  simp [Clusters.merge, P.self_mem]

@[simp] lemma Clusters.merge_at_v (P : Clusters V) (u v : V) :
    (P.merge u v).block v = P.block u ∪ P.block v := by
  simp [Clusters.merge, P.self_mem]

lemma Clusters.merge_same (P : Clusters V) {u v : V} (h : P.block u = P.block v) :
    P.merge u v = P := by
  apply Clusters.ext
  funext k
  change (if k ∈ P.block u ∪ P.block v then P.block u ∪ P.block v else P.block k) = P.block k
  rw [h, union_self]
  split_ifs with hk
  · exact (P.coherent v k hk).symm
  · rfl

lemma Clusters.disjoint {P : Clusters V} {u v : V} (h : P.block u ≠ P.block v) :
    Disjoint (P.block u) (P.block v) := by
  apply disjoint_left.mpr
  intro k hu hv
  exact h ((P.coherent u k hu).symm.trans (P.coherent v k hv))

noncomputable def Clusters.parts (P : Clusters V) : Finset (Finset V) := univ.image P.block

lemma Clusters.mem_parts (P : Clusters V) (k : V) : P.block k ∈ P.parts :=
  mem_image.mpr ⟨k, mem_univ k, rfl⟩

lemma Clusters.parts_merge (P : Clusters V) (u v : V) :
    (P.merge u v).parts = insert (P.block u ∪ P.block v)
      ((P.parts.erase (P.block u)).erase (P.block v)) := by
  ext S
  constructor
  · intro h
    obtain ⟨k, _, rfl⟩ := mem_image.mp h
    by_cases hk : k ∈ P.block u ∪ P.block v
    · exact mem_insert.mpr (Or.inl (by simp only [Clusters.merge, if_pos hk]))
    · apply mem_insert.mpr; right
      have ha : P.block k ≠ P.block u := by
        intro h; exact hk (mem_union.mpr (Or.inl (by rw [← h]; exact P.self_mem k)))
      have hb : P.block k ≠ P.block v := by
        intro h; exact hk (mem_union.mpr (Or.inr (by rw [← h]; exact P.self_mem k)))
      change (if k ∈ P.block u ∪ P.block v then P.block u ∪ P.block v else P.block k) ∈ _
      rw [if_neg hk]
      exact mem_erase.mpr ⟨hb, mem_erase.mpr ⟨ha, P.mem_parts k⟩⟩
  · intro h
    rcases mem_insert.mp h with h | h
    · subst S
      exact mem_image.mpr ⟨u, mem_univ u, P.merge_at_u u v⟩
    · obtain ⟨hb, ha, hS⟩ := by simpa [mem_erase] using h
      obtain ⟨k, _, hk⟩ := mem_image.mp hS
      have hku : k ∉ P.block u := by
        intro h; exact ha (hk ▸ (P.coherent u k h))
      have hkv : k ∉ P.block v := by
        intro h; exact hb (hk ▸ (P.coherent v k h))
      exact mem_image.mpr ⟨k, mem_univ k, by simpa [Clusters.merge, hku, hkv] using hk⟩

lemma Clusters.parts_merge_card (P : Clusters V) {u v : V}
    (h : P.block u ≠ P.block v) : (P.merge u v).parts.card + 1 = P.parts.card := by
  have hu := P.mem_parts u
  have hv := P.mem_parts v
  have hunion : P.block u ∪ P.block v ∉ P.parts := by
    intro hm
    obtain ⟨k, _, hk⟩ := mem_image.mp hm
    have hmu : u ∈ P.block k := by rw [hk]; simp [P.self_mem]
    have hmv : v ∈ P.block k := by rw [hk]; simp [P.self_mem]
    exact h ((P.coherent k u hmu).trans (P.coherent k v hmv).symm)
  rw [P.parts_merge]
  have hnot : P.block u ∪ P.block v ∉ (P.parts.erase (P.block u)).erase (P.block v) := by
    intro hh; exact hunion (mem_of_mem_erase (mem_of_mem_erase hh))
  rw [card_insert_of_notMem hnot, card_erase_of_mem (by simp [hv, Ne.symm h]), card_erase_of_mem hu]
  have htwo : 2 ≤ P.parts.card := by
    have hs : ({P.block u, P.block v} : Finset (Finset V)) ⊆ P.parts := by
      intro S hS; rcases mem_insert.mp hS with rfl | hh
      · exact hu
      · have hh := mem_singleton.mp hh
        subst S
        exact hv
    simpa [h] using card_le_card hs
  omega

end Carpooling
