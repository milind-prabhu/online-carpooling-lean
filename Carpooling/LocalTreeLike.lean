import Carpooling.WitnessCover

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def Clusters.partsOn (P : Clusters V) (C : Finset V) : Finset (Finset V) := C.image P.block

lemma Clusters.partsOn_merge (P : Clusters V) (C : Finset V) {u v : V} (hu : u ∈ C) (hv : v ∈ C) :
    (P.merge u v).partsOn C = insert (P.block u ∪ P.block v)
      (((P.partsOn C).erase (P.block u)).erase (P.block v)) := by
  ext S
  constructor
  · intro h
    obtain ⟨k, hkC, rfl⟩ := mem_image.mp h
    by_cases hk : k ∈ P.block u ∪ P.block v
    · exact mem_insert.mpr (Or.inl (by simp only [Clusters.merge, if_pos hk]))
    · apply mem_insert.mpr; right
      have ha : P.block k ≠ P.block u := by
        intro h; exact hk (mem_union.mpr (Or.inl (by rw [← h]; exact P.self_mem k)))
      have hb : P.block k ≠ P.block v := by
        intro h; exact hk (mem_union.mpr (Or.inr (by rw [← h]; exact P.self_mem k)))
      change (if k ∈ P.block u ∪ P.block v then P.block u ∪ P.block v else P.block k) ∈ _
      rw [if_neg hk]
      exact mem_erase.mpr ⟨hb, mem_erase.mpr ⟨ha, mem_image.mpr ⟨k,hkC,rfl⟩⟩⟩
  · intro h
    rcases mem_insert.mp h with h | h
    · subst S
      exact mem_image.mpr ⟨u, hu, P.merge_at_u u v⟩
    · obtain ⟨hb, ha, hS⟩ := by simpa [mem_erase] using h
      obtain ⟨k, hkC, hk⟩ := mem_image.mp hS
      have hku : k ∉ P.block u := by intro h; exact ha (hk.symm.trans (P.coherent u k h))
      have hkv : k ∉ P.block v := by intro h; exact hb (hk.symm.trans (P.coherent v k h))
      exact mem_image.mpr ⟨k, hkC, by simpa [Clusters.merge, hku, hkv] using hk⟩

lemma Clusters.partsOn_merge_card (P : Clusters V) (C : Finset V) {u v : V}
    (huC : u ∈ C) (hvC : v ∈ C) (h : P.block u ≠ P.block v) :
    ((P.merge u v).partsOn C).card + 1 = (P.partsOn C).card := by
  have hu : P.block u ∈ P.partsOn C := mem_image.mpr ⟨u,huC,rfl⟩
  have hv : P.block v ∈ P.partsOn C := mem_image.mpr ⟨v,hvC,rfl⟩
  have hunion : P.block u ∪ P.block v ∉ P.partsOn C := by
    intro hm
    obtain ⟨k, _, hk⟩ := mem_image.mp hm
    have hmu : u ∈ P.block k := by rw [hk]; simp [P.self_mem]
    have hmv : v ∈ P.block k := by rw [hk]; simp [P.self_mem]
    exact h ((P.coherent k u hmu).trans (P.coherent k v hmv).symm)
  rw [P.partsOn_merge C huC hvC]
  have hnot : P.block u ∪ P.block v ∉ ((P.partsOn C).erase (P.block u)).erase (P.block v) := by
    intro hh; exact hunion (mem_of_mem_erase (mem_of_mem_erase hh))
  rw [card_insert_of_notMem hnot, card_erase_of_mem (by simp [hv, Ne.symm h]), card_erase_of_mem hu]
  have htwo : 2 ≤ (P.partsOn C).card := by
    have hs : ({P.block u, P.block v} : Finset (Finset V)) ⊆ P.partsOn C := by
      intro S hS; rcases mem_insert.mp hS with rfl | hh
      · exact hu
      · have hh := mem_singleton.mp hh; subst S; exact hv
    simpa [h] using card_le_card hs
  omega

lemma Clusters.partsOn_merge_outside (P : Clusters V) (C : Finset V) {u v : V}
    (hC : ∀ k ∈ C, P.block k ⊆ C) (hu : u ∉ C) (hv : v ∉ C) :
    (P.merge u v).partsOn C = P.partsOn C := by
  apply image_congr
  intro k hk
  have hku : k ∉ P.block u := fun hh => hu (hC k hk (P.mem_symm hh))
  have hkv : k ∉ P.block v := fun hh => hv (hC k hk (P.mem_symm hh))
  simp [Clusters.merge, hku, hkv]

def Run.LocalInternal {T : ℕ} (R : Run V T) (C : Finset V) (t : ℕ) : Prop :=
  ∃ h : t < T, (R.clusters t).block (R.step t h).u = (R.clusters t).block (R.step t h).v ∧
    (R.step t h).u ∈ C

noncomputable def Run.localSurplus {T : ℕ} (R : Run V T) (C : Finset V) (t : ℕ) : ℕ :=
  ((range t).filter (R.LocalInternal C)).card

lemma Run.localSurplus_succ {T : ℕ} (R : Run V T) (C : Finset V) (t : ℕ) :
    R.localSurplus C (t+1) = R.localSurplus C t + if R.LocalInternal C t then 1 else 0 := by
  simp only [Run.localSurplus, range_add_one, filter_insert]
  split_ifs <;> simp_all

lemma internalCount_succ {T : ℕ} (R : Run V T) (C : Finset V) {t : ℕ} (ht : t < T) :
    internalCount R C (t+1) = internalCount R C t + if (R.step t ht).u ∈ C then 1 else 0 := by
  simp only [internalCount, range_add_one, filter_insert]
  by_cases h : (R.step t ht).u ∈ C <;> simp [ht,h]

lemma Run.terminal_block_subset {T : ℕ} (R : Run V T) (k : V) {t : ℕ} (ht : t ≤ T)
    {j : V} (hj : j ∈ (R.clusters T).block k) :
    (R.clusters t).block j ⊆ (R.clusters T).block k := by
  rw [← (R.clusters T).coherent k j hj]
  exact R.clusters_subset ht j

/-- Local form of the Euler/surplus identity, for a single final component. -/
theorem Run.local_surplus_identity {T : ℕ} (R : Run V T) (k : V) :
    R.localSurplus ((R.clusters T).block k) T =
      internalCount R ((R.clusters T).block k) T - (((R.clusters T).block k).card - 1) := by
  let C := (R.clusters T).block k
  have hC : R.Closed C := R.terminal_closed k
  have hinv : ∀ t ≤ T, R.localSurplus C t + C.card =
      internalCount R C t + ((R.clusters t).partsOn C).card := by
    intro t
    induction t with
    | zero =>
      intro ht
      simp only [Run.localSurplus, internalCount, range_zero, filter_empty, card_empty, zero_add, Run.clusters]
      simpa only [Clusters.partsOn, Clusters.singletons] using
        (card_image_of_injective C (Finset.singleton_injective)).symm
    | succ t ih =>
      intro ht
      have ih := ih (by omega)
      have htT : t < T := by omega
      let e := R.step t htT
      let P := R.clusters t
      change R.localSurplus C t + C.card = internalCount R C t + (P.partsOn C).card at ih
      have hnext : R.clusters (t+1) = P.merge e.u e.v := by simp [Run.clusters,htT,P,e]
      rw [R.localSurplus_succ, internalCount_succ R C htT, hnext]
      by_cases hu : e.u ∈ C
      · have hv := (hC t htT).mp hu
        by_cases hint : P.block e.u = P.block e.v
        · have hlocal : R.LocalInternal C t := ⟨htT,hint,hu⟩
          rw [if_pos hlocal, if_pos hu, P.merge_same hint]
          omega
        · have hlocal : ¬R.LocalInternal C t := by rintro ⟨h,hh,_⟩; exact hint hh
          rw [if_neg hlocal, if_pos hu]
          have hp := P.partsOn_merge_card C hu hv hint
          rw [← hp] at ih
          dsimp [e,P] at ih ⊢
          omega
      · have hv : e.v ∉ C := fun hv => hu ((hC t htT).mpr hv)
        have hlocal : ¬R.LocalInternal C t := by rintro ⟨h,_,hh⟩; exact hu hh
        rw [if_neg hlocal, if_neg hu, P.partsOn_merge_outside C
          (fun j hj => R.terminal_block_subset k (by omega) hj) hu hv]
        exact ih
  have hfinal : (R.clusters T).partsOn C = {C} := by
    ext S
    constructor
    · intro hS
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hS
      exact mem_singleton.mpr ((R.clusters T).coherent k j hj)
    · intro hS
      rw [mem_singleton] at hS
      subst S
      exact mem_image.mpr ⟨k,(R.clusters T).self_mem k,rfl⟩
  have h := hinv T (le_refl T)
  rw [hfinal, card_singleton] at h
  have hpos : 1 ≤ C.card := card_pos.mpr ⟨k,(R.clusters T).self_mem k⟩
  change R.localSurplus C T = internalCount R C T - (C.card-1)
  omega

lemma Run.clusters_mask {T : ℕ} (R : Run V T) (C : Finset V) (hC : R.Closed C) (t : ℕ) :
    (R.mask C hC).clusters t = R.clusters t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Run.clusters]
    split_ifs with h
    · rw [ih]; rfl
    · exact ih

lemma Run.internal_mask {T : ℕ} (R : Run V T) (C : Finset V) (hC : R.Closed C) (t : ℕ) :
    (R.mask C hC).IsInternal t ↔ R.IsInternal t := by
  unfold Run.IsInternal
  rw [R.clusters_mask]
  rfl

noncomputable def Run.locallyShifted {T : ℕ} (R : Run V T) (C : Finset V)
    (hC : R.Closed C) : DRun V T where
  d := (R.mask C hC).shift
  charge := fun t => decide (R.LocalInternal C t)
  step := fun t ht => by
    let M := R.mask C hC
    by_cases hu : (R.step t ht).u ∈ C
    · have heq : M.IsInternal t ↔ R.LocalInternal C t := by
        rw [R.internal_mask C hC t]
        unfold Run.IsInternal Run.LocalInternal
        constructor
        · rintro ⟨h,hh⟩; exact ⟨h,hh,hu⟩
        · rintro ⟨h,hh,_⟩; exact ⟨h,hh⟩
      simpa only [decide_eq_decide.mpr heq] using M.shift_step ht
    · apply DStep.drop
      intro k
      have hv : (R.step t ht).v ∉ C := fun hv => hu ((hC t ht).mpr hv)
      have hw : (M.step t ht).weight = 0 := by simp [M, Run.mask, hu]
      have hd : M.d (t+1) k = M.d t k := by
        rw [(M.step t ht).update, hw]
        simp
      have hr : (M.rank t k : ℝ) ≤ M.rank (t+1) k := by exact_mod_cast M.rank_mono t k
      dsimp [Run.shift]
      rw [hd]
      linarith

lemma Run.locallyShifted_count {T : ℕ} (R : Run V T) (C : Finset V) (hC : R.Closed C) (t : ℕ) :
    (R.locallyShifted C hC).count t = R.localSurplus C t := by
  simp [Run.locallyShifted, DRun.count, Run.localSurplus]

theorem local_positive_tree_bound {T : ℕ} (R : Run V T) (hi : ∀ k, R.d 0 k = 0)
    (C : Finset V) (hC : R.Closed C) {k : V} (hk : k ∈ C) :
    R.d T k ≤ 4*(R.localSurplus C T : ℝ)^((1:ℝ)/3) + 2*(R.rank T k : ℝ) := by
  have hh := (R.locallyShifted C hC).position_bound
    (by intro k; simp [Run.locallyShifted, Run.shift, Run.rank, Run.clusters, Clusters.singletons, Run.mask,hi]) k
  rw [R.locallyShifted_count] at hh
  have hr : (R.mask C hC).rank T k = R.rank T k := by simp [Run.rank,R.clusters_mask]
  change (R.mask C hC).d T k - 2*((R.mask C hC).rank T k : ℝ) ≤ _ at hh
  rw [hr] at hh
  have hd : (R.mask C hC).d T k = R.d T k := by simp [Run.mask,hk]
  rw [hd] at hh
  linarith

lemma Run.closed_neg {T : ℕ} (R : Run V T) (C : Finset V) (hC : R.Closed C) : R.neg.Closed C := by
  intro t ht
  exact (hC t ht).symm

lemma Run.localSurplus_neg {T : ℕ} (R : Run V T) (C : Finset V) (hC : R.Closed C) (t : ℕ) :
    R.neg.localSurplus C t = R.localSurplus C t := by
  unfold Run.localSurplus
  congr 1
  apply filter_congr
  intro s hs
  unfold Run.LocalInternal
  rw [R.clusters_neg]
  apply exists_congr
  intro h
  change ((R.clusters s).block (R.step s h).v = (R.clusters s).block (R.step s h).u ∧
      (R.step s h).v ∈ C) ↔ _
  constructor
  · rintro ⟨he,hm⟩; exact ⟨he.symm,(hC s h).mpr hm⟩
  · rintro ⟨he,hm⟩; exact ⟨he.symm,(hC s h).mp hm⟩

/-- The refined deterministic estimate localized to a single final component.
Here p is exactly its number of edges beyond a spanning tree. -/
theorem local_tree_like_bound {T : ℕ} (R : Run V T) (hi : ∀ k, R.d 0 k = 0) (k : V) :
    |R.d T k| ≤
      4*((internalCount R ((R.clusters T).block k) T - (((R.clusters T).block k).card-1) : ℕ) : ℝ)^((1:ℝ)/3) +
      2*(Nat.log 2 ((R.clusters T).block k).card : ℝ) := by
  let C := (R.clusters T).block k
  have hC : R.Closed C := R.terminal_closed k
  have hk : k ∈ C := (R.clusters T).self_mem k
  have hp := local_positive_tree_bound R hi C hC hk
  have hn := local_positive_tree_bound R.neg (by intro k; simp [Run.neg,hi]) C (R.closed_neg C hC) hk
  rw [R.localSurplus_neg C hC] at hn
  have hr : R.neg.rank T k = R.rank T k := by simp [Run.rank,R.clusters_neg]
  rw [hr] at hn
  change -R.d T k ≤ _ at hn
  rw [R.local_surplus_identity k] at hp hn
  apply abs_le.mpr
  constructor <;> dsimp [Run.rank,C] at * <;> linarith

end Carpooling
