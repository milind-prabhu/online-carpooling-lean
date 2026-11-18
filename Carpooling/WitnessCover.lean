import Carpooling.TreeLike
import Carpooling.WitnessCounting
import Carpooling.Components

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def Run.edgeBag {T : ℕ} (R : Run V T) : ℕ → Multiset (Sym2 V)
  | 0 => 0
  | t+1 => if h : t < T then R.edgeBag t + {s((R.step t h).u,(R.step t h).v)} else R.edgeBag t

lemma Run.edgeBag_mono {T : ℕ} (R : Run V T) {s t : ℕ} (hst : s ≤ t) : R.edgeBag s ≤ R.edgeBag t := by
  induction t with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact le_rfl
  | succ t ih =>
    by_cases heq : s = t+1
    · subst s; exact le_rfl
    · have hh := ih (by omega)
      rw [Run.edgeBag]
      split_ifs
      · exact hh.trans (Multiset.le_add_right _ _)
      · exact hh

lemma Run.edgeBag_prefix {T : ℕ} (R : Run V T) {t : ℕ} (ht : t ≤ T) {s : ℕ} (hs : s ≤ t) :
    (R.prefix t ht).edgeBag s = R.edgeBag s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have hst : s < t := by omega
    have hsT : s < T := by omega
    simp only [Run.edgeBag, dif_pos hst, dif_pos hsT]
    rw [ih (by omega)]
    rfl

def inBlock (C : Finset V) (e : Sym2 V) : Prop := e.out.1 ∈ C

lemma inBlock_pair {C : Finset V} {u v : V} (h : u ∈ C ↔ v ∈ C) :
    inBlock C s(u,v) ↔ u ∈ C := by
  have hm := Sym2.out_fst_mem s(u,v)
  rcases Sym2.mem_iff.mp hm with hm | hm
  · simp [inBlock, hm]
  · simpa [inBlock, hm] using h.symm

noncomputable def selected (C : Finset V) (B : Multiset (Sym2 V)) : Multiset (Sym2 V) :=
  B.filter (inBlock C)

lemma selected_union {A B : Finset V} (h : Disjoint A B) (S : Multiset (Sym2 V)) :
    selected (A ∪ B) S = selected A S + selected B S := by
  induction S using Multiset.induction_on with
  | empty => simp [selected]
  | cons e S ih =>
    simp only [selected, Multiset.filter_cons, inBlock, mem_union] at *
    by_cases ha : e.out.1 ∈ A <;> by_cases hb : e.out.1 ∈ B
    · exact False.elim (Finset.disjoint_left.mp h ha hb)
    · simp [ha, hb, ih]
    · simp [ha, hb, ih, Multiset.cons_add, Multiset.add_cons]
    · simp [ha, hb, ih]

/-- Every component's full edge multiset admits a graph-respecting witness forest.
Repeated requests are retained with their multiplicities. -/
theorem Run.component_witness {T : ℕ} (R : Run V T) (Adj : V → V → Prop)
    (hsymm : ∀ {u v}, Adj u v → Adj v u)
    (hAdj : ∀ s (hs : s < T), Adj (R.step s hs).u (R.step s hs).v)
    {t : ℕ} (ht : t ≤ T) (k : V) :
    ∃ F : Tree V, Witness.Valid Adj k F ∧
      Witness.edges k F = selected ((R.clusters t).block k) (R.edgeBag t) ∧
      Witness.vertices k F = (R.clusters t).block k := by
  induction t generalizing k with
  | zero => exact ⟨.nil, trivial, rfl, rfl⟩
  | succ t ih =>
    have htT : t < T := by omega
    let P := R.clusters t
    let e := R.step t htT
    let U := P.block e.u ∪ P.block e.v
    have hnext : R.clusters (t+1) = P.merge e.u e.v := by simp [Run.clusters, htT, P, e]
    have hbag : R.edgeBag (t+1) = R.edgeBag t + {s(e.u,e.v)} := by simp [Run.edgeBag, htT, e]
    by_cases hk : k ∈ U
    · have hb : (R.clusters (t+1)).block k = U := by
        rw [hnext]
        change (if k ∈ U then U else P.block k) = U
        exact if_pos hk
      obtain ⟨F, hF, heF, hvF⟩ := ih (by omega) e.u
      by_cases hint : P.block e.u = P.block e.v
      · have hU : U = P.block e.u := by simp [U, ← hint]
        have hv : e.v ∈ P.block e.u := by rw [hint]; exact P.self_mem _
        let G := Tree.node e.v Tree.nil F
        have hG : Witness.Valid Adj e.u G := ⟨hAdj t htT, trivial, hF⟩
        have hvG : Witness.vertices e.u G = U := by
          dsimp [G, Witness.vertices]
          rw [hvF, hU]
          exact union_eq_right.mpr (singleton_subset_iff.mpr hv)
        have hkG : k ∈ Witness.vertices e.u G := by rw [hvG]; exact hk
        obtain ⟨H, hH, heH, hvH⟩ := Witness.reroot hsymm hkG hG
        refine ⟨H, hH, ?_, hvH.trans (hvG.trans hb.symm)⟩
        rw [heH, hb, hbag]
        have hnew : inBlock U s(e.u,e.v) :=
          (inBlock_pair (by simp [U, P.self_mem])).mpr (by simp [U, P.self_mem])
        simp only [selected, Multiset.filter_add, Multiset.filter_singleton, if_pos hnew]
        dsimp [G, Witness.edges]
        rw [heF, hU]
        change {s(e.u,e.v)} + selected (P.block e.u) (R.edgeBag t) =
          selected (P.block e.u) (R.edgeBag t) + {s(e.u,e.v)}
        ac_rfl
      · obtain ⟨G, hG, heG, hvG⟩ := ih (by omega) e.v
        let K := Tree.node e.v G F
        have hK : Witness.Valid Adj e.u K := ⟨hAdj t htT, hG, hF⟩
        have hvK : Witness.vertices e.u K = U := by
          dsimp [K, Witness.vertices]
          rw [hvF, hvG]
          exact union_comm _ _
        have hkK : k ∈ Witness.vertices e.u K := by rw [hvK]; exact hk
        obtain ⟨H, hH, heH, hvH⟩ := Witness.reroot hsymm hkK hK
        refine ⟨H, hH, ?_, hvH.trans (hvK.trans hb.symm)⟩
        rw [heH, hb, hbag]
        have hnew : inBlock U s(e.u,e.v) :=
          (inBlock_pair (by simp [U, P.self_mem])).mpr (by simp [U, P.self_mem])
        change Witness.edges e.u K = _
        simp only [selected, Multiset.filter_add, Multiset.filter_singleton, if_pos hnew]
        change Witness.edges e.u K = selected U (R.edgeBag t) + {s(e.u,e.v)}
        rw [selected_union (P.disjoint hint)]
        dsimp [K, Witness.edges]
        rw [heF, heG]
        change ({s(e.u,e.v)} + selected (P.block e.v) (R.edgeBag t)) +
          selected (P.block e.u) (R.edgeBag t) =
          (selected (P.block e.u) (R.edgeBag t) + selected (P.block e.v) (R.edgeBag t)) + {s(e.u,e.v)}
        ac_rfl
    · obtain ⟨F, hF, heF, hvF⟩ := ih (by omega) k
      have hb : (R.clusters (t+1)).block k = P.block k := by
        rw [hnext]
        change (if k ∈ U then U else P.block k) = P.block k
        exact if_neg hk
      refine ⟨F, hF, ?_, hvF.trans hb.symm⟩
      rw [hb, hbag]
      have hu : e.u ∉ P.block k := by
        intro hh
        exact hk (mem_union.mpr (Or.inl (P.mem_symm hh)))
      have hv : e.v ∉ P.block k := by
        intro hh
        exact hk (mem_union.mpr (Or.inr (P.mem_symm hh)))
      have hnew : ¬inBlock (P.block k) s(e.u,e.v) := by
        rw [inBlock_pair (by simp [hu,hv])]; exact hu
      simpa [selected, Multiset.filter_add, Multiset.filter_singleton, hnew] using heF

lemma Run.clusters_subset {T : ℕ} (R : Run V T) {s t : ℕ} (h : s ≤ t) (k : V) :
    (R.clusters s).block k ⊆ (R.clusters t).block k := by
  induction t with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact subset_rfl
  | succ t ih =>
    by_cases heq : s = t+1
    · subst s; exact subset_rfl
    · exact (ih (by omega)).trans (R.clusters_mono t k)

lemma Run.terminal_closed {T : ℕ} (R : Run V T) (k : V) : R.Closed ((R.clusters T).block k) := by
  intro t ht
  let e := R.step t ht
  have hm : e.v ∈ (R.clusters (t+1)).block e.u := by
    simp [Run.clusters, ht, e, Clusters.merge, Clusters.self_mem]
  have hmT := R.clusters_subset (by omega : t+1 ≤ T) e.u hm
  have heq : (R.clusters T).block e.v = (R.clusters T).block e.u :=
    (R.clusters T).coherent _ _ hmT
  simp only [Clusters.mem_iff]
  rw [heq]

lemma Run.selected_card {T : ℕ} (R : Run V T) (C : Finset V) (hC : R.Closed C)
    {t : ℕ} (ht : t ≤ T) : (selected C (R.edgeBag t)).card = internalCount R C t := by
  induction t with
  | zero => simp [Run.edgeBag, selected, internalCount]
  | succ t ih =>
    have hlt : t < T := by omega
    rw [Run.edgeBag, dif_pos hlt]
    have hm := inBlock_pair (hC t hlt)
    simp only [selected, Multiset.filter_add, Multiset.card_add, Multiset.filter_singleton]
    rw [show ((R.edgeBag t).filter (inBlock C)).card = internalCount R C t from ih (by omega)]
    simp only [internalCount, range_add_one, filter_insert]
    by_cases hu : (R.step t hlt).u ∈ C
    · have he : inBlock C s((R.step t hlt).u,(R.step t hlt).v) := hm.mpr hu
      simp [he, hlt, hu]
    · have he : ¬inBlock C s((R.step t hlt).u,(R.step t hlt).v) := fun h => hu (hm.mp h)
      simp [he, hlt, hu]

/-- Every prefix is controlled by the total number of arrivals in its final component. -/
theorem component_bound_all_prefixes {T L : ℕ} (R : Run V T) (hi : ∀ k, R.d 0 k = 0)
    (C : Finset V) (hC : R.Closed C) (hL : internalCount R C T ≤ L)
    {t : ℕ} (ht : t ≤ T) {k : V} (hk : k ∈ C) :
    |R.d t k| ≤ 4*(L : ℝ)^((1:ℝ)/3) := by
  let M := R.mask C hC
  let P := M.prefix t ht
  have hp : ∀ k, P.d 0 k = 0 := by intro k; simp [P, M, Run.prefix, Run.mask, hi]
  have hc := abs_cube_bound_expanding P hp k
  have hcount : expandingCount P t ≤ expandingCount M T := by
    apply card_le_card
    intro s hs
    obtain ⟨hr, h, he⟩ := mem_filter.mp hs
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (lt_of_lt_of_le (mem_range.mp hr) ht), ?_⟩
    exact ⟨by omega, he⟩
  have hcounts : (expandingCount P t : ℝ) ≤ L := by
    exact_mod_cast hcount.trans ((mask_expandingCount_le R C hC T).trans hL)
  have hd : P.d t k = R.d t k := by simp [P, M, Run.prefix, Run.mask, hk]
  rw [hd] at hc
  apply le_four_cuberoot (abs_nonneg _) (Nat.cast_nonneg _)
  linarith

end Carpooling
