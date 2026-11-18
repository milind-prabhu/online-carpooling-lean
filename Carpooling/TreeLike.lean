import Carpooling.Dissipative
import Carpooling.Clusters

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def Run.clusters {T : ℕ} (R : Run V T) : ℕ → Clusters V
  | 0 => Clusters.singletons
  | t+1 => if h : t < T then
      (R.clusters t).merge (R.step t h).u (R.step t h).v else R.clusters t

def Run.IsInternal {T : ℕ} (R : Run V T) (t : ℕ) : Prop :=
  ∃ h : t < T, (R.clusters t).block (R.step t h).u = (R.clusters t).block (R.step t h).v

noncomputable def Run.surplus {T : ℕ} (R : Run V T) (t : ℕ) : ℕ :=
  ((range t).filter R.IsInternal).card

lemma log_add_strict {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : Nat.log 2 (a+b) = Nat.log 2 a) : Nat.log 2 b < Nat.log 2 a := by
  by_contra hn
  have hba : Nat.log 2 a ≤ Nat.log 2 b := by omega
  have hpa := Nat.pow_log_le_self 2 ha.ne'
  have hpb := Nat.pow_le_of_le_log hb.ne' hba
  have hp : 2^(Nat.log 2 a + 1) ≤ a+b := by rw [pow_succ]; omega
  have hl := Nat.le_log_of_pow_le (by decide : 1 < 2) hp
  omega

lemma Run.clusters_mono {T : ℕ} (R : Run V T) (t : ℕ) (k : V) :
    (R.clusters t).block k ⊆ (R.clusters (t+1)).block k := by
  rw [Run.clusters]
  split_ifs with h
  · exact Clusters.subset_merge _ _ _ _
  · exact subset_rfl

noncomputable def Run.rank {T : ℕ} (R : Run V T) (t : ℕ) (k : V) : ℕ :=
  Nat.log 2 ((R.clusters t).block k).card

lemma Run.rank_mono {T : ℕ} (R : Run V T) (t : ℕ) (k : V) :
    R.rank t k ≤ R.rank (t+1) k := Nat.log_mono_right (card_le_card (R.clusters_mono t k))

noncomputable def Run.shift {T : ℕ} (R : Run V T) (t : ℕ) (k : V) : ℝ :=
  R.d t k - 2 * (R.rank t k : ℝ)

lemma Run.shift_step {T : ℕ} (R : Run V T) {t : ℕ} (ht : t < T) :
    DStep (R.shift t) (R.shift (t+1)) (decide (R.IsInternal t)) := by
  let P := R.clusters t
  let e := R.step t ht
  have hnext : R.clusters (t+1) = P.merge e.u e.v := by simp [Run.clusters, ht, P, e]
  have hrmono : ∀ k, (R.rank t k : ℝ) ≤ R.rank (t+1) k := by
    intro k; exact_mod_cast R.rank_mono t k
  by_cases hint : P.block e.u = P.block e.v
  · have hsame : R.clusters (t+1) = P := hnext.trans (P.merge_same hint)
    have hruv : R.rank t e.u = R.rank t e.v := congrArg (fun S : Finset V => Nat.log 2 S.card) hint
    have hrs : ∀ k, R.rank (t+1) k = R.rank t k := by intro k; simp [Run.rank, hsame, P]
    let z : V → ℝ := R.shift (t+1)
    let em : Move (R.shift t) z := {
      u := e.u, v := e.v, distinct := e.distinct, weight := e.weight,
      weight_nonneg := e.weight_nonneg, weight_le_one := e.weight_le_one,
      ordered := by dsimp [Run.shift]; rw [hruv]; exact sub_le_sub_right e.ordered _,
      update := by
        intro k
        dsimp [z, Run.shift]
        rw [hrs, e.update]
        ring }
    exact DStep.move em (fun _ => le_rfl) (by intro _; apply decide_eq_true; exact ⟨ht, hint⟩)
  · have hnew : R.rank (t+1) e.u = R.rank (t+1) e.v := by
      simp [Run.rank, hnext]
    by_cases hgrow : R.rank t e.u < R.rank (t+1) e.u
    · apply DStep.drop
      intro k
      by_cases hku : k = e.u
      · subst k
        have hh : (R.rank t e.u : ℝ) + 1 ≤ R.rank (t+1) e.u := by exact_mod_cast hgrow
        dsimp [Run.shift]
        rw [e.at_u]
        linarith [e.weight_le_one]
      · by_cases hkv : k = e.v
        · subst k
          dsimp [Run.shift]
          rw [e.at_v]
          linarith [hrmono e.v, e.weight_nonneg]
        · dsimp [Run.shift]
          rw [e.update]
          simp only [if_neg hku, if_neg hkv, add_zero, sub_zero]
          linarith [hrmono k]
    · have heq : R.rank (t+1) e.u = R.rank t e.u := by
        have hh := R.rank_mono t e.u; omega
      have ha : 0 < (P.block e.u).card := card_pos.mpr ⟨e.u, P.self_mem _⟩
      have hb : 0 < (P.block e.v).card := card_pos.mpr ⟨e.v, P.self_mem _⟩
      have hlog : Nat.log 2 ((P.block e.u).card + (P.block e.v).card) = R.rank t e.u := by
        have hc : (P.block e.u ∪ P.block e.v).card = (P.block e.u).card + (P.block e.v).card :=
          card_union_of_disjoint (P.disjoint hint)
        simpa [Run.rank, hnext, hc] using heq
      have hlt : R.rank t e.v < R.rank t e.u := log_add_strict ha hb hlog
      have hltR : (R.rank t e.v : ℝ) + 1 ≤ R.rank t e.u := by exact_mod_cast hlt
      have hgap : R.shift t e.u + e.weight ≤ R.shift t e.v := by
        dsimp [Run.shift]
        linarith [e.ordered, e.weight_le_one]
      let z : V → ℝ := fun k => R.shift t k + (if k = e.u then e.weight else 0) -
        (if k = e.v then e.weight else 0)
      let em : Move (R.shift t) z := {
        u := e.u, v := e.v, distinct := e.distinct, weight := e.weight,
        weight_nonneg := e.weight_nonneg, weight_le_one := e.weight_le_one,
        ordered := by linarith [e.weight_nonneg], update := fun _ => rfl }
      apply DStep.move em
      · intro k
        dsimp [z, Run.shift]
        rw [e.update]
        linarith [hrmono k]
      · intro hex
        change R.shift t e.v < R.shift t e.u + e.weight at hex
        exact False.elim (not_lt_of_ge hgap hex)

noncomputable def Run.shifted {T : ℕ} (R : Run V T) : DRun V T where
  d := R.shift
  charge := fun t => decide (R.IsInternal t)
  step := fun _ ht => R.shift_step ht

lemma Run.shifted_count {T : ℕ} (R : Run V T) (t : ℕ) :
    R.shifted.count t = R.surplus t := by simp [DRun.count, Run.shifted, Run.surplus]

lemma Run.clusters_neg {T : ℕ} (R : Run V T) (t : ℕ) : R.neg.clusters t = R.clusters t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Run.clusters]
    split_ifs with h
    · rw [ih]; exact Clusters.merge_comm _ _ _
    · exact ih

lemma Run.surplus_neg {T : ℕ} (R : Run V T) (t : ℕ) : R.neg.surplus t = R.surplus t := by
  unfold Run.surplus
  congr 1
  apply filter_congr
  intro s _
  simp only [Run.IsInternal]
  apply exists_congr
  intro h
  rw [R.clusters_neg]
  change (R.clusters s).block (R.step s h).v = (R.clusters s).block (R.step s h).u ↔ _
  exact eq_comm

/-- A refined deterministic bound with only internal requests charged. -/
theorem tree_like_surplus_bound {T : ℕ} (R : Run V T) (hi : ∀ k, R.d 0 k = 0) (i : V) :
    |R.d T i| ≤ 4 * (R.surplus T : ℝ)^((1:ℝ)/3) +
      2 * (Nat.log 2 ((R.clusters T).block i).card : ℝ) := by
  have hpos := R.shifted.position_bound (by intro k; simp [Run.shifted, Run.shift, Run.rank, Run.clusters, Clusters.singletons, hi]) i
  have hneg := R.neg.shifted.position_bound (by intro k; simp [Run.shifted, Run.shift, Run.rank, Run.clusters, Clusters.singletons, Run.neg, hi]) i
  rw [R.shifted_count] at hpos
  rw [R.neg.shifted_count, R.surplus_neg] at hneg
  change R.d T i - 2*(R.rank T i : ℝ) ≤ _ at hpos
  change -R.d T i - 2*(R.neg.rank T i : ℝ) ≤ _ at hneg
  have hr : R.neg.rank T i = R.rank T i := by simp [Run.rank, R.clusters_neg]
  rw [hr] at hneg
  apply abs_le.mpr
  constructor <;> change _ ≤ _ <;> dsimp [Run.rank] at * <;> linarith

lemma Run.surplus_succ {T : ℕ} (R : Run V T) (t : ℕ) :
    R.surplus (t+1) = R.surplus t + if R.IsInternal t then 1 else 0 := by
  simp only [Run.surplus, range_add_one, filter_insert]
  split_ifs <;> simp_all

lemma Clusters.singletons_parts_card : (Clusters.singletons : Clusters V).parts.card = Fintype.card V := by
  rw [Clusters.parts, card_image_of_injective]
  · simp
  · intro i j h
    exact singleton_injective h

/-- The number of merging arrivals equals the drop in the number of blocks. -/
theorem Run.surplus_identity {T : ℕ} (R : Run V T) {t : ℕ} (ht : t ≤ T) :
    R.surplus t + Fintype.card V = t + (R.clusters t).parts.card := by
  induction t with
  | zero => simp [Run.surplus, Run.clusters, Clusters.singletons_parts_card]
  | succ t ih =>
    have ih := ih (by omega)
    have hnext : R.clusters (t+1) = (R.clusters t).merge (R.step t (by omega)).u (R.step t (by omega)).v := by
      simp [Run.clusters, show t < T by omega]
    rw [R.surplus_succ]
    by_cases hint : R.IsInternal t
    · rw [if_pos hint]
      obtain ⟨h, hint⟩ := hint
      rw [hnext, Clusters.merge_same _ hint]
      omega
    · rw [if_neg hint, hnext]
      have hne : (R.clusters t).block (R.step t (by omega)).u ≠
          (R.clusters t).block (R.step t (by omega)).v := by
        intro hh; exact hint ⟨by omega, hh⟩
      have hc := (R.clusters t).parts_merge_card hne
      omega

/-- Lemma 4.2 in a finite union-find presentation of connectedness.
`hconn` says the requested multigraph has one component on V. -/
theorem lemma_4_2 {T : ℕ} (R : Run V T) (hi : ∀ k, R.d 0 k = 0)
    (hconn : ∀ k, (R.clusters T).block k = univ) (i : V) :
    |R.d T i| ≤ 4 * ((T - (Fintype.card V - 1) : ℕ) : ℝ)^((1:ℝ)/3) +
      2 * (Nat.log 2 (Fintype.card V) : ℝ) := by
  have hparts : (R.clusters T).parts = {univ} := by
    ext S
    simp only [Clusters.parts, mem_image, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨k, hk⟩; exact hk.symm.trans (hconn k)
    · intro h; exact ⟨i, (hconn i).trans h.symm⟩
  have hid := R.surplus_identity (le_refl T)
  rw [hparts, card_singleton] at hid
  have hn : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨i⟩
  have hp : R.surplus T = T - (Fintype.card V - 1) := by omega
  simpa [hp, hconn] using tree_like_surplus_bound R hi i

end Carpooling
