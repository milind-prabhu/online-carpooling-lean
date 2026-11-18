import Carpooling.WitnessCover
import Carpooling.FiniteProbability
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Order.Field.GeomSum

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

section Bags
variable {A E : Type*} [DecidableEq A] [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def bagEnumeration (m : Multiset A) : Fin m.toList.length → A := m.toList.get

lemma bagEnumeration_bag (m : Multiset A) :
    (univ : Finset (Fin m.toList.length)).val.map (bagEnumeration m) = m := by
  simp [-Multiset.length_toList, bagEnumeration, List.ofFn_getElem]

noncomputable def sampleBag {T : ℕ} (g : E → A) (x : Fin T → E) : Multiset A :=
  (univ : Finset (Fin T)).val.map (fun i => g (x i))

@[simp] lemma sampleBag_card {T : ℕ} (g : E → A) (x : Fin T → E) : (sampleBag g x).card = T := by
  simp [sampleBag]

noncomputable def bagOccurrenceEvent {T : ℕ} (g : E → A) (m : Multiset A) : Finset (Fin T → E) :=
  mappedOccurrenceEvent g (bagEnumeration m)

lemma bag_occurrence_probability {T : ℕ} (g : E → A) (hg : Function.Injective g) (m : Multiset A) :
    uniformProb (bagOccurrenceEvent (T := T) g m) ≤ ((T : ℝ) / Fintype.card E)^m.card := by
  simpa [bagOccurrenceEvent, Multiset.length_toList] using
    mapped_occurrence_probability_bound (T := T) g hg (bagEnumeration m)

lemma mem_bagOccurrence {T : ℕ} (g : E → A) (m : Multiset A) (x : Fin T → E)
    (h : m ≤ sampleBag g x) : x ∈ bagOccurrenceEvent g m := by
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  apply embedding_of_bag_le (bagEnumeration m) (fun i => g (x i))
  rwa [bagEnumeration_bag]

end Bags

lemma Witness.decorate_nodes {N : V → Finset V} {root : V} {S : Tree Unit} {F : Tree V}
    (h : F ∈ Witness.decorate N root S) : F.numNodes = S.numNodes := by
  induction S generalizing root F with
  | nil => have : F = .nil := mem_singleton.mp h; subst F; rfl
  | node a L R ihL ihR =>
    obtain ⟨v, hv, hF⟩ := mem_biUnion.mp h
    obtain ⟨⟨X,Y⟩, hXY, rfl⟩ := mem_image.mp hF
    simp only [mem_product] at hXY
    simp only [Tree.numNodes, ihL hXY.1, ihR hXY.2]

lemma Witness.families_nodes {N : V → Finset V} {r : ℕ} {w : V × Tree V}
    (h : w ∈ Witness.families N r) : w.2.numNodes = r := by
  obtain ⟨root, _, hw⟩ := mem_biUnion.mp h
  obtain ⟨S, hS, hw⟩ := mem_biUnion.mp hw
  obtain ⟨F, hF, rfl⟩ := mem_image.mp hw
  exact (Witness.decorate_nodes hF).trans (Tree.mem_treesOfNumNodesEq.mp hS)

section Probability
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

noncomputable def witnessEvent (N : V → Finset V) (g : E → Sym2 V) (T r : ℕ) : Finset (Fin T → E) :=
  (Witness.families N r).biUnion fun w => bagOccurrenceEvent g (Witness.edges w.1 w.2)

/-- Equations (6) and (7) combined, without assuming the witness encoding. -/
theorem witness_event_probability (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (g : E → Sym2 V) (hg : Function.Injective g) (T r : ℕ) :
    uniformProb (witnessEvent N g T r) ≤
      (Fintype.card V : ℝ) * (4 * Δ * T / Fintype.card E)^r := by
  have hu := uniformProb_biUnion_le (Witness.families N r)
    (fun w => bagOccurrenceEvent (T := T) g (Witness.edges w.1 w.2))
  have hs : (∑ w ∈ Witness.families N r,
      uniformProb (bagOccurrenceEvent (T := T) g (Witness.edges w.1 w.2))) ≤
      (Witness.families N r).card * ((T : ℝ) / Fintype.card E)^r := by
    calc
      _ ≤ ∑ w ∈ Witness.families N r, ((T : ℝ) / Fintype.card E)^r := by
        apply sum_le_sum
        intro w hw
        simpa only [Witness.edges_card, Witness.families_nodes hw] using bag_occurrence_probability (T := T) g hg (Witness.edges w.1 w.2)
      _ = _ := by simp
  have hc : ((Witness.families N r).card : ℝ) ≤ (4 : ℝ)^r * Fintype.card V * (Δ : ℝ)^r := by
    exact_mod_cast Witness.families_card_bound N hΔ r
  calc
    uniformProb (witnessEvent N g T r) ≤ (Witness.families N r).card * ((T : ℝ) / Fintype.card E)^r := hu.trans hs
    _ ≤ ((4 : ℝ)^r * Fintype.card V * (Δ : ℝ)^r) * ((T : ℝ) / Fintype.card E)^r :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = (Fintype.card V : ℝ) * (4 * Δ * T / Fintype.card E)^r := by
      simp only [div_pow, mul_pow]
      ring

/-- Large-component event quantified over all legal weighted Greedy runs with the sampled bag.
The request order and all weights may be selected after the edge samples are known. -/
noncomputable def badComponentEvent (N : V → Finset V) (g : E → Sym2 V) (T L : ℕ) : Finset (Fin T → E) :=
  univ.filter fun x => ∃ R : Run V T,
    (∀ s (hs : s < T), (R.step s hs).v ∈ N (R.step s hs).u) ∧
    R.edgeBag T = sampleBag g x ∧
    ∃ k, L ≤ (selected ((R.clusters T).block k) (R.edgeBag T)).card

lemma bad_component_cover (N : V → Finset V)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v) (g : E → Sym2 V) (T L : ℕ) :
    badComponentEvent N g T L ⊆ (Ico L (T+1)).biUnion fun r => witnessEvent N g T r := by
  intro x hx
  obtain ⟨R, hAdj, hbag, k, hL⟩ := (mem_filter.mp hx).2
  obtain ⟨F, hF, he, hv⟩ := R.component_witness (fun u v => v ∈ N u) hsymm hAdj (le_refl T) k
  let r := F.numNodes
  have hle : Witness.edges k F ≤ sampleBag g x := by
    rw [he, ← hbag]
    exact Multiset.filter_le _ _
  have hrle : r ≤ T := by simpa [r] using Multiset.card_le_card hle
  have hLr : L ≤ r := by simpa [← he] using hL
  apply mem_biUnion.mpr
  refine ⟨r, mem_Ico.mpr ⟨hLr, by omega⟩, ?_⟩
  apply mem_biUnion.mpr
  refine ⟨(k,F), Witness.mem_families hF rfl, ?_⟩
  exact mem_bagOccurrence g (Witness.edges k F) x hle

/-- Explicit high-probability component estimate for a subcritical batch.
`hbalance` is the degree-sum identity for a regular undirected sampling graph. -/
theorem stochastic_component_tail (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (T L : ℕ) (hT : 16*T ≤ Fintype.card V) :
    uniformProb (badComponentEvent N g T L) ≤ 2 * Fintype.card V / (2 : ℝ)^L := by
  have hM : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hbal : (2 : ℝ)*Fintype.card E = Fintype.card V * (Δ : ℝ) := by exact_mod_cast hbalance
  have hTr : (16 : ℝ)*T ≤ Fintype.card V := by exact_mod_cast hT
  have hq : 4*(Δ : ℝ)*T / Fintype.card E ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ hM).mpr
    have hd : 0 ≤ (Δ : ℝ) := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_right hTr hd
    nlinarith
  have hu := (uniformProb_mono (bad_component_cover N hsymm g T L)).trans
    (uniformProb_biUnion_le (Ico L (T+1)) (fun r => witnessEvent N g T r))
  have hs : (∑ r ∈ Ico L (T+1), uniformProb (witnessEvent N g T r)) ≤
      (Fintype.card V : ℝ) * ∑ r ∈ Ico L (T+1), ((1:ℝ)/2)^r := by
    rw [mul_sum]
    apply sum_le_sum
    intro r hr
    exact (witness_event_probability N hΔ g hg T r).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq r) (Nat.cast_nonneg _))
  have hg := geom_sum_Ico_le_of_lt_one (m := L) (n := T+1)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
  have hgeom : (∑ r ∈ Ico L (T+1), ((1:ℝ)/2)^r) ≤ 2 / (2:ℝ)^L := by
    convert hg using 1 <;> simp [div_pow] <;> ring
  exact (hu.trans hs).trans (by
    have hh := mul_le_mul_of_nonneg_left hgeom (Nat.cast_nonneg (Fintype.card V))
    convert hh using 1 <;> ring)

noncomputable def badDiscrepancyEvent (N : V → Finset V) (g : E → Sym2 V) (T L : ℕ) : Finset (Fin T → E) :=
  univ.filter fun x => ∃ R : Run V T,
    (∀ k, R.d 0 k = 0) ∧
    (∀ s (hs : s < T), (R.step s hs).v ∈ N (R.step s hs).u) ∧
    R.edgeBag T = sampleBag g x ∧
    ∃ t ≤ T, ∃ k, 4*(L : ℝ)^((1:ℝ)/3) < |R.d t k|

lemma bad_discrepancy_subset (N : V → Finset V) (g : E → Sym2 V) (T L : ℕ) :
    badDiscrepancyEvent N g T L ⊆ badComponentEvent N g T L := by
  intro x hx
  obtain ⟨R, hi, hAdj, hbag, t, ht, k, hbad⟩ := (mem_filter.mp hx).2
  apply mem_filter.mpr
  refine ⟨mem_univ _, R, hAdj, hbag, k, ?_⟩
  by_contra hn
  have hL : internalCount R ((R.clusters T).block k) T ≤ L := by
    rw [← R.selected_card _ (R.terminal_closed k) (le_refl T)]
    omega
  have hgood := component_bound_all_prefixes R hi _ (R.terminal_closed k) hL ht
    ((R.clusters T).self_mem k)
  exact (not_lt_of_ge hgood) hbad

/-- The basic stochastic upper bound, with explicit finite-sample failure probability.
It simultaneously controls every prefix, every legal tie rule, and every weight assignment. -/
theorem stochastic_upper_tail (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (T L : ℕ) (hT : 16*T ≤ Fintype.card V) :
    uniformProb (badDiscrepancyEvent N g T L) ≤ 2 * Fintype.card V / (2 : ℝ)^L :=
  (uniformProb_mono (bad_discrepancy_subset N g T L)).trans
    (stochastic_component_tail N hΔ hpos hsymm g hg hbalance T L hT)

noncomputable def stochasticThreshold (n : ℕ) : ℕ := Nat.clog 2 (2*n^2)

/-- A concrete form of the cube-root logarithmic stochastic bound for a batch:
discrepancy at most `4 * (clog 2 (2*n^2))^(1/3)`, except with probability at most 1/n. -/
theorem stochastic_basic_high_probability (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (T : ℕ) (hT : 16*T ≤ Fintype.card V) (hn : 0 < Fintype.card V) :
    uniformProb (badDiscrepancyEvent N g T (stochasticThreshold (Fintype.card V))) ≤
      1 / (Fintype.card V : ℝ) := by
  have ht := stochastic_upper_tail N hΔ hpos hsymm g hg hbalance T
    (stochasticThreshold (Fintype.card V)) hT
  have hpow := Nat.le_pow_clog (by decide : 1 < 2) (2*(Fintype.card V)^2)
  have hp : 2*(Fintype.card V : ℝ)^2 ≤ (2:ℝ)^(stochasticThreshold (Fintype.card V)) := by
    exact_mod_cast hpow
  have hnR : (0:ℝ) < Fintype.card V := by exact_mod_cast hn
  apply ht.trans
  apply (div_le_div_iff₀ (by positivity) hnR).mpr
  nlinarith

end Probability
end Carpooling
