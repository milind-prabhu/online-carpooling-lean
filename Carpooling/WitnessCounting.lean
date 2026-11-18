import Carpooling.WitnessForest
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Bounds

namespace Carpooling.Witness
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def shape (F : Tree V) : Tree Unit := F.map fun _ => ()

@[simp] lemma shape_nodes (F : Tree V) : (shape F).numNodes = F.numNodes := by
  induction F with
  | nil => rfl
  | node v L R ihL ihR => simp [shape, Tree.map, Tree.numNodes] at *; omega

/-- All graph-respecting vertex labels for one rooted ordered tree shape. -/
noncomputable def decorate (N : V → Finset V) (root : V) : Tree Unit → Finset (Tree V)
  | .nil => {.nil}
  | .node _ L R => (N root).biUnion fun v =>
      ((decorate N v L) ×ˢ (decorate N root R)).image fun p => .node v p.1 p.2

lemma decorate_card_le (N : V → Finset V) {Δ : ℕ} (hΔ : ∀ v, (N v).card ≤ Δ)
    (root : V) (S : Tree Unit) : (decorate N root S).card ≤ Δ^S.numNodes := by
  induction S generalizing root with
  | nil => simp [decorate, Tree.numNodes]
  | node a L R ihL ihR =>
    calc
      (decorate N root (.node a L R)).card ≤
          ∑ v ∈ N root, (((decorate N v L) ×ˢ (decorate N root R)).image
            (fun p => Tree.node v p.1 p.2)).card := card_biUnion_le
      _ ≤ ∑ v ∈ N root, Δ^L.numNodes * Δ^R.numNodes := by
        apply sum_le_sum
        intro v hv
        exact (card_image_le).trans (by
          rw [card_product]
          exact Nat.mul_le_mul (ihL v) (ihR root))
      _ = (N root).card * (Δ^L.numNodes * Δ^R.numNodes) := by simp
      _ ≤ Δ * (Δ^L.numNodes * Δ^R.numNodes) := Nat.mul_le_mul_right _ (hΔ root)
      _ = Δ^(.node a L R : Tree Unit).numNodes := by
        simp only [Tree.numNodes, pow_add, pow_one]
        ring

lemma mem_decorate {N : V → Finset V} {root : V} {F : Tree V}
    (hF : Valid (fun u v => v ∈ N u) root F) : F ∈ decorate N root (shape F) := by
  induction F generalizing root with
  | nil => simp [shape, Tree.map, decorate]
  | node v L R ihL ihR =>
    apply mem_biUnion.mpr
    refine ⟨v, hF.1, mem_image.mpr ?_⟩
    exact ⟨(L,R), mem_product.mpr ⟨ihL hF.2.1, ihR hF.2.2⟩, rfl⟩

noncomputable def families (N : V → Finset V) (r : ℕ) : Finset (V × Tree V) :=
  univ.biUnion fun root => (Tree.treesOfNumNodesEq r).biUnion fun S =>
    (decorate N root S).image fun F => (root,F)

lemma mem_families {N : V → Finset V} {root : V} {F : Tree V} {r : ℕ}
    (hF : Valid (fun u v => v ∈ N u) root F) (hr : F.numNodes = r) :
    (root,F) ∈ families N r := by
  apply mem_biUnion.mpr
  refine ⟨root, mem_univ _, mem_biUnion.mpr ?_⟩
  refine ⟨shape F, Tree.mem_treesOfNumNodesEq.mpr (by simpa using hr), ?_⟩
  exact mem_image.mpr ⟨F, mem_decorate hF, rfl⟩

lemma families_card_le_catalan (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (r : ℕ) :
    (families N r).card ≤ Fintype.card V * catalan r * Δ^r := by
  calc
    (families N r).card ≤ ∑ root : V,
        ((Tree.treesOfNumNodesEq r).biUnion fun S =>
          (decorate N root S).image fun F => (root,F)).card := card_biUnion_le
    _ ≤ ∑ root : V, ∑ S ∈ Tree.treesOfNumNodesEq r, Δ^r := by
      apply sum_le_sum
      intro root _
      apply card_biUnion_le.trans
      apply sum_le_sum
      intro S hS
      have hrS := Tree.mem_treesOfNumNodesEq.mp hS
      exact card_image_le.trans (by simpa [hrS] using decorate_card_le N hΔ root S)
    _ = Fintype.card V * catalan r * Δ^r := by
      simp [Tree.treesOfNumNodesEq_card_eq_catalan, mul_assoc]

lemma catalan_le_four_pow (r : ℕ) : catalan r ≤ 4^r := by
  calc
    catalan r = Nat.centralBinom r / (r+1) := catalan_eq_centralBinom_div r
    _ ≤ Nat.centralBinom r := Nat.div_le_self _ _
    _ ≤ 2^(2*r) := Nat.choose_le_two_pow _ _
    _ = 4^r := by rw [pow_mul]; norm_num

/-- Equation (6), for all rooted graph-respecting witness forests. -/
theorem families_card_bound (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (r : ℕ) :
    (families N r).card ≤ 4^r * Fintype.card V * Δ^r := by
  have h := families_card_le_catalan N hΔ r
  have hc := catalan_le_four_pow r
  calc
    (families N r).card ≤ Fintype.card V * catalan r * Δ^r := h
    _ ≤ Fintype.card V * 4^r * Δ^r := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc)
    _ = 4^r * Fintype.card V * Δ^r := by ac_rfl

end Carpooling.Witness
