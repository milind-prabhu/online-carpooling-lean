import Carpooling.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-! Unit-weight lower bound against arbitrary orientations. The adversary
requests equal-discrepancy endpoints until a large discrepancy has occurred.
Unlike `Move`, `UnitMove` imposes no Greedy ordering restriction. -/
namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

structure UnitMove (x y : V → ℤ) where
  u : V
  v : V
  distinct : u ≠ v
  update : ∀ k, y k = x k + (if k = u then 1 else 0) - (if k = v then 1 else 0)

def integerPotential (x : V → ℤ) : ℤ := ∑ v, x v ^ 2

lemma UnitMove.potential_change {x y : V → ℤ} (e : UnitMove x y) :
    integerPotential y = integerPotential x + 2*(x e.u-x e.v) + 2 := by
  have hsq : ∀ k, y k ^ 2 = x k ^ 2 +
      (if k = e.u then 2*x e.u+1 else 0) +
      (if k = e.v then -2*x e.v+1 else 0) := by
    intro k
    rw [e.update]
    by_cases hu : k = e.u <;> by_cases hv : k = e.v
    · exact (e.distinct (hu.symm.trans hv)).elim
    · subst k; simp [hv]; ring
    · subst k; simp [hu]; ring
    · simp [hu,hv]
  unfold integerPotential
  simp_rw [hsq, sum_add_distrib]
  simp
  ring

lemma equal_pair_of_bounded_integer_positions (x : V → ℤ) (h : ℕ)
    (hcard : 2*h+1 < Fintype.card V) (hx : ∀ v, |x v| ≤ (h:ℤ)) :
    ∃ u v, u ≠ v ∧ x u = x v := by
  have hb : ∀ v, -(h:ℤ) ≤ x v ∧ x v ≤ (h:ℤ) := fun v => abs_le.mp (hx v)
  let f : V → Fin (2*h+1) := fun v => ⟨(x v + h).toNat, by
    have hv := hb v
    omega⟩
  obtain ⟨u,v,huv,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hcard)
  refine ⟨u,v,huv,?_⟩
  have he := congrArg Fin.val heq
  have hu := hb u
  have hv := hb v
  dsimp [f] at he
  omega

structure IntegerRun (V : Type*) [Fintype V] [DecidableEq V] (T : ℕ) where
  d : ℕ → V → ℤ
  step : ∀ t, t < T → UnitMove (d t) (d (t+1))

/-- The pathwise lower-bound engine. When the adversary finds equal endpoints,
either orientation increases the full quadratic potential by exactly two. -/
theorem equal_endpoint_lower_bound {T h : ℕ} (R : IntegerRun V T)
    (hi : ∀ v, R.d 0 v = 0)
    (hequal : ∀ t (ht : t < T),
      (∀ v, |R.d t v| < (h:ℤ)) → R.d t (R.step t ht).u = R.d t (R.step t ht).v)
    (horizon : (Fintype.card V:ℤ)*(h:ℤ)^2 < 2*(T:ℤ)) :
    ∃ t ≤ T, ∃ v, (h:ℤ) ≤ |R.d t v| := by
  by_contra hn
  have hb : ∀ t, t ≤ T → ∀ v, |R.d t v| < (h:ℤ) := by
    intro t ht v
    by_contra hv
    exact hn ⟨t,ht,v,le_of_not_gt hv⟩
  have hp : ∀ t, t ≤ T → integerPotential (R.d t) = 2*(t:ℤ) := by
    intro t ht
    induction t with
    | zero => simp [integerPotential,hi]
    | succ t ih =>
      have hlt : t < T := by omega
      have he := (R.step t hlt).potential_change
      rw [hequal t hlt (hb t (by omega)), sub_self, mul_zero, add_zero] at he
      rw [he, ih (by omega)]
      push_cast
      ring
  have hsq : ∀ v, R.d T v ^ 2 ≤ (h:ℤ)^2 := by
    intro v
    have hv := le_of_lt (hb T (le_refl T) v)
    have habs := abs_nonneg (R.d T v)
    nlinarith [sq_abs (R.d T v)]
  have hsum := sum_le_sum (s := (univ : Finset V)) (fun v _ => hsq v)
  have hbound : integerPotential (R.d T) ≤ (Fintype.card V:ℤ)*(h:ℤ)^2 := by
    simpa [integerPotential] using hsum
  rw [hp T (le_refl T)] at hbound
  omega

/-- A causal adversary: choose an equal pair if one exists, otherwise use 0,1. -/
noncomputable def lowerPair (h : ℕ) (x : Fin (2*h+2) → ℤ) :
    Fin (2*h+2) × Fin (2*h+2) :=
  if he : ∃ u v, u ≠ v ∧ x u = x v then (he.choose,he.choose_spec.choose)
  else (⟨0,by omega⟩,⟨1,by omega⟩)

lemma lowerPair_distinct (h : ℕ) (x : Fin (2*h+2) → ℤ) :
    (lowerPair h x).1 ≠ (lowerPair h x).2 := by
  unfold lowerPair
  split_ifs with he
  · exact he.choose_spec.choose_spec.1
  · simp

lemma lowerPair_equal (h : ℕ) (x : Fin (2*h+2) → ℤ)
    (hx : ∀ v, |x v| < (h:ℤ)) : x (lowerPair h x).1 = x (lowerPair h x).2 := by
  have he : ∃ u v, u ≠ v ∧ x u = x v :=
    equal_pair_of_bounded_integer_positions x h (by simp) (fun v => le_of_lt (hx v))
  simp only [lowerPair,dif_pos he]
  exact he.choose_spec.choose_spec.2

def orientUnit (x : V → ℤ) (a b : V) (flip : Bool) : V → ℤ :=
  let u := if flip then b else a
  let v := if flip then a else b
  fun k => x k + (if k = u then 1 else 0) - (if k = v then 1 else 0)

def orientUnit_move (x : V → ℤ) (a b : V) (hab : a ≠ b) (flip : Bool) :
    UnitMove x (orientUnit x a b flip) where
  u := if flip then b else a
  v := if flip then a else b
  distinct := by cases flip <;> simp [hab,Ne.symm hab]
  update := fun _ => rfl

/-- `directions` can be any realized sequence of the algorithm's choices,
including choices made with arbitrary internal randomness and memory. -/
noncomputable def lowerStates (h : ℕ) (directions : ℕ → Bool) : ℕ → Fin (2*h+2) → ℤ
  | 0 => fun _ => 0
  | t+1 => let p := lowerPair h (lowerStates h directions t)
    orientUnit (lowerStates h directions t) p.1 p.2 (directions t)

noncomputable def lowerRun (h : ℕ) (directions : ℕ → Bool) (T : ℕ) :
    IntegerRun (Fin (2*h+2)) T where
  d := lowerStates h directions
  step := fun t _ => orientUnit_move _ _ _ (lowerPair_distinct h _) (directions t)

/-- The adversary uses only previous orientation decisions. -/
lemma lowerStates_prefix_congr (h : ℕ) (directions directions' : ℕ → Bool) (t : ℕ)
    (heq : ∀ s < t, directions s = directions' s) :
    lowerStates h directions t = lowerStates h directions' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [lowerStates]
    rw [heq t (Nat.lt_succ_self t), ih (fun s hs => heq s (Nat.lt_succ_of_lt hs))]

/-- Explicit deterministic cube-root lower bound: on 2h+2 vertices, an adaptive
unit-weight adversary forces discrepancy at least h within (2h+2)h² requests,
for every sequence of orientation choices. -/
theorem adversarial_cubic_lower_bound (h : ℕ) (hh : 0 < h) (directions : ℕ → Bool) :
    ∃ t ≤ (2*h+2)*h^2, ∃ v, (h:ℤ) ≤ |lowerStates h directions t v| := by
  let T := (2*h+2)*h^2
  apply equal_endpoint_lower_bound (lowerRun h directions T) (fun _ => rfl)
  · intro t ht hb
    have he := lowerPair_equal h (lowerStates h directions t) hb
    change lowerStates h directions t _ = lowerStates h directions t _
    cases hd : directions t
    · simpa [lowerRun,orientUnit_move,hd] using he
    · simpa [lowerRun,orientUnit_move,hd] using he.symm
  · simp only [Fintype.card_fin]
    dsimp [T]
    push_cast
    have hpos : (0:ℤ) < h := by exact_mod_cast hh
    nlinarith [sq_nonneg (h:ℤ)]

theorem adversarial_lower_bound_four_cubes (h : ℕ) (hh : 0 < h)
    (directions : ℕ → Bool) :
    ∃ t ≤ 4*h^3, ∃ v, (h:ℤ) ≤ |lowerStates h directions t v| := by
  obtain ⟨t,ht,v,hv⟩ := adversarial_cubic_lower_bound h hh directions
  refine ⟨t,ht.trans ?_,v,hv⟩
  have hmul := Nat.mul_le_mul_right (h^2) (show 2*h+2 ≤ 4*h by omega)
  nlinarith

end Carpooling
