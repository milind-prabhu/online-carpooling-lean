import Carpooling.UpperBounds

namespace Carpooling
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A weighted undirected arrival. The endpoint order only fixes the tie rule. -/
structure Request (V : Type*) where
  a : V
  b : V
  distinct : a ≠ b
  weight : ℝ
  nonneg : 0 ≤ weight
  le_one : weight ≤ 1

noncomputable def Request.apply (q : Request V) (x : V → ℝ) : V → ℝ :=
  if x q.a ≤ x q.b then
    fun k => x k + (if k = q.a then q.weight else 0) - (if k = q.b then q.weight else 0)
  else
    fun k => x k + (if k = q.b then q.weight else 0) - (if k = q.a then q.weight else 0)

noncomputable def Request.move (q : Request V) (x : V → ℝ) : Move x (q.apply x) := by
  by_cases h : x q.a ≤ x q.b
  · exact ⟨q.a, q.b, q.distinct, q.weight, q.nonneg, q.le_one, h,
      by intro k; simp [Request.apply, h]⟩
  · exact ⟨q.b, q.a, Ne.symm q.distinct, q.weight, q.nonneg, q.le_one,
      le_of_lt (lt_of_not_ge h), by intro k; simp [Request.apply, h]⟩

noncomputable def states (requests : ℕ → Request V) : ℕ → V → ℝ
  | 0 => fun _ => 0
  | t+1 => (requests t).apply (states requests t)

noncomputable def runRequests (requests : ℕ → Request V) (T : ℕ) : Run V T where
  d := states requests
  step := fun t _ => (requests t).move (states requests t)

/-- An end-to-end statement about the actual Greedy recurrence. -/
theorem greedy_requests_upper_bound (requests : ℕ → Request V) (t : ℕ) (i : V) :
    |states requests t i| ≤ min (4 * (t : ℝ)^((1:ℝ)/3)) (Fintype.card V) :=
  theorem_1_1 (runRequests requests t) (fun _ => rfl) (le_refl t) i

end Carpooling
