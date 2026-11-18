import Carpooling.StochasticRefined

namespace Carpooling
open scoped Classical
open Finset

def degreeRoot (Δ : ℕ) : ℕ := 2^(Nat.log 2 Δ / 4)
def refinedThreshold (n Δ : ℕ) : ℕ := 24 * Nat.clog 2 n / Nat.log 2 Δ + 1

lemma degreeRoot_fourth_le {Δ : ℕ} (hΔ : 0 < Δ) : (degreeRoot Δ)^4 ≤ Δ := by
  unfold degreeRoot
  rw [← pow_mul]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.div_mul_le_self _ _)).trans
    (Nat.pow_log_le_self 2 hΔ.ne')

lemma degreeRoot_pos (Δ : ℕ) : 0 < degreeRoot Δ := by unfold degreeRoot; positivity

lemma refinedThreshold_power {n Δ : ℕ} (hΔ : 256 ≤ Δ) :
    n^3 ≤ (degreeRoot Δ)^(refinedThreshold n Δ) := by
  let q := Nat.log 2 Δ
  let a := q/4
  let b := Nat.clog 2 n
  let p := refinedThreshold n Δ
  have hq : 8 ≤ q := Nat.le_log_of_pow_le (by decide : 1 < 2) hΔ
  have hqa : q ≤ 8*a := by dsimp [a]; omega
  have hrem := Nat.mod_lt (24*b) (by omega : 0 < q)
  have hdiv := Nat.mod_add_div (24*b) q
  have hquot : 24*b < q*p := by dsimp [p,refinedThreshold,q,b] at *; nlinarith
  have hmul := Nat.mul_le_mul_right p hqa
  have hab : 3*b ≤ a*p := by nlinarith
  calc
    n^3 ≤ (2^b)^3 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide : 1 < 2) n) 3
    _ = 2^(3*b) := by rw [← pow_mul]; congr 1; omega
    _ ≤ 2^(a*p) := Nat.pow_le_pow_right (by decide : 0 < 2) hab
    _ = (degreeRoot Δ)^(refinedThreshold n Δ) := by simp [degreeRoot,a,q,p,pow_mul]

lemma root_condition {L Δ : ℕ} (hL : L^3 ≤ Δ) (hΔ : 0 < Δ) :
    L^2 * degreeRoot Δ ≤ 8*Δ := by
  let D := degreeRoot Δ
  have hD4 : D^4 ≤ Δ := degreeRoot_fourth_le hΔ
  have hDpos : 0 < D := degreeRoot_pos Δ
  have hh : L^2*D ≤ Δ := by
    by_cases hDL : D ≤ L
    · exact (Nat.mul_le_mul_left (L^2) hDL).trans (by nlinarith [hL])
    · have hLD : L ≤ D := by omega
      have hh := Nat.mul_le_mul_right D (Nat.pow_le_pow_left hLD 2)
      have h34 : D^3 ≤ D^4 := Nat.pow_le_pow_right hDpos (by decide : 3 ≤ 4)
      nlinarith
  change L^2*D ≤ 8*Δ
  omega

lemma threshold_failure_bound {n : ℕ} (hn : 0 < n) :
    2*(n:ℝ)/(2:ℝ)^(stochasticThreshold n) ≤ 1/(n:ℝ) := by
  have hp : 2*(n:ℝ)^2 ≤ (2:ℝ)^(stochasticThreshold n) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (2*n^2)
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  apply (div_le_div_iff₀ (by positivity) hnR).mpr
  nlinarith

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Nonempty E]

/-- The refined stochastic upper bound with explicit integer logarithms.
L = ceil(log_2(2 n^2)), p = floor(24 ceil(log_2 n)/floor(log_2 Δ)) + 1.
Outside an event of probability at most 3/n, every compatible subrun has
discrepancy at most 4 p^(1/3) + 2 floor(log_2 L). -/
theorem stochastic_refined_high_probability (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (T : ℕ) (hT : 16*T ≤ Fintype.card V) (hn : 0 < Fintype.card V)
    (hlarge : 256 ≤ Δ) (hdegree : (stochasticThreshold (Fintype.card V))^3 ≤ Δ) :
    uniformProb (badRefinedEvent N g T (stochasticThreshold (Fintype.card V))
      (refinedThreshold (Fintype.card V) Δ)) ≤ 3/(Fintype.card V:ℝ) := by
  let n := Fintype.card V
  let L := stochasticThreshold n
  let p := refinedThreshold n Δ
  let D := degreeRoot Δ
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hDR : (0:ℝ) < D := by exact_mod_cast degreeRoot_pos Δ
  have hΔR : (0:ℝ) < Δ := by exact_mod_cast hpos
  have hcondition : (L:ℝ)^2*D ≤ 8*Δ := by exact_mod_cast root_condition hdegree hpos
  have hratio : (L:ℝ)^2/(8*Δ) ≤ 1/(D:ℝ) :=
    (div_le_div_iff₀ (by positivity) hDR).mpr (by simpa using hcondition)
  have hpower : (n:ℝ)^3 ≤ (D:ℝ)^p := by exact_mod_cast refinedThreshold_power (n := n) hlarge
  have hinv : 1/(D:ℝ)^p ≤ 1/(n:ℝ)^3 := one_div_le_one_div_of_le (by positivity) hpower
  have hqpow : ((L:ℝ)^2/(8*Δ))^p ≤ 1/(n:ℝ)^3 := by
    exact (pow_le_pow_left₀ (by positivity) hratio p).trans (by simpa [div_pow] using hinv)
  have hsmall : 2*(n:ℝ)*((L:ℝ)^2/(8*Δ))^p ≤ 2/(n:ℝ)^2 := by
    calc
      _ ≤ 2*(n:ℝ)*(1/(n:ℝ)^3) := mul_le_mul_of_nonneg_left hqpow (by positivity)
      _ = _ := by field_simp
  have ht := stochastic_refined_tail N hΔ hpos hsymm g hg hbalance T L p hT
  have hfirst := threshold_failure_bound hn
  change 2*(n:ℝ)/(2:ℝ)^L ≤ 1/(n:ℝ) at hfirst
  change uniformProb (badRefinedEvent N g T L p) ≤
    2*(n:ℝ)/(2:ℝ)^L + 2*(n:ℝ)*((L:ℝ)^2/(8*Δ))^p at ht
  have hnone : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hinv2 : 1/(n:ℝ)^2 ≤ 1/(n:ℝ) := one_div_le_one_div_of_le hnR (by nlinarith)
  change uniformProb (badRefinedEvent N g T L p) ≤ 3/(n:ℝ)
  calc
    _ ≤ 2*(n:ℝ)/(2:ℝ)^L + 2*(n:ℝ)*((L:ℝ)^2/(8*Δ))^p := ht
    _ ≤ 1/(n:ℝ) + 2/(n:ℝ)^2 := add_le_add hfirst hsmall
    _ ≤ 1/(n:ℝ) + 2*(1/(n:ℝ)) := by
      apply add_le_add_left
      calc
        2/(n:ℝ)^2 = 2*(1/(n:ℝ)^2) := by ring
        _ ≤ 2*(1/(n:ℝ)) := mul_le_mul_of_nonneg_left hinv2 (by norm_num)
    _ = 3/(n:ℝ) := by ring

end Carpooling
