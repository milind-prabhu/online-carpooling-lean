import Carpooling.WeightedOccupancy

namespace Carpooling
open Finset
open scoped Classical
variable {Ω J : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
 [Fintype J] [DecidableEq J] [Nonempty J]

noncomputable def populated (c : Ω → J → ℕ) (L : ℕ) (x : Ω) : Finset J :=
  univ.filter fun j => L ≤ c x j

noncomputable def lowCountEvent (c : Ω → J → ℕ) (L : ℕ) (j : J) : Finset Ω :=
  univ.filter fun x => c x j < L

lemma lowCount_probability (c : Ω → J → ℕ) {N L : ℕ} (hN : 0 < N) (hL : 2*L ≤ N)
    (hv : ∀ j, uniformMean (fun x => ((c x j:ℝ)-N)^2) ≤ (N:ℝ)) (j : J) :
    uniformProb (lowCountEvent c L j) ≤ 4/(N:ℝ) := by
  have hpoint : ∀ x, eventIndicator (lowCountEvent c L j) x*(N:ℝ)^2 ≤ 4*((c x j:ℝ)-N)^2 := by
    intro x
    by_cases hx : c x j < L
    · have hlow : 2*(c x j:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 2*c x j ≤ N)
      have hn : (0:ℝ) ≤ c x j := Nat.cast_nonneg _
      simp only [eventIndicator,lowCountEvent,mem_filter,mem_univ,true_and,if_pos hx]
      nlinarith [sq_nonneg ((N:ℝ)-2*(c x j:ℝ))]
    · simp [eventIndicator,lowCountEvent,hx,sq_nonneg]
  have hb := uniformMean_mono hpoint
  rw [uniformMean_mul_const,uniformMean_indicator,uniformMean_const_mul] at hb
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hNR).mpr
  apply (mul_le_mul_iff_left₀ hNR).mp
  nlinarith [hv j]

noncomputable def fewPopulated (c : Ω → J → ℕ) (L : ℕ) : Finset Ω :=
  univ.filter fun x => 2*(populated c L x).card < Fintype.card J

theorem fewPopulated_probability (c : Ω → J → ℕ) {N L : ℕ}
    (hN : 0 < N) (hL : 2*L ≤ N)
    (hv : ∀ j, uniformMean (fun x => ((c x j:ℝ)-N)^2) ≤ (N:ℝ)) :
    uniformProb (fewPopulated c L) ≤ 8/(N:ℝ) := by
  have hbadcount : ∀ x, (∑ j, eventIndicator (lowCountEvent c L j) x) =
      (Fintype.card J:ℝ)-(populated c L x).card := by
    intro x
    have hcomp : (univ.filter fun j => c x j < L) = univ \ populated c L x := by
      ext j; simp [populated,not_le]
    have hcard : (populated c L x).card ≤ Fintype.card J := card_le_univ _
    simp only [eventIndicator,lowCountEvent,mem_filter,mem_univ,true_and]
    rw [sum_boole,hcomp,card_sdiff]
    simp [Nat.cast_sub hcard]
  have hpoint : ∀ x, eventIndicator (fewPopulated c L) x*(Fintype.card J:ℝ) ≤
      2*∑ j, eventIndicator (lowCountEvent c L j) x := by
    intro x
    rw [hbadcount]
    by_cases hx : 2*(populated c L x).card < Fintype.card J
    · have hxR : 2*((populated c L x).card:ℝ) < (Fintype.card J:ℝ) := by exact_mod_cast hx
      simp only [eventIndicator,fewPopulated,mem_filter,mem_univ,true_and,if_pos hx]
      linarith
    · have hcard : ((populated c L x).card:ℝ) ≤ (Fintype.card J:ℝ) := by exact_mod_cast card_le_univ (populated c L x)
      simp only [eventIndicator,fewPopulated,mem_filter,mem_univ,true_and,if_neg hx,zero_mul]
      linarith
  have hb := uniformMean_mono hpoint
  rw [uniformMean_mul_const,uniformMean_indicator,uniformMean_const_mul,uniformMean_sum] at hb
  simp only [uniformMean_indicator] at hb
  have hs : (∑ j, uniformProb (lowCountEvent c L j)) ≤ (Fintype.card J:ℝ)*(4/(N:ℝ)) := by
    calc
      _ ≤ ∑ _j : J, (4/(N:ℝ)) := sum_le_sum (fun j _ => lowCount_probability c hN hL hv j)
      _ = _ := by simp
  have hM : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    _ ≤ 2*∑ j, uniformProb (lowCountEvent c L j) := by simpa only [mul_comm] using hb
    _ ≤ 2*((Fintype.card J:ℝ)*(4/(N:ℝ))) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end Carpooling
