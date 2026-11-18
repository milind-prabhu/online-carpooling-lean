import Carpooling.Amplification

/-! Direct fixed-horizon occupancy estimates. Poissonization is not required. -/
namespace Carpooling
open Finset
open scoped Classical
variable {Ω A : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
  [Fintype A] [DecidableEq A]

lemma indicator_sum_variance (B : A → Finset Ω) (p : ℝ)
    (hfirst : ∀ a, uniformProb (B a) = p)
    (hsecond : ∀ a b, a ≠ b → uniformProb (B a ∩ B b) = p^2) :
    uniformMean (fun x => (∑ a, (eventIndicator (B a) x-p))^2) =
      (Fintype.card A:ℝ)*p*(1-p) := by
  have hmoment : ∀ a b,
      uniformMean (fun x => (eventIndicator (B a) x-p)*(eventIndicator (B b) x-p)) =
        if a = b then p*(1-p) else 0 := by
    intro a b
    have hexpand : (fun x => (eventIndicator (B a) x-p)*(eventIndicator (B b) x-p)) =
        (fun x => eventIndicator (B a) x*eventIndicator (B b) x -
          p*eventIndicator (B a) x - p*eventIndicator (B b) x + p*p) := by
      funext x; ring
    rw [hexpand]
    simp only [uniformMean_add,uniformMean_sub,uniformMean_const_mul,
      eventIndicator_mul,uniformMean_indicator,uniformMean_const,hfirst]
    by_cases hab : a = b
    · subst b; simp [hfirst] <;> ring
    · rw [if_neg hab,hsecond a b hab]; ring
  have he : (fun x => (∑ a, (eventIndicator (B a) x-p))^2) =
      (fun x => ∑ a, ∑ b, (eventIndicator (B a) x-p)*(eventIndicator (B b) x-p)) := by
    funext x
    simp only [pow_two,sum_mul_sum]
  rw [he,uniformMean_sum]
  simp_rw [uniformMean_sum,hmoment]
  simp [mul_assoc]

section Labels
variable {J : Type*} [Fintype J] [DecidableEq J] [Nonempty J]

noncomputable def labelEvent {T : ℕ} (j : J) (t : Fin T) : Finset (Fin T → J) :=
  univ.filter fun x => x t = j

lemma labelEvent_eq_selected {T : ℕ} (j : J) (t : Fin T) :
    labelEvent j t = selectedMatchingEvent {t} (fun _ _ => j) := by
  ext x
  simp [labelEvent,selectedMatchingEvent]

lemma labelEvent_probability {T : ℕ} (j : J) (t : Fin T) :
    uniformProb (labelEvent j t) = 1/(Fintype.card J:ℝ) := by
  rw [labelEvent_eq_selected,selected_matching_probability]
  simp

lemma labelEvent_pair_probability {T : ℕ} (j : J) (s t : Fin T) (hst : s ≠ t) :
    uniformProb (labelEvent j s ∩ labelEvent j t) = (1/(Fintype.card J:ℝ))^2 := by
  rw [labelEvent_eq_selected,labelEvent_eq_selected,←selectedMatchingEvent_union,
    selected_matching_probability]
  simp [hst,Ne.symm hst,div_pow]

noncomputable def occupancy {T : ℕ} (x : Fin T → J) (j : J) : ℕ :=
  (univ.filter fun t => x t = j).card

lemma occupancy_eq_sum {T : ℕ} (x : Fin T → J) (j : J) :
    (occupancy x j:ℝ) = ∑ t, eventIndicator (labelEvent j t) x := by
  simp [occupancy,eventIndicator,labelEvent]

/-- With M labels and MN iid uniform samples, each label's count has variance
N(1-1/M), in particular at most N. -/
theorem occupancy_variance (N : ℕ) (j : J) :
    uniformMean (fun x : Fin (Fintype.card J*N) → J =>
      ((occupancy x j:ℝ)-(N:ℝ))^2) ≤ (N:ℝ) := by
  have hM : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hcenter : ∀ x : Fin (Fintype.card J*N) → J,
      (occupancy x j:ℝ)-(N:ℝ) =
        ∑ t, (eventIndicator (labelEvent j t) x-1/(Fintype.card J:ℝ)) := by
    intro x
    rw [sum_sub_distrib,←occupancy_eq_sum]
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul]
    field_simp
  simp_rw [hcenter]
  rw [indicator_sum_variance (labelEvent j) _ (labelEvent_probability j)
    (fun s t hst => labelEvent_pair_probability j s t hst)]
  simp only [Fintype.card_fin,Nat.cast_mul]
  have heq : (Fintype.card J:ℝ)*N*(1/(Fintype.card J:ℝ)) = (N:ℝ) := by field_simp
  rw [heq]
  have hnonneg : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hfrac : (0:ℝ) ≤ 1/(Fintype.card J:ℝ) := le_of_lt (one_div_pos.mpr hM)
  nlinarith

noncomputable def underfilledEvent (N L : ℕ) (j : J) :
    Finset (Fin (Fintype.card J*N) → J) := univ.filter fun x => occupancy x j < L

/-- A weak Chebyshev bound is sufficient for the paper's high-probability
lower bound: a label receives fewer than L requests with probability ≤4/N. -/
theorem underfilled_probability {N L : ℕ} (hN : 0 < N) (hL : 2*L ≤ N) (j : J) :
    uniformProb (underfilledEvent N L j) ≤ 4/(N:ℝ) := by
  have hpoint : ∀ x : Fin (Fintype.card J*N) → J,
      eventIndicator (underfilledEvent N L j) x*(N:ℝ)^2 ≤
        4*((occupancy x j:ℝ)-(N:ℝ))^2 := by
    intro x
    by_cases hx : occupancy x j < L
    · have hlow : 2*(occupancy x j:ℝ) ≤ (N:ℝ) := by exact_mod_cast (by omega : 2*occupancy x j ≤ N)
      have hcount : (0:ℝ) ≤ occupancy x j := Nat.cast_nonneg _
      simp only [eventIndicator,underfilledEvent,mem_filter,mem_univ,true_and,if_pos hx]
      nlinarith [sq_nonneg ((N:ℝ)-2*(occupancy x j:ℝ))]
    · simp [eventIndicator,underfilledEvent,hx,sq_nonneg]
  have hb := uniformMean_mono hpoint
  rw [uniformMean_mul_const,uniformMean_indicator,uniformMean_const_mul] at hb
  have hv := occupancy_variance N j
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hNR).mpr
  apply (mul_le_mul_iff_left₀ hNR).mp
  nlinarith

noncomputable def goodLabels {T : ℕ} (x : Fin T → J) (L : ℕ) : Finset J :=
  univ.filter fun j => L ≤ occupancy x j

noncomputable def fewGoodLabelsEvent (N L : ℕ) : Finset (Fin (Fintype.card J*N) → J) :=
  univ.filter fun x => 2*(goodLabels x L).card < Fintype.card J

/-- With probability at least 1-8/N, at least half of all labels receive at
least L requests, provided 2L≤N. No independence across label counts is used. -/
theorem few_good_labels_probability {N L : ℕ} (hN : 0 < N) (hL : 2*L ≤ N) :
    uniformProb (fewGoodLabelsEvent (J := J) N L) ≤ 8/(N:ℝ) := by
  have hbadcount : ∀ x : Fin (Fintype.card J*N) → J,
      (∑ j, eventIndicator (underfilledEvent N L j) x) =
        (Fintype.card J:ℝ)-(goodLabels x L).card := by
    intro x
    have hcomp : (univ.filter fun j => occupancy x j < L) = univ \ goodLabels x L := by
      ext j
      simp [goodLabels,not_le]
    have hcard : (goodLabels x L).card ≤ Fintype.card J := card_le_univ _
    simp only [eventIndicator,underfilledEvent,mem_filter,mem_univ,true_and]
    rw [sum_boole,hcomp,card_sdiff]
    simp [Nat.cast_sub hcard]
  have hpoint : ∀ x : Fin (Fintype.card J*N) → J,
      eventIndicator (fewGoodLabelsEvent N L) x*(Fintype.card J:ℝ) ≤
        2*∑ j, eventIndicator (underfilledEvent N L j) x := by
    intro x
    rw [hbadcount]
    by_cases hx : 2*(goodLabels x L).card < Fintype.card J
    · have hxR : 2*((goodLabels x L).card:ℝ) < (Fintype.card J:ℝ) := by exact_mod_cast hx
      simp only [eventIndicator,fewGoodLabelsEvent,mem_filter,mem_univ,true_and,if_pos hx]
      linarith
    · have hcard : ((goodLabels x L).card:ℝ) ≤ (Fintype.card J:ℝ) := by exact_mod_cast card_le_univ (goodLabels x L)
      simp only [eventIndicator,fewGoodLabelsEvent,mem_filter,mem_univ,true_and,if_neg hx,zero_mul]
      linarith
  have hb := uniformMean_mono hpoint
  rw [uniformMean_mul_const,uniformMean_indicator,uniformMean_const_mul,uniformMean_sum] at hb
  simp only [uniformMean_indicator] at hb
  have hs : (∑ j : J, uniformProb (underfilledEvent N L j)) ≤
      (Fintype.card J:ℝ)*(4/(N:ℝ)) := by
    calc
      _ ≤ ∑ _j : J, (4/(N:ℝ)) := sum_le_sum (fun j _ => underfilled_probability hN hL j)
      _ = _ := by simp
  have hM : (0:ℝ) < Fintype.card J := by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hM).mp
  calc
    _ ≤ 2 * ∑ j : J, uniformProb (underfilledEvent N L j)  := by simpa only [mul_comm] using hb
    _ ≤ 2 * ((Fintype.card J:ℝ)*(4/(N:ℝ))) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end Labels
end Carpooling
