import Carpooling.RefinedWitnesses

namespace Carpooling
open Finset
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma multiset_choose_card {A : Type*} (S : Multiset A) {p : ℕ} (hp : p ≤ S.card) :
    ∃ Q : Multiset A, Q ≤ S ∧ Q.card = p := by
  induction p generalizing S with
  | zero => exact ⟨0,zero_le _,rfl⟩
  | succ p ih =>
    have hne : S ≠ 0 := by intro h; simp [h] at hp
    obtain ⟨a,ha⟩ := Multiset.exists_mem_of_ne_zero hne
    obtain ⟨W,rfl⟩ := Multiset.exists_cons_of_mem ha
    obtain ⟨Q,hQ,hcard⟩ := ih W (by simpa using hp)
    exact ⟨a ::ₘ Q, Multiset.cons_le_cons a hQ, by simp [hcard]⟩

section Samples
variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- The refined witness cover is constructed, not supplied as an assumption. -/
theorem refined_cover_of_forest {N : V → Finset V} {g : E → Sym2 V} {T p : ℕ}
    (x : Fin T → E) {root : V} {F : Tree V}
    (hF : Witness.Valid (fun u v => v ∈ N u) root F)
    (hbag : Witness.edges root F ≤ sampleBag g x)
    (hp : p ≤ F.numNodes - ((Witness.vertices root F).card-1)) :
    x ∈ refinedWitnessEvent N g T (Witness.vertices root F).card p := by
  let m := (Witness.vertices root F).card
  obtain ⟨G,hG,hcore,hverts,hnum⟩ := Witness.spanning hF
  have hnodes : G.numNodes = m-1 := by omega
  obtain ⟨W,hW⟩ := Multiset.le_iff_exists_add.mp hcore
  have hcard := congrArg Multiset.card hW
  simp only [Multiset.card_add,Witness.edges_card] at hcard
  have hpW : p ≤ W.card := by omega
  obtain ⟨Q,hQ,hQcard⟩ := multiset_choose_card W hpW
  have hQF : Q ≤ Witness.edges root F := by
    rw [hW]
    exact hQ.trans (Multiset.le_add_left _ _)
  have hsupport : ∀ e ∈ Q, ∀ v ∈ e, v ∈ Witness.vertices root G := by
    intro e he v hv
    rw [hverts]
    exact Witness.edges_support (Multiset.mem_of_le hQF he) hv
  obtain ⟨code,hcode⟩ := Witness.encode_extras (show G.numNodes+1=m from hnum) Q hQcard hsupport
  apply mem_biUnion.mpr
  refine ⟨((root,G),code), mem_product.mpr ⟨Witness.mem_families hG hnodes,mem_univ _⟩, ?_⟩
  apply mem_bagOccurrence
  change Witness.edges root G + Witness.extraBag root G code ≤ sampleBag g x
  rw [hcode]
  apply le_trans _ hbag
  rw [hW]
  exact add_le_add_left hQ _

noncomputable def badRefinedEvent (N : V → Finset V) (g : E → Sym2 V) (T L p : ℕ) : Finset (Fin T → E) :=
  univ.filter fun x => ∃ t ≤ T, ∃ R : Run V t,
    (∀ k, R.d 0 k = 0) ∧
    (∀ s (hs : s < t), (R.step s hs).v ∈ N (R.step s hs).u) ∧
    R.edgeBag t ≤ sampleBag g x ∧
    ∃ k, 4*(p : ℝ)^((1:ℝ)/3) + 2*(Nat.log 2 L : ℝ) < |R.d t k|

theorem refined_bad_event_cover (N : V → Finset V)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v) (g : E → Sym2 V) (T L p : ℕ) :
    badRefinedEvent N g T L p ⊆
      ((Ico L (T+1)).biUnion fun r => witnessEvent N g T r) ∪
      ((Ico 1 (L+1)).biUnion fun m => refinedWitnessEvent N g T m p) := by
  intro x hx
  obtain ⟨t,ht,R,hi,hAdj,hbag,k,hbad⟩ := (mem_filter.mp hx).2
  obtain ⟨F,hF,he,hv⟩ := R.component_witness (fun u v => v ∈ N u) hsymm hAdj (le_refl t) k
  have hFbag : Witness.edges k F ≤ sampleBag g x := by
    rw [he]
    exact (Multiset.filter_le _ _).trans hbag
  have hrT : F.numNodes ≤ T := by simpa using Multiset.card_le_card hFbag
  by_cases hlarge : L ≤ F.numNodes
  · apply mem_union_left
    apply mem_biUnion.mpr
    refine ⟨F.numNodes,mem_Ico.mpr ⟨hlarge,by omega⟩,?_⟩
    apply mem_biUnion.mpr
    exact ⟨(k,F),Witness.mem_families hF rfl,mem_bagOccurrence g _ x hFbag⟩
  · let m := (Witness.vertices k F).card
    obtain ⟨G,hG,hcore,hvG,hnum⟩ := Witness.spanning hF
    have hGle : G.numNodes ≤ F.numNodes := by simpa using Multiset.card_le_card hcore
    have hmpos : 1 ≤ m := by omega
    have hmL : m ≤ L := by omega
    have hcnt : internalCount R ((R.clusters t).block k) t = F.numNodes := by
      rw [← R.selected_card _ (R.terminal_closed k) (le_refl t),← he,Witness.edges_card]
    have hmcard : ((R.clusters t).block k).card = m := by rw [← hv]
    have hp : p ≤ F.numNodes - (m-1) := by
      by_contra hn
      have hple : F.numNodes - (m-1) ≤ p := by omega
      have hc : ((F.numNodes-(m-1) : ℕ) : ℝ)^((1:ℝ)/3) ≤ (p : ℝ)^((1:ℝ)/3) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hple) (by norm_num)
      have hl : (Nat.log 2 m : ℝ) ≤ Nat.log 2 L := by exact_mod_cast Nat.log_mono_right hmL
      have hbound := local_tree_like_bound R hi k
      rw [hcnt,hmcard] at hbound
      linarith
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨m,mem_Ico.mpr ⟨hmpos,by omega⟩,?_⟩
    exact refined_cover_of_forest x hF hFbag hp

theorem large_witness_tail (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (T L : ℕ) (hT : 16*T ≤ Fintype.card V) :
    uniformProb ((Ico L (T+1)).biUnion fun r => witnessEvent N g T r) ≤ 2 * Fintype.card V / (2 : ℝ)^L := by
  have hM : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hbal : (2 : ℝ)*Fintype.card E = Fintype.card V * (Δ : ℝ) := by exact_mod_cast hbalance
  have hTr : (16 : ℝ)*T ≤ Fintype.card V := by exact_mod_cast hT
  have hq : 4*(Δ : ℝ)*T / Fintype.card E ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ hM).mpr
    have hd : 0 ≤ (Δ : ℝ) := Nat.cast_nonneg _
    have hm := mul_le_mul_of_nonneg_right hTr hd
    nlinarith
  have hu := uniformProb_biUnion_le (Ico L (T+1)) (fun r => witnessEvent N g T r)
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

lemma uniformProb_union_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (A B : Finset Ω) :
    uniformProb (A ∪ B) ≤ uniformProb A + uniformProb B := by
  unfold uniformProb
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast card_union_le A B) (Nat.cast_nonneg _)

theorem refined_witness_regular_bound (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (T m p : ℕ) (hT : 16*T ≤ Fintype.card V) :
    uniformProb (refinedWitnessEvent N g T m p) ≤
      (Fintype.card V : ℝ) * ((1:ℝ)/2)^(m-1) * ((m:ℝ)^2/(8*Δ))^p := by
  have hM : (0 : ℝ) < Fintype.card E := by exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < Δ := by exact_mod_cast hpos
  have hbal : (2:ℝ)*Fintype.card E = Fintype.card V * (Δ:ℝ) := by exact_mod_cast hbalance
  have hTr : (16:ℝ)*T ≤ Fintype.card V := by exact_mod_cast hT
  have hm := mul_le_mul_of_nonneg_right hTr hD.le
  have hq1 : 4*(Δ:ℝ)*T/Fintype.card E ≤ (1:ℝ)/2 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith
  have hq2 : (m:ℝ)^2*T/Fintype.card E ≤ (m:ℝ)^2/(8*Δ) := by
    apply (div_le_div_iff₀ hM (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_left (show 8*(Δ:ℝ)*T ≤ Fintype.card E by nlinarith) (sq_nonneg (m:ℝ))
    nlinarith
  have heq : ((4:ℝ)^(m-1)*Fintype.card V*(Δ:ℝ)^(m-1)*(m:ℝ)^(2*p))*
      ((T:ℝ)/Fintype.card E)^(m-1+p) =
      (Fintype.card V:ℝ)*(4*(Δ:ℝ)*T/Fintype.card E)^(m-1)*
        ((m:ℝ)^2*T/Fintype.card E)^p := by
    simp only [pow_add,mul_pow,div_pow,pow_mul]
    ring
  have hh := refined_witness_probability N hΔ g hg T m p
  rw [heq] at hh
  exact hh.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq1 (m-1)) (Nat.cast_nonneg _))
    (pow_le_pow_left₀ (by positivity) hq2 p) (by positivity) (by positivity))

/-- Full finite-sample refined stochastic bound. Both the large-component failure
and the surplus-edge failure are explicit; no witness estimate is assumed. -/
theorem stochastic_refined_tail (N : V → Finset V) {Δ : ℕ}
    (hΔ : ∀ v, (N v).card ≤ Δ) (hpos : 0 < Δ)
    (hsymm : ∀ {u v}, v ∈ N u → u ∈ N v)
    (g : E → Sym2 V) (hg : Function.Injective g)
    (hbalance : 2 * Fintype.card E = Fintype.card V * Δ)
    (T L p : ℕ) (hT : 16*T ≤ Fintype.card V) :
    uniformProb (badRefinedEvent N g T L p) ≤
      2*Fintype.card V/(2:ℝ)^L + 2*Fintype.card V*((L:ℝ)^2/(8*Δ))^p := by
  have hc := (uniformProb_mono (refined_bad_event_cover N hsymm g T L p)).trans
    (uniformProb_union_le _ _)
  have hlarge := large_witness_tail N hΔ hpos hsymm g hg hbalance T L hT
  have hsmallU := uniformProb_biUnion_le (Ico 1 (L+1)) (fun m => refinedWitnessEvent N g T m p)
  have hsmall : (∑ m ∈ Ico 1 (L+1), uniformProb (refinedWitnessEvent N g T m p)) ≤
      2*Fintype.card V*((L:ℝ)^2/(8*Δ))^p := by
    have hD : (0:ℝ) < Δ := by exact_mod_cast hpos
    have hsum : (∑ m ∈ Ico 1 (L+1), ((1:ℝ)/2)^(m-1)) ≤ 2 := by
      rw [sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
      have hh := geom_sum_Ico_le_of_lt_one (m := 0) (n := L)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1)
      norm_num at hh
      simpa only [Nat.Ico_zero_eq_range] using hh
    calc
      _ ≤ ∑ m ∈ Ico 1 (L+1), (Fintype.card V:ℝ)*((1:ℝ)/2)^(m-1)*((L:ℝ)^2/(8*Δ))^p := by
        apply sum_le_sum
        intro m hm
        have hml : (m:ℝ) ≤ L := by exact_mod_cast (show m ≤ L by have := (mem_Ico.mp hm).2; omega)
        have hratio : (m:ℝ)^2/(8*Δ) ≤ (L:ℝ)^2/(8*Δ) :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hml 2) (by positivity)
        exact (refined_witness_regular_bound N hΔ hpos g hg hbalance T m p hT).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio p) (by positivity))
      _ = (Fintype.card V:ℝ)*((L:ℝ)^2/(8*Δ))^p * ∑ m ∈ Ico 1 (L+1), ((1:ℝ)/2)^(m-1) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro m _; ring
      _ ≤ (Fintype.card V:ℝ)*((L:ℝ)^2/(8*Δ))^p * 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  exact hc.trans (add_le_add hlarge (hsmallU.trans hsmall))

end Samples
end Carpooling
