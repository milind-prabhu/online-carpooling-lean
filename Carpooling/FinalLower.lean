import Carpooling.OnlineLower

namespace Carpooling
open Finset
open scoped Classical

/-- The stochastic lower bound for every admissible vertex count and degree.
The scale parameter a is any fixed integer ≥48 with 6 log₂ n ≤ a(Δ+1).
Thus Δ=Ω(log n) is represented with its constant explicitly visible.
The constructed graph has exactly n vertices and degree Δ. For every causal
online algorithm, with failure probability at most 10/(Δ+1), a discrepancy h
is attained and (log n/log Δ)^(1/3) ≤ (64a)^(1/3) h. -/
theorem theorem_1_3 (n d a : ℕ) (hd : 2 ≤ d) (hn : d < n)
    (heven : (n*d)%2 = 0) (ha48 : 48 ≤ a)
    (hscale : 6*Nat.log 2 n ≤ a*(d+1)) :
    ∃ (G : FiniteCarpoolGraph) (h : ℕ), StochasticLowerGuarantee n d a h G := by
  classical
  let N := d+1
  let M := n/N-1
  let r := N+n%N
  have hpar := padding_parameters hn heven
  change n = M*N+r ∧ N ≤ r ∧ r < 2*N ∧ (r*d)%2 = 0 at hpar
  rcases hpar with ⟨hsplit,hrlo,hrhi,hreven⟩
  have hN2 : 2 ≤ N := by dsimp [N]; omega
  have hNp : 0 < N := by omega
  have hrp : 0 < r := by omega
  have hdr : d < r := by dsimp [N] at hrlo; omega
  obtain ⟨H,hH⟩ := exists_regular_graph hdr hreven
  let V := (Fin M × Fin N) ⊕ Fin r
  let P : SimpleGraph V := paddedGraph (J := Fin M) (U := Fin N) H
  let G : FiniteCarpoolGraph := ⟨V,inferInstance,inferInstance,P⟩
  let q := Nat.log N M
  let h := cubicHeight a q
  have hap : 0 < a := by omega
  have hhp : 0 < h := cubicHeight_pos a q
  have hcard : Fintype.card V = n := by
    simp only [V,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hreg : P.IsRegularOfDegree d := by
    apply sum_regular _ H _ hH
    have hg := disjointCliques_regular (J := Fin M) (U := Fin N)
    simp only [Fintype.card_fin,N,Nat.add_sub_cancel] at hg
    convert hg using 1
  have hlogn : Nat.log N n ≤ 16*a*h^3 := by
    have hl := padding_log_compare hN2 (show 0 < n by omega)
      (show n < (M+2)*N by nlinarith)
    have hc := cubicHeight_covers (q := q) hap
    have hh3 : 1 ≤ h^3 := Nat.one_le_pow _ _ hhp
    change q < 8*a*h^3 at hc
    change Nat.log N n ≤ q+3 at hl
    nlinarith
  refine ⟨G,h,hcard,hreg,hhp,?_,?_⟩
  · exact cubic_log_rate hd hn hap hhp hlogn
  · intro R
    by_cases he : h = 1
    · rw [he,first_discrepancy_probability (show 0 < Fintype.card G.Vertex by change 0 < Fintype.card V; omega)
        R.run R.initial]
      positivity
    · have hheight : a*h^3 ≤ q := by
        rcases cubicHeight_spec (q := q) hap with hh | hh
        · exact False.elim (he hh)
        · exact hh
      have hM : 0 < M := by
        by_contra hm
        have hzero : M = 0 := by omega
        have hqzero : q = 0 := by simp [q,hzero]
        have hp : 0 < a*h^3 := Nat.mul_pos hap (pow_pos hhp 3)
        omega
      have hMn : M ≤ n := by
        have hm := Nat.mul_le_mul_left M (show 1 ≤ N by omega)
        simp only [mul_one] at hm
        omega
      have hq2 : q ≤ Nat.log 2 n := by
        have hp : 2^q ≤ n := (Nat.pow_le_pow_left hN2 q).trans
          ((Nat.pow_log_le_self N hM.ne').trans hMn)
        exact Nat.le_log_of_pow_le (by decide : 1 < 2) hp
      have hsize : 6*h^3 ≤ N := by
        have hm : a*(6*h^3) ≤ a*N := by dsimp [N]; nlinarith [hheight,hq2,hscale]
        by_contra hs
        have hgt := Nat.mul_lt_mul_of_pos_left (show N < 6*h^3 by omega) hap
        omega
      have hlog : 48*h^3 ≤ q := by
        have hm := Nat.mul_le_mul_right (h^3) ha48
        omega
      letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
      letI : Nonempty (⊤ : SimpleGraph (Fin N)).edgeSet :=
        ⟨⟨s((⟨0,by omega⟩ : Fin N),(⟨1,by omega⟩ : Fin N)),by simp⟩⟩
      have hE : 0 < Fintype.card H.edgeSet := by
        have hb := regular_edge_balance H hH
        simp only [Fintype.card_fin] at hb
        have hp := Nat.mul_pos hrp (show 0 < d by omega)
        omega
      letI : Nonempty H.edgeSet := Fintype.card_pos_iff.mp hE
      have hH' : H.IsRegularOfDegree (Fintype.card (Fin N)-1) := by
        simpa only [Fintype.card_fin,N,Nat.add_sub_cancel] using hH
      have hp := padded_graph_lower_logarithmic (J := Fin M) (U := Fin N) H hH' hhp
        (by simpa only [Fintype.card_fin] using hsize)
        (by simpa only [Fintype.card_fin] using le_of_lt hrhi)
        (by simpa only [Fintype.card_fin,q] using hlog)
        R.run R.initial R.request R.causal
      simpa only [Fintype.card_fin,N] using hp

end Carpooling
