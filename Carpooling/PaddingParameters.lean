import Carpooling.RegularExistence
import Carpooling.LowerThresholds
import Mathlib.Data.Nat.Find

namespace Carpooling
open Finset
open scoped Classical

theorem padding_parameters {n d : ℕ} (hd : d < n) (heven : (n*d)%2 = 0) :
    let N := d+1
    let M := n/N-1
    let r := N+n%N
    n = M*N+r ∧ N ≤ r ∧ r < 2*N ∧ (r*d)%2 = 0 := by
  dsimp
  let N := d+1
  let M := n/N-1
  let r := N+n%N
  have hN : 0 < N := by dsimp [N]; omega
  have hq : 1 ≤ n/N := Nat.one_le_div_iff hN |>.mpr (by dsimp [N]; omega)
  have hq' : n/N = M+1 := by dsimp [M]; omega
  have hrem := Nat.mod_lt n hN
  have hsum := Nat.mod_add_div n N
  rw [hq'] at hsum
  have hsplit : n = M*N+r := by dsimp [r]; nlinarith
  have hNd : (N*d)%2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one d with he | he <;> simp [N,Nat.mul_mod,he,Nat.add_mod]
  have hMd : (M*N*d)%2 = 0 := by simp [Nat.mul_assoc,Nat.mul_mod,hNd]
  have hrEven : (r*d)%2 = 0 := by
    rw [hsplit,Nat.add_mul,Nat.add_mod,hMd,Nat.zero_add,Nat.mod_mod] at heven
    exact heven
  have hlow : N ≤ r := by dsimp [r]; omega
  have hhigh : r < 2*N := by dsimp [r]; omega
  exact ⟨hsplit,hlow,hhigh,hrEven⟩

def cubicHeight (a q : ℕ) : ℕ := max 1 (Nat.findGreatest (fun h => h^3 ≤ q/a) (q/a))

lemma cubicHeight_pos (a q : ℕ) : 0 < cubicHeight a q := by unfold cubicHeight; omega

lemma cubicHeight_spec {a q : ℕ} (ha : 0 < a) :
    cubicHeight a q = 1 ∨ a*(cubicHeight a q)^3 ≤ q := by
  let b := q/a
  let h := Nat.findGreatest (fun h => h^3 ≤ b) b
  have hh : h^3 ≤ b := Nat.findGreatest_spec (P := fun h => h^3 ≤ b) (Nat.zero_le b) (by simp)
  by_cases he : h ≤ 1
  · left; dsimp [cubicHeight,h,b] at *; omega
  · right
    have heq : cubicHeight a q = h := by dsimp [cubicHeight,h,b] at *; omega
    rw [heq]
    have hdiv := Nat.div_mul_le_self q a
    dsimp [b] at hh
    nlinarith [Nat.mul_le_mul_left a hh]

lemma cubicHeight_covers {a q : ℕ} (ha : 0 < a) :
    q < 8*a*(cubicHeight a q)^3 := by
  let b := q/a
  let h := Nat.findGreatest (fun h => h^3 ≤ b) b
  have hroot : b < (h+1)^3 := by
    by_cases hb : h+1 ≤ b
    · exact lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun h => h^3 ≤ b) (n := b) (k := h+1) (by omega : h < h+1) hb)
    · have hp : h+1 ≤ (h+1)^3 := by
        simpa using Nat.pow_le_pow_right (by omega : 0 < h+1) (by decide : 1 ≤ 3)
      omega
  have hH : h+1 ≤ 2*cubicHeight a q := by dsimp [cubicHeight,h,b] at *; omega
  have hp := Nat.pow_le_pow_left hH 3
  have hq : q < a*(b+1) := by
    have hr := Nat.mod_lt q ha
    have he := Nat.mod_add_div q a
    dsimp [b]
    nlinarith
  have hm := Nat.mul_le_mul_left a (show b+1 ≤ (h+1)^3 by omega)
  have hm' := Nat.mul_le_mul_left a hp
  nlinarith

lemma padding_log_compare {n N M : ℕ} (hN : 2 ≤ N) (hn : 0 < n)
    (hsplit : n < (M+2)*N) : Nat.log N n ≤ Nat.log N M+3 := by
  let q := Nat.log N M
  have hp := Nat.lt_pow_succ_log_self (show 1 < N by omega) M
  have hMp : M+1 ≤ N^(q+1) := by simpa [q] using hp
  have hNN : 2*N ≤ N^2 := by nlinarith
  have hmul := Nat.mul_le_mul_left (N^(q+1)) hNN
  have hmp := Nat.mul_le_mul_right (2*N) hMp
  have hpow : n < N^(q+3) := by
    have he : N^(q+3) = N^(q+1)*N^2 := by rw [←pow_add]
    rw [he]
    have hn2 : n < 2*(M+1)*N := by nlinarith
    nlinarith
  have hl := Nat.log_lt_of_lt_pow hn.ne' hpow
  dsimp [q] at hl
  omega

end Carpooling
