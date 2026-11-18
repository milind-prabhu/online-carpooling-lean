import Carpooling.RegularGraphs
import Mathlib.Algebra.Group.Fin.Basic

namespace Carpooling
open Finset
open scoped Classical

section Jumps
variable {r : ℕ} [NeZero r]

def jumpGraph (S : Finset (Fin r)) (hzero : (0:Fin r) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) : SimpleGraph (Fin r) where
  Adj x y := y-x ∈ S
  symm := by intro x y h; simpa using hneg (y-x) h
  loopless := by intro x h; exact hzero (by simpa using h)

theorem jumpGraph_regular (S : Finset (Fin r)) (hzero : (0:Fin r) ∉ S)
    (hneg : ∀ x ∈ S, -x ∈ S) :
    (jumpGraph S hzero hneg).IsRegularOfDegree S.card := by
  intro x
  let e : (jumpGraph S hzero hneg).neighborSet x ≃ S := {
    toFun := fun y => ⟨y.val-x,y.property⟩
    invFun := fun z => ⟨z.val+x,by simpa [jumpGraph] using z.property⟩
    left_inv := by intro y; apply Subtype.ext; simp
    right_inv := by intro z; apply Subtype.ext; simp }
  rw [←SimpleGraph.card_neighborSet_eq_degree]
  simpa using Fintype.card_congr e

def positiveJump (k : ℕ) (hk : 2*k < r) (i : Fin k) : Fin r :=
  ⟨i.val+1,by omega⟩

lemma positiveJump_injective (k : ℕ) (hk : 2*k < r) :
    Function.Injective (positiveJump k hk) := by
  intro i j hij
  apply Fin.ext
  have he := congrArg (fun z : Fin r => z.val) hij
  dsimp [positiveJump] at he
  omega

lemma positiveJump_ne_zero (k : ℕ) (hk : 2*k < r) (i : Fin k) :
    positiveJump k hk i ≠ 0 := by
  intro he
  have hv := congrArg (fun z : Fin r => z.val) he
  dsimp [positiveJump] at hv
  omega

lemma neg_positiveJump_val (k : ℕ) (hk : 2*k < r) (i : Fin k) :
    (-positiveJump k hk i).val = r-(i.val+1) := by
  change (r-(i.val+1))%r = r-(i.val+1)
  apply Nat.mod_eq_of_lt
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  omega

end Jumps

/-- Every admissible pair (r,d) has a d-regular simple graph on exactly r
vertices. The explicit construction uses paired positive/negative jumps,
and adds the antipodal jump when d is odd. -/
theorem exists_regular_graph {r d : ℕ} (hd : d < r) (heven : (r*d)%2 = 0) :
    ∃ G : SimpleGraph (Fin r), G.IsRegularOfDegree d := by
  classical
  have hr : 0 < r := by omega
  letI : NeZero r := ⟨hr.ne'⟩
  let k := d/2
  have hk : 2*k < r := by dsimp [k]; omega
  let S : Finset (Fin r) := univ.image (positiveJump k hk)
  let A := S ∪ S.image (fun x => -x)
  have hScard : S.card = k := by simp [S,card_image_of_injective _ (positiveJump_injective k hk)]
  have hSzero : (0:Fin r) ∉ S := by
    intro h
    obtain ⟨i,_,hi⟩ := mem_image.mp h
    exact positiveJump_ne_zero k hk i hi
  have hSdisjoint : Disjoint S (S.image (fun x => -x)) := by
    apply disjoint_left.mpr
    intro z hz hn
    obtain ⟨i,_,hi⟩ := mem_image.mp hz
    obtain ⟨w,hw,hneg⟩ := mem_image.mp hn
    obtain ⟨j,_,hj⟩ := mem_image.mp hw
    have he : positiveJump k hk i = -positiveJump k hk j := by rw [hi,hj,hneg]
    have hv := congrArg (fun z : Fin r => z.val) he
    change (positiveJump k hk i).val = (-positiveJump k hk j).val at hv
    rw [neg_positiveJump_val] at hv
    dsimp [positiveJump] at hv
    omega
  have hAcard : A.card = 2*k := by
    dsimp [A]
    rw [card_union_of_disjoint hSdisjoint,card_image_of_injective _ neg_injective,hScard]
    omega
  have hAzero : (0:Fin r) ∉ A := by
    simp only [A,mem_union,mem_image]
    rintro (hz | ⟨x,hx,hneg⟩)
    · exact hSzero hz
    · have he : x = 0 := neg_eq_zero.mp hneg
      exact hSzero (he ▸ hx)
  have hAneg : ∀ x ∈ A, -x ∈ A := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact mem_union_right _ (mem_image.mpr ⟨x,hx,rfl⟩)
    · obtain ⟨y,hy,he⟩ := mem_image.mp hx
      rw [←he,neg_neg]
      exact mem_union_left _ hy
  by_cases hodd : d%2 = 1
  · have hre : r%2 = 0 := by simpa [Nat.mul_mod,hodd] using heven
    have hr2 : 2 ≤ r := by omega
    let mid : Fin r := ⟨r/2,by omega⟩
    have hmidzero : mid ≠ 0 := by
      intro he
      have hv := congrArg (fun z : Fin r => z.val) he
      change r/2 = 0 at hv
      omega
    have hmidneg : -mid = mid := by
      apply Fin.ext
      change (r-r/2)%r = r/2
      rw [Nat.mod_eq_of_lt (by omega : r-r/2 < r)]
      omega
    have hmidS : mid ∉ S := by
      intro h
      obtain ⟨i,_,hi⟩ := mem_image.mp h
      have hv := congrArg (fun z : Fin r => z.val) hi
      change i.val+1 = r/2 at hv
      dsimp [k] at *
      omega
    have hmidA : mid ∉ A := by
      intro h
      rcases mem_union.mp h with h | h
      · exact hmidS h
      · obtain ⟨x,hx,he⟩ := mem_image.mp h
        have hxmid : x = mid := by simpa [hmidneg] using congrArg Neg.neg he
        exact hmidS (hxmid ▸ hx)
    let B := insert mid A
    have hBzero : (0:Fin r) ∉ B := by simpa [B,hAzero] using Ne.symm hmidzero
    have hBneg : ∀ x ∈ B, -x ∈ B := by
      intro x hx
      rcases mem_insert.mp hx with hx | hx
      · subst x; rw [hmidneg]; exact mem_insert_self _ _
      · exact mem_insert_of_mem (hAneg x hx)
    refine ⟨jumpGraph B hBzero hBneg,?_⟩
    have hb := jumpGraph_regular B hBzero hBneg
    have hcard : B.card = d := by simp only [B,card_insert_of_notMem hmidA,hAcard]; dsimp [k]; omega
    rwa [hcard] at hb
  · refine ⟨jumpGraph A hAzero hAneg,?_⟩
    have hcard : A.card = d := by rw [hAcard]; dsimp [k]; omega
    have ha := jumpGraph_regular A hAzero hAneg
    rwa [hcard] at ha

end Carpooling
