import Carpooling.DisjointCliques
import Mathlib.Combinatorics.SimpleGraph.Sum

namespace Carpooling
open Finset
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem sum_regular (G : SimpleGraph V) (H : SimpleGraph W)
    {d : ℕ} (hG : G.IsRegularOfDegree d) (hH : H.IsRegularOfDegree d) :
    (G ⊕g H).IsRegularOfDegree d := by
  intro x
  cases x with
  | inl v =>
    let e : (G ⊕g H).neighborSet (Sum.inl v) ≃ G.neighborSet v := {
      toFun := fun w => match w with
        | ⟨Sum.inl u,h⟩ => ⟨u,h⟩
        | ⟨Sum.inr _,h⟩ => False.elim (by simpa using h)
      invFun := fun u => ⟨Sum.inl u.val,u.property⟩
      left_inv := by
        rintro ⟨u,hu⟩
        cases u with
        | inl u => rfl
        | inr u => exact False.elim (by simpa using hu)
      right_inv := fun _ => rfl }
    rw [←SimpleGraph.card_neighborSet_eq_degree,←hG v,←SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e
  | inr w =>
    let e : (G ⊕g H).neighborSet (Sum.inr w) ≃ H.neighborSet w := {
      toFun := fun v => match v with
        | ⟨Sum.inl _,h⟩ => False.elim (by simpa using h)
        | ⟨Sum.inr u,h⟩ => ⟨u,h⟩
      invFun := fun u => ⟨Sum.inr u.val,u.property⟩
      left_inv := by
        rintro ⟨u,hu⟩
        cases u with
        | inl u => exact False.elim (by simpa using hu)
        | inr u => rfl
      right_inv := fun _ => rfl }
    rw [←SimpleGraph.card_neighborSet_eq_degree,←hH w,←SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e

noncomputable def sumEdgeMap (G : SimpleGraph V) (H : SimpleGraph W) :
    G.edgeSet ⊕ H.edgeSet → (G ⊕g H).edgeSet
  | Sum.inl e => ⟨e.val.map Sum.inl,by
      obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
      have hmem := e.property
      rw [←he,SimpleGraph.mem_edgeSet] at hmem
      rw [←he,Sym2.map_pair_eq,SimpleGraph.mem_edgeSet]
      exact hmem⟩
  | Sum.inr e => ⟨e.val.map Sum.inr,by
      obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
      have hmem := e.property
      rw [←he,SimpleGraph.mem_edgeSet] at hmem
      rw [←he,Sym2.map_pair_eq,SimpleGraph.mem_edgeSet]
      exact hmem⟩

lemma sumEdgeMap_injective (G : SimpleGraph V) (H : SimpleGraph W) :
    Function.Injective (sumEdgeMap G H) := by
  intro a b hab
  have he := congrArg Subtype.val hab
  cases a with
  | inl a =>
    obtain ⟨⟨u,v⟩,ha⟩ := Sym2.mk_surjective a.val
    cases b with
    | inl b =>
      obtain ⟨⟨w,z⟩,hb⟩ := Sym2.mk_surjective b.val
      change a.val.map Sum.inl = b.val.map Sum.inl at he
      rw [←ha,←hb,Sym2.map_pair_eq,Sym2.map_pair_eq] at he
      apply congrArg Sum.inl
      apply Subtype.ext
      rw [←ha,←hb]
      simpa only [Sym2.eq_iff,Sum.inl.injEq] using he
    | inr b =>
      obtain ⟨⟨w,z⟩,hb⟩ := Sym2.mk_surjective b.val
      change a.val.map Sum.inl = b.val.map Sum.inr at he
      simpa [←ha,←hb,Sym2.map_pair_eq,Sym2.eq_iff] using he
  | inr a =>
    obtain ⟨⟨u,v⟩,ha⟩ := Sym2.mk_surjective a.val
    cases b with
    | inl b =>
      obtain ⟨⟨w,z⟩,hb⟩ := Sym2.mk_surjective b.val
      change a.val.map Sum.inr = b.val.map Sum.inl at he
      simpa [←ha,←hb,Sym2.map_pair_eq,Sym2.eq_iff] using he
    | inr b =>
      obtain ⟨⟨w,z⟩,hb⟩ := Sym2.mk_surjective b.val
      change a.val.map Sum.inr = b.val.map Sum.inr at he
      rw [←ha,←hb,Sym2.map_pair_eq,Sym2.map_pair_eq] at he
      apply congrArg Sum.inr
      apply Subtype.ext
      rw [←ha,←hb]
      simpa only [Sym2.eq_iff,Sum.inr.injEq] using he

lemma sumEdgeMap_surjective (G : SimpleGraph V) (H : SimpleGraph W) :
    Function.Surjective (sumEdgeMap G H) := by
  intro e
  obtain ⟨⟨u,v⟩,he⟩ := Sym2.mk_surjective e.val
  have hm := e.property
  rw [←he,SimpleGraph.mem_edgeSet] at hm
  cases u with
  | inl u =>
    cases v with
    | inl v =>
      refine ⟨Sum.inl ⟨s(u,v),hm⟩,?_⟩
      apply Subtype.ext; exact he
    | inr v => exact False.elim (by simpa using hm)
  | inr u =>
    cases v with
    | inl v => exact False.elim (by simpa using hm)
    | inr v =>
      refine ⟨Sum.inr ⟨s(u,v),hm⟩,?_⟩
      apply Subtype.ext; exact he

noncomputable def sumEdgeEquiv (G : SimpleGraph V) (H : SimpleGraph W) :
    G.edgeSet ⊕ H.edgeSet ≃ (G ⊕g H).edgeSet :=
  Equiv.ofBijective (sumEdgeMap G H) ⟨sumEdgeMap_injective G H,sumEdgeMap_surjective G H⟩

end Carpooling
