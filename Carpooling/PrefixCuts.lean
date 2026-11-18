import Carpooling.AdaptiveProbability

namespace Carpooling
open Finset
open scoped Classical

/-- Every finite chronological set with at least L occurrences has a cutoff
containing exactly its first L occurrences. -/
theorem exists_prefix_cut {T L : ℕ} (S : Finset (Fin T)) (hL : L ≤ S.card) :
    ∃ c ≤ T, (S.filter fun t => t.val < c).card = L := by
  by_cases hz : L = 0
  · exact ⟨0,Nat.zero_le _,by simp [hz]⟩
  have hex : ∃ c, L ≤ (S.filter fun t => t.val < c).card :=
    ⟨T,by simpa using hL⟩
  let c := Nat.find hex
  have hc : c ≤ T := Nat.find_min' hex (by simpa using hL)
  have hcL : L ≤ (S.filter fun t => t.val < c).card := Nat.find_spec hex
  have hcpos : 0 < c := by
    by_contra hn
    have he : c = 0 := by omega
    simp only [he,Nat.not_lt_zero,filter_false,card_empty] at hcL
    omega
  have hprev : ¬ L ≤ (S.filter fun t => t.val < c-1).card :=
    Nat.find_min hex (show c-1 < c by omega)
  have hi : c-1 < T := by omega
  have hset : (S.filter fun t => t.val < c) ⊆
      insert (⟨c-1,hi⟩ : Fin T) (S.filter fun t => t.val < c-1) := by
    intro t ht
    obtain ⟨htS,htc⟩ := mem_filter.mp ht
    by_cases htp : t.val < c-1
    · exact mem_insert_of_mem (mem_filter.mpr ⟨htS,htp⟩)
    · apply mem_insert.mpr
      left
      apply Fin.ext
      change t.val = c-1
      omega
  have hcard := (card_le_card hset).trans (card_insert_le _ _)
  exact ⟨c,hc,by omega⟩

end Carpooling
