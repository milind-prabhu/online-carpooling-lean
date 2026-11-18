import Carpooling.EmbeddedLower

namespace Carpooling
open Finset
open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def extendPosition (f : V ↪ W) (x : V → ℤ) (w : W) : ℤ :=
  if h : ∃ v, f v = w then x h.choose else 0

@[simp] lemma extendPosition_at (f : V ↪ W) (x : V → ℤ) (v : V) :
    extendPosition f x (f v) = x v := by
  have h : ∃ a, f a = f v := ⟨v,rfl⟩
  simp only [extendPosition,dif_pos h]
  exact congrArg x (f.injective h.choose_spec)

noncomputable def UnitMove.pushforward {x y : V → ℤ} (e : UnitMove x y) (f : V ↪ W) :
    UnitMove (extendPosition f x) (extendPosition f y) where
  u := f e.u
  v := f e.v
  distinct := f.injective.ne e.distinct
  update := by
    intro w
    by_cases hw : ∃ v, f v = w
    · obtain ⟨v,rfl⟩ := hw
      simp only [extendPosition_at,f.injective.eq_iff]
      exact e.update v
    · have hu : w ≠ f e.u := fun he => hw ⟨e.u,he.symm⟩
      have hv : w ≠ f e.v := fun he => hw ⟨e.v,he.symm⟩
      simp [extendPosition,hw,hu,hv]

noncomputable def IntegerRun.pushforward {T : ℕ} (R : IntegerRun V T) (f : V ↪ W) :
    IntegerRun W T where
  d := fun t => extendPosition f (R.d t)
  step := fun t ht => (R.step t ht).pushforward f

lemma IntegerRun.pushforward_initial {T : ℕ} (R : IntegerRun V T) (f : V ↪ W)
    (hi : ∀ v, R.d 0 v = 0) : ∀ w, (R.pushforward f).d 0 w = 0 := by
  intro w
  simp [IntegerRun.pushforward,extendPosition,hi]

lemma pushforward_discrepancy_iff {T h : ℕ} (hh : 0 < h) (R : IntegerRun V T) (f : V ↪ W) :
    (∃ t ≤ T, ∃ w, (h:ℤ) ≤ |(R.pushforward f).d t w|) ↔
      ∃ t ≤ T, ∃ v, (h:ℤ) ≤ |R.d t v| := by
  constructor
  · rintro ⟨t,ht,w,hw⟩
    by_cases hr : ∃ v, f v = w
    · obtain ⟨v,rfl⟩ := hr
      exact ⟨t,ht,v,by simpa [IntegerRun.pushforward] using hw⟩
    · have hn : (h:ℤ) ≤ 0 := by simpa [IntegerRun.pushforward,extendPosition,hr] using hw
      have hp : (0:ℤ) < h := by exact_mod_cast hh
      omega
  · rintro ⟨t,ht,v,hv⟩
    exact ⟨t,ht,f v,by simpa [IntegerRun.pushforward] using hv⟩

end Carpooling
