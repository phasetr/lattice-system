import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreBasis

/-!
# Configuration of a one-hole hard-core state after a hole-filling hop

This file establishes the spatial content of Tasaki eq. (11.2.4) at the level
of occupation configurations: when an electron of spin `s` hops from an
occupied site `y` into the hole `x` of the one-hole hard-core state
`|Φ_{x,σ}⟩`, the resulting computational basis configuration is exactly the
one of `|Φ_{y, σ_{y→x}}⟩`, where the new hole is at `y` and the moved electron
carries its spin to `x` (`σ_{y→x} = σ` with `x ↦ σ y`).

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.4), pp. 383-384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The spin configuration `σ_{y→x}` obtained from `σ` by moving the electron
at `y` to the former hole site `x`: it agrees with `σ` everywhere except at
`x`, where it takes the spin `σ y` of the moved electron. -/
def hubbardSpinMove (N : ℕ) (σ : Fin (N + 1) → Bool) (x y : Fin (N + 1)) :
    Fin (N + 1) → Bool :=
  Function.update σ x (σ y)

/-- Every spinful JW index decomposes as a `spinfulIndex`. -/
private theorem exists_spinfulIndex_eq (N : ℕ) (k : Fin (2 * N + 2)) :
    ∃ (a : Fin (N + 1)) (r : Fin 2), k = spinfulIndex N a r := by
  have hk := k.isLt
  refine ⟨⟨k.val / 2, (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)⟩,
    ⟨k.val % 2, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  apply Fin.ext
  simp only [spinfulIndex]
  omega

/-- Injectivity of `spinfulIndex` jointly in the site and the spin label. -/
private theorem spinfulIndex_eq_iff (N : ℕ) (a a' : Fin (N + 1)) (r r' : Fin 2) :
    spinfulIndex N a r = spinfulIndex N a' r' ↔ a = a' ∧ r = r' := by
  constructor
  · intro h
    have hv : 2 * a.val + r.val = 2 * a'.val + r'.val := by
      have := congrArg Fin.val h
      simpa [spinfulIndex] using this
    have hr := r.isLt
    have hr' := r'.isLt
    exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- A `Fin 2` value that is not `0` is `1`. -/
private theorem fin_two_ne_zero {v : Fin 2} (h : v ≠ 0) : v = 1 := by
  have h2 := v.isLt
  exact Fin.ext (by have : v.val ≠ 0 := fun hv => h (Fin.ext hv); omega)

/-- Spatial content of (11.2.4): filling the hole `x` with an electron of spin
`s` hopped from `y` turns the configuration of `|Φ_{x,σ}⟩` into that of
`|Φ_{y, σ_{y→x}}⟩`. The hypothesis `hs` says the `s`-orbital at `y` is
occupied, which forces `s` to be the spin of the electron at `y`. -/
theorem hubbardOneHoleConfig_hop
    (N : ℕ) (x y : Fin (N + 1)) (σ : Fin (N + 1) → Bool) (s : Fin 2)
    (hxy : x ≠ y)
    (hs : hubbardOneHoleConfig N x σ (spinfulIndex N y s) = 1) :
    Function.update
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N y s) 0)
        (spinfulIndex N x s) 1 =
      hubbardOneHoleConfig N y (hubbardSpinMove N σ x y) := by
  have hxy' : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  -- From `hs`, the orbital `s` matches the spin of the electron at `y`:
  -- `σ y = true ↔ s = 0`.
  have hsy : (σ y = true) ↔ (s = 0) := by
    by_cases hs0 : s = 0
    · subst hs0
      rw [hubbardOneHoleConfig_apply_up, if_neg (Ne.symm hxy')] at hs
      refine ⟨fun _ => rfl, fun _ => ?_⟩
      by_cases hσ : σ y <;> simp_all
    · obtain rfl : s = 1 := fin_two_ne_zero hs0
      rw [hubbardOneHoleConfig_apply_down, if_neg (Ne.symm hxy')] at hs
      refine ⟨fun hσ => ?_, fun h => absurd h (by decide)⟩
      rw [hσ] at hs; simp at hs
  funext k
  obtain ⟨a, r, rfl⟩ := exists_spinfulIndex_eq N k
  simp only [Function.update_apply, spinfulIndex_eq_iff]
  -- LHS = if a=x ∧ r=s then 1 else if a=y ∧ r=s then 0
  --       else hubbardOneHoleConfig N x σ (spinfulIndex N a r)
  have hrs : (r = 0) ∨ (r = 1) := by
    rcases eq_or_ne r 0 with h | h
    · exact Or.inl h
    · exact Or.inr (fin_two_ne_zero h)
  have hss : (s = 0) ∨ (s = 1) := by
    rcases eq_or_ne s 0 with h | h
    · exact Or.inl h
    · exact Or.inr (fin_two_ne_zero h)
  rcases eq_or_ne a x with rfl | hax
  · -- former hole site x (note a = x ≠ y)
    rcases hrs with rfl | rfl <;> rcases hss with rfl | rfl <;>
      simp_all [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_down,
        hubbardSpinMove]
  · have hax' : a.val ≠ x.val := fun h => hax (Fin.ext h)
    rcases eq_or_ne a y with rfl | hay
    · -- new hole site y
      rcases hrs with rfl | rfl <;> rcases hss with rfl | rfl <;>
        simp_all [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_down,
          hubbardSpinMove]
    · -- untouched site a ∉ {x, y}
      have hay' : a.val ≠ y.val := fun h => hay (Fin.ext h)
      rcases hrs with rfl | rfl <;> rcases hss with rfl | rfl <;>
        simp_all [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_down,
          hubbardSpinMove]

end LatticeSystem.Fermion
