import LatticeSystem.Fermion.JordanWigner.Hubbard.HopConfig
import LatticeSystem.Fermion.JordanWigner.HopBasisVec

/-!
# Operator-level action of a hopping term on a one-hole basis state

This file assembles the operator content of Tasaki eq. (11.2.4): the action of
a single spinful hopping term `c†_{(x,s)} c_{(y,s)}` — creating at the hole
site `x` and annihilating at an occupied site `y` — on the one-hole hard-core
basis state `|Φ_{x,σ}⟩`. Combining the basis-state hop computation
(`fermionMultiCreation_mul_Annihilation_mulVec_basisVec`) with the hop
configuration identity (`hubbardOneHoleConfig_hop`), the result is the moved
basis state `|Φ_{y, σ_{y→x}}⟩` weighted by the product of the two
Jordan–Wigner string signs.

The scalar coefficient here is the honest computational-basis fermion sign
`jwSign · jwSign`; this is the operator-level fact in the sign-free `basisVec`
convention. (Tasaki's uniform `-t_{x,y}` of (11.2.5) arises in his ordered
creation-operator basis (11.2.3); recovering it is the next layer.)

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.4), pp. 383-384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The one-hole configuration is empty on both orbitals at the hole site. -/
private theorem hubbardOneHoleConfig_hole_zero
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) (s : Fin 2) :
    hubbardOneHoleConfig N x σ (spinfulIndex N x s) = 0 := by
  by_cases h : s = 0
  · subst h; rw [hubbardOneHoleConfig_apply_up, if_pos rfl]
  · obtain rfl : s = 1 := fin_two_ne_zero h
    rw [hubbardOneHoleConfig_apply_down, if_pos rfl]

/-- Operator content of (11.2.4): the hole-filling hopping term
`c†_{(x,s)} c_{(y,s)}` (create at the hole `x`, annihilate at the occupied site
`y` of spin `s`) sends `|Φ_{x,σ}⟩` to the moved basis state
`|Φ_{y, σ_{y→x}}⟩` weighted by the product of the two Jordan–Wigner string
signs. The hypothesis `hs` records that the `s`-orbital at `y` is occupied. -/
theorem hubbardHop_mulVec_hardcoreBasisState
    (N : ℕ) (x y : Fin (N + 1)) (σ : Fin (N + 1) → Bool) (s : Fin 2)
    (hxy : x ≠ y)
    (hs : hubbardOneHoleConfig N x σ (spinfulIndex N y s) = 1) :
    (fermionMultiCreation (2 * N + 1) (spinfulIndex N x s) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y s)).mulVec
        (hubbardHardcoreBasisState N x σ) =
      (jwSign (2 * N + 1) (spinfulIndex N y s) (hubbardOneHoleConfig N x σ) *
          jwSign (2 * N + 1) (spinfulIndex N x s)
            (Function.update (hubbardOneHoleConfig N x σ)
              (spinfulIndex N y s) 0)) •
        hubbardHardcoreBasisState N y (hubbardSpinMove N σ x y) := by
  unfold hubbardHardcoreBasisState
  rw [fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  have hpq : spinfulIndex N x s ≠ spinfulIndex N y s := by
    intro h
    have hv := congrArg Fin.val h
    simp only [spinfulIndex] at hv
    exact hxy (Fin.ext (by omega))
  have hp0 : (Function.update (hubbardOneHoleConfig N x σ)
      (spinfulIndex N y s) 0) (spinfulIndex N x s) = 0 := by
    rw [Function.update_of_ne hpq, hubbardOneHoleConfig_hole_zero]
  rw [if_pos ⟨hs, hp0⟩, hubbardOneHoleConfig_hop N x y σ s hxy hs]

end LatticeSystem.Fermion
