import LatticeSystem.Fermion.JordanWigner.Hubbard.HopAction

/-!
# Matrix element of a single hopping term between one-hole basis states

This file computes the (real bilinear) matrix element of a single hole-filling
hopping term `c†_{(x,s)} c_{(y,s)}` between two one-hole hard-core basis
states, the per-term content of Tasaki eq. (11.2.5). Combining the operator
hop action (`hubbardHop_mulVec_hardcoreBasisState`) with the orthonormality of
the basis states (`hubbardHardcoreBasisState_inner`), the matrix element is the
Jordan–Wigner sign product times the indicator that the target spin
configuration equals the moved configuration `σ_{y→x}`.

The scalar prefactor is the honest computational-basis fermion sign in the
sign-free `basisVec` convention; the uniform `-t_{x,y}` of (11.2.5) requires the
ordered creation-operator basis (11.2.3) and is assembled in a later layer.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.5), p. 384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- Matrix element of the hole-filling hopping term `c†_{(x,s)} c_{(y,s)}`
between one-hole basis states: it is the Jordan–Wigner sign product times the
indicator that the target configuration `|Φ_{y,τ}⟩` is the moved configuration
`|Φ_{y, σ_{y→x}}⟩`. This is the per-term content of (11.2.5); the off-diagonal
support is exactly `τ = σ_{y→x}`. -/
theorem hubbardHopTerm_inner_hardcoreBasisState
    (N : ℕ) (x y : Fin (N + 1)) (σ τ : Fin (N + 1) → Bool) (s : Fin 2)
    (hxy : x ≠ y)
    (hs : hubbardOneHoleConfig N x σ (spinfulIndex N y s) = 1) :
    (∑ w : Fin (2 * N + 2) → Fin 2,
        hubbardHardcoreBasisState N y τ w *
          (fermionMultiCreation (2 * N + 1) (spinfulIndex N x s) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y s)).mulVec
            (hubbardHardcoreBasisState N x σ) w) =
      (jwSign (2 * N + 1) (spinfulIndex N y s) (hubbardOneHoleConfig N x σ) *
          jwSign (2 * N + 1) (spinfulIndex N x s)
            (Function.update (hubbardOneHoleConfig N x σ)
              (spinfulIndex N y s) 0)) *
        (if hubbardOneHoleConfig N y (hubbardSpinMove N σ x y) =
            hubbardOneHoleConfig N y τ then 1 else 0) := by
  set coeff :=
    jwSign (2 * N + 1) (spinfulIndex N y s) (hubbardOneHoleConfig N x σ) *
      jwSign (2 * N + 1) (spinfulIndex N x s)
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N y s) 0)
    with hcoeff
  rw [hubbardHop_mulVec_hardcoreBasisState N x y σ s hxy hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun w _ =>
    show hubbardHardcoreBasisState N y τ w *
        (coeff * hubbardHardcoreBasisState N y (hubbardSpinMove N σ x y) w) =
      coeff * (hubbardHardcoreBasisState N y τ w *
        hubbardHardcoreBasisState N y (hubbardSpinMove N σ x y) w) from by ring),
    ← Finset.mul_sum,
    hubbardHardcoreBasisState_inner N y y τ (hubbardSpinMove N σ x y)]

end LatticeSystem.Fermion
