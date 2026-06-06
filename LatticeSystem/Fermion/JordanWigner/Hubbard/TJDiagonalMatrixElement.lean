import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis

/-!
# Tasaki 11.5: the diagonal terms have no off-diagonal matrix elements (Prop 11.24 PR-B6)

The interaction term `n̂_x n̂_y / 4 − Ŝ_x · Ŝ_y` of the t-J Hamiltonian splits into the ladder part
`½(Ŝ⁺_xŜ⁻_y + Ŝ⁻_xŜ⁺_y)` (off-diagonal, handled in PR-B5) and the *diagonal* part
`n̂_x n̂_y / 4 − Ŝ³_x Ŝ³_y`.  The per-site number `n̂_x` and spin-z `Ŝ³_x` are diagonal operators on the
computational basis (combinations of mode-number operators), so their products act as scalars on
`|Φ_s⟩`, and hence have **vanishing off-diagonal matrix element** `⟨Φ_{s'} | · | Φ_s⟩ = 0` for
`s' ≠ s`.  This isolates the off-diagonal part of the effective matrix to the sign-free hopping and
spin-flip entries.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- `n̂_x = n̂_{x↑} + n̂_{x↓}` acts diagonally on a computational basis state. -/
theorem fermionSiteNumber_mulVec_basisVec (N : ℕ) (x : Fin (N + 1))
    (c : Fin (2 * N + 2) → Fin 2) :
    (fermionSiteNumber N x).mulVec (basisVec c) =
      (((c (spinfulIndex N x 0)).val : ℂ) + ((c (spinfulIndex N x 1)).val : ℂ)) • basisVec c := by
  unfold fermionSiteNumber fermionUpNumber fermionDownNumber
  rw [Matrix.add_mulVec, fermionMultiNumber_mulVec_basisVec, fermionMultiNumber_mulVec_basisVec,
    add_smul]

/-- `Ŝ³_x = (n̂_{x↑} − n̂_{x↓})/2` acts diagonally on a computational basis state. -/
theorem fermionSiteSpinZ_mulVec_basisVec (N : ℕ) (x : Fin (N + 1))
    (c : Fin (2 * N + 2) → Fin 2) :
    (fermionSiteSpinZ N x).mulVec (basisVec c) =
      ((1 / 2 : ℂ) * (((c (spinfulIndex N x 0)).val : ℂ) - ((c (spinfulIndex N x 1)).val : ℂ)))
        • basisVec c := by
  unfold fermionSiteSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    show fermionUpCreation N x * fermionUpAnnihilation N x = fermionUpNumber N x from rfl,
    show fermionDownCreation N x * fermionDownAnnihilation N x = fermionDownNumber N x from rfl]
  unfold fermionUpNumber fermionDownNumber
  rw [fermionMultiNumber_mulVec_basisVec, fermionMultiNumber_mulVec_basisVec, ← sub_smul,
    smul_smul]

/-- A diagonal operator (acting as a scalar on `|Φ_s⟩`) has vanishing off-diagonal matrix element. -/
theorem diagonal_offdiag_matrixElement_eq_zero (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (op : ManyBodyOp (Fin (2 * N + 2)))
    (hd : ∃ sc : ℂ, op.mulVec (basisVec (tJConfigOf N s)) = sc • basisVec (tJConfigOf N s))
    (hne : s' ≠ s) :
    (∑ w, basisVec (tJConfigOf N s') w * (op.mulVec (basisVec (tJConfigOf N s))) w) = 0 := by
  obtain ⟨sc, hd⟩ := hd
  rw [hd]
  have : (∑ w, basisVec (tJConfigOf N s') w * (sc • basisVec (tJConfigOf N s)) w)
      = sc * ∑ w, basisVec (tJConfigOf N s') w * basisVec (tJConfigOf N s) w := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  rw [this, tJConfigOf_basisVec_inner, if_neg hne, mul_zero]

/-- **The number-product `n̂_x n̂_y` has no off-diagonal matrix element.** -/
theorem fermionSiteNumber_mul_offdiag_matrixElement_eq_zero (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (x y : Fin (N + 1)) (hne : s' ≠ s) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionSiteNumber N x * fermionSiteNumber N y).mulVec
            (basisVec (tJConfigOf N s))) w) = 0 := by
  exact diagonal_offdiag_matrixElement_eq_zero N s s' _
    ⟨_, by rw [← Matrix.mulVec_mulVec, fermionSiteNumber_mulVec_basisVec, Matrix.mulVec_smul,
      fermionSiteNumber_mulVec_basisVec, smul_smul]⟩ hne

/-- **The spin-z-product `Ŝ³_x Ŝ³_y` has no off-diagonal matrix element.** -/
theorem fermionSiteSpinZ_mul_offdiag_matrixElement_eq_zero (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (x y : Fin (N + 1)) (hne : s' ≠ s) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionSiteSpinZ N x * fermionSiteSpinZ N y).mulVec
            (basisVec (tJConfigOf N s))) w) = 0 := by
  exact diagonal_offdiag_matrixElement_eq_zero N s s' _
    ⟨_, by rw [← Matrix.mulVec_mulVec, fermionSiteSpinZ_mulVec_basisVec, Matrix.mulVec_smul,
      fermionSiteSpinZ_mulVec_basisVec, smul_smul]⟩ hne

end LatticeSystem.Fermion
