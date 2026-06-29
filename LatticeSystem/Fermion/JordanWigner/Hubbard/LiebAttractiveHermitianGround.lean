import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaAntilinear

/-!
# A Hermitian-`W` ground-state representative (Tasaki §10.2.4)

Layer PR37 of the **Γ-family** toward discharging
`theorem_10_2_lieb_attractive_unique_singlet`. The energy reconciliation (PR33d) only
applies when the coefficient `W := blockWCoeff ψ` is Hermitian, i.e. (PR35) when `ψ` is
fixed by the Γ-reflection `Θ`. This layer shows that **the ground energy is attained by
a Θ-fixed (hence Hermitian-`W`) state**: given any nonzero ground vector `ψ₀`, the
`Θ`-symmetrization `ψ₀ + Θψ₀` is `Θ`-fixed and is again a ground vector (`Θ` commutes
with `Ĥ` and preserves real eigenvalues, PR36c/d); if it vanishes, the rotated
combination `i·ψ₀ + Θ(i·ψ₀) = 2i·ψ₀` is nonzero and serves instead (`Θ` is anti-linear,
so this is also `Θ`-fixed).

Consequently there is a nonzero ground vector with a **Hermitian** reconciliation
coefficient `W`, to which the energy reconciliation and SRP monotonicity
(`liebSRPEnergy_abs_le`) apply in the next layer (PR38).

## Main results

* `gammaThetaSymm_fixed` — `x + Θx` is `Θ`-fixed.
* `gammaThetaSymm_eigenvector` — `x + Θx` is a `Ĥ`-eigenvector at a real eigenvalue if `x` is.
* `exists_hermitianW_ground` — a nonzero ground vector with Hermitian `blockWCoeff`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- `gammaWState` is additive. -/
theorem gammaWState_add (W W' : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    gammaWState N (W + W') = gammaWState N W + gammaWState N W' := by
  rw [gammaWState, gammaWState, gammaWState, map_add, Matrix.mulVec_add]

/-- The Γ-reflection is additive (it is anti-linear). -/
theorem gammaThetaVec_add (ψ φ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    gammaThetaVec N (ψ + φ) = gammaThetaVec N ψ + gammaThetaVec N φ := by
  apply blockWCoeff_injective
  simp only [blockWCoeff_add, blockWCoeff_gammaThetaVec, Matrix.conjTranspose_add]

/-- The `Θ`-symmetrization `x + Θx` is fixed by `Θ`. -/
theorem gammaThetaSymm_fixed (x : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    gammaThetaVec N (x + gammaThetaVec N x) = x + gammaThetaVec N x := by
  rw [gammaThetaVec_add, gammaThetaVec_gammaThetaVec]
  exact add_comm _ _

/-- If `x` is a `Ĥ`-eigenvector at a real eigenvalue `E`, so is `x + Θx`. -/
theorem gammaThetaSymm_eigenvector
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (x : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℝ)
    (hx : (attractiveHubbardHamiltonian N T U).mulVec x = (E : ℂ) • x) :
    (attractiveHubbardHamiltonian N T U).mulVec (x + gammaThetaVec N x)
      = (E : ℂ) • (x + gammaThetaVec N x) := by
  rw [Matrix.mulVec_add, hx, gammaThetaVec_preserves_eigenvector T U x E hx, smul_add]

/-- **A Hermitian-`W` ground representative.** Given a nonzero `Ĥ`-eigenvector `ψ₀` at a
real eigenvalue `E`, there is a nonzero eigenvector `φ` at the same eigenvalue whose
reconciliation coefficient `blockWCoeff φ` is Hermitian. -/
theorem exists_hermitianW_ground
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (ψ₀ : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℝ) (hψ₀ : ψ₀ ≠ 0)
    (hE : (attractiveHubbardHamiltonian N T U).mulVec ψ₀ = (E : ℂ) • ψ₀) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0 ∧ (blockWCoeff N φ).IsHermitian
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ = (E : ℂ) • φ := by
  -- `i·ψ₀` is also an eigenvector at `E`.
  have hIE : (attractiveHubbardHamiltonian N T U).mulVec (Complex.I • ψ₀)
      = (E : ℂ) • (Complex.I • ψ₀) := by
    rw [Matrix.mulVec_smul, hE, smul_comm]
  by_cases h0 : ψ₀ + gammaThetaVec N ψ₀ = 0
  · -- `ψ₀ + Θψ₀ = 0`, so `Θψ₀ = -ψ₀`; use `i·ψ₀ + Θ(i·ψ₀) = 2i·ψ₀`.
    refine ⟨Complex.I • ψ₀ + gammaThetaVec N (Complex.I • ψ₀), ?_,
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr (gammaThetaSymm_fixed _),
      gammaThetaSymm_eigenvector T U _ E hIE⟩
    have hθ : gammaThetaVec N ψ₀ = -ψ₀ := by
      rw [eq_neg_iff_add_eq_zero, add_comm (gammaThetaVec N ψ₀) ψ₀]; exact h0
    have hθI : gammaThetaVec N (Complex.I • ψ₀) = Complex.I • ψ₀ := by
      rw [gammaThetaVec_smul, Complex.conj_I, hθ, neg_smul, smul_neg, neg_neg]
    have hval : Complex.I • ψ₀ + gammaThetaVec N (Complex.I • ψ₀)
        = (2 : ℂ) • (Complex.I • ψ₀) := by
      rw [hθI, ← two_smul ℂ]
    rw [hval]
    exact smul_ne_zero (by norm_num) (smul_ne_zero Complex.I_ne_zero hψ₀)
  · exact ⟨ψ₀ + gammaThetaVec N ψ₀, h0,
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr (gammaThetaSymm_fixed _),
      gammaThetaSymm_eigenvector T U ψ₀ E hE⟩

end LatticeSystem.Fermion
