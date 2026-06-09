import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandModeCreation
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Tasaki §11.3.1: the β-Gram matrix and its invertibility (towards the dual annihilators)

The `β`-Gram matrix `G_{uv} = ∑_x β_u(x) β_v(x)` (the `{b̂_u, b̂†_v}` anticommutator coefficient) is
invertible: `{β_u}` is linearly independent (Lemma 11.10), so the Gram matrix is positive definite.
Its inverse defines the *dual annihilators* `d_u = ∑_v (G⁻¹)_{uv} b̂_v` with
`{d_u, b̂†_w} = δ_{uw}`, the key tool of the `BKernel ⊆ AlphaFock` Fock factorisation.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {K : ℕ} {ν : ℝ}

/-- The `β`-Gram matrix `G_{uv} = ∑_x β_u(x) β_v(x)` (the bilinear overlap of the `β` states; equals
the `{b̂_u, b̂†_v}` anticommutator scalar). -/
noncomputable def flatBandBetaGram (K : ℕ) (ν : ℝ) : Matrix (Fin (K + 1)) (Fin (K + 1)) ℂ :=
  Matrix.of fun u v => ∑ x, flatBandBetaC K ν u x * flatBandBetaC K ν v x

/-- The `β` states retyped as `EuclideanSpace ℂ` vectors (`WithLp` is a type synonym, so the
coefficient function is unchanged). -/
noncomputable def flatBandBetaEuclidean (K : ℕ) (ν : ℝ) (u : Fin (K + 1)) :
    EuclideanSpace ℂ (Fin (2 * K + 2)) :=
  (WithLp.equiv 2 (Fin (2 * K + 2) → ℂ)).symm (flatBandBetaC K ν u)

/-- The `β`-Gram matrix is the mathlib inner-product Gram matrix of the `β` Euclidean vectors (the
coefficients are real, so conjugation is invisible). -/
theorem flatBandBetaGram_eq_gram (K : ℕ) (ν : ℝ) :
    flatBandBetaGram K ν = Matrix.gram ℂ (flatBandBetaEuclidean K ν) := by
  ext u v
  rw [flatBandBetaGram, Matrix.of_apply, Matrix.gram_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  change flatBandBetaC K ν u x * flatBandBetaC K ν v x
    = flatBandBetaC K ν v x * star (flatBandBetaC K ν u x)
  simp only [flatBandBetaC, RCLike.star_def, Complex.conj_ofReal]
  ring

/-- **The `β`-Gram matrix is positive definite** (its `{β}` family is linearly independent). -/
theorem flatBandBetaGram_posDef (K : ℕ) (ν : ℝ) : (flatBandBetaGram K ν).PosDef := by
  rw [flatBandBetaGram_eq_gram]
  refine Matrix.posDef_gram_of_linearIndependent ?_
  refine (flatBandBetaC_linearIndependent K ν).map'
    (WithLp.linearEquiv 2 ℂ (Fin (2 * K + 2) → ℂ)).symm.toLinearMap ?_
  exact LinearMap.ker_eq_bot.mpr (WithLp.linearEquiv 2 ℂ (Fin (2 * K + 2) → ℂ)).symm.injective

/-- The `β`-Gram matrix is invertible (its determinant is a unit). -/
theorem flatBandBetaGram_isUnit_det (K : ℕ) (ν : ℝ) : IsUnit (flatBandBetaGram K ν).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (flatBandBetaGram_posDef K ν).isUnit

end LatticeSystem.Fermion
