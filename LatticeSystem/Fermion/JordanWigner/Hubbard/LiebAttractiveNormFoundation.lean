import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaReflection
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHermitianAbs
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveEnergyTrace
import LatticeSystem.Quantum.SpinS.RayleighUnitarySimilarity

/-!
# Norm/isometry foundation for the PSD ground representative (Tasaki §10.2.4)

Layer PR38a toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. To pass
from the Hermitian-`W` ground representative (PR37) to a **positive-semidefinite**-`W`
one via the SRP monotonicity `liebSRPEnergy_abs_le`, we must match norms: the squared
state norm, the Frobenius norm of the coefficient matrix, and the Frobenius norm of the
spectral absolute value `|W|`.

The coordinate map `ψ ↦ blockWCoeff ψ = hubbardBlockCoeffLinearEquiv (Uᴴψ)` is an
**isometry**: a configuration reshaping composed with the unitary back-rotation `Uᴴ`.
And `|W| = hermitianAbs W` has the same Frobenius norm as `W` (`|W|² = W²`,
`tr(|W|ᴴ|W|) = tr(W²) = tr(WᴴW)`).

## Main results

* `dotProduct_star_self_eq_sum_normSq` — `⟨v, v⟩ = Σ |v_c|²`.
* `blockWCoeff_dotProduct_eq` — `⟨ψ, ψ⟩ = Σ_{u,h} |W_{u,h}|²` (`W = blockWCoeff ψ`).
* `gammaWState_dotProduct_eq` — `⟨Γ(W), Γ(W)⟩ = Σ_{u,h} |W_{u,h}|²`.
* `hermitianAbs_sum_normSq_eq` — `Σ_{u,h} ||W|_{u,h}|² = Σ_{u,h} |W_{u,h}|²`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, pp. 363–367; E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The self inner product as a sum of squared magnitudes. -/
theorem dotProduct_star_self_eq_sum_normSq {ι : Type*} [Fintype ι] (v : ι → ℂ) :
    dotProduct (star v) v = ∑ c : ι, (Complex.normSq (v c) : ℂ) := by
  rw [dotProduct]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Pi.star_apply, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]

/-- **The squared state norm equals the Frobenius norm of its coefficient matrix.**
The coordinate map `ψ ↦ blockWCoeff ψ` is an isometry (reshape ∘ unitary). -/
theorem blockWCoeff_dotProduct_eq (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    dotProduct (star ψ) ψ
      = ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
          (Complex.normSq (blockWCoeff N ψ u h) : ℂ) := by
  -- `blockWCoeff ψ u h = (Uᴴψ)(merge u h)`.
  have hbw : ∀ u h, blockWCoeff N ψ u h
      = (hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ
          (hubbardBlockMergeConfig N u h) := by
    intro u h
    rw [blockWCoeff_eq_linearEquiv]
    simp only [hubbardBlockCoeffLinearEquiv, LinearEquiv.coe_mk]
    rfl
  rw [← LatticeSystem.Quantum.dotProduct_star_conjTranspose_mulVec_self
        (hubbardBlockToSpinfulPermutationOperator_mul_conjTranspose N) ψ,
    dotProduct_star_self_eq_sum_normSq]
  rw [← Equiv.sum_comp (hubbardBlockSpinConfigEquiv N).symm
        (fun c => (Complex.normSq
          ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ c) : ℂ)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun h _ => ?_))
  rw [hbw u h]; rfl

/-- The squared norm of the realizing state `Γ(W)` equals the Frobenius norm of `W`. -/
theorem gammaWState_dotProduct_eq
    (W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    dotProduct (star (gammaWState N W)) (gammaWState N W)
      = ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
          (Complex.normSq (W u h) : ℂ) := by
  rw [blockWCoeff_dotProduct_eq, blockWCoeff, blockWCoeff_gammaWState]

/-- **`|W|` has the same Frobenius norm as `W`.** Since `|W|² = W²` and both are
Hermitian, `tr(|W|ᴴ|W|) = tr(W²) = tr(WᴴW)`. -/
theorem hermitianAbs_sum_normSq_eq
    {W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ} (hW : W.IsHermitian) :
    ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
        (Complex.normSq (hermitianAbs hW u h) : ℂ)
      = ∑ u : hubbardSpinConfig N, ∑ h : hubbardSpinConfig N,
          (Complex.normSq (W u h) : ℂ) := by
  have key : ∀ (M : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ),
      M.IsHermitian → ∑ u, ∑ h, (Complex.normSq (M u h) : ℂ) = Matrix.trace (M * M) := by
    intro M hM
    rw [show M * M = Mᴴ * M from by rw [hM.eq], trace_conjTranspose_mul_eq_sum]
    refine Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun h _ => ?_))
    rw [Complex.normSq_eq_conj_mul_self, starRingEnd_apply]
  rw [key _ (hermitianAbs_isHermitian hW), key _ hW, hermitianAbs_mul_self]

end LatticeSystem.Fermion
