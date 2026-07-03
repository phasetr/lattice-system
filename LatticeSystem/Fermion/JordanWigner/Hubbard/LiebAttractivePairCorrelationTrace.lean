import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePairTransferMatrix
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveNormFoundation

/-!
# The pair-correlation expectation as a coefficient trace (Tasaki §10.2.4)

Second implementation layer toward discharging
`theorem_10_3_tian_pair_correlation_positive` (Tian's pair-correlation positivity, Tasaki
Theorem 10.3).

Combining the polarized coordinate isometry `blockWCoeff_dotProduct_cross_eq`
(`⟨ψ', ψ⟩ = Tr((blockWCoeff ψ')ᴴ · blockWCoeff ψ)`, Tasaki eq. (10.2.34)) with the
pair-transfer coefficient action `blockWCoeff_pairCorrelation_mulVec` (`blockWCoeff (P·ψ) = S·W·Sᵀ`)
gives the trace formula (Tasaki eq. (10.2.51))

  `⟨φ| P_{x,y} |φ⟩ = Tr(Wᴴ · S · W · Sᵀ)`,

with `W := blockWCoeff φ` and `S := hubbardBlockKineticUpFixedMatrix N (single x y 1)` the fixed
single-hop up-kinetic matrix.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.4, p. 372 (eq. (10.2.51)); E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **The pair-correlation expectation equals a coefficient trace** (Tasaki eq. (10.2.51)).
For any Euclidean state `φ`, writing `W := blockWCoeff N φ` and
`S := hubbardBlockKineticUpFixedMatrix N (single x y 1)`,
`⟨φ| ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑} |φ⟩ = Tr(Wᴴ · S · W · Sᵀ)`.  Immediate from the polarized
coordinate isometry `blockWCoeff_dotProduct_cross_eq` and the coefficient action
`blockWCoeff_pairCorrelation_mulVec`.  This is step L4 of Tasaki §10.2.4 (Theorem 10.3). -/
theorem euclideanExpectation_pairCorrelation_eq_trace (N : ℕ) (x y : Fin (N + 1))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (hubbardPairCorrelationOp N x y) φ
      = Matrix.trace ((blockWCoeff N φ.ofLp)ᴴ
          * (hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1) * blockWCoeff N φ.ofLp
              * (hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1))ᵀ)) := by
  rw [euclideanExpectation, blockWCoeff_dotProduct_cross_eq, blockWCoeff_pairCorrelation_mulVec]

end LatticeSystem.Fermion
