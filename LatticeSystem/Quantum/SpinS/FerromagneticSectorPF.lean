import LatticeSystem.Quantum.SpinS.FerromagneticSectorIrreducible
import LatticeSystem.Quantum.SpinS.SaturatedLadderComponent
import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.ParityBlockUnshiftedFinrank
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge
import LatticeSystem.Math.FiniteStrictUpperBound

/-!
# Tasaki §2.4, p. 34: Perron-Frobenius simplicity on a magnetization sector

The analytic half of the Theorem 2.1 uniqueness argument, on one magnetization sector at a time.
Tasaki's solution of Problem 2.4.a (p. 496) instructs one to apply the Perron-Frobenius theorem
(Theorem A.18, p. 475) to the matrix representation of `Ĥ` in each sector `H_M`.  The repo's
Perron-Frobenius packaging concludes simplicity from an explicit strictly positive eigenvector
rather than from a variational identification of the sectorwise minimum, and the ladder state
`Φ_M = (Ŝ⁻_tot)^k Φ↑` supplies that eigenvector: its closed form (eq. (2.4.9), p. 33) is a
positive real multiple of a product of Clebsch-Gordan weights on its own sector.

The three steps here are: strict positivity of the restricted ladder state, its eigenvector
equation for the real-form sector matrix, and the resulting `finrank ≤ 1` for the complex sector
matrix at the saturated-ferromagnet eigenvalue.  The sector irreducibility input and its diagonal
shift come from `FerromagneticSectorIrreducible`; the shift witness itself is produced here from
`LatticeSystem.Math.exists_gt_of_finite`, so the hypotheses stay those of the book.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; eq. (2.4.9), p. 33; solution of Problem 2.4.a, p. 496;
Theorem A.18, p. 475.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Strict positivity of the ladder state on its own magnetization sector** (Tasaki eq. (2.4.9),
p. 33; solution of Problem 2.4.a, p. 496).

On the sector `magSumS σ = k` the closed component form of `(Ŝ⁻_tot)^k Φ↑` is the real number
`k! · ∏_x √(binom N σ_x)`, whose factors are all positive.  This is the strictly positive
Perron-Frobenius eigenvector candidate of Theorem A.18 (p. 475). -/
theorem ladderIterateUp_restriction_re_pos (k : Fin (Fintype.card V * N + 1))
    (σ : magConfigS V N k.val) :
    0 < (ladderIterateUp V N k σ.1).re := by
  unfold ladderIterateUp
  rw [totalSpinSOpMinus_pow_allAlignedStateS_zero_apply k.val σ.1, if_pos σ.2,
    Complex.ofReal_re]
  have hfac : (0 : ℝ) < (k.val.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k.val
  have hprod : (0 : ℝ) < ∏ x : V, Real.sqrt (N.choose (σ.1 x).val) := by
    refine Finset.prod_pos fun x _ => Real.sqrt_pos.mpr ?_
    exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp (σ.1 x).isLt)
  exact mul_pos hfac hprod

end LatticeSystem.Quantum
