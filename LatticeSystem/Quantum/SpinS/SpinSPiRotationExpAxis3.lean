import LatticeSystem.Quantum.SpinS.SpinSPiRotation
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation

/-!
# The axis-3 `π` rotation as an exponential

The closed-form `π` rotation `û₃` of `Quantum/SpinS/SpinSPiRotation.lean` is the exponential
`Û_π^{(3)} = exp(−iπ Ŝ^{(3)})` of the definition on p. 15, at general spin `S = N/2`: this is the
third line of the closed form (2.1.34), p. 20, `⟨ψ^σ|û₃|ψ^τ⟩ = e^{−iπσ}δ_{σ,τ}`, whose general-`S`
derivation is left to the reader as Problem 2.1.g, p. 20 (solution p. 495).  The exponential side
is the repository's `spinSRot3 N θ = exp(−iθ Ŝ^{(3)})` at `θ = π`, so the whole content is the
scalar phase carried by each diagonal entry of the closed form `spinSRot3_eq_diagonal`.

Statements are phrased in the integer basis index `k` of `Fin (N + 1)`, not in the magnetic
quantum number `σ = m_k = N/2 − k`: the printed exponent `e^{−iπσ}` is not a power of `−1` for
half-odd-integer `S`, whereas the phase pattern `(−i)^N (−1)^k` in the basis index is exact for
every `N`.

The axes `1` and `2` are not treated here; their closed forms `spinSPiRotation1`,
`spinSPiRotation2` carry no exponential identification.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1: the rotation `Û_θ^{(α)} = exp(−iθ Ŝ^{(α)})`, p. 15; the closed form (2.1.34) and
Problem 2.1.g, p. 20 (solution p. 495).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **The scalar phase of the axis-3 `π` rotation**: `e^{−iπ(N/2 − k)} = (−i)^N (−1)^k`.  This is
the diagonal entry of `exp(−iπ Ŝ^{(3)})` at the basis index `k`, i.e. the third line of Tasaki
(2.1.34), p. 20, written in the integer index `k = S − σ`. -/
theorem spinSOp3Eigen_exp_neg_pi_mul_I_eq (N : ℕ) (k : Fin (N + 1)) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) * spinSOp3Eigen N k) =
      ((-Complex.I) ^ N) * (-1 : ℂ) ^ (k : ℕ) := by
  have hhalf : Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) = -Complex.I := by
    rw [show -((Real.pi : ℂ) / 2 * Complex.I) = (-((Real.pi : ℂ) / 2)) * Complex.I by ring,
      Complex.exp_mul_I]
    simp
  have hsplit : -((Real.pi : ℂ) * Complex.I) * spinSOp3Eigen N k =
      (N : ℂ) * (-((Real.pi : ℂ) / 2 * Complex.I)) +
        ((k : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I) := by
    unfold spinSOp3Eigen
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_nat_mul, Complex.exp_nat_mul, hhalf,
    Complex.exp_pi_mul_I]

end LatticeSystem.Quantum
