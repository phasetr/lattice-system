import LatticeSystem.Quantum.SpinS.SpinSPiRotation
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis3

/-!
# Signature pin: PR-A of the Problem 2.1.g exponential-identification arc, axis 3

Repository-internal regression guard for PR-A of the arc that identifies the closed-form
spin-`S` `π`-rotations `spinSPiRotationAxis` with the book's `exp(−iπ Ŝ^{(α)})` (H. Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer, 2020,
**eq. (2.1.34), p. 20**, the general-`S` closed form left to the reader as **Problem 2.1.g,
p. 20**, solution p. 495; the many-body definition **eq. (2.2.11), p. 22**). PR-A closes only
the axis-3 (diagonal) case, the third relation of (2.1.34):
`⟨ψ^σ|û₃|ψ^τ⟩ = e^{−iπσ}δ_{σ,τ}`, phrased in the integer basis index `k = S − σ` rather
than the magnetic quantum number `σ`, since `σ` itself is not an integer for
half-odd-integer `S`, so the printed exponent `e^{−iπσ}` is not a power of `−1`; this is why the
closed form carries `(−i)^N`.

Pinned:
* R0-scalar `spinSOp3Eigen_exp_neg_pi_mul_I_eq` — the scalar phase identity
  `exp(−iπ(N/2 − k)) = (−i)^N (−1)^k` carried by each diagonal entry of Tasaki (2.1.34),
  third relation, p. 20.
* R0 `spinSPiRotation3_eq_spinSRot3_pi` — the axis-3 identification
  `spinSPiRotation3 N = spinSRot3 N Real.pi` (Tasaki (2.1.34), third relation, p. 20;
  Problem 2.1.g, p. 20).
* A definitional guard that the exponential side `spinSRot3` is the genuine `NormedSpace.exp`
  of `Ŝ^{(3)}`, not a closed-form alias.
* Zero-hypothesis positive controls at `N = 1, 2, 3`, cross-checked against the existing
  `spinSRot3_eq_diagonal` closed form and the concrete diagonal entries, including the
  sign-sensitive odd case `N = 3`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.,
Springer, 2020), §2.1, Û_θ^{(α)} definition p. 15, eq. (2.1.34) p. 20, Problem 2.1.g p. 20
(solution p. 495), eq. (2.2.11) p. 22.
Refs #5455.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace

/-! ## R0-scalar: the scalar phase identity -/

/-- R0-scalar pin: locks the exact name/signature of the scalar phase identity
`exp(−iπ(N/2 − k)) = (−i)^N (−1)^k`, the sole computation behind the axis-3
identification. -/
example (N : ℕ) (k : Fin (N + 1)) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) * spinSOp3Eigen N k) =
      ((-Complex.I) ^ N) * (-1 : ℂ) ^ (k : ℕ) :=
  spinSOp3Eigen_exp_neg_pi_mul_I_eq N k

/-! ## R0: the axis-3 exponential identification -/

/-- R0 pin: locks the exact name/signature of the axis-3 identification, Tasaki (2.1.34), third
relation, p. 20 (Problem 2.1.g, p. 20). -/
example (N : ℕ) : spinSPiRotation3 N = spinSRot3 N Real.pi :=
  spinSPiRotation3_eq_spinSRot3_pi N

/-! ## Definitional guard: the exponential side is a genuine `exp` -/

/-- Guards that the exponential object of the identification is the genuine `NormedSpace.exp` of
`Ŝ^{(3)}`: if `spinSRot3` were redefined as its own diagonal closed form, every statement below
would still hold while the content of (2.1.34) — closed form *equals* operator exponential — had
evaporated. -/
example (N : ℕ) (θ : ℝ) :
    spinSRot3 N θ = NormedSpace.exp (-(((θ : ℂ) * Complex.I)) • spinSOp3 N) := rfl

/-! ## Positive controls, zero hypotheses -/

/-- Positive control at `N = 1` (`S = 1/2`): the axis-3 identification instantiated, cross-checked
against the concrete `2 × 2` diagonal `!![-I, 0; 0, I]` via the existing `spinSRot3_eq_diagonal`
closed form. -/
example :
    spinSPiRotation3 1 = spinSRot3 1 Real.pi ∧
      spinSPiRotation3 1 = !![(-Complex.I : ℂ), 0; 0, Complex.I] := by
  refine ⟨spinSPiRotation3_eq_spinSRot3_pi 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]

/-- Positive control at `N = 2` (`S = 1`): the diagonal entries are
`(−i)^2 (−1)^k = −(−1)^k`, i.e. `!![-1, 0, 0; 0, 1, 0; 0, 0, -1]`. -/
example :
    spinSPiRotation3 2 = spinSRot3 2 Real.pi ∧
      spinSPiRotation3 2 =
        !![(-1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1] := by
  refine ⟨spinSPiRotation3_eq_spinSRot3_pi 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]

/-- Positive control at `N = 3` (`S = 3/2`, odd `N`, the sign-sensitive case): the phase
`(−i)^3 = i` multiplies the alternating diagonal `(−1)^k`, giving
`!![i, 0, 0, 0; 0, -i, 0, 0; 0, 0, i, 0; 0, 0, 0, -i]`. -/
example :
    spinSPiRotation3 3 = spinSRot3 3 Real.pi ∧
      spinSPiRotation3 3 =
        !![Complex.I, 0, 0, 0; 0, (-Complex.I : ℂ), 0, 0; 0, 0, Complex.I, 0;
           0, 0, 0, (-Complex.I : ℂ)] := by
  refine ⟨spinSPiRotation3_eq_spinSRot3_pi 3, ?_⟩
  have hI3 : (-Complex.I : ℂ) ^ 3 = Complex.I := by
    have h2 : (-Complex.I : ℂ) ^ 2 = -1 := by
      rw [sq, neg_mul_neg, Complex.I_mul_I]
    rw [pow_succ, h2, neg_one_mul, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne,
      hI3]
  ring

end LatticeSystem.Quantum
