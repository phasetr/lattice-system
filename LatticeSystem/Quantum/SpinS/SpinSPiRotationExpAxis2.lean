import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis1
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis3

/-!
# The axis-2 `π` rotation as an exponential

The closed-form `π` rotation `û₂` of `Quantum/SpinS/SpinSPiRotation.lean` is the exponential
`Û_π^{(2)} = exp(−iπ Ŝ^{(2)})` of the definition on p. 15, at general spin `S = N/2`: this is the
second relation of the closed form (2.1.34), p. 20, whose general-`S` derivation is left to the
reader as Problem 2.1.g, p. 20 (solution p. 495).  Together with the axis-1 and axis-3 modules it
completes the single-site family `û_α = exp(−iπ Ŝ^{(α)})`.

The route is conjugation by a quarter turn about axis 3.  The rotation `spinSRot3 N (−π/2)`
carries `Ŝ^{(2)}` to `Ŝ^{(1)}` (the `π/2` case of (2.1.25), p. 18), so the intertwining bridge
`matrix_exp_intertwine_of_pow_intertwine` — no inverse, no unit packaging — turns the axis-1
exponential into the axis-2 one.  The matching closed-form half is the *angle flip*
`F · spinSRot3 N θ = spinSRot3 N (−θ) · F`: it collapses the two quarter turns flanking the
reversal `F` of `û₁` into the half turn `spinSRot3 N π`, which is `û₃` by the axis-3 module, and
so reproduces the printed product `û₂ = û₃û₁` of eq. (2.1.29), p. 19.

Only the orientation `spinSRot3 N (−π/2) · Ŝ^{(2)} · spinSRot3 N (π/2) = Ŝ^{(1)}` gives the
axis-2 exponential; the opposite quarter turn produces `exp(+iπ Ŝ^{(1)})`, which differs by
`(−1)^{2S}`.  The same sign separates the printed order `û₃û₁` from `û₁û₃`, the matrix part of the
time reversal `Θ̂` of p. 278.  Statements therefore keep the angles written out and use the
integer basis index `k` of `Fin (N + 1)` rather than the magnetic quantum number `σ = N/2 − k`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1: the rotation `Û_θ^{(α)} = exp(−iθ Ŝ^{(α)})`, p. 15; the `π`-rotation relation
(2.1.25), p. 18; the cyclic relation (2.1.29), p. 19; the closed form (2.1.34) and Problem 2.1.g,
p. 20 (solution p. 495).
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## The reversal past a `z`-rotation -/

/-- The basis reversal negates the `Ŝ^{(3)}` eigenvalue: `m_{rev k} = −m_k`, i.e.
`N/2 − (N − k) = −(N/2 − k)`.  This is the arithmetic content of the angle flip below. -/
private lemma spinSOp3Eigen_rev (N : ℕ) (k : Fin (N + 1)) :
    spinSOp3Eigen N (Fin.rev k) = -spinSOp3Eigen N k := by
  have hk : (k : ℕ) ≤ N := Nat.lt_succ_iff.mp k.isLt
  have hrev : ((Fin.rev k : Fin (N + 1)) : ℕ) = N - (k : ℕ) := by
    rw [Fin.val_rev]
    omega
  unfold spinSOp3Eigen
  rw [hrev, Nat.cast_sub hk]
  ring

/-- **The angle flip**: moving the basis reversal `F` past a rotation about axis 3 reverses the
angle, `F · exp(−iθ Ŝ^{(3)}) = exp(+iθ Ŝ^{(3)}) · F`.  The rotation is diagonal, `F` permutes the
basis by `k ↦ N − k`, and the eigenvalue `m_k` changes sign under that permutation.  It is the
matrix form of the axis-1 `π` rotation reversing axis 3 (Tasaki (2.1.25), p. 18). -/
theorem spinReversalS_mul_spinSRot3 (N : ℕ) (θ : ℝ) :
    spinReversalS N * spinSRot3 N θ = spinSRot3 N (-θ) * spinReversalS N := by
  rw [spinSRot3_eq_diagonal, spinSRot3_eq_diagonal]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases eq_or_ne j (Fin.rev i) with h | h
  · subst h
    rw [spinReversalS_apply, if_pos rfl, one_mul, mul_one, spinSOp3Eigen_rev]
    congr 1
    push_cast
    ring
  · rw [spinReversalS_apply, if_neg h, zero_mul, mul_zero]

/-- **The quarter-turn conjugate of `û₁` is `û₂`**, entirely in closed forms: conjugating the
axis-1 `π` rotation `û₁ = (−i)^{2S}F` by the quarter turn `spinSRot3 N (π/2)` produces the printed
product `û₂ = û₃û₁` of Tasaki eq. (2.1.29), p. 19.  The angle flip turns the trailing quarter turn
into a leading one, the two combine into the half turn `spinSRot3 N π = û₃`
(`spinSPiRotation3_eq_spinSRot3_pi`), and the reversal is left carrying the phase of `û₁`. -/
theorem spinSRot3_pi_half_conj_spinSPiRotation1 (N : ℕ) :
    spinSRot3 N (Real.pi / 2) * spinSPiRotation1 N * spinSRot3 N (-(Real.pi / 2)) =
      spinSPiRotation2 N := by
  have hflip : spinReversalS N * spinSRot3 N (-(Real.pi / 2))
      = spinSRot3 N (Real.pi / 2) * spinReversalS N := by
    have h := spinReversalS_mul_spinSRot3 N (-(Real.pi / 2))
    rwa [show -(-(Real.pi / 2)) = (Real.pi / 2 : ℝ) from by ring] at h
  have hhalf : spinSRot3 N (Real.pi / 2) * spinSRot3 N (Real.pi / 2) = spinSRot3 N Real.pi := by
    rw [spinSRot3_mul, show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]
  calc spinSRot3 N (Real.pi / 2) * spinSPiRotation1 N * spinSRot3 N (-(Real.pi / 2))
      = ((-Complex.I) ^ N) •
          (spinSRot3 N (Real.pi / 2) * (spinReversalS N * spinSRot3 N (-(Real.pi / 2)))) := by
        rw [spinSPiRotation1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = ((-Complex.I) ^ N) •
          (spinSRot3 N (Real.pi / 2) * (spinSRot3 N (Real.pi / 2) * spinReversalS N)) := by
        rw [hflip]
    _ = spinSRot3 N Real.pi * (((-Complex.I) ^ N) • spinReversalS N) := by
        rw [← Matrix.mul_assoc, hhalf, Matrix.mul_smul]
    _ = spinSPiRotation2 N := by
        rw [spinSPiRotation2, spinSPiRotation3_eq_spinSRot3_pi, spinSPiRotation1]
end LatticeSystem.Quantum
