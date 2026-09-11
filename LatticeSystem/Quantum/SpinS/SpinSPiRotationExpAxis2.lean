import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis1
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis3

/-!
# The axis-2 `π` rotation as an exponential

The closed-form `π` rotation `û₂` of `Quantum/SpinS/SpinSPiRotation.lean` is the exponential
`Û_π^{(2)} = exp(−iπ Ŝ^{(2)})` of the definition on p. 15, at general spin `S = N/2`: this is the
second relation of the closed form (2.1.34), p. 20, whose general-`S` derivation is left to the
reader as Problem 2.1.g, p. 20 (solution p. 495).  The printed entries
`⟨ψ_σ|û₂|ψ_τ⟩ = (−1)^{S+σ}δ_{σ,−τ}` of that relation are `spinSPiRotation2_apply`, written in the
integer basis index.  Together with the axis-1 and axis-3 modules this completes the single-site
family `û_α = exp(−iπ Ŝ^{(α)})`.

The route is conjugation by a quarter turn about axis 3.  The rotation `spinSRot3 N (−π/2)`
carries `Ŝ^{(2)}` to `Ŝ^{(1)}` (the `π/2` case of (2.1.22), p. 17), so the intertwining bridge
`matrix_exp_intertwine_of_pow_intertwine` — no inverse, no unit packaging — turns the axis-1
exponential into the axis-2 one.  The matching closed-form half is the *angle flip*
`F · spinSRot3 N θ = spinSRot3 N (−θ) · F`: it collapses the two quarter turns flanking the
reversal `F` of `û₁` into the half turn `spinSRot3 N π`, which is `û₃` by the axis-3 module, and
so reproduces the printed product `û₂ = û₃û₁` of eq. (2.1.29), p. 19.

Only the orientation `spinSRot3 N (−π/2) · Ŝ^{(2)} · spinSRot3 N (π/2) = Ŝ^{(1)}` gives the
axis-2 exponential; the opposite quarter turn produces `exp(+iπ Ŝ^{(1)})`, which differs by
`(−1)^{2S}`.  The same sign separates the printed order `û₃û₁` — which is the matrix part of the
time reversal `Θ̂ = û₂K̂` of p. 278 — from the reversed product `û₁û₃ = (−1)^{2S}û₂`.  Statements
therefore keep the angles written out and use the integer basis index `k` of `Fin (N + 1)` rather
than the magnetic quantum number `σ = N/2 − k`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1: the rotation `Û_θ^{(α)} = exp(−iθ Ŝ^{(α)})`, p. 15; the conjugation relations
(2.1.21) (`π` rotation) and (2.1.22) (quarter turn), p. 17; the cyclic relation (2.1.29), p. 19;
the closed form (2.1.34) and Problem 2.1.g, p. 20 (solution p. 495).
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
matrix form of the axis-1 `π` rotation reversing axis 3 (Tasaki (2.1.21), p. 17). -/
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

/-! ## The quarter turn as an axis swap on the generators -/

/-- **The axis swap in commutation form**: `Ŝ^{(1)} · spinSRot3 N (−π/2) =
spinSRot3 N (−π/2) · Ŝ^{(2)}`, the quarter-turn case of Tasaki (2.1.22), p. 17, obtained from
`spinSRot3_neg_pi_half_conj_spinSOp2` by cancelling the trailing rotation.  The orientation is
sign-critical: the opposite quarter turn sends `Ŝ^{(2)}` to `−Ŝ^{(1)}`. -/
theorem spinSOp1_mul_spinSRot3_neg_pi_half (N : ℕ) :
    spinSOp1 N * spinSRot3 N (-(Real.pi / 2)) = spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N := by
  have h := congrArg (fun M => M * spinSRot3 N (-(Real.pi / 2)))
    (spinSRot3_neg_pi_half_conj_spinSOp2 N)
  simp only [Matrix.mul_assoc] at h
  rw [spinSRot3_mul_neg, Matrix.mul_one] at h
  exact h.symm

/-- The axis swap propagated to all powers, the hypothesis shape the intertwining bridge
`matrix_exp_intertwine_of_pow_intertwine` consumes. -/
private lemma spinSOp1_pow_mul_spinSRot3_neg_pi_half (N n : ℕ) :
    spinSOp1 N ^ n * spinSRot3 N (-(Real.pi / 2)) =
      spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.mul_assoc, spinSOp1_mul_spinSRot3_neg_pi_half, ← Matrix.mul_assoc, ih,
      Matrix.mul_assoc, ← pow_succ]

/-! ## The axis-2 identification -/

/-- **The axis-2 exponential is a quarter-turn conjugate of the axis-1 one**:
`exp(−iπ Ŝ^{(2)}) = spinSRot3 N (π/2) · exp(−iπ Ŝ^{(1)}) · spinSRot3 N (−π/2)`.  The powers of the
generators intertwine through the quarter turn (`spinSOp1_pow_mul_spinSRot3_neg_pi_half`), so the
exponentials do as well by `matrix_exp_intertwine_of_pow_intertwine`; no inverse of the quarter
turn is needed, only the cancellation `spinSRot3_mul_neg`. -/
theorem exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_conj (N : ℕ) :
    NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) =
      spinSRot3 N (Real.pi / 2) * spinSRot1 N Real.pi * spinSRot3 N (-(Real.pi / 2)) := by
  have hint : NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp1 N) *
        spinSRot3 N (-(Real.pi / 2)) =
      spinSRot3 N (-(Real.pi / 2)) *
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) :=
    matrix_exp_intertwine_of_pow_intertwine
      (pow_smul_mul_of_pow_mul _ (spinSOp1_pow_mul_spinSRot3_neg_pi_half N))
  have hrot : spinSRot1 N Real.pi
      = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp1 N) := rfl
  calc NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N)
      = spinSRot3 N (Real.pi / 2) * spinSRot3 N (-(Real.pi / 2)) *
          NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) := by
        rw [spinSRot3_mul_neg, Matrix.one_mul]
    _ = spinSRot3 N (Real.pi / 2) * (spinSRot3 N (-(Real.pi / 2)) *
          NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N)) := Matrix.mul_assoc _ _ _
    _ = spinSRot3 N (Real.pi / 2) *
          (NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp1 N) *
            spinSRot3 N (-(Real.pi / 2))) := by rw [hint]
    _ = spinSRot3 N (Real.pi / 2) * spinSRot1 N Real.pi * spinSRot3 N (-(Real.pi / 2)) := by
        rw [hrot, Matrix.mul_assoc]

/-- **The axis-2 `π` rotation is the exponential `exp(−iπ Ŝ^{(2)})`** at every spin `S = N/2`: the
closed form `û₂ = û₃û₁` of `spinSPiRotation2` agrees with the rotation of the definition on p. 15.
This is the second relation of Tasaki (2.1.34), p. 20, left to the reader as Problem 2.1.g, p. 20
(solution p. 495).  Both sides are the same quarter-turn conjugate of the axis-1 `π` rotation: the
closed forms by `spinSRot3_pi_half_conj_spinSPiRotation1`, the exponentials by
`exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_conj`, and the two axis-1 descriptions agree by
`spinSPiRotation1_eq_spinSRot1_pi`. -/
theorem spinSPiRotation2_eq_exp_spinSOp2 (N : ℕ) :
    spinSPiRotation2 N = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) := by
  rw [← spinSRot3_pi_half_conj_spinSPiRotation1, spinSPiRotation1_eq_spinSRot1_pi,
    exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_conj]

/-! ## The printed entry form -/

/-- **The printed entries of `û₂`**: `⟨ψ_σ|û₂|ψ_τ⟩ = (−1)^{S+σ}δ_{σ,−τ}`, the second relation of
Tasaki (2.1.34), p. 20, in the integer basis index `k` of `Fin (N + 1)`.  Row `i` carries its
single nonzero entry in the column `rev i` (the printed `τ = −σ`) with the phase `(−1)^{N+i}`,
which is the printed `(−1)^{S+σ}` because `S + σ = N − i` has the parity of `N + i`. -/
theorem spinSPiRotation2_apply (N : ℕ) (i j : Fin (N + 1)) :
    spinSPiRotation2 N i j = if j = Fin.rev i then (-1 : ℂ) ^ (N + (i : ℕ)) else 0 := by
  have hsq : (-Complex.I) ^ N * (-Complex.I) ^ N = (-1 : ℂ) ^ N := by
    rw [← mul_pow, neg_mul_neg, Complex.I_mul_I]
  rw [spinSPiRotation2, spinSPiRotation3, spinSPiRotation1, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hsq, Matrix.smul_apply, spinSAlternating, Matrix.diagonal_mul, smul_eq_mul,
    spinReversalS_apply, pow_add]
  split <;> ring

/-- **The printed cyclic relation (2.1.29), p. 19, purely in exponentials**:
`exp(−iπ Ŝ^{(2)}) = exp(−iπ Ŝ^{(3)}) · exp(−iπ Ŝ^{(1)})`.  In the repository the relation `û₂ =
û₃û₁` is the *definition* of the axis-2 closed form; here it becomes a theorem about the rotations
of p. 15, which is what the book asserts.  The order matters: the printed `û₂ = û₃û₁` is the
matrix part of the time reversal `Θ̂ = û₂K̂`, p. 278, while the reversed product `û₁û₃` differs
from it by `(−1)^{2S}`. -/
theorem exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_pi_mul_spinSRot1_pi (N : ℕ) :
    NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) =
      spinSRot3 N Real.pi * spinSRot1 N Real.pi := by
  rw [← spinSPiRotation2_eq_exp_spinSOp2, spinSPiRotation2, spinSPiRotation3_eq_spinSRot3_pi,
    spinSPiRotation1_eq_spinSRot1_pi]

/-- **The whole axis family is exponential**: `û_α = exp(−iπ Ŝ^{(α)})` for every axis `α : Fin 3`,
the closed form (2.1.34), p. 20, in the uniform form of eq. (2.1.29), p. 19.  This is the
statement the many-body lift of eq. (2.2.11), p. 22, multiplies over the lattice — a
multiplication proved as `manyBodySPiRotation_eq_exp`. -/
theorem spinSPiRotationAxis_eq_exp (N : ℕ) (α : Fin 3) :
    spinSPiRotationAxis N α =
      NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) • (![spinSOp1 N, spinSOp2 N, spinSOp3 N] α)) := by
  have h1 : spinSRot1 N Real.pi
      = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp1 N) := rfl
  have h3 : spinSRot3 N Real.pi
      = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp3 N) := rfl
  fin_cases α
  · simpa only [spinSPiRotationAxis, Matrix.cons_val_zero] using
      (spinSPiRotation1_eq_spinSRot1_pi N).trans h1
  · simpa only [spinSPiRotationAxis, Matrix.cons_val_one, Matrix.head_cons] using
      spinSPiRotation2_eq_exp_spinSOp2 N
  · simpa only [spinSPiRotationAxis, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      using (spinSPiRotation3_eq_spinSRot3_pi N).trans h3

end LatticeSystem.Quantum
