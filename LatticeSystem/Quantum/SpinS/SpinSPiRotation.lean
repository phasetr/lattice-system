import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import LatticeSystem.Quantum.SpinS.SpinSReversal

/-!
# The spin-`S` `π` rotations `û_α = exp(iπ Ŝ^{(α)})` in closed form

Tasaki's `{1̂, û₁, û₂, û₃}` of eq. (2.1.29): the `π` rotations about the three axes, which for
half-odd-integer spin square to `−1̂` and anticommute (eq. (2.1.31)).  Only the two rotations about
axes `1` and `3` are built here, together with their product `û₁û₃`, which supplies the matrix part
of the time reversal `Θ̂` of p. 278.

In the `Ŝ^{(3)}` eigenbasis `|S, m_k⟩` with `m_k = S − k` and `N = 2S`, the two rotations are
diagonal resp. antidiagonal:

* `exp(iπ Ŝ^{(3)})|S, m⟩ = e^{iπm}|S, m⟩`, and `e^{iπ(N/2 − k)} = i^N (−1)^k`;
* `exp(iπ Ŝ^{(1)})|S, m⟩ = i^{2S}|S, −m⟩ = i^N |S, −m⟩`, the standard `π` rotation about the
  `1` axis (at `S = 1/2` this is `exp(iπσ^x/2) = iσ^x`, at `S = 1` it is the `−1` times the
  reversal that `spinOneHalfTurnS` writes as `1̂ − 2(Ŝ^{(1)})²`; both `S = 1` identifications are
  pinned in `LatticeSystem/Tests/SPTMatrixProductIndex.lean`).

Both are therefore a fixed phase `i^N` times a real involution, and that is how they are defined:
as in `Quantum/SpinS/SpinOneHalfTurn.lean` (`S = 1`) no Lean bridge to `NormedSpace.exp` is
attempted — it is off the critical path, and the repository already lets a concrete matrix and its
`exp` form coexist without a proved bridge.

Since the two phases `i^{2S}` multiply to the real sign `(−1)^{2S}`, the product `û₁û₃` is a real
matrix: entrywise conjugation — the operation `C_g` of eq. (8.3.40) at the antiunitary sign —
fixes it, which is what makes it a legitimate matrix part for an antiunitary symmetry.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1, eqs. (2.1.29)–(2.1.31), pp. 18–19.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## The two real involutions

The basis reversal `|S, m⟩ ↦ |S, −m⟩` is the spin reversal `F` of
`Quantum/SpinS/SpinSReversal.lean`; only the alternating diagonal is new here. -/

/-- The **spin-`S` alternating diagonal** `k ↦ (−1)^k`, the phase pattern of `e^{iπ m_k}` up to the
overall factor `i^N`. -/
def spinSAlternating (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.diagonal fun k => (-1 : ℂ) ^ (k : ℕ)

/-- The alternating diagonal is real, hence self-adjoint. -/
theorem spinSAlternating_conjTranspose (N : ℕ) :
    (spinSAlternating N).conjTranspose = spinSAlternating N := by
  ext i j
  rcases eq_or_ne i j with h | h
  · subst h
    simp [spinSAlternating, Matrix.conjTranspose_apply]
  · simp [spinSAlternating, Matrix.conjTranspose_apply, Matrix.diagonal_apply_ne _ h,
      Matrix.diagonal_apply_ne _ h.symm]

/-- The alternating diagonal is an involution. -/
theorem spinSAlternating_mul_self (N : ℕ) : spinSAlternating N * spinSAlternating N = 1 := by
  rw [spinSAlternating, Matrix.diagonal_mul_diagonal]
  refine (Matrix.diagonal_one (n := Fin (N + 1)) (α := ℂ)) ▸ ?_
  congr 1
  funext k
  change (-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (k : ℕ) = 1
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- Entrywise complex conjugation fixes the alternating diagonal: all its entries are `0` or
`±1`. -/
theorem spinSAlternating_map_conj (N : ℕ) :
    (spinSAlternating N).map (starRingEnd ℂ) = spinSAlternating N := by
  ext i j
  by_cases h : i = j <;> simp [spinSAlternating, Matrix.map_apply, h]

/-- **Tasaki eq. (2.1.31) for half-odd-integer spin.**  The two involutions anticommute exactly
when `N = 2S` is odd: the reversal sends the basis index `k` to `N − k`, and `(−1)^{N−k} = −(−1)^k`
precisely for odd `N`. -/
theorem spinSAlternating_mul_spinReversalS_of_odd {N : ℕ} (hN : Odd N) :
    spinSAlternating N * spinReversalS N = -(spinReversalS N * spinSAlternating N) := by
  ext i j
  rw [spinSAlternating, Matrix.diagonal_mul, Matrix.neg_apply, Matrix.mul_diagonal]
  rcases eq_or_ne i j.rev with h | h
  · subst h
    have hjle : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
    have hrev : ((j.rev : Fin (N + 1)) : ℕ) = N - (j : ℕ) := by
      rw [Fin.val_rev]
      omega
    have hsq : (-1 : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ (j : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    have hsum : (-1 : ℂ) ^ (N - (j : ℕ)) * (-1 : ℂ) ^ (j : ℕ) = -1 := by
      rw [← pow_add, Nat.sub_add_cancel hjle, hN.neg_one_pow]
    have hsign : (-1 : ℂ) ^ (N - (j : ℕ)) = -((-1 : ℂ) ^ (j : ℕ)) :=
      calc (-1 : ℂ) ^ (N - (j : ℕ))
          = (-1 : ℂ) ^ (N - (j : ℕ)) * ((-1 : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ (j : ℕ)) := by
            rw [hsq, mul_one]
        _ = (-1 : ℂ) ^ (N - (j : ℕ)) * (-1 : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ (j : ℕ) := by ring
        _ = -((-1 : ℂ) ^ (j : ℕ)) := by rw [hsum]; ring
    have hentry : spinReversalS N (Fin.rev j) j = 1 := by
      simp [spinReversalS_apply, Fin.rev_rev]
    rw [hentry, hrev, hsign]
    ring
  · have hentry : spinReversalS N i j = 0 := by
      rw [spinReversalS_apply, if_neg fun h' => h (Fin.rev_eq_iff.mp h'.symm)]
    rw [hentry, mul_zero, zero_mul, neg_zero]

/-! ## The `π` rotations -/

/-- **The spin-`S` `π` rotation about the `1` axis**, `û₁ = exp(iπ Ŝ^{(1)})`, in the closed form
`i^{2S}` times the basis reversal (eq. (2.1.29)). -/
noncomputable def spinSPiRotation1 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (Complex.I ^ N) • spinReversalS N

/-- **The spin-`S` `π` rotation about the `3` axis**, `û₃ = exp(iπ Ŝ^{(3)})`, in the closed form
`i^{2S}` times the alternating diagonal: `e^{iπ(N/2 − k)} = i^N (−1)^k` (eq. (2.1.29)). -/
noncomputable def spinSPiRotation3 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  (Complex.I ^ N) • spinSAlternating N

/-- `i^N · conj(i^N) = 1`: the normalising factor of the closed forms is a phase. -/
private theorem I_pow_mul_conj (N : ℕ) :
    Complex.I ^ N * (starRingEnd ℂ) (Complex.I ^ N) = 1 := by
  rw [map_pow, Complex.conj_I, ← mul_pow]
  simp

/-- `(i^N)² = (−1)^{2S}`, the square of the normalising factor. -/
private theorem I_pow_sq (N : ℕ) : Complex.I ^ N * Complex.I ^ N = (-1 : ℂ) ^ N := by
  rw [← mul_pow, Complex.I_mul_I]

/-- A phase times a self-adjoint involution is unitary. -/
private theorem smul_involution_mem_unitaryGroup {N : ℕ} (z : ℂ)
    (hz : z * (starRingEnd ℂ) z = 1) {P : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hP : P.conjTranspose = P) (hPP : P * P = 1) :
    z • P ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul,
    hP, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hPP]
  change (z * (starRingEnd ℂ) z) • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) = 1
  rw [hz, one_smul]

/-- `û₁` is unitary. -/
theorem spinSPiRotation1_mem_unitaryGroup (N : ℕ) :
    spinSPiRotation1 N ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ :=
  smul_involution_mem_unitaryGroup _ (I_pow_mul_conj N) (spinReversalS_conjTranspose N)
    (spinReversalS_mul_self N)

/-- `û₃` is unitary. -/
theorem spinSPiRotation3_mem_unitaryGroup (N : ℕ) :
    spinSPiRotation3 N ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ :=
  smul_involution_mem_unitaryGroup _ (I_pow_mul_conj N) (spinSAlternating_conjTranspose N)
    (spinSAlternating_mul_self N)

/-- **`û₁² = (−1)^{2S}`** (eq. (2.1.30)): the `π` rotation squares to the `2π` rotation, which is
`−1̂` exactly for half-odd-integer spin. -/
theorem spinSPiRotation1_mul_self_of_odd {N : ℕ} (hN : Odd N) :
    spinSPiRotation1 N * spinSPiRotation1 N = -1 := by
  rw [spinSPiRotation1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_pow_sq,
    spinReversalS_mul_self, hN.neg_one_pow, neg_one_smul]

/-- **`û₃² = (−1)^{2S}`** (eq. (2.1.30)). -/
theorem spinSPiRotation3_mul_self_of_odd {N : ℕ} (hN : Odd N) :
    spinSPiRotation3 N * spinSPiRotation3 N = -1 := by
  rw [spinSPiRotation3, Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_pow_sq,
    spinSAlternating_mul_self, hN.neg_one_pow, neg_one_smul]

/-- **Tasaki eq. (2.1.31)**: for half-odd-integer spin the two `π` rotations anticommute. -/
theorem spinSPiRotation3_mul_spinSPiRotation1_of_odd {N : ℕ} (hN : Odd N) :
    spinSPiRotation3 N * spinSPiRotation1 N =
      -(spinSPiRotation1 N * spinSPiRotation3 N) := by
  rw [spinSPiRotation1, spinSPiRotation3, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, spinSAlternating_mul_spinReversalS_of_odd hN,
    smul_neg]

/-! ## The product `û₁û₃`: the matrix part of the time reversal (p. 278) -/

/-- **The product of the two `π` rotations is real**: the two phases `i^{2S}` multiply to the sign
`(−1)^{2S}`, leaving the real matrix `F·D`. -/
theorem spinSPiRotation1_mul_spinSPiRotation3 (N : ℕ) :
    spinSPiRotation1 N * spinSPiRotation3 N =
      ((-1 : ℂ) ^ N) • (spinReversalS N * spinSAlternating N) := by
  rw [spinSPiRotation1, spinSPiRotation3, Matrix.smul_mul, Matrix.mul_smul, smul_smul, I_pow_sq]

/-- **`(û₁û₃)² = −1̂` for half-odd-integer spin**, the identity `Θ̂² = −1̂` of Tasaki p. 278 for
the time reversal `Θ̂ = û₁û₃ K̂`: the two rotations anticommute (eq. (2.1.31)) and each squares to
`−1̂` (eq. (2.1.30)), so the three signs combine to one. -/
theorem spinSPiRotation1_mul_spinSPiRotation3_mul_self_of_odd {N : ℕ} (hN : Odd N) :
    (spinSPiRotation1 N * spinSPiRotation3 N) * (spinSPiRotation1 N * spinSPiRotation3 N) =
      -1 := by
  calc (spinSPiRotation1 N * spinSPiRotation3 N) * (spinSPiRotation1 N * spinSPiRotation3 N)
      = spinSPiRotation1 N * (spinSPiRotation3 N * spinSPiRotation1 N) * spinSPiRotation3 N := by
        simp only [Matrix.mul_assoc]
    _ = spinSPiRotation1 N * -(spinSPiRotation1 N * spinSPiRotation3 N) * spinSPiRotation3 N := by
        rw [spinSPiRotation3_mul_spinSPiRotation1_of_odd hN]
    _ = -((spinSPiRotation1 N * spinSPiRotation1 N) *
          (spinSPiRotation3 N * spinSPiRotation3 N)) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -1 := by
        rw [spinSPiRotation1_mul_self_of_odd hN, spinSPiRotation3_mul_self_of_odd hN,
          neg_mul_neg, mul_one]

end LatticeSystem.Quantum
