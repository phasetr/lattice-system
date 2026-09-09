import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import LatticeSystem.Quantum.SpinS.SpinSReversal

/-!
# The spin-`S` `π` rotations `û_α` in closed form

Tasaki's `{1̂, û₁, û₂, û₃}` of eq. (2.1.29), p. 19: the `π` rotations about the three axes, which
for half-odd-integer spin square to `−1̂` (eq. (2.1.31), p. 20) and anticommute (eq. (2.1.25),
p. 18).  The rotations about axes `1` and `3` are built first, the remaining one as the printed
product `û₂ = û₃û₁`, and the three are collected into the axis-indexed family
`spinSPiRotationAxis`.  That printed product is the matrix part of the time reversal
`Θ̂ = û₂K̂` of p. 278; the reversed product `û₁û₃ = (−1)^{2S}û₂`, built here as well, has the same
square and so carries the identity `Θ̂² = −1̂`.

The sign convention is the book's, `û_α := Û_π^{(α)} = exp(−iπ Ŝ^{(α)})` (p. 19), so that the
many-body products of eq. (2.2.11), p. 22, are the printed ones.

In the `Ŝ^{(3)}` eigenbasis `|S, m_k⟩` with `m_k = S − k` and `N = 2S`, the two rotations are
diagonal resp. antidiagonal:

* `exp(−iπ Ŝ^{(3)})|S, m⟩ = e^{−iπm}|S, m⟩`, and `e^{−iπ(N/2 − k)} = (−i)^N (−1)^k`;
* `exp(−iπ Ŝ^{(1)})|S, m⟩ = (−i)^{2S}|S, −m⟩ = (−i)^N |S, −m⟩`, the standard `π` rotation about
  the `1` axis (at `S = 1/2` this is `exp(−iπσ^x/2) = −iσ^x`, at `S = 1` it is the `−1` times the
  reversal that `spinOneHalfTurnS` writes as `1̂ − 2(Ŝ^{(1)})²`; both `S = 1` identifications are
  pinned in `LatticeSystem/Tests/SPTMatrixProductIndex.lean`).

Both are therefore a fixed phase `(−i)^N` times a real involution, and that is how they are
**defined** here — by the eq. (2.1.24)/(2.1.25)-level algebra of those closed forms, as in
`Quantum/SpinS/SpinOneHalfTurn.lean` (`S = 1`).  **The identification with `exp(−iπ Ŝ^{(α)})` at
general `S` is proved for all three axes**, by `spinSPiRotation1_eq_spinSRot1_pi` of
`Quantum/SpinS/SpinSPiRotationExpAxis1.lean`, `spinSPiRotation3_eq_spinSRot3_pi` of
`Quantum/SpinS/SpinSPiRotationExpAxis3.lean` and `spinSPiRotation2_eq_exp_spinSOp2` of
`Quantum/SpinS/SpinSPiRotationExpAxis2.lean`, uniformly `spinSPiRotationAxis_eq_exp` of the last
file.  No declaration in this file mentions `Matrix.exp` or `NormedSpace.exp`.  Exponential
rotations and bridges do exist elsewhere in the repository —
`spinSRot3 N θ = exp(−iθ Ŝ^{(3)})` of `Quantum/SpinS/Problem25cZAxisRotationInput.lean`, whose
closed form `spinSRot3_eq_diagonal` and general-`S` many-body bridge
`manyBodyTensorS_spinSRot3_eq_exp_totalSpinSOp3` are proved in
`Quantum/SpinS/Problem25cZAxisRotationCommutation.lean`, and `spinSRot1 N θ = exp(−iθ Ŝ^{(1)})`
of `Quantum/SpinS/SpinSRotation1.lean`, whose only closed form is the one at `θ = π`; the
general-`S` global exponentials `saturatedGlobalRot2` / `saturatedGlobalRot3` about the axes `2`
and `3` of `Quantum/SpinS/SaturatedCoherentAmplitude.lean`; the general-`S` twist bridge
`lsmTwistOperator_eq_diagonal` of `Quantum/SpinS/LiebSchultzMattisProof.lean`; and the spin-`1/2`
`totalSpinHalfRot{1,2,3}_eq_exp` of `Quantum/TotalSpin/Rotation.lean` — of these `spinSRot1` and
`spinSRot3` are related to the closed forms `spinSPiRotationAxis` built here, through the three
axis identifications above.  Every `exp(−iπ Ŝ^{(α)})` written in this file is now a proved
equality, not merely the book's notation for the closed-form matrix.

Since the two phases `(−i)^{2S}` multiply to the real sign `(−1)^{2S}`, the product `û₁û₃` is a
real matrix: entrywise conjugation — the operation `C_g` of eq. (8.3.40) at the antiunitary sign —
fixes it, which is what makes it a legitimate matrix part for an antiunitary symmetry.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1, eqs. (2.1.25), (2.1.29)–(2.1.31), pp. 18–20.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## The two real involutions

The basis reversal `|S, m⟩ ↦ |S, −m⟩` is the spin reversal `F` of
`Quantum/SpinS/SpinSReversal.lean`; only the alternating diagonal is new here. -/

/-- The **spin-`S` alternating diagonal** `k ↦ (−1)^k`, the phase pattern of `e^{−iπ m_k}` up to
the overall factor `(−i)^N`. -/
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

/-- **Tasaki eq. (2.1.25), p. 18, at the level of the two real involutions.**  Swapping them costs
the sign `(−1)^{2S}`: the reversal sends the basis index `k` to `N − k`, and
`(−1)^{N−k} = (−1)^N(−1)^k`.  For odd `N` this is the printed anticommutation, for even `N` the
printed commutation. -/
theorem spinSAlternating_mul_spinReversalS (N : ℕ) :
    spinSAlternating N * spinReversalS N =
      ((-1 : ℂ) ^ N) • (spinReversalS N * spinSAlternating N) := by
  ext i j
  rw [spinSAlternating, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.mul_diagonal, smul_eq_mul]
  rcases eq_or_ne i j.rev with h | h
  · subst h
    have hjle : (j : ℕ) ≤ N := Nat.lt_succ_iff.mp j.isLt
    have hrev : ((j.rev : Fin (N + 1)) : ℕ) = N - (j : ℕ) := by
      rw [Fin.val_rev]
      omega
    have hsq : (-1 : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ (j : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    have hsum : (-1 : ℂ) ^ (N - (j : ℕ)) * (-1 : ℂ) ^ (j : ℕ) = (-1 : ℂ) ^ N := by
      rw [← pow_add, Nat.sub_add_cancel hjle]
    have hsign : (-1 : ℂ) ^ (N - (j : ℕ)) = (-1 : ℂ) ^ N * (-1 : ℂ) ^ (j : ℕ) :=
      calc (-1 : ℂ) ^ (N - (j : ℕ))
          = (-1 : ℂ) ^ (N - (j : ℕ)) * ((-1 : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ (j : ℕ)) := by
            rw [hsq, mul_one]
        _ = (-1 : ℂ) ^ (N - (j : ℕ)) * (-1 : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ (j : ℕ) := by ring
        _ = (-1 : ℂ) ^ N * (-1 : ℂ) ^ (j : ℕ) := by rw [hsum]
    have hentry : spinReversalS N (Fin.rev j) j = 1 := by
      simp [spinReversalS_apply, Fin.rev_rev]
    rw [hentry, hrev, hsign]
    ring
  · have hentry : spinReversalS N i j = 0 := by
      rw [spinReversalS_apply, if_neg fun h' => h (Fin.rev_eq_iff.mp h'.symm)]
    rw [hentry, mul_zero, zero_mul, mul_zero]

/-! ## The `π` rotations -/

/-- **The spin-`S` `π` rotation about the `1` axis**, the book's `û₁ = exp(−iπ Ŝ^{(1)})` (p. 19),
*defined* by its closed form `(−i)^{2S}` times the basis reversal; the exponential identification
is `spinSPiRotation1_eq_spinSRot1_pi` of `Quantum/SpinS/SpinSPiRotationExpAxis1.lean`. -/
noncomputable def spinSPiRotation1 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ((-Complex.I) ^ N) • spinReversalS N

/-- **The spin-`S` `π` rotation about the `3` axis**, the book's `û₃ = exp(−iπ Ŝ^{(3)})` (p. 19),
*defined* by its closed form `(−i)^{2S}` times the alternating diagonal
(`e^{−iπ(N/2 − k)} = (−i)^N (−1)^k`); the exponential identification is
`spinSPiRotation3_eq_spinSRot3_pi` of `Quantum/SpinS/SpinSPiRotationExpAxis3.lean`. -/
noncomputable def spinSPiRotation3 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ((-Complex.I) ^ N) • spinSAlternating N

/-- `(−i)^N · conj((−i)^N) = 1`: the normalising factor of the closed forms is a phase. -/
private theorem neg_I_pow_mul_conj (N : ℕ) :
    (-Complex.I) ^ N * (starRingEnd ℂ) ((-Complex.I) ^ N) = 1 := by
  rw [map_pow, ← mul_pow, map_neg, Complex.conj_I, neg_neg, neg_mul, Complex.I_mul_I, neg_neg,
    one_pow]

/-- `((−i)^N)² = (−1)^{2S}`, the square of the normalising factor. -/
private theorem neg_I_pow_sq (N : ℕ) :
    (-Complex.I) ^ N * (-Complex.I) ^ N = (-1 : ℂ) ^ N := by
  rw [← mul_pow, neg_mul_neg, Complex.I_mul_I]

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
  smul_involution_mem_unitaryGroup _ (neg_I_pow_mul_conj N) (spinReversalS_conjTranspose N)
    (spinReversalS_mul_self N)

/-- `û₃` is unitary. -/
theorem spinSPiRotation3_mem_unitaryGroup (N : ℕ) :
    spinSPiRotation3 N ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ :=
  smul_involution_mem_unitaryGroup _ (neg_I_pow_mul_conj N) (spinSAlternating_conjTranspose N)
    (spinSAlternating_mul_self N)

/-- **`û₁² = (−1)^{2S}`** (eq. (2.1.31), p. 20): the `π` rotation squares to the `2π` rotation,
which is `−1̂` exactly for half-odd-integer spin. -/
theorem spinSPiRotation1_mul_self_of_odd {N : ℕ} (hN : Odd N) :
    spinSPiRotation1 N * spinSPiRotation1 N = -1 := by
  rw [spinSPiRotation1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_I_pow_sq,
    spinReversalS_mul_self, hN.neg_one_pow, neg_one_smul]

/-- **`û₃² = (−1)^{2S}`** (eq. (2.1.31), p. 20). -/
theorem spinSPiRotation3_mul_self_of_odd {N : ℕ} (hN : Odd N) :
    spinSPiRotation3 N * spinSPiRotation3 N = -1 := by
  rw [spinSPiRotation3, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_I_pow_sq,
    spinSAlternating_mul_self, hN.neg_one_pow, neg_one_smul]

/-- **Tasaki eq. (2.1.25), p. 18**: swapping two `π` rotations about distinct axes costs the sign
`(−1)^{2S}` — commutation for integer spin, anticommutation for half-odd-integer spin.  The two
phases `(−i)^{2S}` cancel between the sides, so the sign is the one carried by the underlying real
involutions. -/
theorem spinSPiRotation3_mul_spinSPiRotation1 (N : ℕ) :
    spinSPiRotation3 N * spinSPiRotation1 N =
      ((-1 : ℂ) ^ N) • (spinSPiRotation1 N * spinSPiRotation3 N) := by
  rw [spinSPiRotation1, spinSPiRotation3, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, spinSAlternating_mul_spinReversalS, smul_smul,
    smul_smul]
  congr 1
  ring

/-! ## The reversed product `û₁û₃`: the square of the time reversal (p. 278) -/

/-- **The product of the two `π` rotations is real**: the two phases `(−i)^{2S}` multiply to the
sign `(−1)^{2S}`, leaving the real matrix `F·D`. -/
theorem spinSPiRotation1_mul_spinSPiRotation3 (N : ℕ) :
    spinSPiRotation1 N * spinSPiRotation3 N =
      ((-1 : ℂ) ^ N) • (spinReversalS N * spinSAlternating N) := by
  rw [spinSPiRotation1, spinSPiRotation3, Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_I_pow_sq]

/-- **`(û₁û₃)² = −1̂` for half-odd-integer spin**, the identity `Θ̂² = −1̂` of Tasaki p. 278 for
the time reversal `Θ̂ = û₂K̂`: the reversed product is `û₁û₃ = (−1)^{2S}û₂`, so it has the same
square as the matrix part `û₂`.  The two rotations anticommute (eq. (2.1.25), p. 18) and each
squares to `−1̂` (eq. (2.1.31), p. 20), so the three signs combine to one. -/
theorem spinSPiRotation1_mul_spinSPiRotation3_mul_self_of_odd {N : ℕ} (hN : Odd N) :
    (spinSPiRotation1 N * spinSPiRotation3 N) * (spinSPiRotation1 N * spinSPiRotation3 N) =
      -1 := by
  have hanti : spinSPiRotation3 N * spinSPiRotation1 N =
      -(spinSPiRotation1 N * spinSPiRotation3 N) := by
    rw [spinSPiRotation3_mul_spinSPiRotation1, hN.neg_one_pow, neg_one_smul]
  calc (spinSPiRotation1 N * spinSPiRotation3 N) * (spinSPiRotation1 N * spinSPiRotation3 N)
      = spinSPiRotation1 N * (spinSPiRotation3 N * spinSPiRotation1 N) * spinSPiRotation3 N := by
        simp only [Matrix.mul_assoc]
    _ = spinSPiRotation1 N * -(spinSPiRotation1 N * spinSPiRotation3 N) * spinSPiRotation3 N := by
        rw [hanti]
    _ = -((spinSPiRotation1 N * spinSPiRotation1 N) *
          (spinSPiRotation3 N * spinSPiRotation3 N)) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -1 := by
        rw [spinSPiRotation1_mul_self_of_odd hN, spinSPiRotation3_mul_self_of_odd hN,
          neg_mul_neg, mul_one]

/-! ## The axis-indexed family `û_α`

Tasaki's third `π` rotation is the printed product `û₂ = û₃û₁` of eq. (2.1.29), p. 19, and the
three rotations are collected into one family indexed by `α : Fin 3` (index `0, 1, 2` for the
axes `1, 2, 3`).  The family is what the many-body layer of eq. (2.2.11), p. 22, multiplies over
the lattice. -/

/-- **The spin-`S` `π` rotation about the `2` axis**, `û₂ = û₃û₁` — the printed cyclic relation of
Tasaki eq. (2.1.29), p. 19, taken as the closed form of the remaining rotation. -/
noncomputable def spinSPiRotation2 (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  spinSPiRotation3 N * spinSPiRotation1 N

/-- **The axis-indexed family `û_α`** of Tasaki eq. (2.1.29), p. 19: the index `α : Fin 3` selects
the rotation about axis `α + 1`, so `0 ↦ û₁`, `1 ↦ û₂`, `2 ↦ û₃`. -/
noncomputable def spinSPiRotationAxis (N : ℕ) (α : Fin 3) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ![spinSPiRotation1 N, spinSPiRotation2 N, spinSPiRotation3 N] α

/-- **Tasaki eq. (2.1.25), p. 18, uniform in the axis pair**: for any two distinct axes, swapping
the two `π` rotations costs the sign `(−1)^{2S}`.  The `û₁`/`û₃` case is
`spinSPiRotation3_mul_spinSPiRotation1`; the cases involving `û₂ = û₃û₁` follow from it by
associativity, and the reversed orientations by `((−1)^{2S})² = 1`. -/
theorem spinSPiRotationAxis_swap_mul_of_ne {N : ℕ} {α β : Fin 3} (h : α ≠ β) :
    spinSPiRotationAxis N β * spinSPiRotationAxis N α =
      ((-1 : ℂ) ^ N) • (spinSPiRotationAxis N α * spinSPiRotationAxis N β) := by
  have hsq : ((-1 : ℂ) ^ N) * ((-1 : ℂ) ^ N) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hflip : ∀ A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      A * B = ((-1 : ℂ) ^ N) • (B * A) → B * A = ((-1 : ℂ) ^ N) • (A * B) := by
    intro A B hAB
    rw [hAB, smul_smul, hsq, one_smul]
  have h31 := spinSPiRotation3_mul_spinSPiRotation1 N
  have h21 : spinSPiRotation2 N * spinSPiRotation1 N =
      ((-1 : ℂ) ^ N) • (spinSPiRotation1 N * spinSPiRotation2 N) :=
    calc spinSPiRotation2 N * spinSPiRotation1 N
        = spinSPiRotation3 N * spinSPiRotation1 N * spinSPiRotation1 N := rfl
      _ = (((-1 : ℂ) ^ N) • (spinSPiRotation1 N * spinSPiRotation3 N)) *
            spinSPiRotation1 N := by rw [h31]
      _ = ((-1 : ℂ) ^ N) •
            (spinSPiRotation1 N * (spinSPiRotation3 N * spinSPiRotation1 N)) := by
            rw [Matrix.smul_mul, Matrix.mul_assoc]
      _ = ((-1 : ℂ) ^ N) • (spinSPiRotation1 N * spinSPiRotation2 N) := rfl
  have h32 : spinSPiRotation3 N * spinSPiRotation2 N =
      ((-1 : ℂ) ^ N) • (spinSPiRotation2 N * spinSPiRotation3 N) :=
    calc spinSPiRotation3 N * spinSPiRotation2 N
        = spinSPiRotation3 N * (spinSPiRotation3 N * spinSPiRotation1 N) := rfl
      _ = spinSPiRotation3 N *
            (((-1 : ℂ) ^ N) • (spinSPiRotation1 N * spinSPiRotation3 N)) := by rw [h31]
      _ = ((-1 : ℂ) ^ N) •
            (spinSPiRotation3 N * spinSPiRotation1 N * spinSPiRotation3 N) := by
            rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = ((-1 : ℂ) ^ N) • (spinSPiRotation2 N * spinSPiRotation3 N) := rfl
  fin_cases α <;> fin_cases β <;>
    simp only [spinSPiRotationAxis] <;>
    first
      | exact absurd rfl h
      | exact h31
      | exact h21
      | exact h32
      | exact hflip _ _ h31
      | exact hflip _ _ h21
      | exact hflip _ _ h32

/-- Every `û_α` is unitary: axes `1` and `3` are the closed forms above, and `û₂ = û₃û₁` is a
product of two unitaries. -/
theorem spinSPiRotationAxis_mem_unitaryGroup (N : ℕ) (α : Fin 3) :
    spinSPiRotationAxis N α ∈ Matrix.unitaryGroup (Fin (N + 1)) ℂ := by
  fin_cases α <;>
    simp only [spinSPiRotationAxis, spinSPiRotation2]
  · exact spinSPiRotation1_mem_unitaryGroup N
  · exact mul_mem (spinSPiRotation3_mem_unitaryGroup N) (spinSPiRotation1_mem_unitaryGroup N)
  · exact spinSPiRotation3_mem_unitaryGroup N

end LatticeSystem.Quantum
