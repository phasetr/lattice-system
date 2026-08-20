import LatticeSystem.Quantum.SpinS.Operators

/-!
# Single-site spin reversal (π-rotation about axis 1)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The single-site spin reversal `F` reverses the `Ŝ³` basis index `k ↦ N − k` (`Fin.rev`).  As a
linear unitary it is the π-rotation about axis 1: it conjugates `Ŝ³ ↦ −Ŝ³`, `Ŝ⁺ ↦ Ŝ⁻`,
`Ŝ⁻ ↦ Ŝ⁺` (hence `Ŝ¹ ↦ Ŝ¹`, `Ŝ² ↦ −Ŝ²`).  The many-site product `Θ = ⊗_x F` will give the
`M ↔ −M` reflection symmetry `Θ Ŝ³_tot Θ⁻¹ = −Ŝ³_tot` and `Θ Ĥ Θ⁻¹ = Ĥ` used in the
Mattis–Nishimori uniqueness argument (Theorem 2.4).

Being the axis-1 π rotation up to a phase, `F` is also the real involution underlying the closed
form of `û₁ = exp(iπ Ŝ^{(1)})` in `Quantum/SpinS/SpinSPiRotation.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {N : ℕ}

/-- **Single-site spin reversal** `F`: the permutation matrix of `Fin.rev` (`k ↦ N − k`). -/
noncomputable def spinReversalS (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of fun i j => if j = Fin.rev i then (1 : ℂ) else 0

/-- Entries of `F`: the row `i` carries its single `1` in the column `rev i`. -/
theorem spinReversalS_apply (i j : Fin (N + 1)) :
    spinReversalS N i j = if j = Fin.rev i then (1 : ℂ) else 0 := rfl

/-- `F` is symmetric with real entries, hence self-adjoint. -/
theorem spinReversalS_conjTranspose (N : ℕ) :
    (spinReversalS N).conjTranspose = spinReversalS N := by
  ext i j
  rw [Matrix.conjTranspose_apply, spinReversalS_apply, spinReversalS_apply]
  rcases eq_or_ne j (Fin.rev i) with h | h
  · rw [if_pos h, if_pos (Fin.rev_eq_iff.mp h.symm), star_one]
  · rw [if_neg h, if_neg fun h' => h (Fin.rev_eq_iff.mp h'.symm), star_zero]

/-- Entrywise complex conjugation fixes `F`: all its entries are `0` or `1`. -/
theorem spinReversalS_map_conj (N : ℕ) :
    (spinReversalS N).map (starRingEnd ℂ) = spinReversalS N := by
  ext i j
  rw [Matrix.map_apply, spinReversalS_apply]
  rcases eq_or_ne j (Fin.rev i) with h | h
  · rw [if_pos h, map_one]
  · rw [if_neg h, map_zero]

/-- `F` is an involution: `F * F = 1`. -/
theorem spinReversalS_mul_self (N : ℕ) :
    spinReversalS N * spinReversalS N = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · simp only [spinReversalS_apply, Fin.rev_rev]
    by_cases h : i = j <;> simp [h, eq_comm]
  · intro k _ hk
    rw [spinReversalS_apply, if_neg hk, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Conjugation by `F` reindexes by `Fin.rev`**: `(F * M * F) i j = M (rev i) (rev j)`. -/
theorem spinReversalS_conj_apply (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (i j : Fin (N + 1)) :
    (spinReversalS N * M * spinReversalS N) i j = M (Fin.rev i) (Fin.rev j) := by
  rw [Matrix.mul_apply]
  have hFM : ∀ l, (spinReversalS N * M) i l = M (Fin.rev i) l := by
    intro l
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
    · rw [spinReversalS_apply, if_pos rfl, one_mul]
    · intro k _ hk
      rw [spinReversalS_apply, if_neg hk, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_eq_single (Fin.rev j)]
  · rw [hFM, spinReversalS_apply, if_pos (by rw [Fin.rev_rev]), mul_one]
  · intro l _ hl
    rw [hFM, spinReversalS_apply, if_neg (fun h => hl (Fin.rev_eq_iff.mp h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **`F` conjugates `Ŝ³` to `−Ŝ³`** (axis-1 π-rotation reverses the longitudinal axis). -/
theorem spinReversalS_conj_spinSOp3 (N : ℕ) :
    spinReversalS N * spinSOp3 N * spinReversalS N = -spinSOp3 N := by
  ext i j
  rw [spinReversalS_conj_apply]
  unfold spinSOp3
  rw [Matrix.neg_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, Fin.val_rev, Nat.add_sub_add_right]
    push_cast [Nat.cast_sub (Nat.le_of_lt_succ i.isLt)]
    ring
  · rw [if_neg (fun hrev => h (Fin.rev_injective hrev)), if_neg h, neg_zero]

/-- **`F` conjugates `Ŝ⁺` to `Ŝ⁻`**. -/
theorem spinReversalS_conj_spinSOpPlus (N : ℕ) :
    spinReversalS N * spinSOpPlus N * spinReversalS N = spinSOpMinus N := by
  ext i j
  rw [spinReversalS_conj_apply, spinSOpPlus, spinSOpMinus, Fin.val_rev, Fin.val_rev,
    Nat.add_sub_add_right, Nat.add_sub_add_right]
  have hi := Nat.le_of_lt_succ i.isLt
  have hj := Nat.le_of_lt_succ j.isLt
  by_cases h : j.val + 1 = i.val
  · rw [if_pos (by omega), if_pos h]
    congr 2
    have : (N : ℝ) - ((N - j.val : ℕ) : ℝ) = (j.val : ℝ) := by
      rw [Nat.cast_sub hj]; ring
    rw [this]; push_cast [Nat.cast_sub hj]; ring
  · rw [if_neg (by omega), if_neg h]

/-- **`F` conjugates `Ŝ⁻` to `Ŝ⁺`**. -/
theorem spinReversalS_conj_spinSOpMinus (N : ℕ) :
    spinReversalS N * spinSOpMinus N * spinReversalS N = spinSOpPlus N := by
  ext i j
  rw [spinReversalS_conj_apply, spinSOpMinus, spinSOpPlus, Fin.val_rev, Fin.val_rev,
    Nat.add_sub_add_right, Nat.add_sub_add_right]
  have hi := Nat.le_of_lt_succ i.isLt
  have hj := Nat.le_of_lt_succ j.isLt
  by_cases h : i.val + 1 = j.val
  · rw [if_pos (by omega), if_pos h]
    congr 2
    have : (N : ℝ) - ((N - j.val : ℕ) : ℝ) = (j.val : ℝ) := by
      rw [Nat.cast_sub hj]; ring
    rw [this]; push_cast [Nat.cast_sub hj]; ring
  · rw [if_neg (by omega), if_neg h]

/-- **`F` fixes `Ŝ¹`** (the axis-1 π-rotation leaves the longitudinal-in-plane axis 1 invariant).
From `Ŝ¹ = ½(Ŝ⁺ + Ŝ⁻)` and `F Ŝ⁺ F = Ŝ⁻`, `F Ŝ⁻ F = Ŝ⁺`. -/
theorem spinReversalS_conj_spinSOp1 (N : ℕ) :
    spinReversalS N * spinSOp1 N * spinReversalS N = spinSOp1 N := by
  rw [spinSOp1, mul_smul_comm, smul_mul_assoc, mul_add, add_mul,
    spinReversalS_conj_spinSOpPlus, spinReversalS_conj_spinSOpMinus,
    add_comm (spinSOpMinus N) (spinSOpPlus N)]

/-- **`F` conjugates `Ŝ²` to `−Ŝ²`** (the axis-1 π-rotation reverses the transverse axis 2).
From `Ŝ² = (Ŝ⁺ − Ŝ⁻)/(2i)` and `F Ŝ⁺ F = Ŝ⁻`, `F Ŝ⁻ F = Ŝ⁺`. -/
theorem spinReversalS_conj_spinSOp2 (N : ℕ) :
    spinReversalS N * spinSOp2 N * spinReversalS N = -spinSOp2 N := by
  rw [spinSOp2, mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul,
    spinReversalS_conj_spinSOpPlus, spinReversalS_conj_spinSOpMinus, ← neg_sub, smul_neg]

end LatticeSystem.Quantum
