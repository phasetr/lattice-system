import LatticeSystem.Quantum.SpinS.OffsetUnitAdjoin

/-!
# Every matrix unit `E_{i, j}` lies in `Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-31)

We assemble the previous results to show that **every** matrix unit
`E_{i, j} = Matrix.single i j 1` is a member of the unital
`ℂ`-subalgebra of `Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ` generated
by `{Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`.

Three cases:
* `i = j`: `E_{i, i} = P_i` (β-27).
* `i.val < j.val`: stride-`(j.val - i.val)` upper unit (β-30 upper).
* `j.val < i.val`: stride-`(i.val - j.val)` lower unit (β-30 lower).

This is the **last building block** for the spanning theorem
(β-32+): combined with the entry-wise decomposition
`M = ∑_{i, j} M_{i,j} • E_{i, j}` (`Matrix.matrix_eq_sum_single`),
every matrix is a `ℂ`-linear combination of elements of the adjoin
and hence in the adjoin.

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- The diagonal matrix unit `E_{i, i}` equals the diagonal projector `P_i`. -/
private theorem matrix_single_diag_eq_diagProj (i : Fin (N + 1)) :
    Matrix.single i i (1 : ℂ) = spinSDiagProj N i := by
  rw [← Matrix.diagonal_single]
  unfold spinSDiagProj
  congr 1
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single, Function.update, h]

/-- **Every** matrix unit lives in `Algebra.adjoin ℂ {Ŝ^{(1)}, Ŝ^{(2)}, Ŝ^{(3)}}`. -/
theorem matrix_single_mem_adjoin (i j : Fin (N + 1)) :
    Matrix.single i j (1 : ℂ) ∈
      Algebra.adjoin ℂ
        ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
  by_cases hij : i = j
  · subst hij
    rw [matrix_single_diag_eq_diagProj]
    exact spinSDiagProj_mem_adjoin N i
  · by_cases hlt : i.val < j.val
    · set k := j.val - i.val - 1
      have hjk : j.val = i.val + (k + 1) := by omega
      have h' : i.val + (k + 1) < N + 1 := hjk ▸ j.isLt
      have hje : j = (⟨i.val + (k + 1), h'⟩ : Fin (N + 1)) := by
        apply Fin.ext; exact hjk
      rw [hje]
      exact single_offset_succ_mem_adjoin i k h'
    · -- j.val ≤ i.val and i ≠ j, hence j.val < i.val
      have hgt : j.val < i.val := by
        have hle : j.val ≤ i.val := Nat.le_of_not_lt hlt
        rcases lt_or_eq_of_le hle with hlt2 | heq
        · exact hlt2
        · exfalso; apply hij; apply Fin.ext; exact heq.symm
      set k := i.val - j.val - 1
      have hik : i.val = j.val + (k + 1) := by omega
      have h' : j.val + (k + 1) < N + 1 := hik ▸ i.isLt
      have hie : i = (⟨j.val + (k + 1), h'⟩ : Fin (N + 1)) := by
        apply Fin.ext; exact hik
      rw [hie]
      exact single_offset_succ_swap_mem_adjoin j k h'

end LatticeSystem.Quantum
