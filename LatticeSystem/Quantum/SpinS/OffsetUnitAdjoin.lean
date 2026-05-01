import LatticeSystem.Quantum.SpinS.NeighborUnitAdjoin
import Mathlib.Data.Matrix.Basis

/-!
# Arbitrary off-diagonal matrix units live in `Algebra.adjoin ℂ {Ŝ^{(α)}}`
(Tasaki §2.1 P1d''' β-30)

We extend β-29 from immediate-neighbor matrix units `E_{i, i+1}` to
arbitrary "stride-`(k+1)`" units in either direction:

  `E_{i, i + (k+1)} = E_{i, i+1} · E_{i+1, i+2} · … · E_{i+k, i+k+1}`,
  `E_{i + (k+1), i} = E_{i+k+1, i+k} · E_{i+k, i+k-1} · … · E_{i+1, i}`.

By induction on `k`, both products live in the spin-operator
subalgebra. The single-step lemma
`Matrix.single_mul_single_same : E_{i, j} · E_{j, k} = E_{i, k}`
(with the stale entry `c · d` reducing to `1 · 1 = 1`) chains the
factors.

Combined with β-27 (`P_k = E_{k, k} ∈ adjoin`) this shows that
every matrix unit `E_{i, j}` is in the spin-operator subalgebra,
which is the final ingredient for the spanning theorem (β-31+).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a.
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {N : ℕ}

/-- Upper-stride matrix unit `E_{i, i + (k+1)}` is in the adjoin. -/
theorem single_offset_succ_mem_adjoin (i : Fin (N + 1)) :
    ∀ (k : ℕ) (h : i.val + (k + 1) < N + 1),
      Matrix.single i (⟨i.val + (k + 1), h⟩ : Fin (N + 1)) (1 : ℂ) ∈
        Algebra.adjoin ℂ
          ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
            Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))
  | 0, h => by
      simpa using single_succ_mem_adjoin (N := N) i h
  | k + 1, h => by
      -- Set `i' := ⟨i.val + 1, h'⟩`. We need h' : i.val + 1 < N + 1.
      have h' : i.val + 1 < N + 1 := by omega
      set i' : Fin (N + 1) := ⟨i.val + 1, h'⟩
      -- Need h'' : i'.val + (k + 1) < N + 1, which is i.val + 1 + (k+1) < N + 1.
      have h'' : i'.val + (k + 1) < N + 1 := by
        change i.val + 1 + (k + 1) < N + 1
        omega
      -- IH at `i', k`: E_{i', ⟨i'.val + (k+1), h''⟩} ∈ adjoin
      have hIH := single_offset_succ_mem_adjoin i' k h''
      -- And `E_{i, i'} ∈ adjoin` by β-29.
      have hbase : Matrix.single i i' (1 : ℂ) ∈
          Algebra.adjoin ℂ
            ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
              Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
        single_succ_mem_adjoin (N := N) i h'
      -- Goal: E_{i, ⟨i.val + (k+2)⟩} ∈ adjoin
      have hidx : (⟨i.val + (k + 1 + 1), h⟩ : Fin (N + 1)) =
                  (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) := by
        apply Fin.ext
        change i.val + (k + 1 + 1) = i.val + 1 + (k + 1)
        ring
      rw [hidx]
      -- E_{i, ⟨i'.val + (k+1)⟩} = E_{i, i'} * E_{i', ⟨i'.val + (k+1)⟩} (by single_mul_single_same)
      have hprod :
          Matrix.single i i' (1 : ℂ) *
            Matrix.single i' (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) 1 =
          Matrix.single i (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) (1 * 1) :=
        Matrix.single_mul_single_same (1 : ℂ) i i'
          (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) 1
      rw [show Matrix.single i (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) (1 : ℂ) =
            Matrix.single i (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) (1 * 1) from by
              rw [mul_one]]
      rw [← hprod]
      exact Subalgebra.mul_mem _ hbase hIH

/-- Lower-stride matrix unit `E_{i + (k+1), i}` is in the adjoin. -/
theorem single_offset_succ_swap_mem_adjoin (i : Fin (N + 1)) :
    ∀ (k : ℕ) (h : i.val + (k + 1) < N + 1),
      Matrix.single (⟨i.val + (k + 1), h⟩ : Fin (N + 1)) i (1 : ℂ) ∈
        Algebra.adjoin ℂ
          ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
            Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))
  | 0, h => by
      simpa using single_succ_swap_mem_adjoin (N := N) i h
  | k + 1, h => by
      have h' : i.val + 1 < N + 1 := by omega
      set i' : Fin (N + 1) := ⟨i.val + 1, h'⟩
      have h'' : i'.val + (k + 1) < N + 1 := by
        change i.val + 1 + (k + 1) < N + 1
        omega
      have hIH := single_offset_succ_swap_mem_adjoin i' k h''
      have hbase : Matrix.single i' i (1 : ℂ) ∈
          Algebra.adjoin ℂ
            ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
              Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :=
        single_succ_swap_mem_adjoin (N := N) i h'
      have hidx : (⟨i.val + (k + 1 + 1), h⟩ : Fin (N + 1)) =
                  (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) := by
        apply Fin.ext
        change i.val + (k + 1 + 1) = i.val + 1 + (k + 1)
        ring
      rw [hidx]
      -- E_{⟨i'.val + (k+1)⟩, i} = E_{⟨i'.val + (k+1)⟩, i'} * E_{i', i}
      have hprod :
          Matrix.single (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) i' (1 : ℂ) *
            Matrix.single i' i 1 =
          Matrix.single (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) i (1 * 1) :=
        Matrix.single_mul_single_same (1 : ℂ)
          (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) i' i 1
      rw [show Matrix.single (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) i (1 : ℂ) =
            Matrix.single (⟨i'.val + (k + 1), h''⟩ : Fin (N + 1)) i (1 * 1) from by
              rw [mul_one]]
      rw [← hprod]
      exact Subalgebra.mul_mem _ hIH hbase

end LatticeSystem.Quantum
