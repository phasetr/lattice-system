import LatticeSystem.Quantum.SpinS.AevalDiagonal
import LatticeSystem.Quantum.SpinS.DiagProj
import Mathlib.LinearAlgebra.Lagrange

/-!
# Spin-`S` diagonal projector as a Lagrange-interpolation polynomial in `Ŝ^{(3)}`
(Tasaki §2.1 P1d''' β-25)

We prove that each diagonal projector `P_k = |k⟩⟨k|` (β-4) is the
**algebra-evaluation of a Lagrange-basis polynomial** at the spin-`Ŝ^{(3)}`
operator:

  `P_k = aeval (Ŝ^{(3)}) (Lagrange.basis Finset.univ (λ j => N/2 − j.val) k)`.

Combined with β-9 this gives an explicit polynomial decomposition of the
identity `1̂ = ∑_k P_k` in terms of `Ŝ^{(3)}` alone — a key step
toward the full polynomial decomposition of `M_{N+1}(ℂ)` in
`{1̂, Ŝ^{(α)}}` (Tasaki Problem 2.1.a).

The proof combines β-24 (`aeval` at a diagonal matrix is diagonal,
with entries `p.eval (v i)`) with the Lagrange-basis identities
`(Lagrange.basis s v i).eval (v i) = 1` and
`(Lagrange.basis s v i).eval (v j) = 0` for `j ≠ i` (which require
`v` to be injective on `s`; here `v j = (N : ℂ)/2 − j.val` is
injective on `Finset.univ` because the values `j.val` are distinct
naturals).

Tracked in #458.

Reference: Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, §2.1 Problem 2.1.a (p.15), solution S.1 (p.493).
-/

namespace LatticeSystem.Quantum

open Matrix Complex Polynomial

variable {N : ℕ}

/-- The eigenvalue of `Ŝ^{(3)}` at index `k`. (Public version of the
    `private` definition in `Algebra.lean`.) -/
noncomputable def spinSOp3Eigen (N : ℕ) (k : Fin (N + 1)) : ℂ :=
  (N : ℂ) / 2 - (k.val : ℂ)

/-- `spinSOp3 N` is `Matrix.diagonal` of `spinSOp3Eigen N`. -/
theorem spinSOp3_eq_diagonal_eigen (N : ℕ) :
    spinSOp3 N = Matrix.diagonal (spinSOp3Eigen N) := rfl

/-- The eigenvalues `(N/2 - k.val)` are distinct on `Finset.univ`. -/
theorem spinSOp3Eigen_injOn (N : ℕ) :
    Set.InjOn (spinSOp3Eigen N) (Finset.univ : Finset (Fin (N + 1))) := by
  intro a _ b _ hab
  unfold spinSOp3Eigen at hab
  apply Fin.ext
  have h2 : ((a.val : ℂ)) = ((b.val : ℂ)) := by linear_combination -hab
  exact_mod_cast h2

/-- **Lagrange-interpolation formula for the diagonal projector**:
the projector `P_k = |k⟩⟨k|` equals the algebra-evaluation of the
Lagrange-basis polynomial `L_k` at `Ŝ^{(3)}`, where the
interpolation nodes are the eigenvalues `λ_j = (N : ℂ)/2 - j.val`.

Explicitly,
`P_k = ∏_{j ≠ k} (Ŝ^{(3)} − λ_j • 1) / (λ_k − λ_j)`. -/
theorem spinSDiagProj_eq_lagrange_aeval (N : ℕ) (k : Fin (N + 1)) :
    spinSDiagProj N k =
      Polynomial.aeval (spinSOp3 N)
        (Lagrange.basis (Finset.univ : Finset (Fin (N + 1)))
          (spinSOp3Eigen N) k) := by
  rw [spinSOp3_eq_diagonal_eigen, aeval_diagonal]
  unfold spinSDiagProj
  congr 1
  ext i
  by_cases hik : i = k
  · subst hik
    rw [if_pos rfl]
    exact (Lagrange.eval_basis_self (spinSOp3Eigen_injOn N) (Finset.mem_univ i)).symm
  · rw [if_neg hik]
    exact (Lagrange.eval_basis_of_ne (Ne.symm hik) (Finset.mem_univ i)).symm

end LatticeSystem.Quantum
