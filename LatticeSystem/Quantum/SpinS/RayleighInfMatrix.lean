import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.Matrix

/-!
# Rayleigh infimum of a complex matrix (foundation for min-eigenvalue continuity)

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2) deformation foundation.

For a complex matrix `M : Matrix n n ℂ` (with `n` a nonempty finite type), the
Rayleigh infimum is
`rayleighInf M := ⨅ ψ : { x : n → ℂ // ‖x‖ = 1 }, (dotProduct (star ψ) (M.mulVec ψ)).re`
using the standard L² norm on `n → ℂ`. For Hermitian `M` this equals
`hermitianMinEigenvalue M`. The definition is continuous in `M` (foundation for
the min-eigenvalue continuity needed by the obligation (2) deformation argument).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {n : Type*} [Fintype n]

/-- The Rayleigh quotient of `M` at a vector `ψ : n → ℂ` (no normalisation),
defined as `re (∑ i j, conj (ψ i) * M i j * ψ j) = re ⟨ψ, M ψ⟩`. -/
noncomputable def rayleighOnVec (M : Matrix n n ℂ) (ψ : n → ℂ) : ℝ :=
  (dotProduct (star ψ) (M.mulVec ψ)).re

/-- The Rayleigh-on-vec quotient is continuous in `M` for any fixed `ψ`.
This is the entry point for `rayleighInf` continuity via the parametrised iInf. -/
theorem continuous_rayleighOnVec_matrix (ψ : n → ℂ) :
    Continuous (fun M : Matrix n n ℂ => rayleighOnVec M ψ) := by
  unfold rayleighOnVec
  refine Complex.continuous_re.comp ?_
  -- dotProduct (star ψ) (M.mulVec ψ) = ∑ i, conj (ψ i) * (∑ j, M i j * ψ j)
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine continuous_const.mul ?_
  refine continuous_finset_sum _ (fun j _ => ?_)
  exact (continuous_apply_apply i j).mul continuous_const

/-- The Rayleigh-on-vec quotient is jointly continuous in `(M, ψ)` (as a function
of `Matrix n n ℂ × (n → ℂ)`). -/
theorem continuous_rayleighOnVec :
    Continuous (fun p : Matrix n n ℂ × (n → ℂ) => rayleighOnVec p.1 p.2) := by
  unfold rayleighOnVec
  refine Complex.continuous_re.comp ?_
  refine continuous_finset_sum _ (fun i _ => ?_)
  refine Continuous.mul ?_ ?_
  · refine continuous_star.comp ?_
    exact (continuous_apply i).comp continuous_snd
  · refine continuous_finset_sum _ (fun j _ => ?_)
    refine Continuous.mul ?_ ?_
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply j).comp continuous_snd

/-- The Rayleigh quotient is `ℝ`-additive in `M` (since `dotProduct` and `mulVec` are linear in
the matrix and `Complex.re` is linear). -/
theorem rayleighOnVec_add_matrix (M N : Matrix n n ℂ) (ψ : n → ℂ) :
    rayleighOnVec (M + N) ψ = rayleighOnVec M ψ + rayleighOnVec N ψ := by
  unfold rayleighOnVec
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]


end LatticeSystem.Quantum
