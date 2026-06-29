import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockKineticMatrix

/-!
# The block kinetic energy as a coefficient-matrix trace (Tasaki §10.2.1)

Nineteenth layer (PR19) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

This file begins the reflection-positive energy assembly. The block-order kinetic
energy of a state vector `ψ` is expressed as a trace on the block coefficient
matrix `C = hubbardBlockCoeff ψ`. Reindexing the energy dot-product sum over
configurations by the bijection `(u, h) ↦ merge u (P h)` (`hubbardBlockSpinConfigEquiv`
composed with the particle–hole involution `P`), and inserting the PR10
coefficient action `kinetic = A·C + C·Bᵣ`, gives

  `⟨ψ| Ĥkin |ψ⟩ = tr(Cᴴ · (A·C + C·Bᵣ))`.

This holds for *every* state vector `ψ` (no electron-number/half-filling
restriction; the filling condition enters later, at the Perron–Frobenius / polar
step). It is the bridge from the operator energy to the spin-reflection Gram form
`0 ≤ Re tr(C·A·C·Aᴴ)` (PR1 `spinReflection_gramMatrix_nonneg`), which a subsequent
layer reaches via the adjoint relation `Bᵣ = P·Aᵀ·P` (PR18).

## Main results

* `trace_conjTranspose_mul_eq_sum` — `tr(Cᴴ·M) = ∑_{u,h} conj(C u h)·M u h`.
* `hubbardBlockKinetic_dotProduct_eq_trace` — the block kinetic energy of `ψ`
  equals `tr(Cᴴ·(A·C + C·Bᵣ))` with `C = hubbardBlockCoeff ψ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The trace of `Cᴴ·M` expands as the conjugated entrywise pairing
`∑_{u,h} conj(C u h)·M u h`. -/
theorem trace_conjTranspose_mul_eq_sum {ι : Type*} [Fintype ι]
    (C M : Matrix ι ι ℂ) :
    Matrix.trace (Cᴴ * M) = ∑ u : ι, ∑ h : ι, star (C u h) * M u h := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

/-- **The block-order kinetic energy of a state vector equals the coefficient-matrix
trace `tr(Cᴴ·(A·C + C·Bᵣ))`.** Holds for every `ψ`. -/
theorem hubbardBlockKinetic_dotProduct_eq_trace (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    dotProduct (star ψ) ((hubbardBlockKinetic N T).mulVec ψ)
      = Matrix.trace ((hubbardBlockCoeff N ψ)ᴴ *
          hubbardBlockKineticCoeffAction N T (hubbardBlockCoeff N ψ)) := by
  rw [trace_conjTranspose_mul_eq_sum]
  -- The right side: rewrite the coefficient action back through PR10.
  have hM : ∀ u h, hubbardBlockKineticCoeffAction N T (hubbardBlockCoeff N ψ) u h
      = hubbardBlockCoeff N ((hubbardBlockKinetic N T).mulVec ψ) u h := fun u h => by
    rw [hubbardBlockCoeff_hubbardBlockKinetic_mulVec]
  simp only [hM]
  -- The left side: reindex the configuration sum by `(u,h) ↦ merge u (P h)`.
  rw [dotProduct, ← Equiv.sum_comp (hubbardBlockSpinConfigEquiv N).symm
      (fun c => (star ψ) c * ((hubbardBlockKinetic N T).mulVec ψ) c),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← Equiv.sum_comp (particleHoleConfigEquiv N)
      (fun d => (star ψ) (hubbardBlockSpinConfigEquiv N |>.symm (u, d)) *
        ((hubbardBlockKinetic N T).mulVec ψ) (hubbardBlockSpinConfigEquiv N |>.symm (u, d)))]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  simp only [hubbardBlockSpinConfigEquiv, particleHoleConfigEquiv, Equiv.coe_fn_symm_mk,
    Function.Involutive.coe_toPerm, Pi.star_apply, hubbardBlockCoeff]

end LatticeSystem.Fermion
