import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandPeel
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandSubspaces

/-!
# Tasaki §11.3.1: `BKernel ⊆ AlphaFock` (the flat-band uniqueness inclusion)

Combining the dual-annihilator occupation projector with the rotated occupation basis: a vector in
the `b̂`-kernel has no β-occupation in its occupation-basis expansion (each `d_{u,σ}` annihilates it,
so `b̂†_{u,σ} d_{u,σ}` kills it, forcing the β-occupied coordinates to vanish by basis
independence), hence lies in the span of the β-free occupation monomials, which is the α-Fock
subspace.  This is the hard inclusion of Tasaki's flat-band uniqueness (Theorem 11.11).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **The dual annihilator kills every `b̂`-kernel vector** (it is a linear combination of the
`b̂_{v,σ}`, each of which annihilates the vector). -/
theorem flatBandDualBAnnihilation_mulVec_eq_zero_of_mem_BKernel (u : Fin (K + 1)) (σ : Fin 2)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (hv : v ∈ flatBandBKernelSubmodule K ν) :
    (flatBandDualBAnnihilation K ν u σ).mulVec v = 0 := by
  rw [flatBandDualBAnnihilation, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero (fun w _ => ?_)
  rw [Matrix.smul_mulVec, (mem_flatBandBKernelSubmodule_iff K ν).mp hv w σ, smul_zero]

/-- The occupation basis vectors are the occupation monomials. -/
theorem flatBandOccBasis_apply (f : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) :
    flatBandOccBasis K ν f = occMonomial K ν f :=
  congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) f

/-- **A `b̂`-kernel vector has no β-occupied coordinate.**  Applying the projector
`b̂†_{u,σ} d_{u,σ}` (which kills `v` since `d_{u,σ} v = 0`) and reading off the occupation-basis
coordinate of any config `g` with the β-mode `(inr u, σ)` occupied gives `0`. -/
theorem flatBandOccBasis_repr_eq_zero_of_mem_BKernel (u : Fin (K + 1)) (σ : Fin 2)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (hv : v ∈ flatBandBKernelSubmodule K ν)
    {g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2} (hg : (Sum.inr u, σ) ∈ occFinset g) :
    (flatBandOccBasis K ν).repr v g = 0 := by
  have hPv : (flatBandBCreation K ν u σ).mulVec
      ((flatBandDualBAnnihilation K ν u σ).mulVec v) = 0 := by
    rw [flatBandDualBAnnihilation_mulVec_eq_zero_of_mem_BKernel u σ hv, Matrix.mulVec_zero]
  have hsum : (flatBandBCreation K ν u σ).mulVec ((flatBandDualBAnnihilation K ν u σ).mulVec v)
      = ∑ f, (flatBandOccBasis K ν).repr v f •
          (if (Sum.inr u, σ) ∈ occFinset f then occMonomial K ν f else 0) := by
    conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v]
    simp only [flatBandOccBasis_apply, Matrix.mulVec_sum, Matrix.mulVec_smul,
      flatBandBCreation_dual_mulVec_occMonomial]
  rw [hsum] at hPv
  have hLI : ∑ f, (if (Sum.inr u, σ) ∈ occFinset f then (flatBandOccBasis K ν).repr v f else 0) •
      flatBandOccBasis K ν f = 0 := by
    rw [← hPv]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [flatBandOccBasis_apply]
    split_ifs <;> simp
  have hcoeff := Fintype.linearIndependent_iff.mp (flatBandOccBasis K ν).linearIndependent _ hLI g
  simpa [if_pos hg] using hcoeff

end LatticeSystem.Fermion
