import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundWeightOne
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Tasaki 11.5: `Ŝ³` structural facts for the weight direct-sum decomposition (Prop 11.24 E5b)

The degeneracy upper bound `finrank G ≤ Ne+1` for the ground subspace
`G = groundSubmoduleAtFilling Ĥ_tJ Ne` follows from decomposing `G` into the `Ŝ³` weight spaces,
each of which is `≤ 1`-dimensional (`tJ_ground_weight_finrank_le_one_pos/_neg`, E5b).  The two
structural inputs for that decomposition are collected here:

* `fermionTotalSpinZ_mulVec_mem_groundSubmodule` — `Ŝ³` preserves `G` (it commutes with `Ĥ_tJ`
  and `N̂` and keeps the hard-core subspace), so `G` is an invariant submodule of `Ŝ³`;
* `fermionTotalSpinZ_iSup_eigenspace_eq_top` — the `Ŝ³` eigenspaces span the whole space (`Ŝ³`
  acts diagonally on the computational basis, so every standard basis vector is an eigenvector).

Together with finite-dimensionality these feed `Submodule.eq_iSup_inf_genEigenspace`, giving the
weight decomposition `G = ⨆ μ, G ⊓ eigenspace Ŝ³ μ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- **`Ŝ³_tot` preserves the hard-core subspace** (mirror of the `Ŝ⁻`/`Ŝ⁺` versions). -/
theorem fermionTotalSpinZ_mulVec_mem_hardcore (N : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardHardcoreSubspace N) :
    (fermionTotalSpinZ N).mulVec v ∈ hubbardHardcoreSubspace N := by
  have hself : (hubbardHardcoreProjection N).mulVec ((fermionTotalSpinZ N).mulVec v)
      = (fermionTotalSpinZ N).mulVec v := by
    rw [Matrix.mulVec_mulVec,
      (fermionTotalSpinZ_commute_hubbardHardcoreProjection N).symm.eq,
      ← Matrix.mulVec_mulVec, hubbardHardcoreProjection_mulVec_eq_self_of_mem N hv]
  rw [← hself]
  exact hubbardHardcoreProjection_mulVec_mem N _

/-- **`Ŝ³` preserves the ground subspace `G`.**  It commutes with `Ĥ_tJ` and `N̂` and keeps the
hard-core subspace, so `G` is an invariant submodule of `Ŝ³` — the input to the weight
decomposition. -/
theorem fermionTotalSpinZ_mulVec_mem_groundSubmodule (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : v ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne) :
    (fermionTotalSpinZ N).mulVec v ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne := by
  rw [groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
    Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
    Matrix.mulVecLin_apply] at hv ⊢
  obtain ⟨⟨hH, hNn⟩, hhc⟩ := hv
  refine ⟨⟨?_, ?_⟩, fermionTotalSpinZ_mulVec_mem_hardcore N hhc⟩
  · have hcomm : Commute (tJHamiltonian N G τ J) (fermionTotalSpinZ N) :=
      (fermionTotalSpinZ_commute_tJHamiltonian N G τ J).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]
  · have hcomm : Commute (fermionTotalNumber (2 * N + 1)) (fermionTotalSpinZ N) :=
      (fermionTotalSpinZ_commute_fermionTotalNumber N).symm
    rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hNn, Matrix.mulVec_smul]

/-- **The `Ŝ³` eigenspaces span the whole space.**  `Ŝ³` is diagonal on the computational basis,
so every standard basis vector `Pi.single c 1` is an eigenvector (eigenvalue = its `Ŝ³` count);
the basis spans `⊤`, hence so do the eigenspaces.  This is the diagonalizability input to the
weight decomposition. -/
theorem fermionTotalSpinZ_iSup_eigenspace_eq_top (N : ℕ) :
    ⨆ μ : ℂ, Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℂ (Fin (2 * N + 2) → Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  set μc : ℂ := (((∑ i : Fin (N + 1), ((c (spinfulIndex N i 0)).val : ℂ)) -
      (∑ i : Fin (N + 1), ((c (spinfulIndex N i 1)).val : ℂ))) / 2) with hμc
  refine Submodule.mem_iSup_of_mem μc ?_
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  funext w
  rw [fermionTotalSpinZ_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hwc : w = c
  · subst hwc; rfl
  · have hzero : (Pi.basisFun ℂ (Fin (2 * N + 2) → Fin 2) c) w = 0 := by
      simp [Pi.basisFun_apply, hwc]
    rw [hzero, mul_zero, mul_zero]

/-- **`Ŝ³` weight decomposition of the ground subspace.**  Since `Ŝ³` preserves `G` and its
eigenspaces span `⊤`, the ground subspace decomposes as the supremum of its `Ŝ³` weight spaces:
`G = ⨆ μ, G ⊓ eigenspace Ŝ³ μ` (`Submodule.eq_iSup_inf_genEigenspace`, `G` invariant). -/
theorem tJ_groundSubmodule_eq_iSup_inf_eigenspace (N Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne =
      ⨆ μ : ℂ, groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne ⊓
        Module.End.eigenspace (fermionTotalSpinZ N).mulVecLin μ := by
  have hinv : ∀ x ∈ groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne,
      (fermionTotalSpinZ N).mulVecLin x ∈
        groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne := by
    intro x hx
    rw [Matrix.mulVecLin_apply]
    exact fermionTotalSpinZ_mulVec_mem_groundSubmodule N Ne G τ J hx
  have htop : ⨆ μ : ℂ,
      Module.End.genEigenspace (fermionTotalSpinZ N).mulVecLin μ 1 = ⊤ := by
    simpa only [Module.End.genEigenspace_one] using fermionTotalSpinZ_iSup_eigenspace_eq_top N
  simpa only [Module.End.genEigenspace_one] using
    Submodule.eq_iSup_inf_genEigenspace (p := groundSubmoduleAtFilling (tJHamiltonian N G τ J) Ne)
      (f := (fermionTotalSpinZ N).mulVecLin) 1 hinv htop

end LatticeSystem.Fermion
