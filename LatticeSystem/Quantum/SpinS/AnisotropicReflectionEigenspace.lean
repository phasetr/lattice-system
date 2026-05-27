import LatticeSystem.Quantum.SpinS.AnisotropicReflectionSymmetry
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergU1
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# `M ↔ −M` reflection symmetry of the anisotropic Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The spin reversal `Θ` (axis-1 `π`-rotation, `manyBodyReversalS`) anticommutes with `Ŝ³_tot`
and commutes with the anisotropic Hamiltonian `Ĥ` (`Θ Ĥ Θ = Ĥ`, #3745).  Hence `Θ` maps the
magnetization sector `magSubspaceS Λ N M` onto `magSubspaceS Λ N (−M)` while preserving every
`Ĥ`-eigenspace, giving the reflection symmetry of the per-sector spectrum: the `μ`-eigenspace
of `Ĥ` intersected with sector `M` and with sector `−M` have equal dimension (`E_M = E_{-M}`).

This is the symmetry behind the "first-crossing forces `≥3`-fold degeneracy" step of the
Mattis–Nishimori uniqueness argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The reflection anticommutes with `Ŝ³_tot`: `Ŝ³_tot Θ = −(Θ Ŝ³_tot)`. -/
theorem totalSpinSOp3_mul_manyBodyReversalS :
    totalSpinSOp3 Λ N * manyBodyReversalS Λ N =
      -(manyBodyReversalS Λ N * totalSpinSOp3 Λ N) := by
  have h2 := congrArg (manyBodyReversalS Λ N * ·) (manyBodyReversalS_conj_totalSpinSOp3 Λ N)
  simp only at h2
  rw [← mul_assoc, ← mul_assoc, manyBodyReversalS_mul_self, Matrix.one_mul,
    Matrix.mul_neg] at h2
  exact h2

/-- The reflection commutes with the anisotropic Hamiltonian: `Ĥ Θ = Θ Ĥ`. -/
theorem anisotropicHeisenbergS_mul_manyBodyReversalS (J : Λ → Λ → ℂ) (lam D : ℂ) :
    anisotropicHeisenbergS J lam D N * manyBodyReversalS Λ N =
      manyBodyReversalS Λ N * anisotropicHeisenbergS (Λ := Λ) J lam D N := by
  have h2 := congrArg (· * manyBodyReversalS Λ N)
    (manyBodyReversalS_conj_anisotropicHeisenbergS (Λ := Λ) J lam D)
  simp only at h2
  rw [mul_assoc, manyBodyReversalS_mul_self, Matrix.mul_one] at h2
  exact h2.symm

/-- The reflection maps the magnetization sector `M` into the sector `−M`. -/
theorem manyBodyReversalS_mulVec_mem_magSubspaceS_neg {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (manyBodyReversalS Λ N).mulVec v ∈ magSubspaceS Λ N (-M) := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec, totalSpinSOp3_mul_manyBodyReversalS, Matrix.neg_mulVec,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, neg_smul]

/-- **`M ↔ −M` reflection symmetry of the per-sector spectrum**: for the anisotropic
Hamiltonian `Ĥ`, the `μ`-eigenspace intersected with magnetization sector `M` and with sector
`−M` have equal dimension.  The reflection `Θ` (an involution commuting with `Ĥ`) carries one
onto the other.  This is the `E_M = E_{-M}` symmetry of Tasaki §2.5 Theorem 2.4. -/
theorem manyBodyReversalS_anisotropic_sector_eigenspace_finrank_eq
    (J : Λ → Λ → ℂ) (lam D μ M : ℂ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ ⊓
        magSubspaceS Λ N M) =
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (anisotropicHeisenbergS (Λ := Λ) J lam D N)) μ ⊓
        magSubspaceS Λ N (-M)) := by
  set H := anisotropicHeisenbergS (Λ := Λ) J lam D N with hH
  set e : ((Λ → Fin (N + 1)) → ℂ) ≃ₗ[ℂ] ((Λ → Fin (N + 1)) → ℂ) :=
    Matrix.toLin'OfInv (manyBodyReversalS_mul_self Λ N) (manyBodyReversalS_mul_self Λ N) with he
  have he_v : ∀ v, e v = (manyBodyReversalS Λ N).mulVec v := fun v => by
    rw [he]; exact Matrix.toLin'_apply _ v
  have he_symm : ∀ w, e.symm w = (manyBodyReversalS Λ N).mulVec w := fun w => by
    rw [he]; exact Matrix.toLin'_apply _ w
  have hmap : (End.eigenspace (Matrix.toLin' H) μ ⊓ magSubspaceS Λ N M).map e.toLinearMap =
      End.eigenspace (Matrix.toLin' H) μ ⊓ magSubspaceS Λ N (-M) := by
    ext w
    simp only [Submodule.mem_map, Submodule.mem_inf, End.mem_eigenspace_iff, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, ⟨hve, hvm⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [he_v, Matrix.mulVec_mulVec, anisotropicHeisenbergS_mul_manyBodyReversalS,
          ← Matrix.mulVec_mulVec, hve, Matrix.mulVec_smul]
      · rw [he_v]; exact manyBodyReversalS_mulVec_mem_magSubspaceS_neg hvm
    · rintro ⟨hwe, hwm⟩
      refine ⟨e.symm w, ⟨?_, ?_⟩, e.apply_symm_apply w⟩
      · rw [he_symm, Matrix.mulVec_mulVec, anisotropicHeisenbergS_mul_manyBodyReversalS,
          ← Matrix.mulVec_mulVec, hwe, Matrix.mulVec_smul]
      · rw [he_symm]
        have hb := manyBodyReversalS_mulVec_mem_magSubspaceS_neg hwm
        rwa [neg_neg] at hb
  rw [LinearEquiv.finrank_eq
    (e.submoduleMap (End.eigenspace (Matrix.toLin' H) μ ⊓ magSubspaceS Λ N M)), hmap]

end LatticeSystem.Quantum
