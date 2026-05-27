import LatticeSystem.Quantum.SpinS.Operators
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Eigenspace dimension is preserved under matrix similarity

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

For an invertible matrix `U` and `H' = U⁻¹ H U`, each `μ`-eigenspace of `H'` is carried
isomorphically onto the `μ`-eigenspace of `H` by `U` (`v ↦ U v`), so the two have equal
dimension.  This transfers the ground-state degeneracy bound between the original anisotropic
Hamiltonian and its axis-swapped gauge image `H'` (only the degeneracy count is needed; the
similarity need not be unitary).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Eigenspace dimension is a similarity invariant.** If `U * Uinv = 1`, `Uinv * U = 1`, and
`H' = Uinv * H * U`, then for every `μ` the `μ`-eigenspaces of `H'` and `H` have equal finrank. -/
theorem matrix_similar_eigenspace_finrank_eq
    {U Uinv H H' : Matrix n n ℂ} (hUU : U * Uinv = 1) (hUinvU : Uinv * U = 1)
    (hsim : H' = Uinv * H * U) (μ : ℂ) :
    finrank ℂ (End.eigenspace (Matrix.toLin' H') μ) =
      finrank ℂ (End.eigenspace (Matrix.toLin' H) μ) := by
  -- `e = toLin' U` as a linear equivalence (`toFun = toLin' U`, since here `M' = U`).
  set e : (n → ℂ) ≃ₗ[ℂ] (n → ℂ) := Matrix.toLin'OfInv hUinvU hUU with he
  have he_v : ∀ v, e v = U *ᵥ v := fun v => by rw [he]; exact Matrix.toLin'_apply U v
  have he_symm : ∀ w, e.symm w = Uinv *ᵥ w := fun w => by rw [he]; exact Matrix.toLin'_apply Uinv w
  -- The eigenspace of `H'` maps onto the eigenspace of `H` under `e`.
  have hmap : (End.eigenspace (Matrix.toLin' H') μ).map e.toLinearMap =
      End.eigenspace (Matrix.toLin' H) μ := by
    ext w
    simp only [Submodule.mem_map, End.mem_eigenspace_iff, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨v, hv, rfl⟩
      -- `hv : H' *ᵥ v = μ • v`; goal `H *ᵥ (e v) = μ • e v`.
      rw [hsim] at hv
      rw [he_v, Matrix.mulVec_mulVec]
      have := congrArg (fun x => U *ᵥ x) hv
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at this
      rw [show U * (Uinv * H * U) = H * U by rw [← mul_assoc, ← mul_assoc, hUU, one_mul]] at this
      exact this
    · intro hw
      -- `hw : H *ᵥ w = μ • w`; provide `e.symm w` with `H' *ᵥ (e.symm w) = μ • e.symm w`.
      refine ⟨e.symm w, ?_, by rw [he_v, he_symm, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]⟩
      have key : (Uinv * H * U) *ᵥ (Uinv *ᵥ w) = Uinv *ᵥ (H *ᵥ w) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        congr 2
        rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
      rw [hsim, he_symm, key, hw, Matrix.mulVec_smul]
  rw [LinearEquiv.finrank_eq (e.submoduleMap (End.eigenspace (Matrix.toLin' H') μ)), hmap]

end LatticeSystem.Quantum
