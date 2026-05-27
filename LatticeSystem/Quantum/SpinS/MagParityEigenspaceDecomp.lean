import LatticeSystem.Quantum.SpinS.MagParityOperator
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Eigenspace finrank split under the magnetization-parity involution

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

A finite-dimensional operator `T` commuting with an involution `P` (`P² = 1`) has each of its
eigenspaces split by `P` into the two `P`-eigenspaces `±1`:
`finrank (eigenspace T μ) ≤ finrank (eigenspace T μ ⊓ eigenspace P 1)
  + finrank (eigenspace T μ ⊓ eigenspace P (−1))`.

Applied to the axis-swapped `Ĥ'` and the magnetization-parity operator `P` (#3773), this bounds
the degeneracy of any `Ĥ'`-eigenspace by the sum of its even- and odd-parity Perron–Frobenius
contributions — reducing the `≤ 2` ground-state degeneracy bound to `≤ 1` per parity block.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix Module

/-- **Eigenspace finrank split under a commuting involution.** For finite-dimensional `T, P` with
`T ∘ P = P ∘ T` and `P ∘ P = id`, every `T`-eigenspace splits across the two `P`-eigenspaces. -/
theorem eigenspace_finrank_le_of_commuting_involution
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T P : V →ₗ[ℂ] V) (hcomm : T ∘ₗ P = P ∘ₗ T) (hP : P ∘ₗ P = LinearMap.id) (μ : ℂ) :
    finrank ℂ (End.eigenspace T μ) ≤
      finrank ℂ ↥(End.eigenspace T μ ⊓ End.eigenspace P 1) +
        finrank ℂ ↥(End.eigenspace T μ ⊓ End.eigenspace P (-1)) := by
  set W := End.eigenspace T μ
  have hPP : ∀ w : V, P (P w) = w := fun w => by
    have := congrArg (fun f => f w) hP; simpa using this
  have hle : W ≤ (W ⊓ End.eigenspace P 1) ⊔ (W ⊓ End.eigenspace P (-1)) := by
    intro w hw
    have hWinv : P w ∈ W := by
      rw [End.mem_eigenspace_iff] at hw ⊢
      have hTP : T (P w) = P (T w) := by
        rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply]
      rw [hTP, hw, map_smul]
    have hsplit : w = ((2 : ℂ)⁻¹ • (w + P w)) + ((2 : ℂ)⁻¹ • (w - P w)) := by
      rw [smul_add, smul_sub]; module
    rw [hsplit]
    apply Submodule.add_mem_sup
    · refine Submodule.mem_inf.mpr ⟨W.smul_mem _ (W.add_mem hw hWinv), ?_⟩
      rw [End.mem_eigenspace_iff, map_smul, map_add, hPP, one_smul]; module
    · refine Submodule.mem_inf.mpr ⟨W.smul_mem _ (W.sub_mem hw hWinv), ?_⟩
      rw [End.mem_eigenspace_iff, map_smul, map_sub, hPP]; module
  calc finrank ℂ W
      ≤ finrank ℂ ↥((W ⊓ End.eigenspace P 1) ⊔ (W ⊓ End.eigenspace P (-1))) :=
        Submodule.finrank_mono hle
    _ ≤ _ := by
        have := Submodule.finrank_sup_add_finrank_inf_eq
          (W ⊓ End.eigenspace P 1) (W ⊓ End.eigenspace P (-1))
        omega

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The degeneracy of any `Ĥ'`-eigenspace is bounded by the sum of its even/odd
magnetization-parity contributions. -/
theorem axisSwappedAnisotropicHeisenbergS_eigenspace_finrank_le_parity_blocks
    {J : Λ → Λ → ℂ} (hJself : ∀ x, J x x = 0) (lam D μ : ℂ) :
    finrank ℂ (End.eigenspace
        (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ) ≤
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) 1) +
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (axisSwappedAnisotropicHeisenbergS J lam D N)) μ ⊓
        End.eigenspace (Matrix.toLin' (magParityDiagS Λ N)) (-1)) := by
  refine eigenspace_finrank_le_of_commuting_involution _ _ ?_ ?_ μ
  · rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      axisSwappedAnisotropicHeisenbergS_commute_magParityDiagS hJself lam D]
  · rw [← Matrix.toLin'_mul, magParityDiagS_mul_self, Matrix.toLin'_one]

end LatticeSystem.Quantum
