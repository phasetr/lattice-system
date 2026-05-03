import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum
import LatticeSystem.Quantum.SpinS.SaturatedPairLinearIndependent

/-!
# All-aligned states at distinct constants are linearly independent

For `[Nonempty V]`, the family
`c ↦ allAlignedStateS V N c` indexed by `c : Fin (N + 1)` is
`LinearIndependent ℂ`.

Each `allAlignedStateS V N c` lies in the `Ŝ^z_tot`-eigenspace at
`magEigenvalueS (allAlignedConfigS V N c) = |V|·N/2 − |V|·c.val`
(via PR #875). For distinct `c`, these eigenvalues are distinct
(when `[Nonempty V]`), so by `Module.End.eigenvectors_linearIndependent'`
the family is LI.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The all-aligned `Ŝ^z_tot` eigenvalue function
`c ↦ |V|·N/2 − |V|·c.val` is injective for `[Nonempty V]`. -/
theorem allAlignedConfigS_eigenvalue_injective [Nonempty V] :
    Function.Injective
      (fun c : Fin (N + 1) =>
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 -
          (Fintype.card V : ℂ) * (c.val : ℂ))) := by
  intros c₁ c₂ h
  -- Cancel m_max to get |V| · c₁.val = |V| · c₂.val.
  have h_card : (Fintype.card V : ℂ) ≠ 0 := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos
    exact_mod_cast Nat.pos_iff_ne_zero.mp hpos
  have h_val : (c₁.val : ℂ) = (c₂.val : ℂ) := by
    have hcancel : (Fintype.card V : ℂ) * (c₁.val : ℂ) =
        (Fintype.card V : ℂ) * (c₂.val : ℂ) := by
      linear_combination -h
    exact (mul_left_cancel₀ h_card hcancel)
  apply Fin.ext
  exact_mod_cast h_val

/-- The all-aligned states at distinct `c` are linearly independent. -/
theorem allAlignedStateS_linearIndependent [Nonempty V] :
    LinearIndependent ℂ
      (fun c : Fin (N + 1) =>
        (allAlignedStateS V N c : (V → Fin (N + 1)) → ℂ)) := by
  let f : Module.End ℂ ((V → Fin (N + 1)) → ℂ) :=
    (totalSpinSOp3 V N).mulVecLin
  let μ : Fin (N + 1) → ℂ := fun c =>
    (Fintype.card V : ℂ) * (N : ℂ) / 2 -
      (Fintype.card V : ℂ) * (c.val : ℂ)
  have hμ_inj : Function.Injective μ := allAlignedConfigS_eigenvalue_injective
  have h_eigenvec : ∀ c : Fin (N + 1),
      Module.End.HasEigenvector f (μ c) (allAlignedStateS V N c) := by
    intro c
    refine ⟨?_, ?_⟩
    · -- eigenspace membership: f · |c..c⟩ = μ c • |c..c⟩.
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      rw [totalSpinSOp3_mulVec_allAlignedStateS,
        magEigenvalueS_allAlignedConfigS]
    · -- non-vanishing.
      exact allAlignedStateS_ne_zero c
  exact Module.End.eigenvectors_linearIndependent' f μ hμ_inj _ h_eigenvec

end LatticeSystem.Quantum
