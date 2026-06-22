import LatticeSystem.Quantum.SpinS.AllAlignedStateCore

/-!
# Magnetization subspace extremal dimension: eigenvalue characterisation (foundation)

Foundational layer extracted from `MagSubspaceExtremalDim.lean` for build speed.  This file proves
the eigenvalue characterisation of the extremal configurations (the magnetization eigenvalue equals
`±m_max` iff the all-aligned config is the zero / last config).

The magnetization subspace at the extremal eigenvalues (its dimension) is kept in the capstone
module `MagSubspaceExtremalDim.lean`.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Eigenvalue characterisation of the extremal configurations -/

set_option linter.unusedSectionVars false in
omit [DecidableEq V] in
/-- `magEigenvalueS σ = m_max` iff `σ = allAlignedConfigS V N 0`. -/
theorem magEigenvalueS_eq_mMax_iff_allAlignedConfigS_zero
    (σ : V → Fin (N + 1)) :
    magEigenvalueS σ = (Fintype.card V : ℂ) * (N : ℂ) / 2 ↔
      σ = allAlignedConfigS V N 0 := by
  classical
  constructor
  · intro h
    -- magEigenvalueS σ = (|V|·N : ℂ)/2 − magSumS σ = (|V|·N)/2 ⇒ magSumS σ = 0.
    have h1 : (magSumS σ : ℂ) = 0 := by
      unfold magEigenvalueS at h
      linear_combination -h
    have h2 : magSumS σ = 0 := by exact_mod_cast h1
    -- magSumS σ = 0 ⇒ each (σ x).val = 0 ⇒ σ x = 0 ⇒ σ = const 0.
    funext x
    have hsum_pos : ∀ y, 0 ≤ (σ y).val := fun y => Nat.zero_le _
    have hx_zero : (σ x).val = 0 := by
      unfold magSumS at h2
      have := Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset V))
        (f := fun y => (σ y).val) (fun y _ => hsum_pos y) |>.mp h2
      exact this x (Finset.mem_univ _)
    apply Fin.ext
    rw [hx_zero]; rfl
  · intro h
    rw [h, magEigenvalueS_allAlignedConfigS]
    rw [show ((0 : Fin (N + 1)).val : ℂ) = 0 from by simp]
    ring

set_option linter.unusedSectionVars false in
omit [DecidableEq V] in
/-- `magEigenvalueS σ = −m_max` iff `σ = allAlignedConfigS V N (Fin.last N)`. -/
theorem magEigenvalueS_eq_neg_mMax_iff_allAlignedConfigS_last
    (σ : V → Fin (N + 1)) :
    magEigenvalueS σ = -((Fintype.card V : ℂ) * (N : ℂ) / 2) ↔
      σ = allAlignedConfigS V N (Fin.last N) := by
  classical
  constructor
  · intro h
    -- magEigenvalueS σ = (|V|·N : ℂ)/2 − magSumS σ = −(|V|·N)/2 ⇒ magSumS σ = |V|·N.
    have h1 : (magSumS σ : ℂ) = (Fintype.card V * N : ℕ) := by
      unfold magEigenvalueS at h
      push_cast
      linear_combination -h
    have h2 : magSumS σ = Fintype.card V * N := by exact_mod_cast h1
    -- magSumS σ = |V|·N maximal ⇒ each (σ x).val = N ⇒ σ x = Fin.last N.
    funext x
    have hUpper : ∀ y, (σ y).val ≤ N := fun y => Nat.lt_succ_iff.mp (σ y).isLt
    have h_eq : ∀ y, (σ y).val = N := by
      intro y
      have hsum_eq : ∑ z : V, (σ z).val = ∑ _ : V, N := by
        unfold magSumS at h2
        rw [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
      have hle : ∀ z ∈ (Finset.univ : Finset V), (σ z).val ≤ N := fun z _ => hUpper z
      have h_pointwise := Finset.sum_eq_sum_iff_of_le hle |>.mp hsum_eq
      exact h_pointwise y (Finset.mem_univ y)
    apply Fin.ext
    rw [h_eq x]; rfl
  · intro h
    rw [h, magEigenvalueS_allAlignedConfigS]
    rw [show ((Fin.last N).val : ℂ) = (N : ℂ) from by simp [Fin.last]]
    ring

end LatticeSystem.Quantum
