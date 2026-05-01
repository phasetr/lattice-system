import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# Test coverage for spin-`S` magnetization
(Tasaki §2.5 Phase B-β β-4a)
-/

namespace LatticeSystem.Tests.SpinSMagnetization

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- `magSumS σ ≤ |Λ| · N`. -/
example {N : ℕ} (σ : Λ → Fin (N + 1)) :
    magSumS σ ≤ Fintype.card Λ * N :=
  magSumS_le σ

/-- Membership in `magSubspaceS` unfolds to the eigenvalue equation. -/
example {N : ℕ} (M : ℂ) (v : (Λ → Fin (N + 1)) → ℂ) :
    v ∈ magSubspaceS Λ N M ↔ (totalSpinSOp3 Λ N).mulVec v = M • v :=
  mem_magSubspaceS_iff M v

/-- Distinct sectors are disjoint. -/
example {N : ℕ} {M M' : ℂ} (hMM' : M ≠ M') :
    Disjoint (magSubspaceS Λ N M) (magSubspaceS Λ N M') :=
  magSubspaceS_disjoint hMM'

/-- `Ŝ_tot^(3) · |σ⟩ = magEigenvalueS σ • |σ⟩`. -/
example {N : ℕ} (σ : Λ → Fin (N + 1)) :
    (totalSpinSOp3 Λ N).mulVec (basisVecS σ) =
      magEigenvalueS σ • basisVecS σ :=
  totalSpinSOp3_mulVec_basisVecS σ

/-- Each basis state lies in its own magnetization subspace. -/
example {N : ℕ} (σ : Λ → Fin (N + 1)) :
    (basisVecS σ : (Λ → Fin (N + 1)) → ℂ) ∈
      magSubspaceS Λ N (magEigenvalueS σ) :=
  basisVecS_mem_magSubspaceS σ

/-- Constant config formula. -/
example {N : ℕ} (s : Fin (N + 1)) :
    magEigenvalueS (fun _ : Λ => s) =
      (Fintype.card Λ : ℂ) * ((N : ℂ) / 2 - (s.val : ℂ)) :=
  magEigenvalueS_const s

/-- All-zero magSumS is 0. -/
example {N : ℕ} :
    magSumS (fun _ : Λ => (0 : Fin (N + 1))) = 0 :=
  magSumS_const_zero

/-- All-zero is the highest-weight state with eigenvalue `|Λ| · N/2`. -/
example {N : ℕ} :
    magEigenvalueS (fun _ : Λ => (0 : Fin (N + 1))) =
      (Fintype.card Λ : ℂ) * (N : ℂ) / 2 :=
  magEigenvalueS_const_zero

end LatticeSystem.Tests.SpinSMagnetization
