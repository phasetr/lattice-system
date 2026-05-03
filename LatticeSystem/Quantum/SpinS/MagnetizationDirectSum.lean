import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.AllAlignedState
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Magnetization subspaces form an internal direct sum (spin-`S`)

Spin-`S` analog of the spin-`1/2` results in
`LatticeSystem/Quantum/MagnetizationSubspace.lean`. The total
`Ŝ_{tot}^{(3)}`-eigenspaces (`magSubspaceS Λ N M`) form an
**internal direct sum** of the multi-site Hilbert space
`(Λ → Fin (N + 1)) → ℂ`, generalising the spin-`1/2` case.

The decomposition has three ingredients:

1. **`magSubspaceS_eq_eigenspace`** — `magSubspaceS Λ N M` coincides
   with the standard `Module.End.eigenspace` of the total
   `Ŝ_{tot}^{(3)}` operator (viewed as an endomorphism via
   `Matrix.mulVecLin`).
2. **`magSubspaceS_iSupIndep`** — distinct magnetization eigenvalues
   give linearly independent eigenspaces. Inherited from
   `Module.End.eigenspaces_iSupIndep` (applicable because `ℂ` is a
   field, hence `IsDomain` and `IsTorsionFree`).
3. **`iSup_magSubspaceS_eq_top`** — the magnetization subspaces span
   the full Hilbert space (already in `Magnetization.lean`).

Combined, these give `magSubspaceS_isInternal`: the magnetization
subspaces form an internal direct sum
`(Λ → Fin (N + 1)) → ℂ ≃ ⊕_M (magSubspaceS Λ N M)`.

As corollaries (using PRs #875, #886, #887), the unnormalised
ferromagnetic ground-state ladder iterates
`(Ŝ_{tot}^∓)^k · |σ_{⊤/⊥}⟩` lie in the magnetization sectors
`magSubspaceS V N (m_max ∓ k)`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Bridge to `Module.End.eigenspace` -/

/-- The magnetization subspace coincides with the standard
`Module.End.eigenspace` of the total `Ŝ_{tot}^{(3)}` operator (viewed
as a `(V → Fin (N + 1)) → ℂ`-endomorphism via `Matrix.mulVecLin`). -/
theorem magSubspaceS_eq_eigenspace (M : ℂ) :
    magSubspaceS V N M =
      Module.End.eigenspace ((totalSpinSOp3 V N).mulVecLin) M := by
  ext v
  rw [mem_magSubspaceS_iff, Module.End.mem_eigenspace_iff,
    Matrix.mulVecLin_apply]

/-! ## Internal direct sum -/

/-- The magnetization subspaces form an `iSupIndep` family: distinct
eigenvalues give linearly independent eigenspaces. Inherited from
`Module.End.eigenspaces_iSupIndep` over `ℂ` (a field, hence `IsDomain`
and `IsTorsionFree`). -/
theorem magSubspaceS_iSupIndep :
    iSupIndep (magSubspaceS V N) := by
  have heq : (magSubspaceS V N : ℂ → Submodule ℂ ((V → Fin (N + 1)) → ℂ)) =
      Module.End.eigenspace ((totalSpinSOp3 V N).mulVecLin) := by
    funext M
    exact magSubspaceS_eq_eigenspace M
  rw [heq]
  exact Module.End.eigenspaces_iSupIndep _

/-- The magnetization subspaces form an internal direct sum:
`(V → Fin (N + 1)) → ℂ ≃ ⊕_M (magSubspaceS V N M)`. -/
theorem magSubspaceS_isInternal :
    DirectSum.IsInternal (magSubspaceS V N) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨magSubspaceS_iSupIndep, iSup_magSubspaceS_eq_top⟩

/-! ## Membership of the saturated-ferromagnet ladder iterates

Combining `totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero`
(PR #887) with `mem_magSubspaceS_iff` shows that the unnormalised
iterates `(Ŝ_{tot}^∓)^k · |σ_{⊤/⊥}⟩` lie in their respective
magnetization sectors. Spin-`S` analog of
`totalSpinHalfOpMinus_pow_basisVec_all_up_mem_magnetizationSubspace`
in `MagnetizationSubspace.lean`.
-/

/-- The unnormalised iterate `(Ŝ_{tot}^-)^k · |σ_⊤⟩` lies in the
magnetization subspace `magSubspaceS V N (|V|·N/2 − k)` (Tasaki
§2.4 eq. (2.4.9), p. 33, spin-`S` extension; companion of PR #887). -/
theorem totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS
    (k : ℕ) :
    ((totalSpinSOpMinus V N) ^ k).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) ∈
      magSubspaceS V N
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)) :=
  totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero k

/-- The unnormalised iterate `(Ŝ_{tot}^+)^k · |σ_⊥⟩` lies in the
magnetization subspace `magSubspaceS V N (−|V|·N/2 + k)` (Tasaki
§2.4 eq. (2.4.9), p. 33, spin-`S` extension, parameterised from the
lowest weight). -/
theorem totalSpinSOpPlus_pow_allAlignedStateS_last_mem_magSubspaceS
    (k : ℕ) :
    ((totalSpinSOpPlus V N) ^ k).mulVec
        (allAlignedStateS V N (Fin.last N)) ∈
      magSubspaceS V N
        ((-((Fintype.card V : ℂ) * (N : ℂ) / 2)) + (k : ℂ)) :=
  totalSpinSOp3_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last k

end LatticeSystem.Quantum
