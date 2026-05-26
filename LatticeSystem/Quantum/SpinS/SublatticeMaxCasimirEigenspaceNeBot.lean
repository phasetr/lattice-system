import LatticeSystem.Quantum.SpinS.SublatticeSpinDot
import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# The sublattice maximal-Casimir eigenspace is non-trivial

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The `(Ŝ_A)²`-eigenspace at the maximal sublattice Casimir `s_A(s_A+1)` (the
"A-symmetric subspace") is non-trivial: the all-up state `|σ_⊤⟩` lies in it
(`sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero`).  This is the sublattice
analogue of `totalSpinSSquaredEigenspace_max_ne_bot`, the base of the
sublattice-symmetric-subspace dimension theory used to produce the
minimal-total-spin highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **The all-up state lies in the maximal sublattice-Casimir eigenspace**. -/
theorem allAlignedStateS_zero_mem_sublatticeMaxCasimirEigenspace (A : Λ → Bool) :
    allAlignedStateS Λ N (0 : Fin (N + 1)) ∈
      Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  exact sublatticeSpinSquaredS_mulVec_allAlignedStateS_zero (N := N) A

/-- **The maximal sublattice-Casimir eigenspace is non-trivial**: the `(Ŝ_A)²`
eigenspace at `s_A(s_A+1)` contains the non-zero all-up state. -/
theorem sublatticeMaxCasimirEigenspace_ne_bot [Nonempty Λ] (A : Λ → Bool) :
    Module.End.eigenspace (sublatticeSpinSquaredS N A).mulVecLin
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) ≠ ⊥ := by
  intro h_eq_bot
  have h_mem := allAlignedStateS_zero_mem_sublatticeMaxCasimirEigenspace (Λ := Λ) (N := N) A
  rw [h_eq_bot, Submodule.mem_bot] at h_mem
  exact allAlignedStateS_ne_zero (V := Λ) (N := N) 0 h_mem

end LatticeSystem.Quantum
