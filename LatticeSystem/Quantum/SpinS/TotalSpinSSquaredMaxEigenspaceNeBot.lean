import LatticeSystem.Quantum.SpinS.AllAlignedStateMemTotalSpinSSquaredMaxEigenspace

/-!
# Max-Casimir `(Ŝ_tot)²` eigenspace is non-trivial

The maximum-Casimir `(Ŝ_tot)²`-eigenspace contains the non-zero
all-up state `|σ_⊤⟩`, so it is non-trivial:

  `Module.End.eigenspace (Ŝ_tot)².mulVecLin
       (saturatedFerromagnetCasimirEigenvalueS V N) ≠ ⊥`.

A-independent, J-independent existence statement underpinning the
operator-level non-emptiness of the §2.4 saturated-FM ground-state
subspace.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

set_option linter.style.longLine false in
/-- **Max-Casimir `(Ŝ_tot)²` eigenspace is non-trivial**:
contains the non-zero `|σ_⊤⟩`. -/
theorem totalSpinSSquaredEigenspace_max_ne_bot
    [Nonempty V] :
    Module.End.eigenspace (totalSpinSSquared V N).mulVecLin
        (saturatedFerromagnetCasimirEigenvalueS V N) ≠ ⊥ := by
  intro h_eq_bot
  -- |σ_⊤⟩ is in the eigenspace.
  have h_mem :=
    allAlignedStateS_zero_mem_totalSpinSSquaredEigenspace_max
      (V := V) (N := N)
  -- If the eigenspace is ⊥, then |σ_⊤⟩ = 0.
  rw [h_eq_bot, Submodule.mem_bot] at h_mem
  -- But |σ_⊤⟩ ≠ 0.
  exact allAlignedStateS_ne_zero (V := V) (N := N) 0 h_mem

end LatticeSystem.Quantum
