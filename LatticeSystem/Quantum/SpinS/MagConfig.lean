import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# The magnetization-`M` configuration subtype
(Tasaki §2.5 Phase B-γ γ-3 final prep)

For the spin-S Marshall–Lieb–Mattis theorem, the irreducibility argument
applies to the dressed Heisenberg matrix restricted to a single
magnetization sector. This module defines the subtype of configurations
with a fixed magnetization sum:

  `magConfigS V N M := { σ : V → Fin (N + 1) // magSumS σ = M }`.

This is the natural index type for the sector-restricted matrix used
in the PF irreducibility application.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The subtype of configurations with magnetization sum `M`. -/
def magConfigS (V : Type*) [Fintype V] (N M : ℕ) :=
  { σ : V → Fin (N + 1) // magSumS σ = M }

omit [DecidableEq V] in
/-- A magConfig has magSumS equal to its tag. -/
theorem magConfigS_magSumS {M : ℕ} (σ : magConfigS V N M) :
    magSumS σ.1 = M := σ.2

instance magConfigS_instDecidableEq {M : ℕ} :
    DecidableEq (magConfigS V N M) := fun _ _ => Subtype.instDecidableEq _ _

instance magConfigS_instFintype {M : ℕ} : Fintype (magConfigS V N M) := by
  unfold magConfigS
  classical
  apply Subtype.fintype

end LatticeSystem.Quantum
