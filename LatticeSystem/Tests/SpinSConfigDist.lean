import LatticeSystem.Quantum.SpinS.ConfigDist

/-!
# Test coverage for spin-`S` configuration distance and reachability
(Tasaki §2.5 Phase B-γ γ-3)
-/

namespace LatticeSystem.Tests.SpinSConfigDist

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Configuration distance is zero iff configurations are equal. -/
example {N : ℕ} (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = 0 ↔ σ = σ' :=
  configDistS_eq_zero_iff σ σ'

/-- Configuration distance is symmetric. -/
example {N : ℕ} (σ σ' : V → Fin (N + 1)) :
    configDistS σ σ' = configDistS σ' σ :=
  configDistS_comm σ σ'

/-- Self-distance is zero. -/
example {N : ℕ} (σ : V → Fin (N + 1)) : configDistS σ σ = 0 :=
  configDistS_self σ

/-- Distance is positive iff configurations differ. -/
example {N : ℕ} (σ σ' : V → Fin (N + 1)) :
    0 < configDistS σ σ' ↔ σ ≠ σ' :=
  configDistS_pos_iff σ σ'

/-- For distinct equal-magnetization configurations, over/under sites
exist. -/
example {N : ℕ} {σ σ' : V → Fin (N + 1)}
    (hne : σ ≠ σ') (hmag : magSumS σ = magSumS σ') :
    (∃ x : V, (σ' x).val < (σ x).val) ∧
      ∃ y : V, (σ y).val < (σ' y).val :=
  exists_over_under_of_eq_magSumS hne hmag

/-- Complete-graph reachability for equal-magnetization configurations. -/
example {N : ℕ} {σ σ' : V → Fin (N + 1)}
    (hmag : magSumS σ = magSumS σ') :
    RaiseLowerReachableS (⊤ : SimpleGraph V) σ σ' :=
  raiseLowerReachableS_completeGraph_of_eq_magSumS hmag

end LatticeSystem.Tests.SpinSConfigDist
