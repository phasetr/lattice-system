import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.BasisVecSOrthonormal

/-!
# Distinct constant-spin states are different

For `[Nonempty V]` and `c₁ ≠ c₂` in `Fin (N + 1)`, the all-aligned
states `|c₁..c₁⟩` and `|c₂..c₂⟩` are distinct vectors.

This follows from `allAlignedConfigS V N c₁ ≠ allAlignedConfigS V N c₂`
when `c₁ ≠ c₂` (different constants on a non-empty `V`), combined
with the injectivity of `basisVecS` (different configs give different
basis vectors, via `basisVecS_inner_of_ne` from PR #914).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- `allAlignedConfigS V N c₁ ≠ allAlignedConfigS V N c₂` when
`c₁ ≠ c₂` and `V` is non-empty. -/
theorem allAlignedConfigS_injective [Nonempty V] :
    Function.Injective (allAlignedConfigS V N) := by
  intros c₁ c₂ h
  obtain ⟨x⟩ := ‹Nonempty V›
  exact congrFun h x

/-- The all-aligned states at distinct constants are distinct. -/
theorem allAlignedStateS_ne_of_ne [Nonempty V] {c₁ c₂ : Fin (N + 1)}
    (hne : c₁ ≠ c₂) :
    allAlignedStateS V N c₁ ≠ allAlignedStateS V N c₂ := by
  intro h
  unfold allAlignedStateS at h
  -- basisVecS σ₁ = basisVecS σ₂ implies σ₁ = σ₂.
  have hcfg : allAlignedConfigS V N c₁ = allAlignedConfigS V N c₂ := by
    -- Evaluate both sides at the all-aligned config c₁ to extract the equality.
    have h_eval := congrFun h (allAlignedConfigS V N c₁)
    simp only [basisVecS_self] at h_eval
    -- h_eval: 1 = basisVecS (allAlignedConfigS V N c₂) (allAlignedConfigS V N c₁).
    -- If σ₂ ≠ σ₁, then RHS = 0, contradiction.
    by_contra hcfg_ne
    -- target: 1 = basisVecS σ₂ σ₁, with σ₂ ≠ σ₁ (i.e., hcfg_ne : σ₁ ≠ σ₂).
    rw [basisVecS_of_ne hcfg_ne] at h_eval
    exact one_ne_zero h_eval
  exact hne (allAlignedConfigS_injective hcfg)

end LatticeSystem.Quantum
