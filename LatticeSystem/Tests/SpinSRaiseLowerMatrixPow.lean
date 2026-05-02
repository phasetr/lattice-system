import LatticeSystem.Quantum.SpinS.RaiseLowerMatrixPow

/-!
# Test coverage for spin-`S` matrix-power positivity from raise/lower
(Tasaki §2.5 Phase B-γ γ-3 PF prep)
-/

namespace LatticeSystem.Tests.SpinSRaiseLowerMatrixPow

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Matrix-power positivity from raise/lower reachability. -/
example {N : ℕ} {G : SimpleGraph V}
    {B : Matrix (V → Fin (N + 1)) (V → Fin (N + 1)) ℝ}
    (hB_nn : ∀ σ τ, 0 ≤ B σ τ)
    (hB_step : ∀ {σ τ : V → Fin (N + 1)},
      RaiseLowerStepS G σ τ → 0 < B τ σ)
    {σ σ' : V → Fin (N + 1)}
    (hreach : RaiseLowerReachableS G σ σ') :
    ∃ k : ℕ, 0 < (B ^ k) σ' σ :=
  exists_matrixPow_apply_pos_of_raiseLowerReachableS hB_nn hB_step hreach

end LatticeSystem.Tests.SpinSRaiseLowerMatrixPow
