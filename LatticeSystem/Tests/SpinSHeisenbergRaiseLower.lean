import LatticeSystem.Quantum.SpinS.HeisenbergRaiseLower

/-!
# Test coverage for spin-`S` Heisenberg matrix on raise/lower steps
(Tasaki §2.5 Phase B-γ γ-3 irreducibility prep)
-/

namespace LatticeSystem.Tests.SpinSHeisenbergRaiseLower

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Heisenberg matrix entry on raise/lower step witness. -/
example {N : ℕ} (J : V → V → ℂ)
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (heisenbergHamiltonianS J N) σ' σ =
      (J x y + J y x) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ :=
  heisenbergHamiltonianS_apply_of_raiseLowerStepS_witness J N hadj hsh hagree

/-- Heisenberg matrix entry strictly real-positive on raise/lower step. -/
example {N : ℕ} {J : V → V → ℂ}
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((heisenbergHamiltonianS J N) σ' σ).re :=
  heisenbergHamiltonianS_apply_re_pos_of_raiseLowerStepS_witness N hadj
    hJ_real hJ_pos hJ_sym hsh hagree

/-- Heisenberg matrix entry non-zero on raise/lower step. -/
example {N : ℕ} {J : V → V → ℂ}
    {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (heisenbergHamiltonianS J N) σ' σ ≠ 0 :=
  heisenbergHamiltonianS_apply_ne_zero_of_raiseLowerStepS_witness N hadj
    hJ_real hJ_pos hJ_sym hsh hagree

end LatticeSystem.Tests.SpinSHeisenbergRaiseLower
