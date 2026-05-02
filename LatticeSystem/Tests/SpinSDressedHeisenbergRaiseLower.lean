import LatticeSystem.Quantum.SpinS.DressedHeisenbergRaiseLower

/-!
# Test coverage for spin-`S` dressed Heisenberg matrix on bipartite raise/lower steps
(Tasaki §2.5 Phase B-γ γ-3 irreducibility)
-/

namespace LatticeSystem.Tests.SpinSDressedHeisenbergRaiseLower

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Dressed Heisenberg matrix entry strictly real-negative on
bipartite raise/lower step. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ}
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (dressedHeisenbergS A J N σ' σ).re < 0 :=
  dressedHeisenbergS_apply_re_neg_of_raiseLowerStepS_witness A N hadj hAne
    hJ_real hJ_pos hJ_sym hsh hagree

/-- Dressed Heisenberg matrix entry non-zero on bipartite raise/lower step. -/
example {N : ℕ} (A : V → Bool) {J : V → V → ℂ}
    {G : SimpleGraph V} {σ' σ : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y) (hAne : A x ≠ A y)
    (hJ_real : (J x y).im = 0) (hJ_pos : 0 < (J x y).re)
    (hJ_sym : J x y = J y x)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergS A J N σ' σ ≠ 0 :=
  dressedHeisenbergS_apply_ne_zero_of_raiseLowerStepS_witness A N hadj hAne
    hJ_real hJ_pos hJ_sym hsh hagree

end LatticeSystem.Tests.SpinSDressedHeisenbergRaiseLower
