import LatticeSystem.Quantum.SpinS.RaiseLower

/-!
# Test coverage for spin-`S` raise/lower step
(Tasaki §2.5 Phase B-γ γ-3 connectivity)
-/

namespace LatticeSystem.Tests.SpinSRaiseLower

open LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reflexivity of `RaiseLowerReachableS`. -/
example {N : ℕ} (G : SimpleGraph V) (σ : V → Fin (N + 1)) :
    RaiseLowerReachableS G σ σ :=
  RaiseLowerReachableS.refl G σ

/-- A single `RaiseLowerStepS` is a `RaiseLowerReachableS`. -/
example {N : ℕ} (G : SimpleGraph V) (σ σ' : V → Fin (N + 1))
    (h : RaiseLowerStepS G σ σ') :
    RaiseLowerReachableS G σ σ' :=
  RaiseLowerReachableS.single h

/-- Transitivity of `RaiseLowerReachableS`. -/
example {N : ℕ} (G : SimpleGraph V) (σ τ σ' : V → Fin (N + 1))
    (h₁ : RaiseLowerReachableS G σ τ) (h₂ : RaiseLowerReachableS G τ σ') :
    RaiseLowerReachableS G σ σ' :=
  h₁.trans h₂

/-- Magnetization conservation under `RaiseLowerStepS`. -/
example {N : ℕ} (G : SimpleGraph V) (σ σ' : V → Fin (N + 1))
    (h : RaiseLowerStepS G σ σ') :
    magSumS σ' = magSumS σ :=
  magSumS_eq_of_raiseLowerStepS h

/-- Magnetization-eigenvalue conservation under `RaiseLowerReachableS`. -/
example {N : ℕ} (G : SimpleGraph V) (σ σ' : V → Fin (N + 1))
    (h : RaiseLowerReachableS G σ σ') :
    magEigenvalueS σ' = magEigenvalueS σ :=
  magEigenvalueS_eq_of_raiseLowerReachableS h

/-- `raiseLowerSwapS` value at `x` is `σ x − 1`. -/
example {N : ℕ} {x y : V} (hxy : x ≠ y)
    {σ : V → Fin (N + 1)} (hxy_strict : (σ y).val < (σ x).val) :
    (raiseLowerSwapS σ x y hxy_strict x).val = (σ x).val - 1 :=
  raiseLowerSwapS_apply_x hxy hxy_strict

/-- `raiseLowerSwapS` value at `y` is `σ y + 1`. -/
example {N : ℕ} {x y : V}
    {σ : V → Fin (N + 1)} (hxy_strict : (σ y).val < (σ x).val) :
    (raiseLowerSwapS σ x y hxy_strict y).val = (σ y).val + 1 :=
  raiseLowerSwapS_apply_y hxy_strict

/-- Single-edge step: G-adjacent + σ y < σ x ⟹ RaiseLowerStepS. -/
example {N : ℕ} {G : SimpleGraph V} {x y : V} (hadj : G.Adj x y)
    {σ : V → Fin (N + 1)} (hxy_strict : (σ y).val < (σ x).val) :
    RaiseLowerStepS G σ (raiseLowerSwapS σ x y hxy_strict) :=
  raiseLowerStepS_of_adj_of_lt hadj hxy_strict

/-- Symmetry of `RaiseLowerStepS`. -/
example {N : ℕ} (G : SimpleGraph V) (σ σ' : V → Fin (N + 1))
    (h : RaiseLowerStepS G σ σ') :
    RaiseLowerStepS G σ' σ :=
  h.symm

/-- Symmetry of `RaiseLowerReachableS`. -/
example {N : ℕ} (G : SimpleGraph V) (σ σ' : V → Fin (N + 1))
    (h : RaiseLowerReachableS G σ σ') :
    RaiseLowerReachableS G σ' σ :=
  h.symm

/-- spinSDot non-zero from raise/lower step witness. -/
example {N : ℕ} {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (spinSDot x y N : ManyBodyOpS V N) σ' σ ≠ 0 :=
  spinSDot_apply_ne_zero_of_raiseLowerStepS_witness hadj hsh hagree

/-- spinSDot real-positive from raise/lower step witness. -/
example {N : ℕ} {G : SimpleGraph V} {σ σ' : V → Fin (N + 1)}
    {x y : V} (hadj : G.Adj x y)
    (hsh : ((σ x).val + 1 = (σ' x).val ∧ (σ' y).val + 1 = (σ y).val) ∨
      ((σ' x).val + 1 = (σ x).val ∧ (σ y).val + 1 = (σ' y).val))
    (hagree : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    0 < ((spinSDot x y N : ManyBodyOpS V N) σ' σ).re :=
  spinSDot_apply_re_pos_of_raiseLowerStepS_witness hadj hsh hagree

end LatticeSystem.Tests.SpinSRaiseLower
