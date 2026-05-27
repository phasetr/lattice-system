import LatticeSystem.Quantum.SpinS.MultiSite
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Many-body tensor (product) operator over the sites

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

`manyBodyTensorS W` is the configuration-indexed operator `⊗_x W x` with matrix entry
`∏_x (W x) (σ' x) (σ x)`.  It is functorial — `manyBodyTensorS W * manyBodyTensorS W' =
manyBodyTensorS (fun x => W x * W' x)` (a product of sums is a sum of products,
`Finset.prod_sum`) — so a single-site operator `onSiteS z A` (the tensor with `A` at `z` and
`1` elsewhere) is conjugated by `Θ_U = ⊗_x U` to `onSiteS z (U A U⁻¹)`.  This is the general
single-site-unitary lift used for the axis-swap gauge of Theorem 2.4 (where `U` is the
`π/2` rotation about axis 1, a Wigner `d`-matrix, not a permutation).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The many-body **tensor operator** `⊗_x W x` with entry `∏_x (W x) (σ' x) (σ x)`. -/
noncomputable def manyBodyTensorS (W : Λ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ManyBodyOpS Λ N :=
  Matrix.of fun σ' σ => ∏ x : Λ, W x (σ' x) (σ x)

omit [DecidableEq Λ] in
theorem manyBodyTensorS_apply (W : Λ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ' σ : Λ → Fin (N + 1)) :
    manyBodyTensorS W σ' σ = ∏ x : Λ, W x (σ' x) (σ x) := rfl

omit [DecidableEq Λ] in
/-- The all-identity tensor is the identity operator. -/
theorem manyBodyTensorS_one : manyBodyTensorS (fun _ : Λ => (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ))
    = 1 := by
  ext σ' σ
  rw [manyBodyTensorS_apply, Matrix.one_apply]
  by_cases h : σ' = σ
  · subst h; simp
  · obtain ⟨z, hz⟩ := Function.ne_iff.mp h
    rw [if_neg h, Finset.prod_eq_zero (Finset.mem_univ z)]
    rw [Matrix.one_apply, if_neg hz]

/-- **Functoriality**: `(⊗ W)(⊗ W') = ⊗ (W · W')` (a product of sums of products). -/
theorem manyBodyTensorS_mul (W W' : Λ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodyTensorS W * manyBodyTensorS W' = manyBodyTensorS (fun x => W x * W' x) := by
  ext σ' σ
  simp only [Matrix.mul_apply, manyBodyTensorS_apply]
  have hps : (∏ x : Λ, ∑ k : Fin (N + 1), W x (σ' x) k * W' x k (σ x)) =
      ∑ τ : Λ → Fin (N + 1), ∏ x : Λ, W x (σ' x) (τ x) * W' x (τ x) (σ x) :=
    Fintype.prod_sum (fun x k => W x (σ' x) k * W' x k (σ x))
  rw [hps]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [Finset.prod_mul_distrib]

end LatticeSystem.Quantum
