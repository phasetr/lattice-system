import LatticeSystem.Quantum.SpinS.Operators
import Mathlib.LinearAlgebra.Matrix.Hermitian
import LatticeSystem.Quantum.SpinS.MultiSiteCore

/-!
# Multi-site spin-`S` operator space and site-embedded operators
(Tasaki §2.5 Phase B-β β-3a)

This module generalises the spin-1/2 many-body operator space
(`Quantum/ManyBody.lean`, `ManyBodyOp Λ`) to **arbitrary spin** by
indexing configurations on `Λ → Fin (N + 1)` (with `N = 2S`).

The principal construction is the site-embedded operator

  `onSiteS i A : ManyBodyOpS Λ N`

which acts as a single-site spin-`S` operator
`A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ` on site `i ∈ Λ` and as
the identity on every other site.

This is the multi-site analogue needed for the spin-`S` Heisenberg
Hamiltonian and the §2.5 Marshall–Lieb–Mattis machinery for general
spin (Issue #412 Phase B-γ).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
/-! ## Specialised site-embedded spin-`S` operators -/

/-- The site-`i` spin-`S` operator `Ŝ_i^{(1)}` on the many-body
Hilbert space `(Λ → Fin (N + 1)) → ℂ`. -/
noncomputable def spinSSiteOp1 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp1 N)

/-- The site-`i` spin-`S` operator `Ŝ_i^{(2)}`. -/
noncomputable def spinSSiteOp2 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp2 N)

/-- The site-`i` spin-`S` operator `Ŝ_i^{(3)}`. -/
noncomputable def spinSSiteOp3 (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOp3 N)

/-- The site-`i` spin-`S` raising operator `Ŝ_i^+`. -/
noncomputable def spinSSiteOpPlus (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOpPlus N)

/-- The site-`i` spin-`S` lowering operator `Ŝ_i^-`. -/
noncomputable def spinSSiteOpMinus (i : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS i (spinSOpMinus N)

/-! ## Definitional unfoldings for site operators -/

/-- Definitional unfolding of `spinSSiteOp3`. -/
theorem spinSSiteOp3_def (i : Λ) (N : ℕ) :
    spinSSiteOp3 (Λ := Λ) i N = onSiteS i (spinSOp3 N) := rfl

/-! ## Computational basis vectors -/

/-- The standard basis vector at configuration `σ : Λ → Fin (N + 1)`:
the function that is `1` at `σ` and `0` elsewhere. Multi-site spin-`S`
generalisation of `basisVec` (`Quantum/ManyBody.lean`). -/
def basisVecS (σ : Λ → Fin (N + 1)) : (Λ → Fin (N + 1)) → ℂ :=
  fun τ => if τ = σ then 1 else 0

omit [DecidableEq Λ] in
/-- Explicit `if`-form of `basisVecS σ τ`. -/
theorem basisVecS_apply (σ τ : Λ → Fin (N + 1)) :
    basisVecS σ τ = if τ = σ then 1 else 0 := rfl

omit [DecidableEq Λ] in
/-- Diagonal value: `basisVecS σ σ = 1`. -/
@[simp]
theorem basisVecS_self (σ : Λ → Fin (N + 1)) : basisVecS σ σ = 1 := by
  unfold basisVecS; rw [if_pos rfl]

omit [DecidableEq Λ] in
/-- Off-diagonal: `basisVecS σ τ = 0` for `τ ≠ σ`. -/
theorem basisVecS_of_ne {σ τ : Λ → Fin (N + 1)} (hne : τ ≠ σ) :
    basisVecS σ τ = 0 := by
  unfold basisVecS; rw [if_neg hne]

/-- Same-site square: `(onSiteS i A) · (onSiteS i A) = onSiteS i (A * A)`. -/
theorem onSiteS_sq (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i A : ManyBodyOpS Λ N) * onSiteS i A = onSiteS i (A * A) :=
  onSiteS_mul_onSiteS_same i A A

/-- Negation distributes over `onSiteS`: `onSiteS i (-A) = -(onSiteS i A)`. -/
theorem onSiteS_neg (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (onSiteS i (-A) : ManyBodyOpS Λ N) = -(onSiteS i A) := by
  rw [show (-A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) =
        (-1 : ℂ) • A from by rw [neg_smul, one_smul]]
  rw [onSiteS_smul]
  rw [show ((-1 : ℂ) • onSiteS (N := N) i A : ManyBodyOpS Λ N) =
        -onSiteS i A from by rw [neg_smul, one_smul]]

/-- Commute version of distinct-site commutativity. -/
theorem onSiteS_commute_of_ne {i j : Λ} (hij : i ≠ j)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (onSiteS i A : ManyBodyOpS Λ N) (onSiteS j B) :=
  onSiteS_mul_onSiteS_of_ne hij A B

/-- Applying `onSiteS i A` to a basis vector and reading the result
at configuration `τ` yields the matrix element `(onSiteS i A) τ σ`:
the basis-vector mulVec collapses to a single matrix entry. -/
theorem onSiteS_mulVec_basisVecS_apply
    (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ τ : Λ → Fin (N + 1)) :
    (onSiteS i A : ManyBodyOpS Λ N).mulVec (basisVecS σ) τ =
      (onSiteS i A : ManyBodyOpS Λ N) τ σ := by
  classical
  change ∑ σ' : Λ → Fin (N + 1), (onSiteS i A) τ σ' * basisVecS σ σ' =
        (onSiteS i A) τ σ
  simp_rw [basisVecS_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ σ (fun σ' => (onSiteS i A) τ σ')]
  simp

/-- **Leibniz action of a one-site operator on an arbitrary vector.**  Applying `onSiteS i A` to
any `v : (Λ → Fin (N + 1)) → ℂ` and reading the result at `σ` sums the site-`i` matrix elements
`A (σ i) c` against the values of `v` on the configurations obtained from `σ` by resetting site
`i` to `c`: off that one-site image the matrix elements of `onSiteS i A` vanish. -/
theorem onSiteS_mulVec_apply (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (v : (Λ → Fin (N + 1)) → ℂ) (σ : Λ → Fin (N + 1)) :
    ((onSiteS i A : ManyBodyOpS Λ N) *ᵥ v) σ
      = ∑ c : Fin (N + 1), A (σ i) c * v (Function.update σ i c) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  have hsupp : ∀ τ ∈ (Finset.univ : Finset (Λ → Fin (N + 1))),
      τ ∉ (Finset.univ : Finset (Fin (N + 1))).image (fun c => Function.update σ i c) →
      (onSiteS i A : ManyBodyOpS Λ N) σ τ * v τ = 0 := by
    intro τ _ hτ
    have hne : ¬ (∀ k, k ≠ i → σ k = τ k) := by
      intro hall
      refine hτ (Finset.mem_image.2 ⟨τ i, Finset.mem_univ _, ?_⟩)
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · rw [Function.update_of_ne hk]; exact hall k hk
    rw [onSiteS_apply_eq_zero_of_off_site_diff i A hne, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ
      ((Finset.univ : Finset (Fin (N + 1))).image (fun c => Function.update σ i c))) hsupp,
    Finset.sum_image (by
      intro a _ b _ hab
      have := congrFun hab i
      simpa using this)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [onSiteS_apply_of_off_site_agree i A (fun k hk => (Function.update_of_ne hk _ _).symm)]
  simp

/-- For distinct sites `x ≠ y`, the product
`onSiteS x (Ŝ^+) * onSiteS y (Ŝ^-)` has non-negative real-part
matrix element on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    exact spinSOpPlus_mul_spinSOpMinus_re_nonneg N (σ' x) (σ x) (σ' y) (σ y)
  · rw [if_neg h]; simp

/-- Symmetric: `onSiteS x (Ŝ^-) * onSiteS y (Ŝ^+)` has non-negative
real-part matrix element on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_re_nonneg
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    0 ≤ ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).re := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    exact spinSOpMinus_mul_spinSOpPlus_re_nonneg N (σ' x) (σ x) (σ' y) (σ y)
  · rw [if_neg h]; simp

/-- For distinct sites `x ≠ y`, the product
`onSiteS x (Ŝ^+) * onSiteS y (Ŝ^-)` has zero imaginary part on every
`(σ', σ)` pair. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOpPlus_apply_im_zero, spinSOpMinus_apply_im_zero]
    ring
  · rw [if_neg h]; simp

/-- Symmetric: `onSiteS x (Ŝ^-) * onSiteS y (Ŝ^+)` has zero imaginary
part on every `(σ', σ)` pair. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOpMinus_apply_im_zero, spinSOpPlus_apply_im_zero]
    ring
  · rw [if_neg h]; simp

end LatticeSystem.Quantum
