import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations
import LatticeSystem.Quantum.SpinS.BasisVecSOrthonormal

/-!
# Transverse single-site spin operators have zero expectation on
basis states

For any configuration `σ : V → Fin (N + 1)` and any site `x : V`,
the single-site transverse spin operators `Ŝ^{(1)}_x` and `Ŝ^{(2)}_x`
have zero diagonal matrix element at `σ` (since both `spinSOp1 N`
and `spinSOp2 N` have all-zero diagonal entries by
`spinSOp1_apply_diag` and `spinSOp2_apply_diag`). Hence:

  `⟨basisVecS σ, Ŝ^{(α)}_x · basisVecS σ⟩ = 0`

for `α = 1, 2` and any `σ`. Specialised to all-aligned states
`|c..c⟩`, this gives the saturated-ferromagnet GS transverse
magnetization expectation value 0.

Combined with PR #925 (`⟨Ŝ^{(3)}_x⟩ = N/2 − c.val`), this completes
the per-axis mean spin expectation profile on the all-aligned
state: `(0, 0, N/2 − c.val)`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- Helper: the diagonal matrix element of `onSiteS x A` at any
configuration `σ` equals `A (σ x) (σ x)` (the single-site diagonal
of `A`). -/
private theorem onSiteS_apply_diag_aux (x : V)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (σ : V → Fin (N + 1)) :
    (onSiteS x A : ManyBodyOpS V N) σ σ = A (σ x) (σ x) := by
  rw [onSiteS_apply, if_pos (fun _ _ => rfl)]

/-- The single-site `Ŝ^{(1)}_x` has zero expectation on any basis
state `basisVecS σ`. -/
theorem basisVecS_expectation_onSiteS_spinSOp1 (x : V)
    (σ : V → Fin (N + 1)) :
    dotProduct (star (basisVecS σ : (V → Fin (N + 1)) → ℂ))
      ((onSiteS x (spinSOp1 N) : ManyBodyOpS V N).mulVec (basisVecS σ)) = 0 := by
  -- (Ŝ^(1)_x).mulVec (basisVecS σ) τ = (Ŝ^(1)_x) τ σ.
  -- Inner product picks out τ = σ, giving (Ŝ^(1)_x) σ σ = 0.
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · -- Diagonal: (basisVecS σ).σ = 1; (Ŝ^(1)_x).mulVec |σ⟩ σ = (Ŝ^(1)_x) σ σ = 0.
    have h_mulVec : (onSiteS x (spinSOp1 N) : ManyBodyOpS V N).mulVec
        (basisVecS σ) σ = 0 := by
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single σ]
      · rw [onSiteS_apply_diag_aux, spinSOp1_apply_diag, basisVecS_self, mul_one]
      · intros τ _ hτne
        rw [basisVecS_of_ne hτne, mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [h_mulVec]; simp
  · -- Off-diagonal: (basisVecS σ) τ = 0 for τ ≠ σ.
    intros τ _ hτne
    simp only [Pi.star_apply]
    rw [show (basisVecS σ : (V → Fin (N + 1)) → ℂ) τ = 0 from
      basisVecS_of_ne hτne]
    simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The single-site `Ŝ^{(2)}_x` has zero expectation on any basis
state `basisVecS σ`. -/
theorem basisVecS_expectation_onSiteS_spinSOp2 (x : V)
    (σ : V → Fin (N + 1)) :
    dotProduct (star (basisVecS σ : (V → Fin (N + 1)) → ℂ))
      ((onSiteS x (spinSOp2 N) : ManyBodyOpS V N).mulVec (basisVecS σ)) = 0 := by
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · have h_mulVec : (onSiteS x (spinSOp2 N) : ManyBodyOpS V N).mulVec
        (basisVecS σ) σ = 0 := by
      rw [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single σ]
      · rw [onSiteS_apply_diag_aux, spinSOp2_apply_diag, basisVecS_self, mul_one]
      · intros τ _ hτne
        rw [basisVecS_of_ne hτne, mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
    rw [h_mulVec]; simp
  · intros τ _ hτne
    simp only [Pi.star_apply]
    rw [show (basisVecS σ : (V → Fin (N + 1)) → ℂ) τ = 0 from
      basisVecS_of_ne hτne]
    simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- Specialisation: all-aligned states `|c..c⟩` have zero
`Ŝ^{(1)}_x` expectation. -/
theorem allAlignedStateS_expectation_onSiteS_spinSOp1
    (x : V) (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
      ((onSiteS x (spinSOp1 N) : ManyBodyOpS V N).mulVec
        (allAlignedStateS V N c)) = 0 := by
  unfold allAlignedStateS
  exact basisVecS_expectation_onSiteS_spinSOp1 x _

/-- Specialisation: all-aligned states `|c..c⟩` have zero
`Ŝ^{(2)}_x` expectation. -/
theorem allAlignedStateS_expectation_onSiteS_spinSOp2
    (x : V) (c : Fin (N + 1)) :
    dotProduct (star (allAlignedStateS V N c))
      ((onSiteS x (spinSOp2 N) : ManyBodyOpS V N).mulVec
        (allAlignedStateS V N c)) = 0 := by
  unfold allAlignedStateS
  exact basisVecS_expectation_onSiteS_spinSOp2 x _

end LatticeSystem.Quantum
