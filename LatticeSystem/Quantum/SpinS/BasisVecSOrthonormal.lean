import LatticeSystem.Quantum.SpinS.AllAlignedStateExpectations

/-!
# Orthonormality of the spin-`S` standard basis

The standard basis vectors `basisVecS σ` (one per configuration
`σ : V → Fin (N + 1)`) form an orthonormal family in the inner
product `⟨v, w⟩ := dotProduct (star v) w`:

  `⟨basisVecS σ, basisVecS τ⟩ = if τ = σ then 1 else 0`.

The diagonal case `σ = τ` was proved as PR #913's
`basisVecS_inner_self`. This file adds the off-diagonal case and
bundles them in Kronecker form.

Corollaries: extremal all-aligned states `|σ_⊤⟩` and `|σ_⊥⟩` are
orthogonal whenever `0 < N`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Off-diagonal orthogonality and Kronecker form -/

/-- Distinct configurations give orthogonal basis vectors. -/
theorem basisVecS_inner_of_ne {σ τ : V → Fin (N + 1)}
    (h : τ ≠ σ) :
    dotProduct (star (basisVecS σ : (V → Fin (N + 1)) → ℂ))
      (basisVecS τ) = 0 := by
  unfold dotProduct
  -- Each term: star (basisVecS σ ρ) * basisVecS τ ρ.
  -- Both factors are 0 unless ρ = σ (left) and ρ = τ (right). With τ ≠ σ,
  -- they can't both be 1, so each term is 0.
  apply Finset.sum_eq_zero
  intros ρ _
  simp only [Pi.star_apply]
  by_cases hρσ : ρ = σ
  · -- ρ = σ: right factor basisVecS τ ρ = basisVecS τ σ = 0 (τ ≠ σ).
    have hzero : (basisVecS τ : (V → Fin (N + 1)) → ℂ) ρ = 0 := by
      rw [hρσ]; exact basisVecS_of_ne (Ne.symm h)
    rw [hzero]; simp
  · -- ρ ≠ σ: left factor basisVecS σ ρ = 0.
    have hzero : (basisVecS σ : (V → Fin (N + 1)) → ℂ) ρ = 0 :=
      basisVecS_of_ne hρσ
    rw [hzero]; simp

/-- Bundled orthonormality of the standard basis in Kronecker form. -/
theorem basisVecS_inner_kronecker (σ τ : V → Fin (N + 1)) :
    dotProduct (star (basisVecS σ : (V → Fin (N + 1)) → ℂ))
      (basisVecS τ) = if τ = σ then (1 : ℂ) else 0 := by
  by_cases h : τ = σ
  · subst h
    rw [if_pos rfl, basisVecS_inner_self]
  · rw [if_neg h, basisVecS_inner_of_ne h]

/-! ## Corollaries: orthogonality of extremal all-aligned states -/

/-- The all-up and all-down states are orthogonal whenever
`[Nonempty V]` and `0 < N` (so they are at distinct configurations). -/
theorem allAlignedStateS_zero_inner_allAlignedStateS_last
    [Nonempty V] (hN : 0 < N) :
    dotProduct (star (allAlignedStateS V N (0 : Fin (N + 1))))
      (allAlignedStateS V N (Fin.last N)) = 0 := by
  unfold allAlignedStateS
  apply basisVecS_inner_of_ne
  intro h
  obtain ⟨x⟩ := ‹Nonempty V›
  have hx : (Fin.last N : Fin (N + 1)) = 0 := by
    have := congrFun h x
    simpa [allAlignedConfigS] using this
  have hval := congrArg Fin.val hx
  simp [Fin.last] at hval
  omega

end LatticeSystem.Quantum
