import LatticeSystem.Quantum.SpinS.MultiSiteCore

/-!
# Permutation matrices of configuration maps

A map `f` of spin configurations `σ : Λ → Fin (N + 1)` induces the many-body operator
`configPermMatrixS f` acting on basis vectors by `e_σ ↦ e_{f σ}`.  When `f` is an involution the
operator is a self-inverse permutation matrix, and conjugation by it is reindexing by `f`.

Two constructions in the library are instances of this pattern: the many-body spin reversal `Θ`
(`ManyBodyReversalS.lean`, `f = revConfigS`, which reverses each site's `Ŝ³` index) and the
bond-centered inversion `Û_inv` of Tasaki eq. (8.3.5) (`VBSInversionParity.lean`,
`f = bondInversionConfigS`, which reverses the *order of the sites*).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.5, p. 43, and §8.3.2, eq. (8.3.5), p. 257.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **permutation matrix of a configuration map** `f`: the many-body operator whose entry at
`(σ', σ)` is `1` exactly when `σ' = f σ`, i.e. the operator sending the basis vector `e_σ` to
`e_{f σ}`. -/
noncomputable def configPermMatrixS {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (f : (Λ → Fin (N + 1)) → Λ → Fin (N + 1)) : ManyBodyOpS Λ N :=
  Matrix.of fun σ' σ => if σ' = f σ then (1 : ℂ) else 0

/-- Matrix entry of `configPermMatrixS f`. -/
theorem configPermMatrixS_apply (f : (Λ → Fin (N + 1)) → Λ → Fin (N + 1))
    (σ' σ : Λ → Fin (N + 1)) :
    configPermMatrixS f σ' σ = if σ' = f σ then (1 : ℂ) else 0 := rfl

/-- For an involutive `f`, the permutation matrix acts on a vector by precomposition with `f`:
`(configPermMatrixS f) Φ = Φ ∘ f`. -/
theorem configPermMatrixS_mulVec {f : (Λ → Fin (N + 1)) → Λ → Fin (N + 1)}
    (hf : Function.Involutive f) (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (configPermMatrixS f).mulVec Φ = fun σ => Φ (f σ) := by
  funext σ
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (f σ)]
  · rw [configPermMatrixS_apply, if_pos (hf σ).symm, one_mul]
  · intro ρ _ hρ
    rw [configPermMatrixS_apply, if_neg (fun h => hρ (by rw [h, hf ρ])), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Conjugation by `configPermMatrixS f` reindexes the matrix entries by `f`. -/
theorem configPermMatrixS_conj_apply {f : (Λ → Fin (N + 1)) → Λ → Fin (N + 1)}
    (hf : Function.Involutive f) (M : ManyBodyOpS Λ N) (σ' σ : Λ → Fin (N + 1)) :
    (configPermMatrixS f * M * configPermMatrixS f) σ' σ = M (f σ') (f σ) := by
  rw [Matrix.mul_apply]
  have hUM : ∀ τ, (configPermMatrixS f * M) σ' τ = M (f σ') τ := by
    intro τ
    rw [Matrix.mul_apply, Finset.sum_eq_single (f σ')]
    · rw [configPermMatrixS_apply, if_pos (hf σ').symm, one_mul]
    · intro ρ _ hρ
      rw [configPermMatrixS_apply, if_neg (fun h => hρ (by rw [h, hf ρ])), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_eq_single (f σ)]
  · rw [hUM, configPermMatrixS_apply, if_pos rfl, mul_one]
  · intro ρ _ hρ
    rw [hUM, configPermMatrixS_apply, if_neg hρ, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The permutation matrix of an involution is its own inverse. -/
theorem configPermMatrixS_mul_self {f : (Λ → Fin (N + 1)) → Λ → Fin (N + 1)}
    (hf : Function.Involutive f) :
    configPermMatrixS f * configPermMatrixS f = (1 : ManyBodyOpS Λ N) := by
  ext σ' σ
  rw [show configPermMatrixS f * configPermMatrixS (Λ := Λ) (N := N) f
        = configPermMatrixS f * 1 * configPermMatrixS f by rw [mul_one],
    configPermMatrixS_conj_apply hf, Matrix.one_apply, Matrix.one_apply]
  by_cases h : σ' = σ
  · subst h; simp
  · have hne : ¬ (f σ' = f σ) := fun hfe => h (hf.injective hfe)
    simp only [if_neg h, if_neg hne]

end LatticeSystem.Quantum
