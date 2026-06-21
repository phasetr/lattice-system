import LatticeSystem.Quantum.SpinS.MagSectorEmbeddingCore

/-!
# Magnetization-sector embedding: sector support and Hamiltonian action (capstone)

Continues MagSectorEmbeddingCore with sector-support / magnetization-eigenspace
results and the heisenbergHamiltonianS action on a sector. Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] {N : ℕ}

/-! ## Sector support and magnetization eigenspaces -/

section Support
variable [DecidableEq V]

/-- Pointwise diagonal action of `Ŝ_tot^(3)` on an arbitrary full
spin-`S` configuration vector.

This is the full-vector form of the computational-basis identity
`Ŝ_tot^(3) |σ⟩ = magEigenvalueS σ • |σ⟩`, used to pass between
`magSumS`-sector support and `magSubspaceS` eigenvector membership. -/
theorem totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul
    (Ψ : (V → Fin (N + 1)) → ℂ) (σ : V → Fin (N + 1)) :
    (totalSpinSOp3 V N).mulVec Ψ σ = magEigenvalueS σ * Ψ σ := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single σ]
  · rw [totalSpinSOp3_apply_diag]
  · intro τ _ hτσ
    rw [totalSpinSOp3_apply_off_diag (Ne.symm hτσ), zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- A zero-extended `magSumS = M` sector vector lies in the corresponding
`Ŝ_tot^(3)` eigenspace, whose eigenvalue is
`|V| * N / 2 - M`. -/
theorem magSectorEmbedding_mem_magSubspaceS {M : ℕ}
    (Φ : magConfigS V N M → ℂ) :
    magSectorEmbedding Φ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) := by
  rw [mem_magSubspaceS_iff]
  funext σ
  rw [totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul]
  by_cases h : magSumS σ = M
  · have hmag :
        magEigenvalueS σ =
          ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ) := by
      unfold magEigenvalueS
      rw [h]
    rw [hmag]
    simp [Pi.smul_apply, smul_eq_mul]
  · have hz : magSectorEmbedding Φ σ = 0 :=
      magSectorEmbedding_apply_of_not_mem Φ h
    simp [Pi.smul_apply, smul_eq_mul, hz]

/-- A vector in the `Ŝ_tot^(3)` eigenspace labelled by `magSumS = M`
vanishes on configurations outside that `magSumS` sector. -/
theorem magSubspaceS_apply_eq_zero_of_magSumS_ne {M : ℕ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)))
    {σ : V → Fin (N + 1)} (hσ : magSumS σ ≠ M) :
    Ψ σ = 0 := by
  rw [mem_magSubspaceS_iff] at hΨ
  have hτ_lhs :
      (totalSpinSOp3 V N).mulVec Ψ σ = magEigenvalueS σ * Ψ σ :=
    totalSpinSOp3_mulVec_apply_eq_magEigenvalueS_mul Ψ σ
  have hτ_rhs :
      ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) • Ψ) σ =
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) * Ψ σ := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq :
      magEigenvalueS σ * Ψ σ =
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) * Ψ σ := by
    rw [← hτ_lhs, hΨ, hτ_rhs]
  have hsub :
      (magEigenvalueS σ -
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ))) * Ψ σ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  have hne :
      magEigenvalueS σ -
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hmag
    apply hσ
    have hcast : (magSumS σ : ℂ) = (M : ℂ) := by
      unfold magEigenvalueS at hmag
      linear_combination -hmag
    exact_mod_cast hcast
  exact (mul_eq_zero.mp hsub).resolve_left hne

/-- A vector in the `magSumS = M` magnetization eigenspace is exactly
the zero-extension of its sector restriction.

This is the inverse support bridge to `magSectorEmbedding_mem_magSubspaceS`:
once a full vector is known to lie in `magSubspaceS V N (|V|·N/2 - M)`,
it can be handled by the sector-vector APIs after restricting it to
`magConfigS V N M`. -/
theorem magSectorEmbedding_magSectorRestriction_of_mem_magSubspaceS {M : ℕ}
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : Ψ ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (M : ℂ))) :
    magSectorEmbedding (magSectorRestriction (M := M) Ψ) = Ψ :=
  magSectorEmbedding_magSectorRestriction_of_supported
    (fun _ hσ => magSubspaceS_apply_eq_zero_of_magSumS_ne hΨ hσ)

end Support

/-! ## Heisenberg matrix element vanishes between different sectors -/

section
variable [DecidableEq V]

omit [DecidableEq V] in
/-- `magSumS σ = magSumS σ' ↔ magEigenvalueS σ = magEigenvalueS σ'`.
The two notions of magnetization differ only by an `(|V| · N) / 2` shift,
hence carry the same equality information. -/
theorem magEigenvalueS_eq_iff_magSumS_eq
    (σ σ' : V → Fin (N + 1)) :
    magEigenvalueS σ = magEigenvalueS σ' ↔ magSumS σ = magSumS σ' := by
  unfold magEigenvalueS
  constructor
  · intro h
    have hcast : (magSumS σ : ℂ) = (magSumS σ' : ℂ) := sub_right_injective h
    exact_mod_cast hcast
  · intro h
    rw [h]

/-- The Heisenberg matrix element vanishes between configurations with
different `magSumS` (corollary of `[H, S^z_tot] = 0`). -/
theorem heisenbergHamiltonianS_apply_eq_zero_of_magSumS_ne
    (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    (h : magSumS σ ≠ magSumS σ') :
    (heisenbergHamiltonianS J N) σ' σ = 0 := by
  apply heisenbergHamiltonianS_apply_eq_zero_of_mag_ne (Λ := V) J N
  -- Goal: magEigenvalueS σ ≠ magEigenvalueS σ'.
  intro hEig
  exact h ((magEigenvalueS_eq_iff_magSumS_eq σ σ').mp hEig)

/-- **Heisenberg-action commutes with sector embedding** (sector
configuration form): for real coupling, applying the full Heisenberg
Hamiltonian to a zero-extended sector vector at a sector
configuration `τ.1 ∈ magConfigS V N M` agrees with applying the
sector matrix to the sector vector at `τ`.

Proof: only sector-`M` configurations contribute to the full
`mulVec` sum (others give zero from the embedding), and on the
sector the embedding agrees with the sector vector. -/
theorem heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype
    (J : V → V → ℂ) {M : ℕ}
    (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N M) :
    (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) τ.1 =
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ τ := by
  change ∑ ρ, (heisenbergHamiltonianS J N) τ.1 ρ * magSectorEmbedding Φ ρ =
    ∑ ρ' : magConfigS V N M,
      heisenbergHamiltonianSMatrixOnMagSector J N M τ ρ' * Φ ρ'
  -- Convert RHS to a sum of `heis τ.1 ρ'.1 * embed Φ ρ'.1` over magConfigS.
  have hRHS : (∑ ρ' : magConfigS V N M,
      heisenbergHamiltonianSMatrixOnMagSector J N M τ ρ' * Φ ρ') =
    ∑ ρ' : magConfigS V N M,
      (heisenbergHamiltonianS J N) τ.1 ρ'.1 * magSectorEmbedding Φ ρ'.1 := by
    refine Finset.sum_congr rfl (fun ρ' _ => ?_)
    rw [heisenbergHamiltonianSMatrixOnMagSector_apply,
      magSectorEmbedding_apply_subtype]
  rw [hRHS]
  -- LHS = ∑ ρ : V → Fin (N+1). Restrict to filter (magSumS ρ = M) since
  -- embed vanishes outside.
  have hLHS_filter : (∑ ρ : V → Fin (N + 1),
        (heisenbergHamiltonianS J N) τ.1 ρ * magSectorEmbedding Φ ρ) =
      ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
        (heisenbergHamiltonianS J N) τ.1 ρ * magSectorEmbedding Φ ρ := by
    refine (Finset.sum_filter_of_ne (p := fun ρ => magSumS ρ = M) ?_).symm
    intro ρ _ hne
    by_contra h
    apply hne
    rw [magSectorEmbedding_apply_of_not_mem Φ h, mul_zero]
  rw [hLHS_filter]
  -- Reindex filter sum to ∑ over magConfigS via `Finset.sum_subtype`.
  rw [Finset.sum_subtype (Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M))
    (p := fun ρ => magSumS ρ = M)
    (fun ρ => by simp [Finset.mem_filter])
    (fun ρ => (heisenbergHamiltonianS J N) τ.1 ρ * magSectorEmbedding Φ ρ)]
  -- The subtype `{ρ // magSumS ρ = M}` is exactly `magConfigS V N M`.
  -- So we get the desired sum (modulo Subtype identification).
  rfl

/-- **Full-Hilbert-space ground-state lift** (Tasaki §2.5 Theorem 2.2,
sector → full bridge): a sector eigenvector of the Heisenberg sector
matrix at eigenvalue `μ` lifts to a full-Hilbert-space eigenvector of
the un-dressed quantum Heisenberg Hamiltonian at the same `μ`, via
zero-extension outside the magnetization sector.

Proof: pointwise on `σ : V → Fin (N + 1)`.
- If `σ ∈ sector M`: use the central bridge
  `heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype` and
  the sector eigenvector equation.
- If `σ ∉ sector M`: both sides vanish — LHS because every term in
  the `mulVec` sum is zero (either the embedding is zero outside the
  sector, or the Hamiltonian matrix element vanishes between
  configurations of different `magSumS` by `[H, S^z_tot] = 0`); RHS
  because the embedding is zero. -/
theorem heisenbergHamiltonianS_mulVec_magSectorEmbedding
    (J : V → V → ℂ) {M : ℕ}
    (Φ : magConfigS V N M → ℂ)
    {μ : ℝ}
    (hΦ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
      (μ : ℂ) • Φ) :
    (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) =
      (μ : ℂ) • (magSectorEmbedding Φ) := by
  funext σ
  by_cases h : magSumS σ = M
  · -- σ ∈ sector M.
    rw [heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype J Φ ⟨σ, h⟩]
    have hsec := congrFun hΦ ⟨σ, h⟩
    rw [hsec]
    change (μ : ℂ) * Φ ⟨σ, h⟩ = ((μ : ℂ) • magSectorEmbedding Φ) σ
    rw [Pi.smul_apply, magSectorEmbedding_apply_of_mem Φ h, smul_eq_mul]
  · -- σ ∉ sector M. Both sides are zero.
    have hLHS : (heisenbergHamiltonianS J N).mulVec (magSectorEmbedding Φ) σ = 0 := by
      change ∑ ρ, heisenbergHamiltonianS J N σ ρ * magSectorEmbedding Φ ρ = 0
      refine Finset.sum_eq_zero (fun ρ _ => ?_)
      by_cases hρ : magSumS ρ = M
      · -- ρ ∈ sector M, but magSumS σ ≠ M = magSumS ρ ⟹ heis σ ρ = 0.
        have hne : magSumS ρ ≠ magSumS σ :=
          fun heq => h (heq.symm.trans hρ)
        rw [heisenbergHamiltonianS_apply_eq_zero_of_magSumS_ne (V := V) J N hne,
          zero_mul]
      · rw [magSectorEmbedding_apply_of_not_mem Φ hρ, mul_zero]
    rw [hLHS]
    change (0 : ℂ) = ((μ : ℂ) • magSectorEmbedding Φ) σ
    rw [Pi.smul_apply, magSectorEmbedding_apply_of_not_mem Φ h, smul_zero]
/-- **Inverse lift**: a full-Hilbert-space eigenvector of the Heisenberg
Hamiltonian `H` at real eigenvalue `μ`, supported entirely on the
magnetization-`M` sector, restricts to a complex sector eigenvector
of the sector matrix `heisenbergHamiltonianSMatrixOnMagSector` at `μ`.

Proof: pointwise on `τ : magConfigS V N M`. The full mulVec sum
`∑ ρ, H τ.1 ρ * Ψ ρ` reduces to a sector sum since `Ψ` vanishes
outside the sector, then matches the sector matrix mulVec definition
via reindexing. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction
    (J : V → V → ℂ) {M : ℕ}
    {μ : ℝ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ)
    (hΨ_supp : ∀ σ, magSumS σ ≠ M → Ψ σ = 0) :
    (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
      (magSectorRestriction (M := M) Ψ) =
      (μ : ℂ) • magSectorRestriction (M := M) Ψ := by
  funext τ
  -- Goal: (heis_sec).mulVec (restrict Ψ) τ = μ • restrict Ψ τ.
  change (∑ τ', heisenbergHamiltonianSMatrixOnMagSector J N M τ τ' * Ψ τ'.1) =
    ((μ : ℂ) • magSectorRestriction (M := M) Ψ) τ
  have hrhs : ((μ : ℂ) • magSectorRestriction (M := M) Ψ) τ = (μ : ℂ) * Ψ τ.1 := rfl
  rw [hrhs]
  -- Convert sector sum to filter sum on V → Fin (N+1).
  have hsec : (∑ τ' : magConfigS V N M,
      heisenbergHamiltonianSMatrixOnMagSector J N M τ τ' * Ψ τ'.1) =
    ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
      (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ := by
    rw [Finset.sum_subtype (Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M))
      (p := fun ρ => magSumS ρ = M)
      (fun ρ => by simp [Finset.mem_filter])
      (fun ρ => (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ)]
    rfl
  rw [hsec]
  -- Extend filter sum to full sum (added terms are zero by hΨ_supp).
  have hfull : ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
      (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ =
    ∑ ρ : V → Fin (N + 1), (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ := by
    refine Finset.sum_filter_of_ne (p := fun ρ => magSumS ρ = M) ?_
    intro ρ _ hne
    by_contra h
    apply hne
    rw [hΨ_supp ρ h, mul_zero]
  rw [hfull]
  -- This is (H · Ψ) τ.1 = (μ • Ψ) τ.1.
  change (heisenbergHamiltonianS J N).mulVec Ψ τ.1 = _
  rw [hΨ]
  rfl

/-- **Sector restriction of a full eigenvector**: because the spin-`S`
Heisenberg Hamiltonian preserves `magSumS`, restricting any full-space
eigenvector to the magnetization-`M` sector gives an eigenvector of the
sector matrix at the same eigenvalue.

Unlike `heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction`,
this version does not require the full vector to be supported on one
sector; the off-sector terms vanish by the magnetization-conservation
matrix-entry lemma. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
    (J : V → V → ℂ) {M : ℕ}
    {μ : ℝ} {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ) :
    (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
      (magSectorRestriction (M := M) Ψ) =
      (μ : ℂ) • magSectorRestriction (M := M) Ψ := by
  funext τ
  change (∑ τ', heisenbergHamiltonianSMatrixOnMagSector J N M τ τ' * Ψ τ'.1) =
    ((μ : ℂ) • magSectorRestriction (M := M) Ψ) τ
  have hrhs : ((μ : ℂ) • magSectorRestriction (M := M) Ψ) τ = (μ : ℂ) * Ψ τ.1 := rfl
  rw [hrhs]
  have hsec : (∑ τ' : magConfigS V N M,
      heisenbergHamiltonianSMatrixOnMagSector J N M τ τ' * Ψ τ'.1) =
    ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
      (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ := by
    rw [Finset.sum_subtype (Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M))
      (p := fun ρ => magSumS ρ = M)
      (fun ρ => by simp [Finset.mem_filter])
      (fun ρ => (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ)]
    rfl
  rw [hsec]
  have hfull : ∑ ρ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
      (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ =
    ∑ ρ : V → Fin (N + 1), (heisenbergHamiltonianS J N) τ.1 ρ * Ψ ρ := by
    refine Finset.sum_filter_of_ne (p := fun ρ => magSumS ρ = M) ?_
    intro ρ _ hne
    by_contra hρM
    apply hne
    have hmag_ne : magSumS ρ ≠ magSumS τ.1 := fun hEq => hρM (hEq.trans τ.2)
    rw [heisenbergHamiltonianS_apply_eq_zero_of_magSumS_ne (V := V) J N hmag_ne,
      zero_mul]
  rw [hfull]
  change (heisenbergHamiltonianS J N).mulVec Ψ τ.1 = _
  rw [hΨ]
  rfl

end

end LatticeSystem.Quantum
