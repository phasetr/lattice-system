import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector

/-!
# Magnetization-sector embedding for spin-`S` configuration vectors
(Tasaki §2.5 Phase B-γ — full ↔ sector bridge)

The sector subtype `magConfigS V N M := { σ : V → Fin (N + 1) // magSumS σ = M }`
is the natural index type for the magnetization-`M` sector of the
Heisenberg Hamiltonian (since `[H, S^z_tot] = 0` makes the Hamiltonian
sector-preserving). To lift sector-level statements (e.g. the ground-
state eigenvector of `heisenbergHamiltonianSMatrixOnMagSector`) to
the full Hilbert space `(V → Fin (N + 1)) → ℂ`, we need the embedding
of sector vectors into full vectors by zero-extension outside the
sector, and its inverse — the restriction of full vectors to the sector.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] {N : ℕ}

/-- Embed a sector vector `Φ : magConfigS V N M → ℂ` into the full
configuration space by zero-extension outside the sector. -/
noncomputable def magSectorEmbedding {M : ℕ}
    (Φ : magConfigS V N M → ℂ) :
    (V → Fin (N + 1)) → ℂ := fun σ =>
  if h : magSumS σ = M then Φ ⟨σ, h⟩ else 0

/-- On a configuration `σ` in the magnetization-`M` sector, the
embedded vector agrees with the sector vector. -/
theorem magSectorEmbedding_apply_of_mem {M : ℕ}
    (Φ : magConfigS V N M → ℂ)
    {σ : V → Fin (N + 1)} (h : magSumS σ = M) :
    magSectorEmbedding Φ σ = Φ ⟨σ, h⟩ := by
  unfold magSectorEmbedding
  rw [dif_pos h]

/-- Outside the magnetization-`M` sector, the embedded vector is zero. -/
theorem magSectorEmbedding_apply_of_not_mem {M : ℕ}
    (Φ : magConfigS V N M → ℂ)
    {σ : V → Fin (N + 1)} (h : magSumS σ ≠ M) :
    magSectorEmbedding Φ σ = 0 := by
  unfold magSectorEmbedding
  rw [dif_neg h]

/-- On a sector configuration `τ : magConfigS V N M`, the embedded
vector at `τ.1` recovers `Φ τ`. -/
theorem magSectorEmbedding_apply_subtype {M : ℕ}
    (Φ : magConfigS V N M → ℂ)
    (τ : magConfigS V N M) :
    magSectorEmbedding Φ τ.1 = Φ τ := by
  rw [magSectorEmbedding_apply_of_mem Φ τ.2]
  congr

/-- Restrict a full vector `f : (V → Fin (N + 1)) → ℂ` to the
magnetization-`M` sector. -/
def magSectorRestriction {M : ℕ}
    (f : (V → Fin (N + 1)) → ℂ) :
    magConfigS V N M → ℂ := fun τ => f τ.1

/-- Restriction-then-embedding agrees with the original vector on the
sector. -/
theorem magSectorEmbedding_magSectorRestriction_apply_of_mem {M : ℕ}
    (f : (V → Fin (N + 1)) → ℂ)
    {σ : V → Fin (N + 1)} (h : magSumS σ = M) :
    magSectorEmbedding (magSectorRestriction (M := M) f) σ = f σ := by
  rw [magSectorEmbedding_apply_of_mem _ h]
  rfl

/-- Embedding-then-restriction is the identity on sector vectors. -/
theorem magSectorRestriction_magSectorEmbedding {M : ℕ}
    (Φ : magConfigS V N M → ℂ) :
    magSectorRestriction (magSectorEmbedding Φ) = Φ := by
  funext τ
  exact magSectorEmbedding_apply_subtype Φ τ

/-! ## Heisenberg matrix element vanishes between different sectors -/

section
variable [DecidableEq V]

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

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), full-Hilbert-
space ground-state existence**: the un-dressed quantum Heisenberg
Hamiltonian on the full multi-spin Hilbert space `(V → Fin (N+1)) → ℂ`
admits a strictly non-zero eigenvector `Ψ : (V → Fin (N+1)) → ℂ` at
some real eigenvalue `μ < c`, supported entirely on the magnetization-
`M` sector and with the Marshall sign structure

  `Ψ σ = ((sign A σ.1).re * v σ : ℂ)` for `σ ∈ sector M`,
  `Ψ σ = 0` for `σ ∉ sector M`,

with `v > 0` componentwise on the sector.

Composition of:
- `exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector`
  (PR #860, complex sector existence).
- `heisenbergHamiltonianS_mulVec_magSectorEmbedding`
  (this PR, sector → full lift).

This is the COMPLEX-Hilbert-space form of Tasaki §2.5 Theorem 2.2 on
the actual quantum Heisenberg Hamiltonian, lifted from the sector
form (PRs #847–#865). -/
theorem exists_marshallSign_eigenvector_heisenbergHamiltonianS_full
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [DecidableEq V]
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector
      (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianS_mulVec_magSectorEmbedding J _ hmul⟩

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

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), full-Hilbert-
space form, BUNDLED**: bundles existence (lift of #860 via #869) with
uniqueness (sector restriction + #862) into the textbook statement of
the §2.5 ground state on the actual quantum Heisenberg Hamiltonian.

  ∃ μ < c, ∃ v > 0,
    let Ψ_GS := magSectorEmbedding (sign · v as ℂ)
    H · Ψ_GS = μ • Ψ_GS ∧
    Ψ_GS supported on sector M ∧
    ∀ {μ'} {Ψ'}, H · Ψ' = μ' • Ψ' → Ψ' supported on sector M →
      Ψ' Marshall-positive on sector M →
      μ' = μ ∧ ∃ r > 0, ∀ τ : sector M, (Ψ' τ.1).re = r * ((sign A τ.1).re * v τ)

This is the COMPLEX-Hilbert-space form of Tasaki §2.5 Theorem 2.2 on
the actual quantum Heisenberg Hamiltonian, lifted from the magnetization
sector form (PRs #847–#865). -/
theorem marshallLiebMattis_spinS_heisenbergHamiltonianS_groundState_full
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [DecidableEq V]
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
      (∀ σ, magSumS σ ≠ M →
        magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ = 0) ∧
      (∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        (∀ σ, magSumS σ ≠ M → Ψ' σ = 0) →
        (∀ τ : magConfigS V N M, 0 < (marshallSignS A τ.1).re * (Ψ' τ.1).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ τ : magConfigS V N M,
            (Ψ' τ.1).re = r * ((marshallSignS A τ.1).re * v τ)) := by
  -- Existence half (combining sector existence + lift).
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianS_full
      (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  refine ⟨μ, v, hμ, hv_pos, hmul, ?_, ?_⟩
  · -- Support: magSectorEmbedding is zero outside the sector by definition.
    intro σ hne
    exact magSectorEmbedding_apply_of_not_mem _ hne
  · -- Uniqueness: restrict to sector + apply complex sector uniqueness.
    intro μ' Ψ' hΨ' hΨ'_supp hΨ'_marshall_pos
    -- Restriction is a complex sector eigenvector at μ'.
    have hΨ'_sec :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction
        J hΨ' hΨ'_supp
    -- The sector ground state Φ_GS := sign · v as ℂ is the embedded eigenvec.
    have hsec_ground :
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) =
          (μ : ℂ) • (fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) := by
      -- This is exactly what `exists_marshallSign_complexEigenvector...` gave us.
      have := exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector
        (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        h_intermediate
      -- We need to show that the SAME (μ, v) witnesses also satisfy the sector
      -- equation. Re-derive by undoing the lift.
      -- Strategy: the lift of `hsec` is `hmul`; restrict back via injectivity.
      funext τ
      -- Use heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype:
      -- (heis_sec * Φ) τ = (heis * embed Φ) τ.1.
      change (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
          (fun τ' : magConfigS V N M =>
            (((marshallSignS A τ'.1).re * v τ' : ℝ) : ℂ)) τ =
        (μ : ℂ) * (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
      rw [← heisenbergHamiltonianS_mulVec_magSectorEmbedding_apply_subtype J _ τ]
      -- Now LHS = (heis * embed Φ) τ.1 = (μ • embed Φ) τ.1 = μ * (embed Φ) τ.1.
      have hμembed := congrFun hmul τ.1
      rw [hμembed]
      change ((μ : ℂ) • magSectorEmbedding _) τ.1 =
        (μ : ℂ) * (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
      rw [Pi.smul_apply, magSectorEmbedding_apply_subtype, smul_eq_mul]
    -- Apply complex sector uniqueness (#862).
    obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
      marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector
        A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
        h_intermediate hsec_ground (by
          intro τ
          change 0 < (marshallSignS A τ.1).re *
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ).re
          rw [Complex.ofReal_re]
          have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
            marshallSignS_re_sq A τ.1
          rw [← mul_assoc, hsq, one_mul]
          exact hv_pos τ)
        hΨ'_sec hΨ'_marshall_pos
    -- hμ_eq : μ = μ', want μ' = μ.
    refine ⟨hμ_eq.symm, r, hr_pos, fun τ => ?_⟩
    -- hrel τ : (magSectorRestriction Ψ' τ).re = r * (embed-Φ τ.1).re
    --        = r * (sign τ.1.re * v τ) (after Complex.ofReal_re).
    -- magSectorRestriction Ψ' τ = Ψ' τ.1 by definition.
    have hτ := hrel τ
    change (magSectorRestriction Ψ' τ).re = r * ((marshallSignS A τ.1).re * v τ)
    rw [hτ]
    rw [Complex.ofReal_re]

end

end LatticeSystem.Quantum
