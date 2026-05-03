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

end

end LatticeSystem.Quantum
