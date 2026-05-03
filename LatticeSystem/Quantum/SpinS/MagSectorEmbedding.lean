import LatticeSystem.Quantum.SpinS.MagConfig

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

end LatticeSystem.Quantum
