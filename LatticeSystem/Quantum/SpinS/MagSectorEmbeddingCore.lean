import LatticeSystem.Quantum.SpinS.MagConfig
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique

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

/-! ## Linearity of `magSectorEmbedding` and `magSectorRestriction` -/

/-- The embedding sends the zero vector to the zero vector. -/
theorem magSectorEmbedding_zero {M : ℕ} :
    magSectorEmbedding (0 : magConfigS V N M → ℂ) = 0 := by
  funext σ
  unfold magSectorEmbedding
  by_cases h : magSumS σ = M
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]; rfl

/-- The embedding distributes over addition. -/
theorem magSectorEmbedding_add {M : ℕ}
    (Φ Ψ : magConfigS V N M → ℂ) :
    magSectorEmbedding (Φ + Ψ) = magSectorEmbedding Φ + magSectorEmbedding Ψ := by
  funext σ
  change magSectorEmbedding (Φ + Ψ) σ = magSectorEmbedding Φ σ + magSectorEmbedding Ψ σ
  by_cases h : magSumS σ = M
  · rw [magSectorEmbedding_apply_of_mem _ h,
      magSectorEmbedding_apply_of_mem Φ h,
      magSectorEmbedding_apply_of_mem Ψ h]
    rfl
  · rw [magSectorEmbedding_apply_of_not_mem _ h,
      magSectorEmbedding_apply_of_not_mem Φ h,
      magSectorEmbedding_apply_of_not_mem Ψ h, add_zero]

/-- The embedding commutes with complex scalar multiplication. -/
theorem magSectorEmbedding_smul {M : ℕ}
    (c : ℂ) (Φ : magConfigS V N M → ℂ) :
    magSectorEmbedding (c • Φ) = c • magSectorEmbedding Φ := by
  funext σ
  change magSectorEmbedding (c • Φ) σ = c • magSectorEmbedding Φ σ
  by_cases h : magSumS σ = M
  · rw [magSectorEmbedding_apply_of_mem _ h,
      magSectorEmbedding_apply_of_mem Φ h]
    rfl
  · rw [magSectorEmbedding_apply_of_not_mem _ h,
      magSectorEmbedding_apply_of_not_mem Φ h, smul_zero]

/-- The restriction sends the zero vector to the zero vector. -/
theorem magSectorRestriction_zero {M : ℕ} :
    magSectorRestriction (M := M) (V := V) (N := N) 0 = 0 := by
  funext _
  rfl

/-- The restriction distributes over addition. -/
theorem magSectorRestriction_add {M : ℕ}
    (f g : (V → Fin (N + 1)) → ℂ) :
    magSectorRestriction (M := M) (f + g) =
      magSectorRestriction f + magSectorRestriction g := by
  funext _
  rfl

/-- The restriction commutes with complex scalar multiplication. -/
theorem magSectorRestriction_smul {M : ℕ}
    (c : ℂ) (f : (V → Fin (N + 1)) → ℂ) :
    magSectorRestriction (M := M) (c • f) = c • magSectorRestriction f := by
  funext _
  rfl

/-- **`magSectorEmbedding` as a linear map** (`ℂ`-linear). -/
noncomputable def magSectorEmbeddingLinearMap (M : ℕ) :
    (magConfigS V N M → ℂ) →ₗ[ℂ] ((V → Fin (N + 1)) → ℂ) where
  toFun := magSectorEmbedding
  map_add' := magSectorEmbedding_add
  map_smul' := magSectorEmbedding_smul

/-- **`magSectorRestriction` as a linear map** (`ℂ`-linear). -/
def magSectorRestrictionLinearMap (M : ℕ) :
    ((V → Fin (N + 1)) → ℂ) →ₗ[ℂ] (magConfigS V N M → ℂ) where
  toFun := magSectorRestriction
  map_add' := magSectorRestriction_add
  map_smul' := magSectorRestriction_smul

/-- The composition `restriction ∘ embedding = id` as a linear-map
identity (lifts the round-trip `magSectorRestriction_magSectorEmbedding`). -/
theorem magSectorRestrictionLinearMap_comp_magSectorEmbeddingLinearMap (M : ℕ) :
    (magSectorRestrictionLinearMap (V := V) (N := N) M).comp
      (magSectorEmbeddingLinearMap M) = LinearMap.id := by
  ext Φ τ
  exact congrFun (magSectorRestriction_magSectorEmbedding Φ) τ

/-! ## Characterisation of the image of `magSectorEmbedding`

A full-Hilbert-space vector lies in the image of the magnetization-`M`
sector embedding iff it is supported on the sector `M`. Together with
the round-trip identity (`magSectorRestriction_magSectorEmbedding`),
this gives a clean characterisation of the magnetization-`M` subspace
of the full space.
-/

/-- Sufficient condition for membership in the image of
`magSectorEmbedding`: a vector `f : (V → Fin (N+1)) → ℂ` supported
entirely on the magnetization-`M` sector equals the embedding of its
restriction. -/
theorem magSectorEmbedding_magSectorRestriction_of_supported {M : ℕ}
    {f : (V → Fin (N + 1)) → ℂ}
    (hf : ∀ σ, magSumS σ ≠ M → f σ = 0) :
    magSectorEmbedding (magSectorRestriction (M := M) f) = f := by
  funext σ
  by_cases h : magSumS σ = M
  · exact magSectorEmbedding_magSectorRestriction_apply_of_mem f h
  · rw [magSectorEmbedding_apply_of_not_mem _ h, hf σ h]

/-- **Image characterisation**: a vector `f` is in the image of
`magSectorEmbedding (M := M)` iff `f` is supported on the
magnetization-`M` sector. -/
theorem mem_range_magSectorEmbedding_iff_supported {M : ℕ}
    (f : (V → Fin (N + 1)) → ℂ) :
    (∃ Φ : magConfigS V N M → ℂ, magSectorEmbedding Φ = f) ↔
      (∀ σ, magSumS σ ≠ M → f σ = 0) := by
  constructor
  · rintro ⟨Φ, rfl⟩ σ h
    exact magSectorEmbedding_apply_of_not_mem Φ h
  · intro hf
    exact ⟨magSectorRestriction f,
      magSectorEmbedding_magSectorRestriction_of_supported hf⟩

/-! ## Kernel of `magSectorRestriction` -/

/-- **Kernel characterisation**: `magSectorRestriction (M := M) f = 0`
iff `f` vanishes on the magnetization-`M` sector. -/
theorem magSectorRestriction_eq_zero_iff_vanishes {M : ℕ}
    (f : (V → Fin (N + 1)) → ℂ) :
    magSectorRestriction (M := M) f = 0 ↔
      (∀ σ, magSumS σ = M → f σ = 0) := by
  constructor
  · intro h σ hσ
    have := congrFun h ⟨σ, hσ⟩
    exact this
  · intro hf
    funext τ
    exact hf τ.1 τ.2

/-! ## Sector disjointness and finite-sum decomposition

Different magnetization sectors are *disjoint* in the full configuration
space: a vector that is simultaneously in the image of
`magSectorEmbedding (M := M₁)` and `magSectorEmbedding (M := M₂)` for
`M₁ ≠ M₂` must be zero. Combined with the fact that every full vector
decomposes as a finite sum of its sector-supported components, this
gives the basic ingredients of the magnetization-sector decomposition

  $\quad\;f \;=\; \sum_{M=0}^{|V|\cdot N}
      \mathrm{magSectorEmbedding}\bigl(\mathrm{magSectorRestriction}_{M}\,f\bigr)
    \quad\text{for every }f.$

(Lifting this to a formal internal `DirectSum` / `Submodule.IsInternal`
statement is a separate downstream packaging step and is not done here.)
-/

/-- **Sector disjointness**: a vector simultaneously supported on
sectors `M₁` and `M₂` (with `M₁ ≠ M₂`) is identically zero. -/
theorem eq_zero_of_supported_on_two_sectors {M₁ M₂ : ℕ}
    (hM : M₁ ≠ M₂)
    {f : (V → Fin (N + 1)) → ℂ}
    (h₁ : ∀ σ, magSumS σ ≠ M₁ → f σ = 0)
    (h₂ : ∀ σ, magSumS σ ≠ M₂ → f σ = 0) :
    f = 0 := by
  funext σ
  rcases eq_or_ne (magSumS σ) M₁ with hσ₁ | hσ₁
  · -- magSumS σ = M₁ ≠ M₂, so apply h₂ at σ.
    have hσ₂ : magSumS σ ≠ M₂ := hσ₁ ▸ hM
    exact h₂ σ hσ₂
  · exact h₁ σ hσ₁

/-- The intersection of the images of two distinct sector embeddings is
trivial: if `magSectorEmbedding Φ₁ = magSectorEmbedding Φ₂` for
sectors `M₁ ≠ M₂`, then both `Φ₁ = 0` and `Φ₂ = 0`. -/
theorem eq_zero_of_magSectorEmbedding_eq_of_ne {M₁ M₂ : ℕ}
    (hM : M₁ ≠ M₂)
    (Φ₁ : magConfigS V N M₁ → ℂ) (Φ₂ : magConfigS V N M₂ → ℂ)
    (hΦ : magSectorEmbedding Φ₁ = magSectorEmbedding Φ₂) :
    Φ₁ = 0 ∧ Φ₂ = 0 := by
  refine ⟨?_, ?_⟩
  · funext τ
    -- τ : magConfigS V N M₁; magSumS τ.1 = M₁ ≠ M₂.
    have h₁ : magSectorEmbedding Φ₁ τ.1 = Φ₁ τ :=
      magSectorEmbedding_apply_subtype Φ₁ τ
    have h₂ : magSectorEmbedding Φ₂ τ.1 = 0 := by
      apply magSectorEmbedding_apply_of_not_mem
      rw [τ.2]
      exact hM
    have := congrFun hΦ τ.1
    rw [h₁, h₂] at this
    exact this
  · funext τ
    have h₁ : magSectorEmbedding Φ₁ τ.1 = 0 := by
      apply magSectorEmbedding_apply_of_not_mem
      rw [τ.2]
      exact Ne.symm hM
    have h₂ : magSectorEmbedding Φ₂ τ.1 = Φ₂ τ :=
      magSectorEmbedding_apply_subtype Φ₂ τ
    have := congrFun hΦ τ.1
    rw [h₁, h₂] at this
    exact this.symm

/-! ## Decomposition of any full vector via the sector-supported parts

For any full vector `f`, we can build for each `M` the "sector-`M`
slice" `f_M : (V → Fin (N+1)) → ℂ` defined as `f_M σ := if magSumS σ = M then f σ else 0`,
which is supported on sector `M` and equals
`magSectorEmbedding (magSectorRestriction (M := M) f)`. The
finite sum over `M : Fin (|V| · N + 1)` of these slices equals `f`,
giving the magnetization-sector decomposition. -/

/-- The "sector-`M` slice" of a full vector `f`: agrees with `f` on
sector `M`, zero elsewhere. -/
def magSectorSlice (M : ℕ)
    (f : (V → Fin (N + 1)) → ℂ) :
    (V → Fin (N + 1)) → ℂ := fun σ =>
  if magSumS σ = M then f σ else 0

/-- The sector slice equals `f` on the sector. -/
theorem magSectorSlice_apply_of_mem (M : ℕ)
    (f : (V → Fin (N + 1)) → ℂ)
    {σ : V → Fin (N + 1)} (h : magSumS σ = M) :
    magSectorSlice M f σ = f σ := by
  unfold magSectorSlice
  rw [if_pos h]

/-- The sector slice vanishes outside the sector. -/
theorem magSectorSlice_apply_of_not_mem (M : ℕ)
    (f : (V → Fin (N + 1)) → ℂ)
    {σ : V → Fin (N + 1)} (h : magSumS σ ≠ M) :
    magSectorSlice M f σ = 0 := by
  unfold magSectorSlice
  rw [if_neg h]

/-- The sector slice is supported on the sector. -/
theorem magSectorSlice_supported (M : ℕ)
    (f : (V → Fin (N + 1)) → ℂ) :
    ∀ σ, magSumS σ ≠ M → magSectorSlice M f σ = 0 :=
  fun _ h => magSectorSlice_apply_of_not_mem M f h

/-- The sector slice equals the embedding of the sector restriction. -/
theorem magSectorSlice_eq_magSectorEmbedding (M : ℕ)
    (f : (V → Fin (N + 1)) → ℂ) :
    magSectorSlice M f =
      magSectorEmbedding (magSectorRestriction (M := M) f) := by
  funext σ
  by_cases h : magSumS σ = M
  · rw [magSectorSlice_apply_of_mem M f h,
      magSectorEmbedding_apply_of_mem _ h]
    rfl
  · rw [magSectorSlice_apply_of_not_mem M f h,
      magSectorEmbedding_apply_of_not_mem _ h]

/-- **Magnetization-sector decomposition** of a full vector `f`: for
any `f : (V → Fin (N+1)) → ℂ`, summing the sector slices over all
attainable magnetization values `M ∈ {0, 1, …, |V| · N}` recovers `f`. -/
theorem sum_magSectorSlice_eq (f : (V → Fin (N + 1)) → ℂ) :
    (∑ M ∈ Finset.range (Fintype.card V * N + 1),
      magSectorSlice M f) = f := by
  funext σ
  rw [Finset.sum_apply]
  -- ∑ M ∈ range, (slice M f) σ. Only the M = magSumS σ term is non-zero.
  have hσ_le : magSumS σ ∈ Finset.range (Fintype.card V * N + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (magSumS_le σ)
  rw [Finset.sum_eq_single (magSumS σ)
    (fun M _ hMne => magSectorSlice_apply_of_not_mem M f (Ne.symm hMne))
    (fun h => absurd hσ_le h)]
  exact magSectorSlice_apply_of_mem (magSumS σ) f rfl

/-- **Magnetization-sector decomposition (LinearMap-image form)**:
every full vector `f` equals the finite sum of sector-embedded
restrictions, one per attainable magnetization. -/
theorem eq_sum_magSectorEmbedding_magSectorRestriction
    (f : (V → Fin (N + 1)) → ℂ) :
    f = ∑ M ∈ Finset.range (Fintype.card V * N + 1),
      magSectorEmbedding (magSectorRestriction (M := M) f) := by
  have h := sum_magSectorSlice_eq f
  rw [Finset.sum_congr rfl (fun M _ => magSectorSlice_eq_magSectorEmbedding M f)] at h
  exact h.symm


end LatticeSystem.Quantum
