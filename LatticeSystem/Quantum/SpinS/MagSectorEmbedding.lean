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
