import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandOccBasis

/-!
# The spectral eigenbasis as a single-particle basis (Tasaki §11.3.4, toward eq. (11.3.46))

For a Hermitian hopping matrix `T`, the orthonormal eigenbasis `T.IsHermitian.eigenvectorBasis`
(on `EuclideanSpace ℂ (Fin (M+1))`) transports to a `Module.Basis` of the plain coordinate space
`Fin (M+1) → ℂ`, on which the general occupation basis (`GeneralFlatBandOccBasis.lean`) is built.
Its orthonormality yields the **dual canonical anticommutation relation**
`{Ĉ_σ(ē_j), Ĉ†_τ(e_k)} = δ_{jk}δ_{στ}·1`, the exact occupation-detection algebra used to peel a flat
band ground state into its zero-eigenvalue (flat-band) modes (eq. (11.3.46)).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.46).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- The orthonormal eigenbasis of a Hermitian `T`, transported from `EuclideanSpace ℂ (Fin (M+1))`
to a `Module.Basis` of the plain coordinate space `Fin (M+1) → ℂ`. -/
noncomputable def eigenbasisAsBasis {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) :
    Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ) :=
  hT.eigenvectorBasis.toBasis.map (WithLp.linearEquiv 2 ℂ (Fin (M + 1) → ℂ))

/-- The `i`-th transported basis vector is the underlying coordinate function of the `i`-th
eigenvector. -/
theorem eigenbasisAsBasis_apply {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    (i : Fin (M + 1)) :
    (eigenbasisAsBasis hT i : Fin (M + 1) → ℂ)
      = (⇑(hT.eigenvectorBasis i) : Fin (M + 1) → ℂ) := by
  rw [eigenbasisAsBasis, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis]
  rfl

/-- **Orthonormality of the eigenbasis, in coordinate form**:
`∑_x conj(e_j(x))·e_k(x) = δ_{jk}`. -/
theorem eigenbasisAsBasis_orthonormal_sum
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j k : Fin (M + 1)) :
    (∑ x : Fin (M + 1),
        star ((eigenbasisAsBasis hT j : Fin (M + 1) → ℂ) x)
          * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) x)
      = if j = k then (1 : ℂ) else 0 := by
  have ho := hT.eigenvectorBasis.orthonormal
  rw [orthonormal_iff_ite] at ho
  have hjk := ho j k
  rw [PiLp.inner_apply] at hjk
  rw [← hjk]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.inner_apply]
  simp only [starRingEnd_apply, eigenbasisAsBasis_apply]
  ring

/-- **The dual canonical anticommutation relation in the eigenbasis**:
`{Ĉ_σ(ē_j), Ĉ†_τ(e_k)} = δ_{jk}·δ_{στ}·1`.  The smeared CAR
(`spinfulFromVector_annihilation_creation_anticomm`) gives the coefficient
`∑_x conj(e_j(x))·e_k(x)`, which the orthonormality collapses to `δ_{jk}`.  This is the exact
occupation-detection algebra for the eq. (11.3.46) Fock-spanning step. -/
theorem eigenbasis_dual_annihilation_creation_anticomm
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian) (j k : Fin (M + 1))
    (σ τ : Fin 2) :
    spinfulAnnihilationFromVector M (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ
        * spinfulCreationFromVector M (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) τ
      + spinfulCreationFromVector M (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) τ
        * spinfulAnnihilationFromVector M (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) σ
      = (if j = k ∧ σ = τ then (1 : ℂ) else 0) • (1 : ManyBodyOp (Fin (2 * M + 2))) := by
  rw [spinfulFromVector_annihilation_creation_anticomm M
        (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) (eigenbasisAsBasis hT k) σ τ]
  by_cases hστ : σ = τ
  · subst hστ
    have hsum : (∑ x : Fin (M + 1),
        (star (eigenbasisAsBasis hT j : Fin (M + 1) → ℂ)) x
          * (eigenbasisAsBasis hT k : Fin (M + 1) → ℂ) x)
        = if j = k then (1 : ℂ) else 0 := by
      simpa only [Pi.star_apply] using eigenbasisAsBasis_orthonormal_sum hT j k
    rw [if_pos rfl, hsum]
    by_cases hjk : j = k <;> simp [hjk]
  · rw [if_neg hστ]
    have : ¬ (j = k ∧ σ = τ) := fun h => hστ h.2
    rw [if_neg this]
end LatticeSystem.Fermion
