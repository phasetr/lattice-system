import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUTrial
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardFerromagnetismStructure
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralBasisHN
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinSymmetryAux
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SiteProjectionsIdempotent
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandPosSemidef
import LatticeSystem.Quantum.SpinS.HermitianVariationalLowerBound
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.RayleighOnEigenvector
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import LatticeSystem.Math.ComplexVectorKernel

/-!
# Hubbard low-`U` impossibility (variational lower bound): foundation

Foundational layer extracted from `HubbardImpossibilityLowUVariational.lean` for build
speed (Tasaki §11.4 / flat-band Hubbard variational impossibility).  This file develops
the **predicate/support-based configuration-sector compression** (`configSector*`), the
number-sector instance built on it, the total down-number operator on eigenmode Slater
determinants, and the interaction bound by the total down number
(`fermionTotalDownNumber_sub_onSiteInteraction_posSemidef`,
`hubbardOnSiteInteraction_rayleigh_bounds`).

The compression machinery is generic in a decidable configuration predicate `P`: the sector is
`configSector N P = {c // P c}`, completeness is stated in **support** form (a vector supported on
`P` equals its sector expansion), and the eigenvector lift only requires that the operator keeps its
expansion `P`-supported.  Both the number sector (`P c := Σ_j c_j = Ne`) and the per-spin balanced
sector (`P c := Σ_i c_{i↑} = k ∧ Σ_i c_{i↓} = k`) are instances; no compression machinery is
duplicated across the two.

The non-vanishing of the eigenmode Slater state and the trial-state Rayleigh quotient
are kept in the capstone module `HubbardImpossibilityLowUVariational.lean`.

## Main results

* `configSector`, `configSectorEmbedding`, `configSectorExpansion`, `configSectorCoeff` — the
  generic sector basis, embedding `T`, expansion `T·`, and coefficient functional `Tᴴ·`.
* `configSector_completeness` — a `P`-supported vector equals its sector expansion `T (Tᴴ u)`.
* `configSectorCompress`, `configSectorCompress_isHermitian`, `rayleighOnVec_configSectorCompress`
  — the compression `Tᴴ A T`, its Hermiticity, and the Rayleigh bridge.
* `configSectorExpansion_of_compress_eigen` — the eigenvector lift: if `A` keeps `T c` supported on
  `P` and `c` is a compression eigenvector at `E`, then the lift is an `A`-eigenvector at `E`.
* `hubbardSectorConfig`, `hubbardSector_minEnergy_eigenspace_ne_bot`,
  `hubbardSector_minEnergy_mul_le_rayleighOnVec` — the number-sector instance (`P = Σ_j c_j = Ne`).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped ComplexOrder

variable {N : ℕ}


/-! ## The fixed-configuration sector basis (predicate/support-based) -/

/-- **A configuration sector** for a decidable predicate `P` on Fock configurations
`c : Fin (2N+2) → Fin 2`: the subtype `{c // P c}`.  Its computational basis vectors `|c⟩` (over the
`c` satisfying `P`) form an orthonormal basis of the `P`-supported subspace. -/
abbrev configSector (N : ℕ) (P : (Fin (2 * N + 2) → Fin 2) → Prop) :=
  {c : Fin (2 * N + 2) → Fin 2 // P c}

/-- **The number-sector predicate**: a Fock configuration `c` has total occupation `Ne`. -/
abbrev hubbardNumberSectorPred (N Ne : ℕ) : (Fin (2 * N + 2) → Fin 2) → Prop :=
  fun c => (∑ j : Fin (2 * N + 2), (c j).val) = Ne

/-- **The `Ne`-electron configuration sector**: computational configurations
`c : Fin (2N+2) → Fin 2` with total occupation `Σ_j c_j = Ne`.  Orthonormal basis of `W`. -/
abbrev hubbardSectorConfig (N Ne : ℕ) := configSector N (hubbardNumberSectorPred N Ne)

/-- **The sector embedding** `T : (sector-coords) → (Fock)`: its column at the configuration `c` is
the computational basis vector `|c⟩`. -/
noncomputable def configSectorEmbedding (N : ℕ) (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] :
    Matrix (Fin (2 * N + 2) → Fin 2) (configSector N P) ℂ :=
  Matrix.of (fun w s => basisVec s.val w)

/-- **The sector expansion** `Φ = Σ_c v_c |c⟩` over the `P`-sector basis. -/
noncomputable def configSectorExpansion (N : ℕ) (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] (v : configSector N P → ℂ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  ∑ s, v s • basisVec s.val

/-- **The sector coefficient functional** `(Tᴴ u)_c = ⟨c, u⟩ = Σ_w |c⟩(w) · u(w)`. -/
noncomputable def configSectorCoeff (N : ℕ) (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] (u : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    configSector N P → ℂ :=
  fun s => ∑ w, basisVec s.val w * u w

/-- `T` maps a coefficient vector to its sector expansion: `T u = Σ_s u_s |s⟩`. -/
theorem configSectorEmbedding_mulVec (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P]
    (u : configSector N P → ℂ) :
    (configSectorEmbedding N P).mulVec u = configSectorExpansion N P u := by
  funext w
  unfold configSectorEmbedding configSectorExpansion
  rw [Matrix.mulVec, dotProduct, Finset.sum_apply]
  exact Finset.sum_congr rfl (fun s _ => by
    rw [Matrix.of_apply, Pi.smul_apply, smul_eq_mul, mul_comm])

/-- `Tᴴ` maps a Fock vector to its sector coefficient functional: `(Tᴴ v)_s = ⟨s, v⟩`. -/
theorem configSectorEmbedding_conjTranspose_mulVec (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (configSectorEmbedding N P)ᴴ.mulVec v = configSectorCoeff N P v := by
  funext s
  unfold configSectorCoeff
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Matrix.conjTranspose_apply, configSectorEmbedding, Matrix.of_apply,
    show star (basisVec s.val w) = basisVec s.val w from by rw [basisVec_apply]; split <;> simp]

/-- **Completeness of the sector basis.**  A vector `u` supported on the sector (`u w = 0` whenever
`¬ P w`) equals its sector expansion `T (Tᴴ u)`; the sector is spanned by the computational basis
vectors on which such a vector is supported. -/
theorem configSector_completeness (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P]
    (u : (Fin (2 * N + 2) → Fin 2) → ℂ) (hsupp : ∀ w, ¬ P w → u w = 0) :
    u = configSectorExpansion N P (configSectorCoeff N P u) := by
  funext w
  unfold configSectorExpansion configSectorCoeff
  rw [Finset.sum_apply]
  by_cases hw : P w
  · set s₀ : configSector N P := ⟨w, hw⟩ with hs₀
    rw [Finset.sum_eq_single s₀]
    · rw [Pi.smul_apply, smul_eq_mul, hs₀, basisVec_apply, if_pos rfl, mul_one, basisVec_sum_mul]
    · intro s _ hss₀
      rw [Pi.smul_apply, smul_eq_mul, basisVec_apply,
        if_neg (fun h => hss₀ (Subtype.ext (by rw [hs₀]; exact h.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  · rw [hsupp w hw]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    rw [Pi.smul_apply, smul_eq_mul, basisVec_apply,
      if_neg (fun h => hw (by rw [h]; exact s.property)), mul_zero]

/-! ## The sector compression and its Rayleigh bridge -/

/-- **The sector compression** `compress(A) = Tᴴ A T`: the matrix of `A` in the `P`-sector basis. -/
noncomputable def configSectorCompress (N : ℕ) (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] (A : ManyBodyOp (Fin (2 * N + 2))) :
    Matrix (configSector N P) (configSector N P) ℂ :=
  (configSectorEmbedding N P)ᴴ * A * configSectorEmbedding N P

/-- **The sector embedding has orthonormal columns:** `Tᴴ T = 1`. -/
theorem configSectorEmbedding_conjTranspose_mul_self (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] :
    (configSectorEmbedding N P)ᴴ * configSectorEmbedding N P = 1 := by
  ext s s'
  rw [Matrix.mul_apply]
  rw [show (∑ w, (configSectorEmbedding N P)ᴴ s w * configSectorEmbedding N P w s')
      = ∑ w, basisVec s.val w * basisVec s'.val w from by
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Matrix.conjTranspose_apply, configSectorEmbedding, Matrix.of_apply, Matrix.of_apply,
      show star (basisVec s.val w) = basisVec s.val w from by rw [basisVec_apply]; split <;> simp]]
  rw [basisVec_inner, Matrix.one_apply]
  by_cases h : s = s'
  · rw [h, if_pos rfl, if_pos rfl]
  · rw [if_neg (fun hc => h (Subtype.ext hc.symm)), if_neg h]

/-- **The sector embedding is an isometry:** `⟨T c, T c⟩ = ⟨c, c⟩`. -/
theorem configSectorExpansion_dotProduct_self (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] (c : configSector N P → ℂ) :
    dotProduct (star (configSectorExpansion N P c)) (configSectorExpansion N P c) =
      dotProduct (star c) c := by
  rw [← configSectorEmbedding_mulVec,
    star_mulVec_dotProduct (configSectorEmbedding N P) c
      ((configSectorEmbedding N P).mulVec c),
    Matrix.mulVec_mulVec, configSectorEmbedding_conjTranspose_mul_self, Matrix.one_mulVec]

/-- **The Rayleigh bridge.** The operator Rayleigh quotient of `A` on a lifted sector vector equals
the matrix Rayleigh quotient of its compression `A_W = Tᴴ A T`. -/
theorem rayleighOnVec_configSectorCompress (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P]
    (A : ManyBodyOp (Fin (2 * N + 2))) (c : configSector N P → ℂ) :
    rayleighOnVec (configSectorCompress N P A) c =
      rayleighOnVec A (configSectorExpansion N P c) := by
  have hmv : (configSectorCompress N P A).mulVec c
      = (configSectorEmbedding N P)ᴴ.mulVec
          (A.mulVec ((configSectorEmbedding N P).mulVec c)) := by
    unfold configSectorCompress
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have key : dotProduct (star c) ((configSectorCompress N P A).mulVec c)
      = dotProduct (star (configSectorExpansion N P c))
          (A.mulVec (configSectorExpansion N P c)) := by
    rw [hmv, (star_mulVec_dotProduct _ c _).symm, configSectorEmbedding_mulVec]
  unfold rayleighOnVec
  rw [key]

/-- **Hermiticity of the compression.** If `A` is Hermitian, so is its sector compression
`Tᴴ A T`. -/
theorem configSectorCompress_isHermitian (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P]
    {A : ManyBodyOp (Fin (2 * N + 2))} (hA : A.IsHermitian) :
    (configSectorCompress N P A).IsHermitian := by
  unfold configSectorCompress Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, Matrix.mul_assoc]

/-! ## Lifting sector eigenvectors -/

/-- **Projection identity (support form).** `T Tᴴ` acts as the identity on `P`-supported vectors:
`T Tᴴ v = v` whenever `v w = 0` for all `w` with `¬ P w` (resolution of identity over the
orthonormal sector basis). -/
theorem configSectorProjection_mulVec_eq_of_supported (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hsupp : ∀ w, ¬ P w → v w = 0) :
    (configSectorEmbedding N P * (configSectorEmbedding N P)ᴴ).mulVec v = v := by
  rw [← Matrix.mulVec_mulVec, configSectorEmbedding_conjTranspose_mulVec,
    configSectorEmbedding_mulVec]
  exact (configSector_completeness P v hsupp).symm

/-- **Eigenvector lift (support form).** If `A` keeps the lift `T c` supported on `P` and `c` is an
eigenvector of the compression `compress(A)` at `E`, then the lift `configSectorExpansion c` is an
eigenvector of `A` at `E`. -/
theorem configSectorExpansion_of_compress_eigen (P : (Fin (2 * N + 2) → Fin 2) → Prop)
    [DecidablePred P] {A : ManyBodyOp (Fin (2 * N + 2))} {c : configSector N P → ℂ} {E : ℂ}
    (hApres : ∀ w, ¬ P w → A.mulVec (configSectorExpansion N P c) w = 0)
    (hE : (configSectorCompress N P A).mulVec c = E • c) :
    A.mulVec (configSectorExpansion N P c) = E • configSectorExpansion N P c := by
  have hinner : (configSectorEmbedding N P)ᴴ.mulVec
      (A.mulVec ((configSectorEmbedding N P).mulVec c))
        = (configSectorCompress N P A).mulVec c := by
    unfold configSectorCompress
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← configSectorProjection_mulVec_eq_of_supported P hApres, ← configSectorEmbedding_mulVec,
    ← Matrix.mulVec_mulVec, hinner, hE, Matrix.mulVec_smul]

/-- A nonzero sector coefficient vector lifts to a nonzero vector (isometry). -/
theorem configSectorExpansion_ne_zero (P : (Fin (2 * N + 2) → Fin 2) → Prop) [DecidablePred P]
    {c : configSector N P → ℂ} (hc : c ≠ 0) : configSectorExpansion N P c ≠ 0 := by
  intro h
  apply hc
  have hiso := configSectorExpansion_dotProduct_self P c
  rw [h, star_zero, zero_dotProduct] at hiso
  -- `hiso : 0 = Σ_s conj(c s) * c s`; each summand has nonneg real part, so all `c s = 0`.
  funext s
  have hsum : (∑ s', (starRingEnd ℂ) (c s') * c s') = 0 := by
    rw [← hiso.symm]; rfl
  have hnn : ∀ s' ∈ (Finset.univ : Finset (configSector N P)),
      0 ≤ (Complex.normSq (c s') : ℝ) := fun s' _ => Complex.normSq_nonneg _
  have hre : (∑ s', Complex.normSq (c s')) = 0 := by
    have : (∑ s', (starRingEnd ℂ) (c s') * c s') = ((∑ s', Complex.normSq (c s') : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl (fun s' _ => ?_)
      rw [Complex.normSq_eq_conj_mul_self]
    rw [this] at hsum
    exact_mod_cast hsum
  have hzero : Complex.normSq (c s) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hre s (Finset.mem_univ s)
  rw [Pi.zero_apply, ← Complex.normSq_eq_zero]
  exact hzero

/-! ## The number sector `W` as an `N̂`-eigenspace -/

/-- The number sector `W = (N̂ = Ne)`-eigenspace, as a submodule. -/
noncomputable def hubbardSectorWSubmodule (N Ne : ℕ) :
    Submodule ℂ ((Fin (2 * N + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ)

/-- Membership in `W`: an `N̂ = Ne` eigenvector. -/
theorem mem_hubbardSectorWSubmodule_iff (Ne : ℕ) {v : (Fin (2 * N + 2) → Fin 2) → ℂ} :
    v ∈ hubbardSectorWSubmodule N Ne ↔
      (fermionTotalNumber (2 * N + 1)).mulVec v = (Ne : ℂ) • v := by
  rw [hubbardSectorWSubmodule, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]

/-- A sector basis vector `|s⟩` lies in `W` (it is an `N̂ = Ne` eigenstate). -/
theorem basisVec_sector_mem (Ne : ℕ) (s : hubbardSectorConfig N Ne) :
    basisVec s.val ∈ hubbardSectorWSubmodule N Ne := by
  rw [mem_hubbardSectorWSubmodule_iff, fermionTotalNumber_mulVec_basisVec]
  rw [show (∑ j : Fin (2 * N + 2), ((s.val j).val : ℂ)) = (Ne : ℂ) from by
    rw [← Nat.cast_sum]; exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) s.property]

/-- A number-sector expansion lies in `W` (a sum of `W`-members). -/
theorem hubbardSectorExpansion_mem (Ne : ℕ) (v : hubbardSectorConfig N Ne → ℂ) :
    configSectorExpansion N (hubbardNumberSectorPred N Ne) v ∈ hubbardSectorWSubmodule N Ne := by
  unfold configSectorExpansion
  exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _ (basisVec_sector_mem Ne s))

/-- **`B` preserves `W`.** The reusable hypothesis for the number-sector eigenvector lift. -/
def PreservesHubbardSectorW (N Ne : ℕ) (B : ManyBodyOp (Fin (2 * N + 2))) : Prop :=
  ∀ v ∈ hubbardSectorWSubmodule N Ne, B.mulVec v ∈ hubbardSectorWSubmodule N Ne

/-- **`Ĥ` preserves `W`** (charge conservation `[Ĥ, N̂] = 0`). -/
theorem preservesHubbardSectorW_hamiltonian (Ne : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    PreservesHubbardSectorW N Ne (hubbardHamiltonian N t U) := by
  intro v hv
  rw [mem_hubbardSectorWSubmodule_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec,
    ← (hubbardHamiltonian_commute_fermionTotalNumber N t U).eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- The `P`-support of a number-sector member: a `W`-vector vanishes off the `Ne`-shell. -/
theorem hubbardNumberSector_supported_of_mem (Ne : ℕ)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ∈ hubbardSectorWSubmodule N Ne)
    (w : Fin (2 * N + 2) → Fin 2) (hw : ¬ hubbardNumberSectorPred N Ne w) : v w = 0 := by
  rw [mem_hubbardSectorWSubmodule_iff] at hv
  exact mulVec_apply_eq_zero_of_number_ne N v (Ne : ℂ) hv w
    (fun hcast => hw (by exact_mod_cast hcast))

/-! ## The number-sector minimum energy and its eigenspace -/

/-- **The number-sector minimum energy supplies a nonzero `Ne`-electron eigenspace.** For a
Hermitian `hopping`/real-`U` Hubbard model, the compression `Ĥ_W`'s minimum eigenvalue `E_min` is
attained by a genuine `Ĥ`-eigenvector in the `Ne`-electron sector, so the `Ĥ`-eigenspace at `E_min`
intersected with that sector is nonzero. -/
theorem hubbardSector_minEnergy_eigenspace_ne_bot (Ne : ℕ)
    [Nonempty (hubbardSectorConfig N Ne)]
    {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    ∃ E : ℂ, E = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
        (hubbardNumberSectorPred N Ne) (hubbardHamiltonian_isHermitian N ht hU)) : ℝ) : ℂ) ∧
      Module.End.eigenspace (hubbardHamiltonian N t U).mulVecLin E ⊓
        Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ) ≠ ⊥ := by
  classical
  set hHW := configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne)
    (hubbardHamiltonian_isHermitian N ht hU) with hHWd
  obtain ⟨c, hc0, hceig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHW
  set E : ℂ := ((hermitianMinEigenvalue hHW : ℝ) : ℂ) with hE
  refine ⟨E, rfl, ?_⟩
  set Φ := configSectorExpansion N (hubbardNumberSectorPred N Ne) c with hΦ
  have hΦ0 : Φ ≠ 0 := configSectorExpansion_ne_zero (hubbardNumberSectorPred N Ne) hc0
  have hΦW : Φ ∈ hubbardSectorWSubmodule N Ne := hubbardSectorExpansion_mem Ne c
  have hApres : ∀ w, ¬ hubbardNumberSectorPred N Ne w →
      (hubbardHamiltonian N t U).mulVec Φ w = 0 :=
    hubbardNumberSector_supported_of_mem Ne
      (preservesHubbardSectorW_hamiltonian Ne t U Φ hΦW)
  have hΦeig : (hubbardHamiltonian N t U).mulVec Φ = E • Φ :=
    configSectorExpansion_of_compress_eigen (hubbardNumberSectorPred N Ne) hApres hceig
  rw [mem_hubbardSectorWSubmodule_iff] at hΦW
  intro hbot
  apply hΦ0
  have hmem : Φ ∈ Module.End.eigenspace (hubbardHamiltonian N t U).mulVecLin E ⊓
      Module.End.eigenspace (fermionTotalNumber (2 * N + 1)).mulVecLin (Ne : ℂ) := by
    rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff,
      Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    exact ⟨hΦeig, hΦW⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

/-- **Variational lower bound on the number sector.** Any `Ne`-electron vector `v` has Rayleigh
quotient at least `E_min · ‖v‖²`, where `E_min` is the compression's minimum eigenvalue. -/
theorem hubbardSector_minEnergy_mul_le_rayleighOnVec
    (Ne : ℕ) [Nonempty (hubbardSectorConfig N Ne)]
    {t : Fin (N + 1) → Fin (N + 1) → ℂ} {U : ℂ}
    (ht : ∀ i j, star (t i j) = t j i) (hU : star U = U)
    {v : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = (Ne : ℂ) • v) :
    (hermitianMinEigenvalue (configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne)
        (hubbardHamiltonian_isHermitian N ht hU))) * (dotProduct (star v) v).re ≤
      rayleighOnVec (hubbardHamiltonian N t U) v := by
  set hHW := configSectorCompress_isHermitian (hubbardNumberSectorPred N Ne)
    (hubbardHamiltonian_isHermitian N ht hU) with hHWd
  set c := configSectorCoeff N (hubbardNumberSectorPred N Ne) v with hc
  have hsupp : ∀ w, ¬ hubbardNumberSectorPred N Ne w → v w = 0 :=
    hubbardNumberSector_supported_of_mem Ne ((mem_hubbardSectorWSubmodule_iff Ne).mpr hv)
  have hexp : v = configSectorExpansion N (hubbardNumberSectorPred N Ne) c :=
    configSector_completeness (hubbardNumberSectorPred N Ne) v hsupp
  have hcc : (dotProduct (star c) c).re = (dotProduct (star v) v).re := by
    rw [hc, ← configSectorExpansion_dotProduct_self (hubbardNumberSectorPred N Ne), ← hexp]
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hHW c
  rw [hcc] at hvar
  calc hermitianMinEigenvalue hHW * (dotProduct (star v) v).re
      ≤ rayleighOnVec (configSectorCompress N (hubbardNumberSectorPred N Ne)
          (hubbardHamiltonian N t U)) c := hvar
    _ = rayleighOnVec (hubbardHamiltonian N t U) v := by
        rw [rayleighOnVec_configSectorCompress, ← hexp]

/-! ## The total down-number on an eigenmode Slater determinant -/

/-- **The total down number raises a smeared creation by `[σ = 1]`**:
`N̂_↓ · Ĉ†_σ(w) = Ĉ†_σ(w)·N̂_↓ + (if σ = 1 then Ĉ†_σ(w) else 0)`. -/
theorem fermionTotalDownNumber_mul_spinfulCreationFromVector (M : ℕ) (w : Fin (M + 1) → ℂ)
    (σ : Fin 2) :
    fermionTotalDownNumber M * spinfulCreationFromVector M w σ
      = spinfulCreationFromVector M w σ * fermionTotalDownNumber M
        + (if σ = 1 then spinfulCreationFromVector M w σ else 0) := by
  rw [spinfulCreationFromVector, Finset.mul_sum, Finset.sum_mul]
  by_cases hσ : σ = 1
  · subst hσ
    rw [if_pos rfl, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul_comm, smul_mul_assoc, ← smul_add]
    congr 1
    have hraise : fermionTotalDownNumber M *
        fermionMultiCreation (2 * M + 1) (spinfulIndex M x 1)
          = fermionMultiCreation (2 * M + 1) (spinfulIndex M x 1) * fermionTotalDownNumber M
            + fermionMultiCreation (2 * M + 1) (spinfulIndex M x 1) := by
      have h := fermionTotalDownNumber_commutator_fermionDownCreation M x
      rw [fermionDownCreation] at h
      rw [sub_eq_iff_eq_add] at h
      rw [h]; abel
    rw [hraise]
  · rw [if_neg hσ, add_zero]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    have hσ0 : σ = 0 := by omega
    subst hσ0
    have hcomm := fermionTotalDownNumber_commute_fermionUpCreation M x
    rw [fermionUpCreation] at hcomm
    exact hcomm.eq

/-- **The total down number is diagonal in the eigenmode Slater monomials**:
`N̂_↓|qs⟩ = (count of down-tags in qs)·|qs⟩`.  List induction via the down-raising relation. -/
theorem fermionTotalDownNumber_mulVec_generalModeMonomial {M : ℕ}
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (qs : List (Fin (M + 1) × Fin 2)) :
    (fermionTotalDownNumber M).mulVec (generalModeMonomial e qs)
      = ((qs.countP (fun q => q.2 = 1) : ℕ) : ℂ) • generalModeMonomial e qs := by
  induction qs with
  | nil =>
    simp only [generalModeMonomial, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.countP_nil, Nat.cast_zero, zero_smul]
    exact fermionTotalDownNumber_mulVec_vacuum M
  | cons q qs' ih =>
    obtain ⟨q1, q2⟩ := q
    set C := spinfulCreationFromVector M (e q1) q2 with hC
    set mon := generalModeMonomial e qs' with hmon
    have hcons : generalModeMonomial e ((q1, q2) :: qs') = C.mulVec mon :=
      (spinfulCreation_mulVec_generalModeMonomial e q1 q2 qs').symm
    rw [hcons, Matrix.mulVec_mulVec, fermionTotalDownNumber_mul_spinfulCreationFromVector,
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ← hC]
    by_cases hq2 : q2 = 1
    · have hop : (if q2 = 1 then C else 0) = C := if_pos hq2
      have hcnt : (((q1, q2) :: qs').countP (fun q => q.2 = 1) : ℂ)
          = (qs'.countP (fun q => q.2 = 1) : ℂ) + 1 := by
        rw [List.countP_cons, if_pos (show decide ((q1, q2).2 = 1) = true by simpa using hq2)]
        push_cast; ring
      rw [hop, hcnt]
      module
    · have hop : (if q2 = 1 then C else 0) = 0 := if_neg hq2
      have hcnt : (((q1, q2) :: qs').countP (fun q => q.2 = 1) : ℂ)
          = (qs'.countP (fun q => q.2 = 1) : ℂ) := by
        rw [List.countP_cons, if_neg (show ¬ decide ((q1, q2).2 = 1) = true by simpa using hq2)]
        push_cast; ring
      rw [hop, Matrix.zero_mulVec, add_zero, hcnt]

/-- The number of down-tags in the subset-pair list is `|SDown|`. -/
theorem spinfulSubsetPairList_countP_down {M : ℕ} (SUp SDown : Finset (Fin (M + 1))) :
    (spinfulSubsetPairList SUp SDown).countP (fun q => q.2 = 1) = SDown.card := by
  rw [spinfulSubsetPairList, List.countP_append]
  rw [show ((SUp.sort (· ≤ ·)).map (fun j => (j, (0 : Fin 2)))).countP (fun q => q.2 = 1)
      = 0 from by
    rw [List.countP_map, List.countP_eq_zero]; intro q _; simp]
  rw [show ((SDown.sort (· ≤ ·)).map (fun j => (j, (1 : Fin 2)))).countP (fun q => q.2 = 1)
      = (SDown.sort (· ≤ ·)).length from by
    rw [List.countP_map, List.countP_eq_length]; intro q _; simp]
  rw [zero_add, Finset.length_sort]

/-- **The total down number on an eigenmode Slater state**: `N̂_↓ Ψ = |SDown| • Ψ` (the Slater state
filling up-modes `SUp` and down-modes `SDown` has exactly `|SDown|` down electrons). -/
theorem fermionTotalDownNumber_mulVec_spinfulGeneralBasisState {M : ℕ}
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp SDown : Finset (Fin (M + 1))) :
    (fermionTotalDownNumber M).mulVec (spinfulGeneralBasisState e SUp SDown)
      = ((SDown.card : ℕ) : ℂ) • spinfulGeneralBasisState e SUp SDown := by
  rw [spinfulGeneralBasisState, fermionTotalDownNumber_mulVec_generalModeMonomial,
    spinfulSubsetPairList_countP_down]

/-! ## The interaction is bounded by the total down number -/

/-- The only-down site projection `(1 − n̂_{i↑}) n̂_{i↓}` is positive-semidefinite (a Hermitian
idempotent, hence `P = Pᴴ P`). -/
theorem onlyDownProjection_posSemidef (M : ℕ) (i : Fin (M + 1)) :
    ((1 - fermionUpNumber M i) * fermionDownNumber M i).PosSemidef := by
  have hEq : ((1 - fermionUpNumber M i) * fermionDownNumber M i)ᴴ *
      ((1 - fermionUpNumber M i) * fermionDownNumber M i)
        = (1 - fermionUpNumber M i) * fermionDownNumber M i := by
    rw [(one_sub_fermionUpNumber_mul_fermionDownNumber_isHermitian M i).eq]
    exact one_sub_fermionUpNumber_mul_fermionDownNumber_sq M i
  have h := Matrix.posSemidef_conjTranspose_mul_self
    ((1 - fermionUpNumber M i) * fermionDownNumber M i)
  rwa [hEq] at h

/-- **`N̂_↓ − Σ_i n̂_{i↑}n̂_{i↓}` is positive-semidefinite**: it is the sum of the only-down site
projections `Σ_i (1 − n̂_{i↑})n̂_{i↓}`, each PSD. -/
theorem fermionTotalDownNumber_sub_onSiteInteraction_posSemidef (M : ℕ) :
    (fermionTotalDownNumber M - hubbardOnSiteInteraction M 1).PosSemidef := by
  rw [show fermionTotalDownNumber M - hubbardOnSiteInteraction M 1
      = ∑ i : Fin (M + 1), ((1 - fermionUpNumber M i) * fermionDownNumber M i) from by
    rw [fermionTotalDownNumber, hubbardOnSiteInteraction, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_smul, sub_mul, Matrix.one_mul]]
  exact Matrix.posSemidef_sum _ (fun i _ => onlyDownProjection_posSemidef M i)

/-- **The on-site interaction energy is sandwiched between `0` and the down-number energy**:
`0 ≤ Re⟨v, Σ_i n̂↑n̂↓ v⟩ ≤ Re⟨v, N̂_↓ v⟩` for every `v` (each `n̂↑n̂↓` is PSD; `N̂_↓ − Σ n̂↑n̂↓`
is PSD). -/
theorem hubbardOnSiteInteraction_rayleigh_bounds (M : ℕ)
    (v : (Fin (2 * M + 2) → Fin 2) → ℂ) :
    0 ≤ (dotProduct (star v) ((hubbardOnSiteInteraction M 1).mulVec v)).re ∧
      (dotProduct (star v) ((hubbardOnSiteInteraction M 1).mulVec v)).re ≤
        (dotProduct (star v) ((fermionTotalDownNumber M).mulVec v)).re := by
  have hintPSD : (hubbardOnSiteInteraction M 1).PosSemidef := by
    unfold hubbardOnSiteInteraction
    refine Matrix.posSemidef_sum _ (fun i _ => ?_)
    rw [one_smul]
    exact hubbardDoubleOccupancy_posSemidef M i
  have hlow := hintPSD.re_dotProduct_nonneg v
  have hdiff := (fermionTotalDownNumber_sub_onSiteInteraction_posSemidef M).re_dotProduct_nonneg v
  refine ⟨hlow, ?_⟩
  rw [Matrix.sub_mulVec (fermionTotalDownNumber M) (hubbardOnSiteInteraction M 1) v,
    dotProduct_sub] at hdiff
  simp only [RCLike.re_to_complex, Complex.sub_re] at hdiff ⊢
  linarith

end LatticeSystem.Fermion
