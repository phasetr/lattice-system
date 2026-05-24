import LatticeSystem.Quantum.SpinS.Theorem23SectorExistenceInterval
import LatticeSystem.Quantum.SpinS.Theorem23Sectors
import LatticeSystem.Quantum.SpinS.Theorem23IntervalCasimirMinimality
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifference
import LatticeSystem.Quantum.SpinS.Theorem23LocalCoefficient
import LatticeSystem.Quantum.SpinS.Theorem23LocalDifferenceMarshall

/-!
# Tasaki §2.5 Theorem 2.3 outside-ground API

This module contains outside-ground lower-bound callbacks and common-energy
final packaging wrappers for the Tasaki §2.5 Theorem 2.3 proof chain. It
imports the interval-Casimir minimality suffix split from
`Theorem23IntervalCasimir.lean` so the base interval-chain module does not
accumulate the outside-ground and final-packaging API tail. The source
predicted-Casimir final-wrapper suffix is split into
`Theorem23OutsideGroundPredictedCasimir.lean`, the threaded predicted-Casimir
final-wrapper suffix is split into
`Theorem23OutsideGroundPredictedCasimirThreaded.lean`, the conditional
left-endpoint predicted-GS final-wrapper suffix is split into
`Theorem23OutsideGroundConditional.lean`, and the left-endpoint threaded
predicted-GS and lowered-Marshall final-wrapper suffix is split into
`Theorem23OutsideGroundPredictedGS.lean`.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector ground-energy lower callback**:
for each nonempty sector outside the admissible interval, the common energy
`μ` is no larger than the Marshall-positive sector ground-representative
energy supplied by the per-sector Theorem 2.2 wrapper.

The Perron-Frobenius bridge turns this callback into a full outside-sector
real spectral lower bound. -/
def tasaki23OutsideGroundEnergyLowerCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c μ : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M ∉ tasaki23GroundStateSectors (V := V) A N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      μ ≤ μM

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector ground-energy lower family**:
after the adjacent-sector chain chooses the common energy `μ`, this
callback supplies the outside-sector lower-bound API at that same `μ`.

This names the final higher-level input used by the threaded
outside-ground wrappers, where `μ` is not an explicit argument but is
produced by the common-energy chain. -/
def tasaki23OutsideGroundEnergyLowerFamilyCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ {μ : ℝ},
    tasaki23CommonEnergyChain (V := V) A J N c μ →
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector admissible-reach callback**:
for each Marshall-positive Theorem 2.2 representative in a sector outside
`tasaki23GroundStateSectors`, the ladder construction reaches a nonzero
sector eigenvector at the same eigenvalue in some admissible sector.

This names the remaining ladder-reach task separately from the final
outside-ground lower-bound comparison: once such an admissible-sector
eigenvector at `μM` is available, the common-energy chain on admissible
sectors proves `μ ≤ μM`. -/
def tasaki23OutsideGroundAdmissibleReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M ∉ tasaki23GroundStateSectors (V := V) A N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ Φ : magConfigS V N K → ℂ,
          Φ ≠ 0 ∧
          (heisenbergHamiltonianSMatrixOnMagSector J N K).mulVec Φ =
            (μM : ℂ) • Φ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 left outside-sector admissible-reach
callback**: for an outside-sector Marshall-positive representative below
the left endpoint of `tasaki23GroundStateSectors A N`, the lowering ladder
direction reaches a nonzero eigenvector at the same eigenvalue in some
admissible sector. -/
def tasaki23OutsideGroundLeftAdmissibleReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    M <
        min (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
          (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
          N →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ Φ : magConfigS V N K → ℂ,
          Φ ≠ 0 ∧
          (heisenbergHamiltonianSMatrixOnMagSector J N K).mulVec Φ =
            (μM : ℂ) • Φ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 right outside-sector admissible-reach
callback**: for an outside-sector Marshall-positive representative above
the right endpoint of `tasaki23GroundStateSectors A N`, the raising ladder
direction reaches a nonzero eigenvector at the same eigenvalue in some
admissible sector. -/
def tasaki23OutsideGroundRightAdmissibleReachCallback
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ) (c : ℝ) : Prop :=
  ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
    max (Finset.card (Finset.filter (fun x : V => A x = true) Finset.univ))
        (Finset.card (Finset.filter (fun x : V => (! A x) = true) Finset.univ)) *
        N < M →
    ∀ {μM : ℝ} {v : magConfigS V N M → ℝ},
      μM < c →
      (∀ τ, 0 < v τ) →
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
        (μM : ℂ) • magSectorEmbedding
          (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) →
      ∃ K : ℕ,
        K ∈ tasaki23GroundStateSectors (V := V) A N ∧
        Nonempty (magConfigS V N K) ∧
        ∃ Φ : magConfigS V N K → ℂ,
          Φ ≠ 0 ∧
          (heisenbergHamiltonianSMatrixOnMagSector J N K).mulVec Φ =
            (μM : ℂ) • Φ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector admissible reach from side
callbacks**: the full outside-sector reach callback follows by splitting an
outside magnetization sector into the left-of-interval and right-of-interval
cases, then applying the corresponding directional ladder-reach callback. -/
theorem tasaki23OutsideGroundAdmissibleReachCallback_of_side_callbacks
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hleft :
      tasaki23OutsideGroundLeftAdmissibleReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightAdmissibleReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c := by
  intro M _ hM_out μM v hμM_lt hv_pos hΦ
  rcases
      (tasaki23GroundStateSectors_not_mem_iff_lt_left_or_right_lt
        (V := V) A N M).mp hM_out with hM_left | hM_right
  · exact hleft M hM_left hμM_lt hv_pos hΦ
  · exact hright M hM_right hμM_lt hv_pos hΦ

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector lower family from sector
minimality**: a sector-minimality callback immediately supplies the
outside-sector ground-energy lower family.  The Marshall-positive
outside-sector representative is restricted to its magnetization sector,
where sector minimality gives `μ ≤ μM`. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_sector_minimality
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hsector_min : tasaki23SectorMinimalityCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c := by
  intro μ hcommon M _ hM_out μM v _hμM_lt hv_pos hΦ
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μM : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hΦ
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hΦ_ne : Φ ≠ 0 := by
    intro hzero
    obtain ⟨τ⟩ := (inferInstance : Nonempty (magConfigS V N M))
    have hτ_complex : (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ) = 0 := by
      simpa [Φ] using congrFun hzero τ
    have hτ_real : (marshallSignS A τ.1).re * v τ = 0 := by
      exact_mod_cast hτ_complex
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv := hv_pos τ
    rcases mul_eq_zero.mp hτ_real with ha | hv_zero
    · nlinarith
    · nlinarith
  exact hsector_min hcommon M hΦ_ne hsector_complex

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 real-sector lower bound on admissible
sectors**: once the common-energy chain has produced a Marshall-positive
sector representative at energy `μ` in an admissible sector, the
Perron-Frobenius shifted-matrix comparison makes `μ` a lower bound for
every real-form eigenvalue in that same sector.

This proves the real-sector spectral-minimality callback on the
`tasaki23GroundStateSectors` interval; sectors outside the interval remain
the separate global spectral input for the final Theorem 2.3 wrapper. -/
theorem tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ) :
    ∀ M : ℕ, M ∈ tasaki23GroundStateSectors (V := V) A N →
      [Nonempty (magConfigS V N M)] →
        ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
          φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
          μ ≤ μ' := by
  intro M hM _ μ' φ hφ_ne hφ_eigen
  obtain ⟨v, _hμ_lt, hv_pos, hfull⟩ := hcommon M hM
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μ : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hfull
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hsector_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) =
        μ • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * v τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hsector_complex
    simpa [Φ] using hre
  exact
    heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hsector_real
      (fun τ => by
        have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
          marshallSignS_re_sq A τ.1
        nlinarith [hv_pos τ])
      hφ_ne hφ_eigen

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from admissible
reach**: if every outside-sector Marshall-positive ground representative
can be transported to a nonzero eigenvector in an admissible sector at
the same eigenvalue, then the outside-sector ground-energy lower family
follows.

The proof applies the admissible-sector real spectral lower bound coming
from the common-energy chain.  The reached complex sector eigenvector has
either nonzero real part or nonzero imaginary part, and the real-coupling
complex-to-real eigenvector bridge supplies the real-form eigen equation
at the same `μM`. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hreach : tasaki23OutsideGroundAdmissibleReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c := by
  intro μ hcommon M _ hM_out μM v hμM_lt hv_pos hΦ
  obtain ⟨K, hK_mem, hK_nonempty, ΦK, hΦK_ne, hΦK_eigen⟩ :=
    hreach M hM_out hμM_lt hv_pos hΦ
  letI : Nonempty (magConfigS V N K) := hK_nonempty
  have hadm_real_min :
      ∀ {μ' : ℝ} {φ : magConfigS V N K → ℝ},
        φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N K).mulVec φ = μ' • φ →
        μ ≤ μ' :=
    tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hcommon K hK_mem
  classical
  by_cases hRe_ne : (fun τ : magConfigS V N K => (ΦK τ).re) ≠ 0
  · exact hadm_real_min (μ' := μM) (φ := fun τ => (ΦK τ).re) hRe_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hΦK_eigen)
  · have hRe_zero : (fun τ : magConfigS V N K => (ΦK τ).re) = 0 := by
      by_contra h
      exact hRe_ne h
    have hIm_ne : (fun τ : magConfigS V N K => (ΦK τ).im) ≠ 0 := by
      intro hIm_zero
      apply hΦK_ne
      funext τ
      apply Complex.ext
      · have h := congrFun hRe_zero τ
        simpa using h
      · have h := congrFun hIm_zero τ
        simpa using h
    exact hadm_real_min (μ' := μM) (φ := fun τ => (ΦK τ).im) hIm_ne
      (heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
        N hJ_real hΦK_eigen)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-ground family from side admissible
reach**: left and right directional outside-sector reach callbacks supply
the outside-sector ground-energy lower family by first recombining into the
full admissible-reach callback and then applying
`tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach`. -/
theorem tasaki23OutsideGroundEnergyLowerFamilyCallback_of_side_admissible_reach
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hleft :
      tasaki23OutsideGroundLeftAdmissibleReachCallback (V := V) A J N c)
    (hright :
      tasaki23OutsideGroundRightAdmissibleReachCallback (V := V) A J N c) :
    tasaki23OutsideGroundEnergyLowerFamilyCallback (V := V) A J N c :=
  tasaki23OutsideGroundEnergyLowerFamilyCallback_of_admissible_reach
    (V := V) A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
    (tasaki23OutsideGroundAdmissibleReachCallback_of_side_callbacks
      (V := V) A (J := J) N c hleft hright)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 outside-sector real lower bound from
outside-sector ground energies**: for sectors outside the admissible
Theorem 2.3 interval, it is enough to prove the lower bound against the
Marshall-positive sector ground-state representative supplied by the
per-sector Theorem 2.2 wrapper.

The Perron-Frobenius comparison for the shifted dressed real sector matrix
then places that sector ground energy below every real-form sector
eigenvalue, giving the full outside-real-sector callback needed by the
final global-minimality step. -/
theorem tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ) :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      M ∉ tasaki23GroundStateSectors (V := V) A N →
      ∀ {μ' : ℝ} {φ : magConfigS V N M → ℝ},
        φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ →
        μ ≤ μ' := by
  intro M _ hM_out μ' φ hφ_ne hφ_eigen
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hΦM, _hsupportM, _huniqM⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  let Φ : magConfigS V N M → ℂ :=
    fun τ => (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ)
  have hsector_complex :
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
        (μM : ℂ) • Φ := by
    have hrestrict :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        (M := M) J hΦM
    rw [magSectorRestriction_magSectorEmbedding] at hrestrict
    exact hrestrict
  have hsector_real :
      (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
          (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * vM τ) =
        μM • (fun τ : magConfigS V N M => (marshallSignS A τ.1).re * vM τ) := by
    have hre :=
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        N hJ_real hsector_complex
    simpa [Φ] using hre
  have hμ_le_μM : μ ≤ μM :=
    houtside_ground_energy_lower M hM_out hμM_lt hvM_pos hΦM
  have hμM_le_μ' : μM ≤ μ' :=
    heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hsector_real
      (fun τ => by
        have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
          marshallSignS_re_sq A τ.1
        have hv := hvM_pos τ
        nlinarith [hv])
      hφ_ne hφ_eigen
  exact hμ_le_μM.trans hμM_le_μ'

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 sector minimality from common interval energy
and outside-sector ground energies**: combine the admissible-sector
minimality supplied by the common-energy chain with the outside-sector
ground-energy bridge, then pass from real-form sector eigenvectors to
complex sector eigenvectors.

This is the sectorwise spectral-minimality package needed to turn the
outside-sector ground-energy lower-bound callback into the final global
minimality callback for Theorem 2.3. -/
theorem
    tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ) :
    ∀ M : ℕ, [Nonempty (magConfigS V N M)] →
      ∀ {μ' : ℝ} {Φ : magConfigS V N M → ℂ},
        Φ ≠ 0 →
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec Φ =
          (μ' : ℂ) • Φ →
        μ ≤ μ' := by
  exact
    tasaki23_sector_minimality_of_real_sector_minimality N hJ_real
      (fun M => by
        by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
        · exact
            tasaki23_real_sector_minimality_on_groundStateSectors_of_common_energy_chain
              A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
              hcommon M hM
        · exact
            tasaki23_outside_real_sector_minimality_of_outside_sector_ground_energy_lower_bound
              A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
              hc_strict h_intermediate houtside_ground_energy_lower M hM)

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from a common interval energy**:
if one real energy `μ` is already realised by Marshall-positive sector
eigenvectors in every admissible sector, then the per-sector Theorem 2.2
uniqueness wrapper upgrades those representatives to the final
existence-and-uniqueness format.

This helper isolates the final packaging step from the particular mechanism
used to construct the common sector energy. -/
theorem tasaki_2_5_theorem_2_3_of_common_energy_chain
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ)
    (hglobal_min :
      ∀ {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ},
        Ψ' ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' →
        μ ≤ μ') :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
    hc_strict h_intermediate _hA_nonempty _hnotA_nonempty
  refine ⟨μ, ?_, hglobal_min⟩
  intro M hM _hM_nonempty
  obtain ⟨v_chain, hμ_chain_lt, hv_chain_pos, hΦ_chain⟩ := hcommon M hM
  obtain ⟨μM, vM, hμM_lt, hvM_pos, hΦM, _hsupportM, huniqM⟩ :=
    tasaki_2_5_theorem_2_3_sector_existence
      (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict h_intermediate
  have hsupport_chain :
      ∀ σ, magSumS σ ≠ M →
        magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v_chain τ : ℝ) : ℂ)) σ = 0 := by
    intro σ hσ
    exact magSectorEmbedding_apply_of_not_mem _ hσ
  have hpos_chain_full :
      ∀ τ : magConfigS V N M,
        0 < (marshallSignS A τ.1).re *
          (magSectorEmbedding
            (fun τ : magConfigS V N M =>
              (((marshallSignS A τ.1).re * v_chain τ : ℝ) : ℂ)) τ.1).re := by
    intro τ
    rw [magSectorEmbedding_apply_subtype, Complex.ofReal_re]
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv := hv_chain_pos τ
    nlinarith
  obtain ⟨hμ_eq_μM, _hr⟩ := huniqM hΦ_chain hsupport_chain hpos_chain_full
  refine ⟨vM, ?_, hvM_pos, ?_, ?_⟩
  · exact hμ_chain_lt
  · rwa [hμ_eq_μM]
  · intro μ' Ψ' hΨ'_eigen hΨ'_support hΨ'_positive
    obtain ⟨hμ'_eq_μM, hr⟩ := huniqM hΨ'_eigen hΨ'_support hΨ'_positive
    exact ⟨by rw [hμ'_eq_μM, ← hμ_eq_μM], hr⟩

set_option linter.style.longLine false in
/-- **Tasaki §2.5 Theorem 2.3 final wrapper from common interval energy and
outside-sector ground energies**: once the adjacent-sector chain has
produced a common Marshall-positive energy on the admissible interval, it
is enough to prove lower bounds only for the Marshall-positive
ground-state representatives in outside sectors.

The sector-minimality bridge packages the admissible and outside sectors,
and the global-minimality bridge then supplies the final full-space
minimality callback required by the textbook statement. -/
theorem
    tasaki_2_5_theorem_2_3_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ}
    (hcommon : tasaki23CommonEnergyChain (V := V) A J N c μ)
    (houtside_ground_energy_lower :
      tasaki23OutsideGroundEnergyLowerCallback (V := V) A J N c μ) :
    tasaki_2_5_theorem_2_3 (V := V) A N J c := by
  intro _hJ_real _hJ_real' _hJ_sym _hJ_nn _hJ_bipartite _hJ_pos
    _hc_strict _h_intermediate hA_nonempty hnotA_nonempty
  exact
    tasaki_2_5_theorem_2_3_of_common_energy_chain
      A N c hcommon
      (tasaki23_global_minimality_of_sector_minimality N
        (tasaki23_sector_minimality_of_common_energy_chain_and_outside_sector_ground_energy_lower_bound
          A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite
          hc_strict h_intermediate hcommon houtside_ground_energy_lower))
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos
      hc_strict h_intermediate hA_nonempty hnotA_nonempty

end LatticeSystem.Quantum
