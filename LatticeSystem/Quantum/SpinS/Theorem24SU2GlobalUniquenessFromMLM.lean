import LatticeSystem.Quantum.SpinS.Theorem23StructuralGeneralFinal
import LatticeSystem.Quantum.SpinS.Theorem23StructuralSectorLiftCasimir
import LatticeSystem.Quantum.SpinS.EigenspaceFinrankLeOneTransfer
import LatticeSystem.Quantum.SpinS.HermitianMinEigenvalueEigenvector
import LatticeSystem.Quantum.SpinS.HermitianMinLeOfEigenvector
import LatticeSystem.Quantum.SpinS.Theorem24SectorPFFromTheorem23
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLMCore

/-!
# SU(2)-point global uniqueness from the MLM endpoint

This file develops the non-circular SU(2)-endpoint input needed for Tasaki
§2.5 Theorem 2.4 obligation (2).  The proof is routed through the
Marshall-Lieb-Mattis / Perron-Frobenius / Casimir infrastructure from Theorem
2.3, not through the strict-gap wrappers used later in the anisotropic
deformation argument.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorems 2.3 and 2.4, pp. 42-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Balanced-sector PF simplicity from the Theorem 2.3 common-minimum
witness**: in the balanced-cardinality case, the structural Theorem 2.3 sector
witness for `M0 = |A| * N` gives a Marshall-positive sector eigenvector at the
common energy.  Perron--Frobenius geometric simplicity then gives the
sector-matrix `finrank <= 1` bound at the full Heisenberg Hermitian minimum. -/
theorem tasaki23_balanced_sector_matrix_finrank_le_one_of_common_min
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    {μ : ℝ}
    (hmin_eq : hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
      (Λ := V) hJ_real' N) = μ) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N
        ((Finset.univ.filter (fun x : V => A x = true)).card * N))) (μ : ℂ)) ≤ 1 := by
  classical
  set M0 := (Finset.univ.filter (fun x : V => A x = true)).card * N with hM0def
  obtain ⟨μ0, hmin_eq0, hsector, _hglobal⟩ :=
    exists_tasaki23_common_energy_eq_hermitianMinEigenvalue A N c hT23
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      hN hcardA hcardB
  have hμ_eq : μ0 = μ := by
    rw [← hmin_eq0, hmin_eq]
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := V) A N := by
    rw [hM0def, tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N _ h_card_eq]
  haveI : Nonempty (magConfigS V N M0) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  obtain ⟨v0, _hμ_lt, hv0_pos, hΦ0_eig_embed, _huniq0⟩ := hsector M0 hM0_mem
  set Φ0 : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun τ : magConfigS V N M0 =>
      (((marshallSignS A τ.1).re * v0 τ : ℝ) : ℂ))
    with hΦ0def
  have hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = (μ0 : ℂ) • Φ0 := by
    simpa [Φ0, hΦ0def] using hΦ0_eig_embed
  have hReEig0 : (heisenbergHamiltonianSReMatrixOnMagSector J N M0).mulVec
      (fun σ => (marshallSignS A σ.1).re * v0 σ) =
      μ0 • (fun σ => (marshallSignS A σ.1).re * v0 σ) := by
    have hc := heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      J (M := M0) hΦ0_eig
    rw [hΦ0def, magSectorRestriction_magSectorEmbedding] at hc
    have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N
      hJ_real hc
    simpa only [Complex.ofReal_re] using hre
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcardA)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcardB)
    have hb_not := (Finset.mem_filter.mp hb).2
    cases hAb : A b
    · exact ⟨b, hAb⟩
    · rw [hAb] at hb_not
      cases hb_not
  have hpf_mu0 :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M0)) (μ0 : ℂ)) ≤ 1 :=
    heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive
      (V := V) (N := N) A c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite
      hc_strict hA_ne hB_ne hN hv0_pos hReEig0
  rw [hμ_eq] at hpf_mu0
  simpa [M0, hM0def] using hpf_mu0

/-- **Packaged MLM-to-SU(2) uniqueness endpoint**: under balanced sublattice
cardinality, the structural Theorem 2.3 predicate identifies its common energy
with the full Heisenberg Hermitian minimum and collapses the admissible band to
the singleton balanced sector.  If, at that common energy, the balanced sector
has Perron--Frobenius `finrank <= 1` and every other sector has strictly larger
real eigenvalues, then the full SU(2)-point ground eigenspace has `finrank <= 1`.

This is the consumer-facing non-circular endpoint for the remaining Theorem 2.4
obligation: the two callbacks are exactly the sector PF simplicity and the
strict MLM/Casimir outside-sector ordering, with no dependence on anisotropic
strict-gap wrappers. -/
theorem exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N
          ((Finset.univ.filter (fun x : V => A x = true)).card * N))) (μ : ℂ)) ≤ 1)
    (h_strict_outside : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ →
      ∀ M : ℕ,
        M ≠ (Finset.univ.filter (fun x : V => A x = true)).card * N →
        [Nonempty (magConfigS V N M)] →
        ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
          μ < μM) :
    ∃ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ ∧
      tasaki23GroundStateSectors (V := V) A N =
        {((Finset.univ.filter (fun x : V => A x = true)).card * N)} ∧
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := V) J N)) (μ : ℂ)) ≤ 1 := by
  classical
  set M0 := (Finset.univ.filter (fun x : V => A x = true)).card * N with hM0def
  obtain ⟨μ, hmin_eq, _hsector, _hglobal⟩ :=
    exists_tasaki23_common_energy_eq_hermitianMinEigenvalue A N c hT23
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      hN hcardA hcardB
  have hsectors_singleton :
      tasaki23GroundStateSectors (V := V) A N = {M0} := by
    rw [hM0def]
    exact tasaki23GroundStateSectors_eq_singleton_of_card_eq A N h_card_eq
  have hpf :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N M0)) (μ : ℂ)) ≤ 1 := by
    rw [hM0def]
    exact h_sector_pf μ hmin_eq
  have hstrict : ∀ M : ℕ, M ≠ M0 → [Nonempty (magConfigS V N M)] →
      ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
        μ < μM := by
    intro M hM_ne
    rw [hM0def] at hM_ne
    exact h_strict_outside μ hmin_eq M hM_ne
  have huniq :
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := V) J N)) (μ : ℂ)) ≤ 1 :=
    heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower
      (V := V) (N := N) J M0 hJ_real hstrict hpf
  exact ⟨μ, hmin_eq, by simpa [M0, hM0def] using hsectors_singleton, huniq⟩

set_option linter.style.longLine false in
/-- **Packaged MLM-to-SU(2) uniqueness endpoint from the Casimir ladder
obstruction**: the preceding endpoint no longer needs an abstract strict
outside-sector callback once the balanced zero-Casimir ladder obstruction is
available.  The structural Theorem 2.3 data provide the common energy and the
balanced PF vector; the balanced PF/Casimir lift makes that vector a non-zero
zero-Casimir full eigenvector; and
`tasaki23_strict_hOutside_of_card_eq_zero_casimir_ladder_obstruction` constructs
the strict outside-sector ordering consumed by the PR #4020 endpoint. -/
theorem exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (h_sector_pf : ∀ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ →
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := V) J N
          ((Finset.univ.filter (fun x : V => A x = true)).card * N))) (μ : ℂ)) ≤ 1) :
    ∃ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ ∧
      tasaki23GroundStateSectors (V := V) A N =
        {((Finset.univ.filter (fun x : V => A x = true)).card * N)} ∧
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := V) J N)) (μ : ℂ)) ≤ 1 := by
  classical
  set M0 := (Finset.univ.filter (fun x : V => A x = true)).card * N with hM0def
  obtain ⟨μ, hmin_eq, hsector, _hglobal⟩ :=
    exists_tasaki23_common_energy_eq_hermitianMinEigenvalue A N c hT23
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
      hN hcardA hcardB
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := V) A N := by
    rw [hM0def, tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N _ h_card_eq]
  haveI : Nonempty (magConfigS V N M0) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  obtain ⟨v0, _hμ_lt, hv0_pos, hΦ0_eig_embed, _huniq0⟩ := hsector M0 hM0_mem
  set Φ0 : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun τ : magConfigS V N M0 =>
      (((marshallSignS A τ.1).re * v0 τ : ℝ) : ℂ))
    with hΦ0def
  have hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0 := by
    simpa [Φ0, hΦ0def] using hΦ0_eig_embed
  have hΦ0_ne : Φ0 ≠ 0 := by
    intro hzero
    let τ : magConfigS V N M0 := Classical.arbitrary _
    have hτ_zero := congrFun hzero τ.1
    rw [hΦ0def, magSectorEmbedding_apply_subtype] at hτ_zero
    have hreal_zero : (marshallSignS A τ.1).re * v0 τ = 0 := by
      exact_mod_cast congrArg Complex.re hτ_zero
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv0_zero : v0 τ = 0 := by
      calc
        v0 τ = ((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) * v0 τ := by
          rw [hsq, one_mul]
        _ = (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * v0 τ) := by ring
        _ = 0 := by rw [hreal_zero, mul_zero]
    exact (ne_of_gt (hv0_pos τ)) hv0_zero
  have hΦ0_mem : Φ0 ∈
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ)) := by
    rw [hΦ0def]
    exact magSectorEmbedding_mem_magSubspaceS _
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcardA)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp (lt_of_lt_of_le Nat.zero_lt_one hcardB)
    have hb_not := (Finset.mem_filter.mp hb).2
    cases hAb : A b
    · exact ⟨b, hAb⟩
    · rw [hAb] at hb_not
      cases hb_not
  have hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
      (N : ℝ) / 2 := by
    have hBpos : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hcardB)
    have hNpos : 0 < (N : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    nlinarith
  have hReEig0 : (heisenbergHamiltonianSReMatrixOnMagSector J N M0).mulVec
      (fun σ => (marshallSignS A σ.1).re * v0 σ) =
      μ • (fun σ => (marshallSignS A σ.1).re * v0 σ) := by
    have hc := heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      J (M := M0) hΦ0_eig
    rw [hΦ0def, magSectorRestriction_magSectorEmbedding] at hc
    have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N
      hJ_real hc
    simpa only [Complex.ofReal_re] using hre
  obtain ⟨_hΦ0_eig_lift, hΦ0_cas_lift⟩ :=
    tasaki23_sector_lift_and_casimir_zero_of_card_eq A N c c_toy h_card_eq hsB hM0_mem
      hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict hc_strict_toy
      hA_ne hB_ne hN hv0_pos hReEig0
  have hΦ0_cas : (totalSpinSSquared V N).mulVec Φ0 = 0 := by
    rw [hΦ0def]
    simpa using hΦ0_cas_lift
  have hcommon : ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ) := by
    intro M hM
    haveI : Nonempty (magConfigS V N M) :=
      magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM)
    obtain ⟨vM, _hμ_lt_M, hvM_pos, hΦM_eig_embed, _huniqM⟩ := hsector M hM
    refine ⟨vM, hvM_pos, ?_⟩
    set ΦM : (V → Fin (N + 1)) → ℂ :=
      magSectorEmbedding (fun τ : magConfigS V N M =>
        (((marshallSignS A τ.1).re * vM τ : ℝ) : ℂ))
      with hΦMdef
    have hΦM_eig : (heisenbergHamiltonianS J N).mulVec ΦM = (μ : ℂ) • ΦM := by
      simpa [ΦM, hΦMdef] using hΦM_eig_embed
    have hc := heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
      J (M := M) hΦM_eig
    rw [hΦMdef, magSectorRestriction_magSectorEmbedding] at hc
    have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N
      hJ_real hc
    simpa only [Complex.ofReal_re] using hre
  have hstrict : ∀ μ' : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ' →
      ∀ M : ℕ,
        M ≠ (Finset.univ.filter (fun x : V => A x = true)).card * N →
        [Nonempty (magConfigS V N M)] →
        ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
          μ' < μM := by
    intro μ' hmin_eq' M hM_ne _ μM φ hφ_ne hφ
    have hμ' : μ' = μ := by
      rw [hmin_eq] at hmin_eq'
      exact hmin_eq'.symm
    have hlt : μ < μM :=
      tasaki23_strict_hOutside_of_card_eq_zero_casimir_ladder_obstruction
        A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict h_card_eq
        hcommon hΦ0_ne hΦ0_eig
        (by simpa [M0, hM0def] using hΦ0_mem)
        hΦ0_cas (h_sector_pf μ hmin_eq) hM_ne hφ_ne hφ
    simpa [hμ'] using hlt
  exact exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one
    A N c hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict
    h_card_eq hN hcardA hcardB h_sector_pf hstrict

set_option linter.style.longLine false in
/-- **Packaged MLM-to-SU(2) uniqueness endpoint with sector PF constructed
from Theorem 2.3**: this removes the final balanced-sector PF simplicity
callback from the preceding Casimir-ladder endpoint.
The balanced sector matrix `finrank <= 1` bound is obtained directly from the
Theorem 2.3 Marshall-positive sector witness by Perron--Frobenius geometric
simplicity. -/
theorem exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder_t23_pf
    (A : V → Bool) (N : ℕ) {J : V → V → ℂ} (c c_toy : ℝ)
    (hT23 : tasaki_2_5_theorem_2_3 A N J c)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card) :
    ∃ μ : ℝ,
      hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
        (Λ := V) hJ_real' N) = μ ∧
      tasaki23GroundStateSectors (V := V) A N =
        {((Finset.univ.filter (fun x : V => A x = true)).card * N)} ∧
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := V) J N)) (μ : ℂ)) ≤ 1 := by
  exact
    exists_tasaki23_common_energy_and_heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_casimir_ladder
      (V := V) A N c c_toy hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
      hJ_pos hc_strict hc_strict_toy h_card_eq hN hcardA hcardB
      (fun μ hmin_eq =>
        tasaki23_balanced_sector_matrix_finrank_le_one_of_common_min
          (V := V) A N c hT23 hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite
          hJ_pos hc_strict h_card_eq hN hcardA hcardB hmin_eq)

end LatticeSystem.Quantum
