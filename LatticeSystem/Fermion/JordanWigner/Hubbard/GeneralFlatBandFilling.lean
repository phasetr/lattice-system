import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandSpanning

/-!
# Filling constraint on the flat-band Fock spanning (Tasaki §11.3.4, toward 11.3.47)

Refines eq. (11.3.46): a flat-band Hubbard ground state at filling `N = D₀` lies in the span of the
flat-band-supported occupation monomials **with exactly `D₀` occupied modes**.  The total fermion
number operator `N̂` is diagonal in the occupation basis (`N̂ occMon(g) = |occupied(g)|·occMon(g)`,
list induction via `[N̂, Ĉ†(w)] = Ĉ†(w)`), so a `D₀`-electron ground state has occupation-basis
coefficients supported on the `D₀`-electron configurations.  Together with the spin /
no-double-occupancy
arguments this gives the spin-system representation (eq. 11.3.47).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eqs. (11.3.46)–(11.3.47).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- **The total number operator raises a smeared creation by one**:
`N̂·Ĉ†_σ(w) = Ĉ†_σ(w)·N̂ + Ĉ†_σ(w)`.  Bilinear extension of `[N̂, ĉ†_x] = ĉ†_x`. -/
theorem fermionTotalNumber_mul_spinfulCreationFromVector (M : ℕ) (w : Fin (M + 1) → ℂ)
    (σ : Fin 2) :
    fermionTotalNumber (2 * M + 1) * spinfulCreationFromVector M w σ
      = spinfulCreationFromVector M w σ * fermionTotalNumber (2 * M + 1)
        + spinfulCreationFromVector M w σ := by
  rw [spinfulCreationFromVector, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← smul_add]
  congr 1
  exact (eq_add_of_sub_eq
    (fermionTotalNumber_commutator_fermionMultiCreation (2 * M + 1)
      (spinfulIndex M x σ))).trans (add_comm _ _)

/-- **The total number operator is diagonal in the mode monomials**: `N̂|qs⟩ = (length qs)·|qs⟩`
(every creation adds one particle).  List induction via the raising relation, down to
`N̂|vac⟩ = 0`. -/
theorem fermionTotalNumber_mulVec_generalModeMonomial
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (qs : List (Fin (M + 1) × Fin 2)) :
    (fermionTotalNumber (2 * M + 1)).mulVec (generalModeMonomial e qs)
      = (qs.length : ℂ) • generalModeMonomial e qs := by
  induction qs with
  | nil =>
    simp only [generalModeMonomial, List.map_nil, List.prod_nil, Matrix.one_mulVec,
      List.length_nil, Nat.cast_zero, zero_smul]
    exact fermionTotalNumber_mulVec_vacuum (2 * M + 1)
  | cons q qs' ih =>
    obtain ⟨q1, q2⟩ := q
    have hcons : generalModeMonomial e ((q1, q2) :: qs')
        = (spinfulCreationFromVector M (e q1) q2).mulVec (generalModeMonomial e qs') :=
      (spinfulCreation_mulVec_generalModeMonomial e q1 q2 qs').symm
    rw [hcons, Matrix.mulVec_mulVec, fermionTotalNumber_mul_spinfulCreationFromVector,
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, List.length_cons]
    push_cast
    rw [add_smul, one_smul]

/-- **The total number operator is diagonal in the occupation monomials**:
`N̂ occMon(g) = |occupied(g)|·occMon(g)`. -/
theorem fermionTotalNumber_mulVec_generalOccMonomial
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (g : Fin (M + 1) × Fin 2 → Fin 2) :
    (fermionTotalNumber (2 * M + 1)).mulVec (generalOccMonomial e g)
      = ((generalOccFinset g).card : ℂ) • generalOccMonomial e g := by
  rw [generalOccMonomial, fermionTotalNumber_mulVec_generalModeMonomial, Finset.length_toList]

open Module in
/-- **Filling coefficient vanishing**: a `D₀`-electron eigenstate of the total number operator has
vanishing occupation-basis coefficient on every configuration with a different particle count.
Since
`N̂` is diagonal in the occupation basis (eigenvalue `|occupied(g)|`), `N̂Φ = D₀Φ` forces
`|occupied(g)|·c_g = D₀·c_g`, hence `c_g = 0` when `|occupied(g)| ≠ D₀`. -/
theorem groundState_generalOccBasis_repr_eq_zero_of_card_ne
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.IsHermitian)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} {D₀ : ℕ}
    (hN : (fermionTotalNumber (2 * M + 1)).mulVec Φ = (D₀ : ℂ) • Φ)
    (g : Fin (M + 1) × Fin 2 → Fin 2) (hg : (generalOccFinset g).card ≠ D₀) :
    (generalOccBasis (eigenbasisAsBasis hT)).repr Φ g = 0 := by
  set e := eigenbasisAsBasis hT with he
  set b := generalOccBasis e with hb
  have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial e h :=
    fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
  have hexp : (fermionTotalNumber (2 * M + 1)).mulVec Φ
      = ∑ h, (b.repr Φ h * ((generalOccFinset h).card : ℂ)) • (b h) := by
    conv_lhs => rw [← b.sum_repr Φ]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Matrix.mulVec_smul, hbcoe, fermionTotalNumber_mulVec_generalOccMonomial, smul_smul,
      ← hbcoe]
  have hrepr : b.repr ((fermionTotalNumber (2 * M + 1)).mulVec Φ) g
      = b.repr Φ g * ((generalOccFinset g).card : ℂ) := by
    rw [hexp, map_sum]
    simp only [map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul, b.repr_self]
    rw [Finset.sum_eq_single g]
    · rw [Finsupp.single_eq_same, mul_one]
    · intro h _ hhg
      rw [Finsupp.single_eq_of_ne (Ne.symm hhg), mul_zero]
    · intro h; exact absurd (Finset.mem_univ g) h
  rw [hN, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hrepr
  -- hrepr : (D₀ : ℂ) * repr Φ g = repr Φ g * (card g : ℂ)
  have hne : ((generalOccFinset g).card : ℂ) - (D₀ : ℂ) ≠ 0 := by
    rw [sub_ne_zero, Ne, Nat.cast_inj]; exact hg
  have : (b.repr Φ g) * (((generalOccFinset g).card : ℂ) - (D₀ : ℂ)) = 0 := by
    rw [mul_sub, ← hrepr]; ring
  exact (mul_eq_zero.mp this).resolve_right hne

open Module in
/-- **Tasaki eq. (11.3.46), filling-refined**: a flat-band Hubbard ground state in the
`D₀`-electron sector lies in the span of the flat-band-supported occupation monomials **with exactly
`D₀` occupied modes**.  Combines the flat-band spanning (`flatBand_groundState_mem_flatFockSpan`'s
coefficient vanishing) with the filling coefficient vanishing. -/
theorem flatBand_groundState_atFilling_mem_flatFockSpan
    {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : T.PosSemidef) (U : ℝ) (hU : 0 < U)
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hΦ : Φ ∈ generalFlatBandGroundSubmodule T U) :
    Φ ∈ Submodule.span ℂ
      {v | ∃ g, IsFlatSupported hT.1 g
        ∧ (generalOccFinset g).card = generalFlatBandDim T
        ∧ generalOccMonomial (eigenbasisAsBasis hT.1) g = v} := by
  have hray : rayleighOnVec (hubbardHamiltonian M T (U : ℂ)) Φ = 0 :=
    hamiltonian_rayleigh_zero_of_mem_groundSubmodule T U hΦ
  have hN : (fermionTotalNumber (2 * M + 1)).mulVec Φ = (generalFlatBandDim T : ℂ) • Φ := by
    have h := (Submodule.mem_inf.mp hΦ).2
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
    exact h
  set e := eigenbasisAsBasis hT.1 with he
  set b := generalOccBasis e with hb
  have hbcoe : ∀ h, (b h : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial e h :=
    fun h => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) h
  rw [← b.sum_repr Φ]
  refine Submodule.sum_mem _ fun g _ => ?_
  by_cases hcard : (generalOccFinset g).card = generalFlatBandDim T
  · by_cases hf : IsFlatSupported hT.1 g
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, hf, hcard, (hbcoe g).symm⟩)
    · obtain ⟨j, σ, hg1, hjne⟩ : ∃ j σ, g (j, σ) = 1 ∧ hT.1.eigenvalues j ≠ 0 := by
        unfold IsFlatSupported at hf
        push Not at hf
        obtain ⟨j, σ, hg1, hjne⟩ := hf
        exact ⟨j, σ, hg1, hjne⟩
      rw [groundState_generalOccBasis_repr_eq_zero_of_occupied hT U hU hray j σ hjne g hg1,
        zero_smul]
      exact Submodule.zero_mem _
  · rw [groundState_generalOccBasis_repr_eq_zero_of_card_ne hT.1 hN g hcard, zero_smul]
    exact Submodule.zero_mem _

end LatticeSystem.Fermion
