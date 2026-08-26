import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityTrial
import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandMultiplet
import LatticeSystem.Math.MatrixAnalysis.CourantFischer

/-!
# Operator core of the Roth variational estimate (Tasaki §11.1.1)

The Roth state `Ψ̃ = Ψ − ν̂Ψ` of the low-density impossibility argument has a doubly occupied
component `ν̂Ψ` whose energy must be estimated.  This module supplies the operator identities that
carry that estimate, all stated on the fully polarized Slater determinant `Φ↑` and its site
occupations rather than on the trial state's Rayleigh quotient:

* the up-electron count of `Φ↑` and the fact that an up occupation keeps `Φ↑` free of ↓ electrons;
* the commutation of the ↑ kinetic fiber with the ↓ annihilations, which is the hypothesis the
  parity δ factorisation consumes;
* the explicit form `ν̂Ψ = Σ_x v_x ĉ†_{x↓}(n̂_{x↑}Φ↑)` of the doubly occupied component and the
  resulting diagonal quadratic form `⟨ν̂Ψ, X ν̂Ψ⟩ = Σ_x |v_x|²⟨n̂_{x↑}Φ↑, X n̂_{x↑}Φ↑⟩`;
* the **number sandwich** `n̂_{xσ} Ĥ^σ n̂_{xσ} = n̂_{xσ}Ĥ^σ − Σ_z t_{xz} ĉ†_{xσ}ĉ_{zσ}
  + t_{xx} n̂_{xσ}`, the exact canonical-anticommutation identity that replaces the mode-expansion
  evaluation of the majority-spin correction;
* the Loewner-to-Rayleigh step for the minority spin, which bounds the ↓ kinetic energy of any
  one-↓-electron vector by a spectral bound times its squared norm.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.9)/(11.1.10), p. 376; the computation replaces
Tasaki, Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3, Appendix F, eqs. (F.4)–(F.11),
pp. 545–546, whose Fourier mode representation is not needed here.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

open scoped BigOperators

variable {M : ℕ}

/-! ## The fully polarized Slater determinant -/

/-- **The up-electron count of the fully polarized Slater determinant**: `N̂_↑Φ↑ = |SUp|Φ↑`.  The
total count is `|SUp|` and the ↓ count is `0`, so the whole count sits in the ↑ channel. -/
theorem fermionTotalUpNumber_mulVec_spinfulGeneralBasisState_empty
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1))) :
    (fermionTotalUpNumber M).mulVec (spinfulGeneralBasisState e SUp ∅)
      = ((SUp.card : ℕ) : ℂ) • spinfulGeneralBasisState e SUp ∅ := by
  have htot := fermionTotalNumber_mulVec_spinfulGeneralBasisState_empty e SUp
  rw [fermionTotalNumber_eq_up_add_down, Matrix.add_mulVec,
    fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty e SUp, add_zero] at htot
  exact htot

/-- **An up occupation preserves full ↓ polarisation**: if `N̂_↓Φ = 0` then
`N̂_↓(n̂_{x↑}Φ) = 0`.  The two number operators commute, so the ↓ count passes through the ↑
occupation and meets the vanishing hypothesis. -/
theorem fermionTotalDownNumber_mulVec_fermionUpNumber_mulVec_eq_zero (x : Fin (M + 1))
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    (fermionTotalDownNumber M).mulVec ((fermionUpNumber M x).mulVec Φ) = 0 := by
  have hcomm : Commute (fermionTotalDownNumber M) (fermionUpNumber M x) := by
    rw [fermionTotalDownNumber]
    refine Commute.sum_left _ _ _ fun y _ => ?_
    exact fermionMultiNumber_commute (2 * M + 1) (spinfulIndex M y 1) (spinfulIndex M x 0)
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΦ, Matrix.mulVec_zero]

/-! ## The ↑ kinetic fiber versus the ↓ ladder -/

/-- **The ↑ kinetic fiber commutes with every ↓ annihilation**: `Commute Ĥ^↑ ĉ_{z↓}`.  Each hopping
bilinear of `Ĥ^↑` is even and lives at ↑ modes disjoint from the ↓ modes.  This is the hypothesis
shape consumed by the parity δ factorisation. -/
theorem hubbardKineticSpin_zero_commute_fermionDownAnnihilation
    (t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (z : Fin (M + 1)) :
    Commute (hubbardKineticSpin M t 0) (fermionDownAnnihilation M z) := by
  rw [hubbardKineticSpin]
  refine Commute.sum_left _ _ _ fun i _ => ?_
  refine Commute.sum_left _ _ _ fun j _ => ?_
  exact (upHopping_commute_fermionDownAnnihilation M i j z).smul_left (t i j)

/-! ## The doubly occupied component of the trial state -/

/-- **The doubly occupied component of the trial state**:
`ν̂Ψ = Σ_x v_x ĉ†_{x↓}(n̂_{x↑}Φ↑)`.  The ↓ occupation at `x` contracts `Ψ` to `v_x ĉ†_{x↓}Φ↑`, and
the ↑ occupation at `x` commutes past the ↓ creation. -/
theorem hubbardOnSiteInteraction_one_mulVec_hubbardLowDensityTrialState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) :
    (hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v)
      = ∑ x : Fin (M + 1), v x • (fermionDownCreation M x).mulVec
          ((fermionUpNumber M x).mulVec (spinfulGeneralBasisState e SUp ∅)) := by
  rw [hubbardOnSiteInteraction, Matrix.sum_mulVec]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [one_smul, ← Matrix.mulVec_mulVec,
    fermionDownNumber_mulVec_hubbardLowDensityTrialState e SUp v x, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec,
    show fermionUpNumber M x * fermionDownCreation M x
        = fermionDownCreation M x * fermionUpNumber M x from
      (upHopping_commute_fermionDownCreation M x x x).eq,
    ← Matrix.mulVec_mulVec]

/-- **The δ-factorised quadratic form of the doubly occupied component**: for `X` commuting with
every ↓ annihilation,
`⟨ν̂Ψ, X ν̂Ψ⟩ = Σ_x conj(v_x)v_x ⟨n̂_{x↑}Φ↑, X n̂_{x↑}Φ↑⟩`.  The off-diagonal terms are killed by
the δ of the parity factorisation, because the two Slater factors sit on opposite sides of the
same inner product.  This single identity carries the double-occupancy weight, the majority-spin
correction and the minority-spin bound. -/
theorem dotProduct_star_hubbardOnSiteInteraction_trial_sandwich
    (X : ManyBodyOp (Fin (2 * M + 2)))
    (hX : ∀ z : Fin (M + 1), Commute X (fermionDownAnnihilation M z))
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) :
    star ((hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v)) ⬝ᵥ
        X.mulVec ((hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v))
      = ∑ x : Fin (M + 1), (star (v x) * v x) *
          (star ((fermionUpNumber M x).mulVec (spinfulGeneralBasisState e SUp ∅)) ⬝ᵥ
            X.mulVec ((fermionUpNumber M x).mulVec (spinfulGeneralBasisState e SUp ∅))) := by
  have hpol : ∀ x : Fin (M + 1), (fermionTotalDownNumber M).mulVec
      ((fermionUpNumber M x).mulVec (spinfulGeneralBasisState e SUp ∅)) = 0 := fun x =>
    fermionTotalDownNumber_mulVec_fermionUpNumber_mulVec_eq_zero x
      (fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty e SUp)
  rw [hubbardOnSiteInteraction_one_mulVec_hubbardLowDensityTrialState e SUp v, star_sum,
    sum_dotProduct]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.mulVec_sum, dotProduct_sum, Finset.sum_eq_single y]
  · rw [star_smul, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
      dotProduct_fermionDownCreation_sandwich X hX (hpol y) y y, if_pos rfl, one_mul,
      smul_eq_mul, smul_eq_mul, ← mul_assoc]
  · intro x _ hxy
    rw [star_smul, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul,
      dotProduct_fermionDownCreation_sandwich X hX (hpol x) x y, if_neg hxy, zero_mul,
      smul_zero, smul_zero]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

/-- **The up occupation moves across the inner product**:
`⟨n̂_{x↑}Φ, X n̂_{x↑}Φ⟩ = ⟨Φ, (n̂_{x↑} X n̂_{x↑})Φ⟩`, because the occupation operator is Hermitian.
This is what turns the δ-factorised quadratic form into a sandwich that the number identities can
evaluate. -/
theorem dotProduct_star_fermionUpNumber_mulVec_sandwich (x : Fin (M + 1))
    (X : ManyBodyOp (Fin (2 * M + 2))) (Φ : (Fin (2 * M + 2) → Fin 2) → ℂ) :
    star ((fermionUpNumber M x).mulVec Φ) ⬝ᵥ X.mulVec ((fermionUpNumber M x).mulVec Φ)
      = star Φ ⬝ᵥ (fermionUpNumber M x * X * fermionUpNumber M x).mulVec Φ := by
  rw [star_mulVec_dotProduct,
    show (fermionUpNumber M x)ᴴ = fermionUpNumber M x from
      (fermionMultiNumber_isHermitian (2 * M + 1) (spinfulIndex M x 0)).eq,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-! ## The number sandwich -/

/-- **The number sandwich of the kinetic fiber**:
`n̂_{xσ} Ĥ^σ n̂_{xσ} = n̂_{xσ}Ĥ^σ − Σ_z t_{xz} ĉ†_{xσ}ĉ_{zσ} + t_{xx} n̂_{xσ}`.  Only the hopping
terms creating at `x` survive the right occupation, and among those only the one annihilating at
`x` survives the left occupation as well; the diagonal term is added back because the correction
sum overcounts it.  This exact canonical-anticommutation identity replaces the Fourier mode
evaluation of the majority-spin correction in Tasaki, Prog. Theor. Phys. **99** (1998) 489,
Appendix F, eq. (F.9), p. 546.  It is spin-agnostic: the whole spin-resolved layer is stated per
`σ`, and both spin tags occur in the argument that consumes it. -/
theorem fermionMultiNumber_mul_hubbardKineticSpin_mul_self (M : ℕ)
    (t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (σ : Fin 2) (x : Fin (M + 1)) :
    fermionMultiNumber (2 * M + 1) (spinfulIndex M x σ) * hubbardKineticSpin M t σ *
        fermionMultiNumber (2 * M + 1) (spinfulIndex M x σ)
      = fermionMultiNumber (2 * M + 1) (spinfulIndex M x σ) * hubbardKineticSpin M t σ
        - (∑ z : Fin (M + 1), t x z • (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ)))
        + t x x • fermionMultiNumber (2 * M + 1) (spinfulIndex M x σ) := by
  set n := fermionMultiNumber (2 * M + 1) (spinfulIndex M x σ) with hn
  have hnC : n * fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)
      = fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) :=
    fermionMultiNumber_mul_fermionMultiCreation_eq_fermionMultiCreation _ _
  have hCn : fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) * n = 0 :=
    fermionMultiCreation_mul_fermionMultiNumber_eq_zero _ _
  have hnA : n * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) = 0 :=
    fermionMultiNumber_mul_fermionMultiAnnihilation_eq_zero _ _
  have hnn : n * n = n := fermionMultiNumber_sq _ _
  have hne : ∀ i : Fin (M + 1), i ≠ x → spinfulIndex M x σ ≠ spinfulIndex M i σ := by
    intro i hix h
    exact hix (((spinfulIndex_eq_iff M x i σ σ).mp h).1).symm
  have hterm : ∀ i j : Fin (M + 1),
      n * (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) * n
        = n * (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
          - (if i = x then
              (if j = x then (0 : ManyBodyOp (Fin (2 * M + 2)))
                else fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
              else 0) := by
    intro i j
    by_cases hi : i = x
    · rw [hi, if_pos rfl]
      by_cases hj : j = x
      · rw [hj, if_pos rfl, sub_zero,
          show fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) = n from rfl,
          hnn, hnn]
      · have hcomA : n * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)
            = fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) * n :=
          (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne (hne j hj)).eq
        have hL : n * (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
            = fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) := by
          rw [← Matrix.mul_assoc, hnC]
        rw [if_neg hj, hL, sub_self, Matrix.mul_assoc, ← hcomA, ← Matrix.mul_assoc, hCn,
          Matrix.zero_mul]
    · have hcomC : n * fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ)
          = fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) * n :=
        (fermionMultiNumber_commute_fermionMultiCreation_of_ne (hne i hi)).eq
      rw [if_neg hi, sub_zero]
      by_cases hj : j = x
      · have hzero : n * (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ)) = 0 := by
          rw [← Matrix.mul_assoc, hcomC, Matrix.mul_assoc, hnA, Matrix.mul_zero]
        rw [hj, hzero, Matrix.zero_mul]
      · have hcomA : n * fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)
            = fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) * n :=
          (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne (hne j hj)).eq
        have hmove : n * (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
            = fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) * n := by
          rw [← Matrix.mul_assoc, hcomC, Matrix.mul_assoc, hcomA, ← Matrix.mul_assoc]
        rw [hmove, Matrix.mul_assoc, hnn]
  have hexpand : n * hubbardKineticSpin M t σ * n
      = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), t i j •
          (n * (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) * n) := by
    rw [hubbardKineticSpin, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hplain : n * hubbardKineticSpin M t σ
      = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), t i j •
          (n * (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))) := by
    rw [hubbardKineticSpin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_smul]
  have hcorr : (∑ i : Fin (M + 1), ∑ j : Fin (M + 1), t i j •
        (if i = x then
          (if j = x then (0 : ManyBodyOp (Fin (2 * M + 2)))
            else fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
          else 0))
      = (∑ z : Fin (M + 1), t x z • (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
          fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z σ))) - t x x • n := by
    rw [Finset.sum_eq_single x]
    · have hsplit : ∀ j : Fin (M + 1),
          t x j • (if x = x then
              (if j = x then (0 : ManyBodyOp (Fin (2 * M + 2)))
                else fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
              else 0)
            = t x j • (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
                fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
              - (if j = x then t x j • (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) else 0) := by
        intro j
        rw [if_pos rfl]
        by_cases hj : j = x
        · rw [if_pos hj, if_pos hj, smul_zero, sub_self]
        · rw [if_neg hj, if_neg hj, sub_zero]
      rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hsplit j,
        Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ x fun j => t x j •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)),
        if_pos (Finset.mem_univ x),
        show fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x σ) = n from rfl]
    · intro i _ hix
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg hix, smul_zero]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  have hmain : n * hubbardKineticSpin M t σ * n
      = n * hubbardKineticSpin M t σ
        - ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), t i j •
          (if i = x then
            (if j = x then (0 : ManyBodyOp (Fin (2 * M + 2)))
              else fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
                fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))
            else 0) := by
    rw [hexpand, hplain, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_sub, hterm i j]
  rw [hmain, hcorr]
  abel

/-! ## The minority-spin Loewner step -/

open scoped MatrixOrder in
/-- **The ↓ kinetic energy of a one-↓-electron vector**: if every single-particle level satisfies
`ε_j ≤ e` and `N̂_↓w = w`, then `⟨w, Ĥ^↓w⟩ ≤ e‖w‖²`.  The Loewner bound `Ĥ^↓ ≤ e N̂_↓` transports to
the Rayleigh quotient, where the ↓ number operator acts as the identity. -/
theorem rayleighOnVec_hubbardKineticSpin_one_le_of_downNumber_one
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) {e : ℝ}
    (he : ∀ j : Fin (M + 1), hT.eigenvalues j ≤ e)
    {w : (Fin (2 * M + 2) → Fin 2) → ℂ} (hw : (fermionTotalDownNumber M).mulVec w = w) :
    rayleighOnVec (hubbardKineticSpin M t 1) w ≤ e * (star w ⬝ᵥ w).re := by
  have hmono := rayleighOnVec_mono (hubbardKineticSpin_le_smul_sum_spinSiteNumber hT 1 he) w
  rw [show (∑ i : Fin (M + 1), fermionMultiNumber (2 * M + 1) (spinfulIndex M i 1))
      = fermionTotalDownNumber M from rfl, rayleighOnVec_real_smul] at hmono
  unfold rayleighOnVec at hmono ⊢
  rwa [hw] at hmono

end LatticeSystem.Fermion
