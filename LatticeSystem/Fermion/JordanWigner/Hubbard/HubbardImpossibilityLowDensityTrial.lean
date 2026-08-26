import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityTrialCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUVariational

/-!
# The spin-flip trial state of the low-density impossibility argument (Tasaki §11.1.1)

Tasaki's variational state for Theorem 11.4 is obtained from the fully polarized Slater
determinant `Φ↑` filling the up-modes `SUp` by adding one ↓ electron in the single-particle state
`v`: `Ψ = Ĉ†_↓(v)Φ↑` (eq. (11.1.6)).  This module defines that state
(`hubbardLowDensityTrialState`) and establishes the properties the variational estimate consumes:

* `Ψ` carries exactly one ↓ electron (`N̂_↓Ψ = Ψ`), which is the sector hypothesis of the on-site
  interaction layer, and exactly `|SUp| + 1` electrons in total;
* `Ψ ≠ 0` whenever `v ≠ 0`, so the Rayleigh quotient of the projected state is well posed;
* the ↓ occupation at a site contracts `Ψ` to a single creation on `Φ↑`;
* the hopping operator's commutation relations with a smeared creation — the same-spin one
  carrying the extra term `Ĉ†_σ(t·v)`, the cross-spin one a plain commutation — whence the
  kinetic energy of `Ψ` is `Σ_{j ∈ SUp} ε_j + ε` when `v` is an eigenvector of `t` for `ε`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.6)–(11.1.9), pp. 375–376; the trial state is Tasaki,
Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3, eq. (3.6), p. 506, and the parity bookkeeping
is the unnumbered substitution of eqs. (F.5)/(F.7) yielding eqs. (F.8)–(F.11), Appendix F,
pp. 545–546.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

open scoped BigOperators

variable {M : ℕ}

/-! ## The trial state -/

/-- **Tasaki's spin-flip trial state** (eq. (11.1.6)): `Ψ = Ĉ†_↓(v)Φ↑`, one ↓ electron in the
single-particle state `v` added to the fully polarized Slater determinant filling the up-modes
`SUp` of the single-particle basis `e`. -/
noncomputable def hubbardLowDensityTrialState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) : (Fin (2 * M + 2) → Fin 2) → ℂ :=
  (spinfulCreationFromVector M v 1).mulVec (spinfulGeneralBasisState e SUp ∅)

/-- **The fully polarized Slater determinant carries no ↓ electron**: `N̂_↓Φ↑ = 0` for the state
filling only up-modes.  This is the hypothesis shape of the parity core. -/
theorem fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1))) :
    (fermionTotalDownNumber M).mulVec (spinfulGeneralBasisState e SUp ∅) = 0 := by
  rw [fermionTotalDownNumber_mulVec_spinfulGeneralBasisState e SUp ∅, Finset.card_empty,
    Nat.cast_zero, zero_smul]

/-! ## Particle content of the trial state -/

/-- **The trial state carries exactly one ↓ electron**: `N̂_↓Ψ = Ψ`.  Adding a ↓ creation to a
fully polarized state raises the ↓ number by one, and the polarized state contributes nothing.
This is the sector hypothesis consumed by the on-site interaction layer. -/
theorem fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) :
    (fermionTotalDownNumber M).mulVec (hubbardLowDensityTrialState e SUp v)
      = hubbardLowDensityTrialState e SUp v := by
  rw [hubbardLowDensityTrialState, Matrix.mulVec_mulVec,
    fermionTotalDownNumber_mul_spinfulCreationFromVector, if_pos rfl, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty,
    Matrix.mulVec_zero, zero_add]

/-- **The trial state carries `|SUp| + 1` electrons**: `N̂Ψ = (|SUp| + 1)Ψ`, the `Ne`-electron
sector label of the variational estimate. -/
theorem fermionTotalNumber_mulVec_hubbardLowDensityTrialState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) :
    (fermionTotalNumber (2 * M + 1)).mulVec (hubbardLowDensityTrialState e SUp v)
      = ((SUp.card + 1 : ℕ) : ℂ) • hubbardLowDensityTrialState e SUp v := by
  have hN : (fermionTotalNumber (2 * M + 1)).mulVec (spinfulGeneralBasisState e SUp ∅)
      = ((SUp.card : ℕ) : ℂ) • spinfulGeneralBasisState e SUp ∅ := by
    rw [spinfulGeneralBasisState, fermionTotalNumber_mulVec_generalModeMonomial,
      spinfulSubsetPairList_length, Finset.card_empty]
    norm_num
  rw [hubbardLowDensityTrialState, Matrix.mulVec_mulVec,
    fermionTotalNumber_mul_spinfulCreationFromVector, Matrix.add_mulVec,
    ← Matrix.mulVec_mulVec, hN, Matrix.mulVec_smul, Nat.cast_add, Nat.cast_one, add_smul,
    one_smul]

/-- **The trial state is nonzero** for a nonzero single-particle state `v`.  Its squared norm is
`(Σ_x |v_x|²)‖Φ↑‖²`, a product of two nonzero factors. -/
theorem hubbardLowDensityTrialState_ne_zero
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    {v : Fin (M + 1) → ℂ} (hv : v ≠ 0) :
    hubbardLowDensityTrialState e SUp v ≠ 0 := by
  intro hzero
  have hnorm := dotProduct_star_self_spinfulCreationFromVector_of_downNumber_zero v
    (fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty e SUp)
  rw [show (spinfulCreationFromVector M v 1).mulVec (spinfulGeneralBasisState e SUp ∅)
      = hubbardLowDensityTrialState e SUp v from rfl, hzero, star_zero, zero_dotProduct] at hnorm
  rcases mul_eq_zero.mp hnorm.symm with h | h
  · exact hv (complexVec_eq_zero_of_star_dotProduct h)
  · exact spinfulGeneralBasisState_ne_zero e SUp ∅ (complexVec_eq_zero_of_star_dotProduct h)

/-- **The ↓ occupation contracts the trial state**: `n̂_{x↓}Ψ = v_x ĉ†_{x↓}Φ↑`.  The trial-state
form of the one-↓ contraction of the parity core. -/
theorem fermionDownNumber_mulVec_hubbardLowDensityTrialState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) (x : Fin (M + 1)) :
    (fermionDownNumber M x).mulVec (hubbardLowDensityTrialState e SUp v)
      = v x • (fermionDownCreation M x).mulVec (spinfulGeneralBasisState e SUp ∅) :=
  fermionDownNumber_mulVec_spinfulCreationFromVector_of_downNumber_zero v x
    (fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty e SUp)

/-! ## The hopping operator versus a smeared creation -/

/-- **Same-spin commutation of the hopping operator with a smeared creation**:
`Ĥ^σ Ĉ†_σ(w) = Ĉ†_σ(w) Ĥ^σ + Ĉ†_σ(t·w)`.  Passing `ĉ†_{x σ}` to the left through
`ĉ†_{iσ}ĉ_{jσ}` costs the contraction `δ_{jx}ĉ†_{iσ}`, and summing that contraction against the
coefficients `t_{ij}w_x` rebuilds the smeared creation of the transported vector `t·w`. -/
theorem hubbardKineticSpin_mul_spinfulCreationFromVector (M : ℕ)
    (t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (w : Fin (M + 1) → ℂ) (σ : Fin 2) :
    hubbardKineticSpin M t σ * spinfulCreationFromVector M w σ
      = spinfulCreationFromVector M w σ * hubbardKineticSpin M t σ
        + spinfulCreationFromVector M (t.mulVec w) σ := by
  have hkey : ∀ i j x : Fin (M + 1),
      fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) *
          fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)
        = (if j = x then fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) else 0)
          + fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ)) := by
    intro i j x
    have hcc : fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
        fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)
          = -(fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ)) :=
      eq_neg_of_add_eq_zero_left (spinful_creation_creation_anticomm_general M i x σ σ)
    have hac : fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) *
        fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)
          = (if j = x then (1 : ManyBodyOp (Fin (2 * M + 2))) else 0)
            - fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) := by
      by_cases hjx : j = x
      · subst hjx
        rw [if_pos rfl,
          fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number]
        rfl
      · have hne : spinfulIndex M j σ ≠ spinfulIndex M x σ := by
          intro h
          exact hjx ((spinfulIndex_eq_iff M j x σ σ).mp h).1
        rw [if_neg hjx, zero_sub]
        exact eq_neg_of_add_eq_zero_left
          (fermionMultiAnnihilation_creation_anticomm_of_ne hne)
    rw [Matrix.mul_assoc, hac, mul_sub, ← Matrix.mul_assoc, hcc, Matrix.neg_mul,
      Matrix.mul_assoc, sub_neg_eq_add]
    congr 1
    by_cases hjx : j = x
    · rw [if_pos hjx, if_pos hjx, Matrix.mul_one]
    · rw [if_neg hjx, if_neg hjx, Matrix.mul_zero]
  have hexpand : hubbardKineticSpin M t σ * spinfulCreationFromVector M w σ
      = ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ x : Fin (M + 1), (t i j * w x) •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) *
            fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)) := by
    rw [hubbardKineticSpin, spinfulCreationFromVector, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_smul]
  have hcross : spinfulCreationFromVector M w σ * hubbardKineticSpin M t σ
      = ∑ x : Fin (M + 1), ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (t i j * w x) •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))) := by
    rw [spinfulCreationFromVector, hubbardKineticSpin, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm (w x) (t i j)]
  have hdiag : ∀ i j : Fin (M + 1),
      (∑ x : Fin (M + 1), (t i j * w x) •
          (if j = x then fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) else 0))
        = (t i j * w j) • fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) := by
    intro i j
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
    · intro x _ hxj
      rw [if_neg (Ne.symm hxj), smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hsmeared : (∑ i : Fin (M + 1), ∑ j : Fin (M + 1),
      (t i j * w j) • fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ))
      = spinfulCreationFromVector M (t.mulVec w) σ := by
    rw [spinfulCreationFromVector]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    rfl
  have hswap : (∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ x : Fin (M + 1), (t i j * w x) •
        (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))))
      = ∑ x : Fin (M + 1), ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), (t i j * w x) •
        (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => (Finset.sum_comm :
      (∑ j : Fin (M + 1), ∑ x : Fin (M + 1), (t i j * w x) •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))))
        = _)]
    exact Finset.sum_comm
  rw [hexpand, hcross]
  rw [show (∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ x : Fin (M + 1), (t i j * w x) •
        (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ) *
          fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ)))
      = (∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ x : Fin (M + 1), (t i j * w x) •
          (if j = x then fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) else 0))
        + ∑ i : Fin (M + 1), ∑ j : Fin (M + 1), ∑ x : Fin (M + 1), (t i j * w x) •
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M x σ) *
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M i σ) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j σ))) from by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hkey i j x, smul_add]]
  rw [hswap, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hdiag i j, hsmeared]
  exact add_comm _ _

/-- **Cross-spin commutation of the hopping operator with a smeared creation**: for `σ ≠ τ`,
`Ĥ^σ` commutes with `Ĉ†_τ(w)`.  Each hopping bilinear is even and lives at `σ` modes disjoint from
the `τ` modes, so no contraction term survives — in contrast with the same-spin relation. -/
theorem hubbardKineticSpin_commute_spinfulCreationFromVector_of_ne (M : ℕ)
    (t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) (w : Fin (M + 1) → ℂ) {σ τ : Fin 2}
    (hστ : σ ≠ τ) :
    Commute (hubbardKineticSpin M t σ) (spinfulCreationFromVector M w τ) := by
  have hne : ∀ a b : Fin (M + 1), spinfulIndex M a σ ≠ spinfulIndex M b τ := by
    intro a b h
    exact hστ ((spinfulIndex_eq_iff M a b σ τ).mp h).2
  rw [hubbardKineticSpin, spinfulCreationFromVector]
  refine Commute.sum_left _ _ _ fun i _ => ?_
  refine Commute.sum_left _ _ _ fun j _ => ?_
  refine Commute.smul_left ?_ _
  refine Commute.sum_right _ _ _ fun x _ => ?_
  refine Commute.smul_right ?_ _
  exact fermionMultiHopping_commute_fermionMultiCreation_of_ne (hne i x) (hne j x)

/-! ## The kinetic energy of the trial state -/

/-- **The trial state is a kinetic eigenvector**: if `t·v = ε v` then
`Ĥ_kin Ψ = (Σ_{j ∈ SUp} ε_j + ε)Ψ`, the kinetic energy of the spin-flipped state, which the book
records as unnumbered running text on p. 375.  The up fiber passes through the ↓ creation and
reproduces the Slater energy of `Φ↑`; the down fiber annihilates `Φ↑` and contributes only the
transported creation `Ĉ†_↓(t·v) = ε Ĉ†_↓(v)`. -/
theorem hubbardKinetic_mulVec_hubbardLowDensityTrialState
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ} {lam : ℂ}
    (hv : t.mulVec v = lam • v) :
    (hubbardKinetic M t).mulVec (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v)
      = (occupiedEigenEnergy hT SUp ∅ + lam) •
        hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v := by
  have h0 : (fermionTotalDownNumber M).mulVec
      (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) = 0 :=
    fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty _ SUp
  have hdown : (hubbardKineticSpin M t 1).mulVec
      (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) = 0 :=
    hubbardKineticSpin_one_mulVec_eq_zero_of_downNumber_zero M t h0
  have hup : (hubbardKineticSpin M t 0).mulVec
      (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)
      = occupiedEigenEnergy hT SUp ∅ • spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅ := by
    have hsum := hubbardKinetic_mulVec_spinfulGeneralBasisState hT SUp ∅
    rw [hubbardKinetic_eq_hubbardKineticSpin_add, Matrix.add_mulVec, hdown, add_zero] at hsum
    exact hsum
  rw [hubbardLowDensityTrialState, hubbardKinetic_eq_hubbardKineticSpin_add, Matrix.add_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    (hubbardKineticSpin_commute_spinfulCreationFromVector_of_ne M t v
      (by decide : (0 : Fin 2) ≠ 1)).eq,
    hubbardKineticSpin_mul_spinfulCreationFromVector M t v 1, hv,
    spinfulCreationFromVector_smul, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hup, hdown, Matrix.mulVec_zero, Matrix.mulVec_smul,
    Matrix.smul_mulVec, zero_add, add_smul]

end LatticeSystem.Fermion
