import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowDensityRothCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardOnSiteInteractionSingleDown
import LatticeSystem.Math.MatrixAnalysis.RowSumEigenvalueBound

/-!
# Roth's variational estimate for the low-density impossibility argument (Tasaki §11.1.1)

The spin-flip trial state `Ψ = Ĉ†_↓(v)Φ↑` has a doubly occupied component that costs an energy
proportional to the interaction strength; Roth's device removes it by passing to
`Ψ̃ = Ψ − ν̂Ψ`, on which the Coulomb interaction vanishes identically.  This module defines that
state and proves the variational bound it was built for: the Rayleigh quotient of the **full**
Hubbard Hamiltonian at `Ψ̃` exceeds the trial kinetic energy by at most `8K|SUp|/(M+1)`, uniformly
in the coupling `U`.

The estimate assembles four ingredients:

* the exact double-occupancy weight `⟨Ψ, ν̂Ψ⟩ = (|SUp|/(M+1))‖Φ↑‖²`, which needs no delocalisation
  assumption on the occupied modes because the ↓ orbital `v` alone is uniform;
* the majority-spin correction, evaluated by the number sandwich and bounded through the row-sum
  eigenvalue bound `|ε_j| ≤ K` and `|t_{xx}| ≤ K`;
* the minority-spin correction, bounded by the Loewner estimate `Ĥ^↓ ≤ K N̂_↓` rather than
  evaluated;
* the norm identity `‖Ψ̃‖² = ‖Ψ‖² − ⟨Ψ, ν̂Ψ⟩`, positive because `2|SUp| ≤ M + 1`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.9)/(11.1.10), p. 376; the argument is Tasaki,
Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3, Appendix F, eqs. (F.1)–(F.3) and (F.8)–(F.13),
pp. 545–546, together with the boundedness assumption on `max_x t_{x,x}`, `max_x Σ_y |t_{x,y}|`
and `ε_1` stated on p. 547.  The Fourier mode representation (F.4)–(F.7), the exact value of the
majority-spin correction (F.9) and the two-point remainder of (F.10)/(F.11) are replaced here by
the sandwich identity and the operator bound, so they are not reproduced.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math

open scoped BigOperators

variable {M : ℕ}

/-! ## The Roth state -/

/-- **Roth's projected trial state** (eq. (11.1.9)): `Ψ̃ = Ψ − ν̂Ψ`, the spin-flip trial state with
its doubly occupied component removed.  On the one-↓-electron sector this is the Gutzwiller
projection `P̂₀Ψ`, and the Coulomb interaction annihilates it at every coupling. -/
noncomputable def hubbardLowDensityRothState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) : (Fin (2 * M + 2) → Fin 2) → ℂ :=
  hubbardLowDensityTrialState e SUp v
    - (hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v)

/-- **The Roth state stays in the `|SUp| + 1`-electron sector**: `N̂Ψ̃ = (|SUp| + 1)Ψ̃`.  The
double-occupancy operator commutes with the total particle number, so both terms of the difference
carry the same electron count. -/
theorem fermionTotalNumber_mulVec_hubbardLowDensityRothState
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) :
    (fermionTotalNumber (2 * M + 1)).mulVec (hubbardLowDensityRothState e SUp v)
      = ((SUp.card + 1 : ℕ) : ℂ) • hubbardLowDensityRothState e SUp v := by
  have hcomm : (fermionTotalNumber (2 * M + 1)).mulVec
      ((hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v))
      = ((SUp.card + 1 : ℕ) : ℂ) •
        (hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v) := by
    rw [Matrix.mulVec_mulVec, ← (hubbardOnSiteInteraction_commute_fermionTotalNumber M 1).eq,
      ← Matrix.mulVec_mulVec, fermionTotalNumber_mulVec_hubbardLowDensityTrialState e SUp v,
      Matrix.mulVec_smul]
  rw [hubbardLowDensityRothState, Matrix.mulVec_sub,
    fermionTotalNumber_mulVec_hubbardLowDensityTrialState e SUp v, hcomm, smul_sub]

/-! ## The doubly occupied component -/

/-- The uniform-modulus hypothesis makes each coefficient's squared modulus the reciprocal of the
number of sites: `conj(v_x)v_x = 1/(M+1)` as a complex scalar. -/
private theorem star_mul_self_of_uniformModulus {v : Fin (M + 1) → ℂ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1)) (x : Fin (M + 1)) :
    star (v x) * v x = ((1 / ((M : ℝ) + 1) : ℝ) : ℂ) := by
  rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hmod x]

/-- **The doubly occupied component absorbs the coefficient weights**: for `X` commuting with the
↓ annihilations, `⟨ν̂Ψ, X ν̂Ψ⟩ = (1/(M+1)) Σ_x ⟨Φ↑, (n̂_{x↑} X n̂_{x↑})Φ↑⟩`.  The δ factorisation of
the parity core diagonalises the double sum, the uniform modulus pulls the common weight out, and
the Hermitian occupation operators fold into a sandwich. -/
private theorem dotProduct_star_doubleOccupancy_sandwich
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1))
    (X : ManyBodyOp (Fin (2 * M + 2)))
    (hX : ∀ z : Fin (M + 1), Commute X (fermionDownAnnihilation M z)) :
    star ((hubbardOnSiteInteraction M 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v)) ⬝ᵥ
        X.mulVec ((hubbardOnSiteInteraction M 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v))
      = ((1 / ((M : ℝ) + 1) : ℝ) : ℂ) * ∑ x : Fin (M + 1),
          (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
            (fermionUpNumber M x * X * fermionUpNumber M x).mulVec
              (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)) := by
  rw [dotProduct_star_hubbardOnSiteInteraction_trial_sandwich X hX (eigenbasisAsBasis hT) SUp v,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [star_mul_self_of_uniformModulus hmod x,
    dotProduct_star_fermionUpNumber_mulVec_sandwich x X
      (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)]

/-- **The doubly occupied weight is a projection expectation**: `⟨Ψ, ν̂Ψ⟩ = ⟨ν̂Ψ, ν̂Ψ⟩`, because the
double-occupancy operator is Hermitian and idempotent on the one-↓-electron sector. -/
private theorem dotProduct_star_hubbardOnSiteInteraction_eq_self
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp : Finset (Fin (M + 1)))
    (v : Fin (M + 1) → ℂ) :
    star (hubbardLowDensityTrialState e SUp v) ⬝ᵥ
        (hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v)
      = star ((hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v)) ⬝ᵥ
          (hubbardOnSiteInteraction M 1).mulVec (hubbardLowDensityTrialState e SUp v) := by
  rw [star_mulVec_dotProduct,
    show (hubbardOnSiteInteraction M 1)ᴴ = hubbardOnSiteInteraction M 1 from
      (hubbardOnSiteInteraction_isHermitian M (by simp)).eq,
    hubbardOnSiteInteraction_mulVec_mulVec_of_downNumber_one M
      (fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState e SUp v)]

/-! ## The two norms -/

/-- **The trial state is normalised against the polarized Slater determinant**:
`⟨Ψ, Ψ⟩ = ⟨Φ↑, Φ↑⟩` when the ↓ orbital has uniform modulus, since its coefficient weights sum to
one. -/
theorem dotProduct_star_self_hubbardLowDensityTrialState
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1)) :
    star (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v) ⬝ᵥ
        hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v
      = star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅ := by
  have hne : ((M : ℂ) + 1) ≠ 0 := by
    have hcast : ((M + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero M)
    push_cast at hcast
    exact hcast
  have hcoef : (∑ x : Fin (M + 1), star (v x) * v x) = 1 := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) =>
        star_mul_self_of_uniformModulus hmod x,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have h := dotProduct_star_self_spinfulCreationFromVector_of_downNumber_zero v
    (fermionTotalDownNumber_mulVec_spinfulGeneralBasisState_empty (eigenbasisAsBasis hT) SUp)
  rw [show (spinfulCreationFromVector M v 1).mulVec
        (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)
      = hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v from rfl, hcoef, one_mul] at h
  exact h

/-- **The ↑ occupations sum to the electron count**: `Σ_x ⟨Φ↑, n̂_{x↑}Φ↑⟩ = |SUp|⟨Φ↑, Φ↑⟩`, since
the site occupations add up to the total ↑ particle number, of which the polarized Slater
determinant is an eigenvector. -/
private theorem sum_dotProduct_star_fermionUpNumber
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) :
    (∑ x : Fin (M + 1),
        star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          (fermionUpNumber M x).mulVec (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅))
      = ((SUp.card : ℕ) : ℂ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) := by
  rw [show (∑ x : Fin (M + 1),
        star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          (fermionUpNumber M x).mulVec (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅))
      = star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
        (fermionTotalUpNumber M).mulVec
          (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) from by
    rw [fermionTotalUpNumber, Matrix.sum_mulVec, dotProduct_sum],
    fermionTotalUpNumber_mulVec_spinfulGeneralBasisState_empty, dotProduct_smul, smul_eq_mul]

/-- **The double-occupancy weight** (replacing eq. (F.8)): `⟨Ψ, ν̂Ψ⟩ = (|SUp|/(M+1))⟨Φ↑, Φ↑⟩`.
The δ factorisation reduces the weight to the ↑ occupations of the polarized Slater determinant,
whose sum is its electron count `|SUp|`; the uniform modulus of the ↓ orbital supplies the factor
`1/(M+1)`.  No delocalisation of the occupied modes enters. -/
theorem dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1)) :
    star (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v) ⬝ᵥ
        (hubbardOnSiteInteraction M 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v)
      = (((SUp.card : ℝ) / ((M : ℝ) + 1) : ℝ) : ℂ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) := by
  have h1 := dotProduct_star_doubleOccupancy_sandwich hT SUp hmod 1 fun _ => Commute.one_left _
  rw [Matrix.one_mulVec] at h1
  have hn : ∀ x : Fin (M + 1),
      fermionUpNumber M x * 1 * fermionUpNumber M x = fermionUpNumber M x := by
    intro x
    rw [Matrix.mul_one]
    exact fermionMultiNumber_sq (2 * M + 1) (spinfulIndex M x 0)
  have hsum : (∑ x : Fin (M + 1),
        star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          (fermionUpNumber M x * 1 * fermionUpNumber M x).mulVec
            (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅))
      = ((SUp.card : ℕ) : ℂ) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => by rw [hn x],
      sum_dotProduct_star_fermionUpNumber hT SUp]
  rw [dotProduct_star_hubbardOnSiteInteraction_eq_self, h1, hsum, ← mul_assoc]
  congr 1
  push_cast
  ring

/-! ## The majority-spin correction -/

/-- **The summed number sandwich of the ↑ kinetic fiber** (replacing eq. (F.9)):
`Σ_x ⟨Φ↑, (n̂_{x↑} Ĥ^↑ n̂_{x↑})Φ↑⟩ = E↑|SUp|⟨Φ↑,Φ↑⟩ − E↑⟨Φ↑,Φ↑⟩ + Σ_x t_{xx}⟨Φ↑, n̂_{x↑}Φ↑⟩`.
The three terms come from the sandwich identity: the polarized Slater determinant is an
eigenvector of `Ĥ^↑`, the double hopping sum reassembles `⟨Φ↑, Ĥ^↑Φ↑⟩` by the very definition of
the kinetic fiber, and the ↑ occupations sum to the electron count. -/
private theorem dotProduct_star_kineticSandwich_sum
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) :
    (∑ x : Fin (M + 1),
        star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          (fermionUpNumber M x * hubbardKineticSpin M t 0 * fermionUpNumber M x).mulVec
            (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅))
      = occupiedEigenEnergy hT SUp ∅ * ((SUp.card : ℕ) : ℂ) *
          (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
            spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)
        - occupiedEigenEnergy hT SUp ∅ *
          (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
            spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)
        + ∑ x : Fin (M + 1), t x x *
          (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
            (fermionUpNumber M x).mulVec
              (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)) := by
  have hHphi : (hubbardKineticSpin M t 0).mulVec
      (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)
      = occupiedEigenEnergy hT SUp ∅ • spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅ :=
    hubbardKineticSpin_zero_mulVec_spinfulGeneralBasisState_empty hT SUp
  have hterm : ∀ x : Fin (M + 1),
      star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          (fermionUpNumber M x * hubbardKineticSpin M t 0 * fermionUpNumber M x).mulVec
            (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)
        = occupiedEigenEnergy hT SUp ∅ *
            (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
              (fermionUpNumber M x).mulVec
                (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅))
          - (∑ z : Fin (M + 1), t x z *
              (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
                (fermionMultiCreation (2 * M + 1) (spinfulIndex M x 0) *
                  fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)).mulVec
                  (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)))
          + t x x *
            (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
              (fermionUpNumber M x).mulVec
                (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)) := by
    intro x
    have hR6 : fermionUpNumber M x * hubbardKineticSpin M t 0 * fermionUpNumber M x
        = fermionUpNumber M x * hubbardKineticSpin M t 0
          - (∑ z : Fin (M + 1), t x z • (fermionMultiCreation (2 * M + 1) (spinfulIndex M x 0) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)))
          + t x x • fermionUpNumber M x :=
      fermionMultiNumber_mul_hubbardKineticSpin_mul_self M t 0 x
    rw [hR6, Matrix.add_mulVec, Matrix.sub_mulVec, dotProduct_add, dotProduct_sub,
      ← Matrix.mulVec_mulVec, hHphi, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.sum_mulVec, dotProduct_sum]
    refine congrArg₂ (· + ·) (congrArg₂ (· - ·) rfl ?_) rfl
    exact Finset.sum_congr rfl fun z _ => by rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hdouble : (∑ x : Fin (M + 1), ∑ z : Fin (M + 1), t x z *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          (fermionMultiCreation (2 * M + 1) (spinfulIndex M x 0) *
            fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)).mulVec
            (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)))
      = occupiedEigenEnergy hT SUp ∅ *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) := by
    have hexp : star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
        (hubbardKineticSpin M t 0).mulVec
          (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)
        = ∑ x : Fin (M + 1), ∑ z : Fin (M + 1), t x z *
          (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
            (fermionMultiCreation (2 * M + 1) (spinfulIndex M x 0) *
              fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M z 0)).mulVec
              (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅)) := by
      rw [hubbardKineticSpin, Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Matrix.sum_mulVec, dotProduct_sum]
      exact Finset.sum_congr rfl fun z _ => by
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [← hexp, hHphi, dotProduct_smul, smul_eq_mul]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hterm x, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, sum_dotProduct_star_fermionUpNumber hT SUp,
    hdouble, mul_assoc]

open scoped ComplexOrder in
/-- **The majority-spin correction is bounded by the density** (replacing eq. (F.9)):
`⟨ν̂Ψ, Ĥ^↑ν̂Ψ⟩ ≤ E↑⟨Ψ, ν̂Ψ⟩ + 2K(|SUp|/(M+1))⟨Φ↑,Φ↑⟩`.  The exact sandwich value is
`E↑|SUp|‖Φ↑‖² − E↑‖Φ↑‖² + Σ_x t_{xx}⟨Φ↑, n̂_{x↑}Φ↑⟩` divided by `M+1`; the first term is the
announced main term, and the two remaining ones are bounded by `|E↑| ≤ |SUp|K` and
`|t_{xx}| ≤ K` against the nonnegative occupations, whose sum is `|SUp|‖Φ↑‖²`. -/
theorem rayleighOnVec_hubbardKineticSpin_zero_doubleOccupancy_le
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ} {K : ℝ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1))
    (hK : ∀ x : Fin (M + 1), ∑ y : Fin (M + 1), ‖t x y‖ ≤ K) :
    rayleighOnVec (hubbardKineticSpin M t 0)
        ((hubbardOnSiteInteraction M 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v))
      ≤ (occupiedEigenEnergy hT SUp ∅).re *
          (((SUp.card : ℝ) / ((M : ℝ) + 1)) *
            (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
              spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅).re)
        + 2 * K * ((SUp.card : ℝ) / ((M : ℝ) + 1)) *
          (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
            spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅).re := by
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  set Φ := spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅ with hΦ
  have hsand := dotProduct_star_doubleOccupancy_sandwich hT SUp hmod (hubbardKineticSpin M t 0)
    (hubbardKineticSpin_zero_commute_fermionDownAnnihilation t)
  rw [dotProduct_star_kineticSandwich_sum hT SUp, ← hΦ] at hsand
  have hoccsum := sum_dotProduct_star_fermionUpNumber hT SUp
  rw [← hΦ] at hoccsum
  -- the polarized Slater norm is a nonnegative real
  have hPc : star Φ ⬝ᵥ Φ = (((star Φ ⬝ᵥ Φ).re : ℝ) : ℂ) := by
    refine (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr ?_)).symm
    rw [dotProduct_star_self_eq_ofReal, Complex.ofReal_im]
  have hPnonneg : 0 ≤ (star Φ ⬝ᵥ Φ).re := by
    rw [dotProduct_star_self_eq_ofReal, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  -- each site occupation expectation is a nonnegative real
  have hnumPSD : ∀ x : Fin (M + 1), (fermionUpNumber M x).PosSemidef := by
    intro x
    rw [show fermionUpNumber M x
        = (fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 0))ᴴ *
          fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M x 0) from by
      rw [fermionMultiAnnihilation_conjTranspose]; rfl]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hGle : ∀ x : Fin (M + 1), (0 : ℂ) ≤ star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ :=
    fun x => (hnumPSD x).dotProduct_mulVec_nonneg Φ
  have hGnonneg : ∀ x : Fin (M + 1), 0 ≤ (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re :=
    fun x => (Complex.le_def.mp (hGle x)).1
  have hGc : ∀ x : Fin (M + 1), star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ
      = (((star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re : ℝ) : ℂ) := fun x =>
    (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr
      (by simpa using ((Complex.le_def.mp (hGle x)).2).symm))).symm
  -- the Slater energy is real
  have hEc : occupiedEigenEnergy hT SUp ∅
      = (((occupiedEigenEnergy hT SUp ∅).re : ℝ) : ℂ) := by
    refine (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr ?_)).symm
    rw [occupiedEigenEnergy, Finset.sum_empty, add_zero, ← Complex.ofReal_sum,
      Complex.ofReal_im]
  -- real part of the exact sandwich value
  have hbrRe : (occupiedEigenEnergy hT SUp ∅ * ((SUp.card : ℕ) : ℂ) * (star Φ ⬝ᵥ Φ)
        - occupiedEigenEnergy hT SUp ∅ * (star Φ ⬝ᵥ Φ)
        + ∑ x : Fin (M + 1), t x x * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ)).re
      = (occupiedEigenEnergy hT SUp ∅).re * (SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re
        - (occupiedEigenEnergy hT SUp ∅).re * (star Φ ⬝ᵥ Φ).re
        + ∑ x : Fin (M + 1),
          (t x x).re * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re := by
    have h1 : (occupiedEigenEnergy hT SUp ∅ * ((SUp.card : ℕ) : ℂ) * (star Φ ⬝ᵥ Φ)).re
        = (occupiedEigenEnergy hT SUp ∅).re * (SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re := by
      conv_lhs => rw [hEc, hPc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
        ← Complex.ofReal_mul]
      exact Complex.ofReal_re _
    have h2 : (occupiedEigenEnergy hT SUp ∅ * (star Φ ⬝ᵥ Φ)).re
        = (occupiedEigenEnergy hT SUp ∅).re * (star Φ ⬝ᵥ Φ).re := by
      conv_lhs => rw [hEc, hPc, ← Complex.ofReal_mul]
      exact Complex.ofReal_re _
    have h3 : (∑ x : Fin (M + 1), t x x * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ)).re
        = ∑ x : Fin (M + 1),
          (t x x).re * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      conv_lhs => rw [hGc x]
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [Complex.add_re, Complex.sub_re, h1, h2, h3]
  -- the occupation expectations sum to the electron count
  have hoccRe : (∑ x : Fin (M + 1), (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re)
      = (SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re := by
    rw [← Complex.re_sum, hoccsum]
    conv_lhs => rw [hPc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  -- the two scalar bounds
  have hEabs : |(occupiedEigenEnergy hT SUp ∅).re| ≤ (SUp.card : ℝ) * K := by
    have hEre : (occupiedEigenEnergy hT SUp ∅).re = ∑ j ∈ SUp, hT.eigenvalues j := by
      rw [occupiedEigenEnergy, Finset.sum_empty, add_zero, ← Complex.ofReal_sum,
        Complex.ofReal_re]
    rw [hEre]
    calc |∑ j ∈ SUp, hT.eigenvalues j| ≤ ∑ j ∈ SUp, |hT.eigenvalues j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ SUp, K := Finset.sum_le_sum fun j _ => abs_eigenvalues_le_of_rowSum_le hT hK j
      _ = (SUp.card : ℝ) * K := by rw [Finset.sum_const, nsmul_eq_mul]
  have htdiag : ∀ x : Fin (M + 1), (t x x).re ≤ K := by
    intro x
    calc (t x x).re ≤ ‖t x x‖ := Complex.re_le_norm _
      _ ≤ ∑ y : Fin (M + 1), ‖t x y‖ :=
        Finset.single_le_sum (f := fun y => ‖t x y‖) (fun y _ => norm_nonneg _)
          (Finset.mem_univ x)
      _ ≤ K := hK x
  have hTbound : (∑ x : Fin (M + 1),
        (t x x).re * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re)
      ≤ K * ((SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re) := by
    calc (∑ x : Fin (M + 1),
          (t x x).re * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re)
        ≤ ∑ x : Fin (M + 1), K * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (htdiag x) (hGnonneg x)
      _ = K * ∑ x : Fin (M + 1), (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re := by
          rw [← Finset.mul_sum]
      _ = K * ((SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re) := by rw [hoccRe]
  -- assemble
  have hkey : -((occupiedEigenEnergy hT SUp ∅).re) * (star Φ ⬝ᵥ Φ).re
        + ∑ x : Fin (M + 1),
          (t x x).re * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re
      ≤ 2 * K * ((SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re) := by
    have hneg : -((occupiedEigenEnergy hT SUp ∅).re) ≤ (SUp.card : ℝ) * K := by
      linarith [(abs_le.mp hEabs).1]
    have hmul : -((occupiedEigenEnergy hT SUp ∅).re) * (star Φ ⬝ᵥ Φ).re
        ≤ ((SUp.card : ℝ) * K) * (star Φ ⬝ᵥ Φ).re :=
      mul_le_mul_of_nonneg_right hneg hPnonneg
    nlinarith [hTbound, hmul]
  unfold rayleighOnVec
  rw [hsand, Complex.re_ofReal_mul, hbrRe]
  have hc : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
  have hstep : (1 / ((M : ℝ) + 1)) *
        ((occupiedEigenEnergy hT SUp ∅).re * (SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re
          - (occupiedEigenEnergy hT SUp ∅).re * (star Φ ⬝ᵥ Φ).re
          + ∑ x : Fin (M + 1),
            (t x x).re * (star Φ ⬝ᵥ (fermionUpNumber M x).mulVec Φ).re)
      ≤ (1 / ((M : ℝ) + 1)) *
        ((occupiedEigenEnergy hT SUp ∅).re * (SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re
          + 2 * K * ((SUp.card : ℝ) * (star Φ ⬝ᵥ Φ).re)) :=
    mul_le_mul_of_nonneg_left (by linarith [hkey]) hc.le
  refine hstep.trans (le_of_eq ?_)
  ring

/-! ## The minority-spin correction -/

/-- **The minority-spin correction is bounded by the double-occupancy weight** (replacing
eqs. (F.10)/(F.11)): `⟨ν̂Ψ, Ĥ^↓ν̂Ψ⟩ ≤ K⟨Ψ, ν̂Ψ⟩`.  The doubly occupied component still carries a
single ↓ electron, so the Loewner bound `Ĥ^↓ ≤ K N̂_↓` collapses to `K` times its squared norm.
No two-point remainder is constructed. -/
theorem rayleighOnVec_hubbardKineticSpin_one_doubleOccupancy_le
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ} {K : ℝ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1))
    (hK : ∀ x : Fin (M + 1), ∑ y : Fin (M + 1), ‖t x y‖ ≤ K) :
    rayleighOnVec (hubbardKineticSpin M t 1)
        ((hubbardOnSiteInteraction M 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v))
      ≤ K * (((SUp.card : ℝ) / ((M : ℝ) + 1)) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅).re) := by
  have he : ∀ j : Fin (M + 1), hT.eigenvalues j ≤ K := fun j =>
    (abs_le.mp (abs_eigenvalues_le_of_rowSum_le hT hK j)).2
  have hw := fermionTotalDownNumber_mulVec_hubbardOnSiteInteraction_mulVec_of_downNumber_one M
    (fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v)
  have hbound := rayleighOnVec_hubbardKineticSpin_one_le_of_downNumber_one hT he hw
  have hnorm : (star ((hubbardOnSiteInteraction M 1).mulVec
        (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v)) ⬝ᵥ
        (hubbardOnSiteInteraction M 1).mulVec
          (hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v)).re
      = ((SUp.card : ℝ) / ((M : ℝ) + 1)) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅).re := by
    rw [← dotProduct_star_hubbardOnSiteInteraction_eq_self,
      dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState hT SUp hmod,
      Complex.re_ofReal_mul]
  rwa [hnorm] at hbound

/-! ## The Roth norm -/

/-- **The norm of the Roth state** (eq. (F.2) combined with the double-occupancy weight):
`‖Ψ̃‖² = (1 − |SUp|/(M+1))‖Φ↑‖²`.  The cross terms of `‖Ψ − ν̂Ψ‖²` collapse because `ν̂` is
Hermitian and idempotent on the one-↓-electron sector. -/
theorem dotProduct_star_self_hubbardLowDensityRothState_re
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1)) :
    (star (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v) ⬝ᵥ
        hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v).re
      = (1 - (SUp.card : ℝ) / ((M : ℝ) + 1)) *
        (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
          spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅).re := by
  have hL4 := dotProduct_star_self_sub_hubbardOnSiteInteraction_re_of_downNumber_one M
    (fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v)
  rw [hubbardLowDensityRothState, hL4,
    dotProduct_star_self_hubbardLowDensityTrialState hT SUp hmod,
    dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState hT SUp hmod,
    Complex.re_ofReal_mul]
  ring

/-- **The Roth state is nonzero**: `0 < ‖Ψ̃‖²` when `2|SUp| ≤ M + 1`.  The projection removes the
fraction `|SUp|/(M+1) ≤ 1/2` of the trial norm, so at least half of it survives, and the polarized
Slater determinant has positive norm. -/
theorem dotProduct_star_self_hubbardLowDensityRothState_pos
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ}
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1))
    (hhalf : 2 * (SUp.card : ℝ) ≤ (M : ℝ) + 1) :
    0 < (star (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v) ⬝ᵥ
      hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v).re := by
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hP : 0 < (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅) ⬝ᵥ
      spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅).re :=
    dotProduct_star_self_re_pos (spinfulGeneralBasisState_ne_zero (eigenbasisAsBasis hT) SUp ∅)
  have hρ : (SUp.card : ℝ) / ((M : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hMpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  rw [dotProduct_star_self_hubbardLowDensityRothState_re hT SUp hmod]
  nlinarith [hP, hρ]

/-! ## The variational bound -/

/-- **Roth's variational estimate** (eqs. (11.1.9)/(11.1.10), the collected bound (F.12)/(F.13)):
`⟨Ψ̃, ĤΨ̃⟩ ≤ (E↑ + ε + 8K|SUp|/(M+1))‖Ψ̃‖²` for **every** coupling `U`, where `ε` is the eigenvalue
of the ↓ orbital `v` and `K` bounds the hopping row sums.  The Coulomb interaction annihilates the
Roth state identically, which is why `U` does not appear on the right; the residual `8K|SUp|/(M+1)`
collects the majority- and minority-spin corrections of the doubly occupied component, using
`2|SUp| ≤ M + 1` to convert the polarized Slater norm into the Roth norm. -/
theorem rayleighOnVec_hubbardHamiltonian_hubbardLowDensityRothState_le
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp : Finset (Fin (M + 1))) {v : Fin (M + 1) → ℂ} {e₁ K : ℝ}
    (hv : t.mulVec v = ((e₁ : ℝ) : ℂ) • v)
    (hmod : ∀ x : Fin (M + 1), ‖v x‖ ^ 2 = 1 / ((M : ℝ) + 1))
    (hK : ∀ x : Fin (M + 1), ∑ y : Fin (M + 1), ‖t x y‖ ≤ K)
    (hhalf : 2 * (SUp.card : ℝ) ≤ (M : ℝ) + 1)
    (U : ℝ) :
    rayleighOnVec (hubbardHamiltonian M t (U : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v)
      ≤ ((occupiedEigenEnergy hT SUp ∅).re + e₁
            + 8 * K * ((SUp.card : ℝ) / ((M : ℝ) + 1)))
        * (star (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v) ⬝ᵥ
            hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v).re := by
  have hMpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  set Φ := spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp ∅ with hΦ
  set Ψ := hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v with hΨ
  -- the Coulomb interaction annihilates the Roth state
  have hdown : (fermionTotalDownNumber M).mulVec Ψ = Ψ :=
    fermionTotalDownNumber_mulVec_hubbardLowDensityTrialState (eigenbasisAsBasis hT) SUp v
  have hint : (hubbardOnSiteInteraction M (U : ℂ)).mulVec
      (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v) = 0 :=
    hubbardOnSiteInteraction_mulVec_sub_self_eq_zero_of_downNumber_one M (U : ℂ) hdown
  have hray : rayleighOnVec (hubbardHamiltonian M t (U : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v)
      = (star (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v) ⬝ᵥ
        (hubbardKinetic M t).mulVec
          (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v)).re := by
    unfold rayleighOnVec
    rw [hubbardHamiltonian, Matrix.add_mulVec, dotProduct_add, hint, dotProduct_zero, add_zero]
  -- the trial state is a kinetic eigenvector with a real eigenvalue
  have hEc : occupiedEigenEnergy hT SUp ∅
      = (((occupiedEigenEnergy hT SUp ∅).re : ℝ) : ℂ) := by
    refine (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr ?_)).symm
    rw [occupiedEigenEnergy, Finset.sum_empty, add_zero, ← Complex.ofReal_sum,
      Complex.ofReal_im]
  have hkin : (hubbardKinetic M t).mulVec Ψ
      = ((((occupiedEigenEnergy hT SUp ∅).re + e₁ : ℝ)) : ℂ) • Ψ := by
    rw [hΨ, hubbardKinetic_mulVec_hubbardLowDensityTrialState hT SUp hv]
    congr 1
    conv_lhs => rw [hEc]
    rw [← Complex.ofReal_add]
  -- moving the Hermitian operators across the inner product
  have hmoveNu : ∀ w : (Fin (2 * M + 2) → Fin 2) → ℂ,
      star ((hubbardOnSiteInteraction M 1).mulVec Ψ) ⬝ᵥ w
        = star Ψ ⬝ᵥ (hubbardOnSiteInteraction M 1).mulVec w := by
    intro w
    rw [star_mulVec_dotProduct,
      show (hubbardOnSiteInteraction M 1)ᴴ = hubbardOnSiteInteraction M 1 from
        (hubbardOnSiteInteraction_isHermitian M (by simp)).eq]
  have hB : star Ψ ⬝ᵥ (hubbardKinetic M t).mulVec ((hubbardOnSiteInteraction M 1).mulVec Ψ)
      = ((((occupiedEigenEnergy hT SUp ∅).re + e₁ : ℝ)) : ℂ) *
        (star Ψ ⬝ᵥ (hubbardOnSiteInteraction M 1).mulVec Ψ) := by
    have hherm : (hubbardKinetic M t)ᴴ = hubbardKinetic M t :=
      (hubbardKinetic_isHermitian M fun i j => hT.apply j i).eq
    have h := star_mulVec_dotProduct (hubbardKinetic M t) Ψ
      ((hubbardOnSiteInteraction M 1).mulVec Ψ)
    rw [hherm] at h
    rw [← h, hkin, star_smul, smul_dotProduct, smul_eq_mul, RCLike.star_def,
      Complex.conj_ofReal]
  -- the exact expansion of the kinetic energy of the Roth state
  have hexpand : star (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v) ⬝ᵥ
        (hubbardKinetic M t).mulVec (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v)
      = ((((occupiedEigenEnergy hT SUp ∅).re + e₁ : ℝ)) : ℂ) * (star Ψ ⬝ᵥ Ψ)
        - 2 * ((((occupiedEigenEnergy hT SUp ∅).re + e₁ : ℝ)) : ℂ) *
          (star Ψ ⬝ᵥ (hubbardOnSiteInteraction M 1).mulVec Ψ)
        + star ((hubbardOnSiteInteraction M 1).mulVec Ψ) ⬝ᵥ
          (hubbardKinetic M t).mulVec ((hubbardOnSiteInteraction M 1).mulVec Ψ) := by
    rw [hubbardLowDensityRothState, ← hΨ, Matrix.mulVec_sub, star_sub, sub_dotProduct,
      dotProduct_sub, dotProduct_sub, hkin, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hmoveNu Ψ, hB]
    ring
  -- real parts
  have hPsi := dotProduct_star_self_hubbardLowDensityTrialState hT SUp hmod
  have hDc := dotProduct_star_hubbardOnSiteInteraction_hubbardLowDensityTrialState hT SUp hmod
  rw [← hΦ, ← hΨ] at hPsi hDc
  have hPc : star Φ ⬝ᵥ Φ = (((star Φ ⬝ᵥ Φ).re : ℝ) : ℂ) := by
    refine (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr ?_)).symm
    rw [dotProduct_star_self_eq_ofReal, Complex.ofReal_im]
  have hsplit : (star ((hubbardOnSiteInteraction M 1).mulVec Ψ) ⬝ᵥ
        (hubbardKinetic M t).mulVec ((hubbardOnSiteInteraction M 1).mulVec Ψ)).re
      = rayleighOnVec (hubbardKineticSpin M t 0) ((hubbardOnSiteInteraction M 1).mulVec Ψ)
        + rayleighOnVec (hubbardKineticSpin M t 1)
          ((hubbardOnSiteInteraction M 1).mulVec Ψ) := by
    rw [← rayleighOnVec_add_matrix, ← hubbardKinetic_eq_hubbardKineticSpin_add]
    rfl
  have hlhs : rayleighOnVec (hubbardHamiltonian M t (U : ℂ))
        (hubbardLowDensityRothState (eigenbasisAsBasis hT) SUp v)
      = ((occupiedEigenEnergy hT SUp ∅).re + e₁) * (star Φ ⬝ᵥ Φ).re
        - 2 * ((occupiedEigenEnergy hT SUp ∅).re + e₁) *
          (((SUp.card : ℝ) / ((M : ℝ) + 1)) * (star Φ ⬝ᵥ Φ).re)
        + (rayleighOnVec (hubbardKineticSpin M t 0) ((hubbardOnSiteInteraction M 1).mulVec Ψ)
          + rayleighOnVec (hubbardKineticSpin M t 1)
            ((hubbardOnSiteInteraction M 1).mulVec Ψ)) := by
    rw [hray, hexpand, hPsi, hDc, Complex.add_re, Complex.sub_re, hsplit,
      Complex.re_ofReal_mul,
      show (2 : ℂ) * (((occupiedEigenEnergy hT SUp ∅).re + e₁ : ℝ) : ℂ) *
            ((((SUp.card : ℝ) / ((M : ℝ) + 1) : ℝ) : ℂ) * (star Φ ⬝ᵥ Φ))
          = ((2 * ((occupiedEigenEnergy hT SUp ∅).re + e₁) *
              ((SUp.card : ℝ) / ((M : ℝ) + 1)) : ℝ) : ℂ) * (star Φ ⬝ᵥ Φ) from by
        push_cast
        ring,
      Complex.re_ofReal_mul]
    ring
  -- the two corrections and the Roth norm
  have hV4 := rayleighOnVec_hubbardKineticSpin_zero_doubleOccupancy_le hT SUp hmod hK
  have hV5 := rayleighOnVec_hubbardKineticSpin_one_doubleOccupancy_le hT SUp hmod hK
  rw [← hΦ, ← hΨ] at hV4 hV5
  have hnorm := dotProduct_star_self_hubbardLowDensityRothState_re hT SUp hmod
  rw [← hΦ] at hnorm
  -- the scalar facts
  have hKnonneg : (0 : ℝ) ≤ K :=
    le_trans (Finset.sum_nonneg fun y _ => norm_nonneg (t 0 y)) (hK 0)
  have hPnonneg : 0 ≤ (star Φ ⬝ᵥ Φ).re := by
    rw [dotProduct_star_self_eq_ofReal, Complex.ofReal_re]
    exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hρnonneg : (0 : ℝ) ≤ (SUp.card : ℝ) / ((M : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg _) (le_of_lt hMpos)
  have hρhalf : (SUp.card : ℝ) / ((M : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hMpos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hvne : v ≠ 0 := by
    intro h
    have h0 := hmod 0
    rw [h, Pi.zero_apply, norm_zero] at h0
    have hpos : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
    rw [← h0] at hpos
    norm_num at hpos
  have he₁ : |e₁| ≤ K := by
    have h := norm_le_of_mulVec_eq_smul_of_rowSum_le hvne hv hK
    rwa [Complex.norm_real, Real.norm_eq_abs] at h
  -- assemble
  rw [hlhs, hnorm]
  have hρP : 0 ≤ ((SUp.card : ℝ) / ((M : ℝ) + 1)) * (star Φ ⬝ᵥ Φ).re :=
    mul_nonneg hρnonneg hPnonneg
  have hKρP : (0 : ℝ) ≤ K * (((SUp.card : ℝ) / ((M : ℝ) + 1)) * (star Φ ⬝ᵥ Φ).re) :=
    mul_nonneg hKnonneg hρP
  have hslack : 4 * (K * (((SUp.card : ℝ) / ((M : ℝ) + 1)) * (star Φ ⬝ᵥ Φ).re))
      ≤ 8 * K * ((SUp.card : ℝ) / ((M : ℝ) + 1)) *
        ((1 - (SUp.card : ℝ) / ((M : ℝ) + 1)) * (star Φ ⬝ᵥ Φ).re) := by
    nlinarith [hKρP, hρhalf]
  have hneg : -e₁ * (((SUp.card : ℝ) / ((M : ℝ) + 1)) * (star Φ ⬝ᵥ Φ).re)
      ≤ K * (((SUp.card : ℝ) / ((M : ℝ) + 1)) * (star Φ ⬝ᵥ Φ).re) :=
    mul_le_mul_of_nonneg_right (by linarith [(abs_le.mp he₁).1]) hρP
  nlinarith [hV4, hV5, hslack, hneg]

end LatticeSystem.Fermion
