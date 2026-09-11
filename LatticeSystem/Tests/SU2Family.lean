import LatticeSystem.Quantum.SU2
import LatticeSystem.Quantum.SU2Integral

/-!
# Test coverage for the SU2 cluster

D coverage for `Quantum/SU2.lean` and `Quantum/SU2Integral.lean`
(per refactor plan v4 §9 mapping table; refactor Phase 1 PR 12).

The `totalSpinHalfRot*` pins below are base-green characterization pins recorded before the
`Quantum/TotalSpin/Rotation.lean` core factoring, not Red tests.
-/

namespace LatticeSystem.Tests.SU2Family

open LatticeSystem.Quantum

/-! ## D. signature shims for `SU2` membership -/

/-- `Û^(1)_θ ∈ SU(2)`. -/
example (θ : ℝ) : spinHalfRot1 θ ∈ SU2 := spinHalfRot1_mem_SU2 θ

/-- `Û^(2)_θ ∈ SU(2)`. -/
example (θ : ℝ) : spinHalfRot2 θ ∈ SU2 := spinHalfRot2_mem_SU2 θ

/-- `Û^(3)_θ ∈ SU(2)`. -/
example (θ : ℝ) : spinHalfRot3 θ ∈ SU2 := spinHalfRot3_mem_SU2 θ

/-- Euler product is in `SU(2)`. -/
example (φ θ ψ : ℝ) : spinHalfEulerProduct φ θ ψ ∈ SU2 :=
  spinHalfEulerProduct_mem_SU2 φ θ ψ

/-! ## D. signature shims for `SU2Integral` -/

example : ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos θ = 0 :=
  integral_cos_zero_two_pi

example : ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin θ = 0 :=
  integral_sin_zero_two_pi

example : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 :=
  integral_sin_zero_pi

/-! ## D. Half-angle / complex-exp helper integrals

These power the SU(2)-averaged singlet computation
(`tasaki_problem_2_2_b_upDown_average`). -/

example : ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.cos θ = 0 :=
  integral_sin_mul_cos_zero_pi

example :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.cos (θ / 2) ^ 2 = 1 :=
  integral_sin_mul_cos_sq_half_zero_pi

example :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.sin (θ / 2) ^ 2 = 1 :=
  integral_sin_mul_sin_sq_half_zero_pi

example :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (Complex.I * (φ : ℂ)) = 0 :=
  integral_cexp_I_mul_zero_two_pi

example :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(Complex.I * (φ : ℂ))) = 0 :=
  integral_cexp_neg_I_mul_zero_two_pi

/-! ## R. Pins for Problem 2.2.b, eqs. (2.2.14)/(2.2.15), p. 23

`tasaki_problem_2_2_b_upDown_average` is the two-conjunct chain of eq. (2.2.14) (component form,
then the singlet identification via `twoSiteSinglet`, App. A.3.3 eq. (A.3.23)).
`tasaki_problem_2_2_b_upUp_average` is the three-conjunct chain of eq. (2.2.15) ending in the
non-SU(2)-invariance of `twoSiteTripletZero` (App. A.3.3 eq. (A.3.22)). The θ-integral helper
`integral_sin_mul_cos_half_mul_sin_half_zero_pi` and the values of the two states are pinned
alongside. -/

/-- Pin: `twoSiteSinglet` on the `upDown` configuration equals `(√2)⁻¹` (Tasaki App. A.3.3,
eq. (A.3.23), p. 474). Distinguishes the `(√2)⁻¹` normalisation from `1/2`. -/
example : twoSiteSinglet upDown = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [twoSiteSinglet, basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown]

/-- Pin: `twoSiteSinglet` on the swapped configuration equals `-(√2)⁻¹` (the singlet's
antisymmetric sign; distinguishes from the triplet's `+(√2)⁻¹` pin below). -/
example : twoSiteSinglet (basisSwap upDown (0 : Fin 2) 1) = -(((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
  simp [twoSiteSinglet, basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown]

/-- Pin: `twoSiteSinglet` vanishes on the all-up configuration (non-vacuity control:
the singlet has no support on `|↑↑⟩`). -/
example : twoSiteSinglet (fun _ : Fin 2 => (0 : Fin 2)) = 0 := by
  simp [twoSiteSinglet, basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown]

/-- Pin: `twoSiteTripletZero` on `upDown` equals `(√2)⁻¹` (Tasaki App. A.3.3, eq. (A.3.22),
p. 474). -/
example : twoSiteTripletZero upDown = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [twoSiteTripletZero, basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown]

/-- Pin: `twoSiteTripletZero` on the swapped configuration equals `+(√2)⁻¹` (the triplet's
symmetric sign, distinguishing it from `twoSiteSinglet` at the same configuration). -/
example : twoSiteTripletZero (basisSwap upDown (0 : Fin 2) 1) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  simp [twoSiteTripletZero, basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown]

/-- Pin: `twoSiteTripletZero` is non-zero on `upDown` (non-vacuity control: the definition
is not the zero function). -/
example : twoSiteTripletZero upDown ≠ 0 := by
  simp [twoSiteTripletZero, basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown]

/-- Pin (θ-integral helper for eq. (2.2.15)): `∫ θ in 0..π, sin θ · cos(θ/2) · sin(θ/2) = π/4`.
Distinguishes `π/4` from `π/8` via `Real.sin_two_mul` and `integral_sin_sq`. -/
example :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * (Real.cos (θ / 2) * Real.sin (θ / 2)) = Real.pi / 4 :=
  integral_sin_mul_cos_half_mul_sin_half_zero_pi

/-- Pin: full signature of eq. (2.2.14) as the printed
chain of equalities — the SU(2)-averaged `|↑↓⟩` state (component form, stated on the exponential
rotations rather than the closed `totalSpinHalfRot*` form) equals the unnormalised singlet
combination, which in turn equals `(√2)⁻¹ • twoSiteSinglet` (Tasaki §2.2, eq. (2.2.14), p. 23,
first display of Problem 2.2.b; App. A.3.3, eq. (A.3.23), p. 474). Distinguishes the prefactor
`1/(4π)` from `1/(2π)` and the `-` combination from `+`. -/
example :
    (∀ τ : Fin 2 → Fin 2,
      (1 / (4 * (Real.pi : ℂ))) * ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..Real.pi,
        ((Real.sin θ : ℂ) *
          ((NormedSpace.exp ((-(Complex.I * (φ : ℂ))) • totalSpinHalfOp3 (Fin 2)) *
              NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp2 (Fin 2))).mulVec
            (basisVec upDown)) τ) =
        ((1 / 2 : ℂ) • (basisVec upDown - basisVec (basisSwap upDown (0 : Fin 2) 1))) τ) ∧
    (1 / 2 : ℂ) • (basisVec upDown - basisVec (basisSwap upDown (0 : Fin 2) 1)) =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • twoSiteSinglet :=
  tasaki_problem_2_2_b_upDown_average

/-- Pin: positive control instantiating the eq. (2.2.14) component chain at
`τ = basisSwap upDown 0 1`, i.e. `|↓↑⟩`: the averaged coefficient is `-1/2` (distinguishes the
sign and the value from the `+π/8` value of the eq. (2.2.15) analogue below). -/
example :
    (1 / (4 * (Real.pi : ℂ))) * ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..Real.pi,
      ((Real.sin θ : ℂ) *
        ((NormedSpace.exp ((-(Complex.I * (φ : ℂ))) • totalSpinHalfOp3 (Fin 2)) *
            NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp2 (Fin 2))).mulVec
          (basisVec upDown)) (basisSwap upDown (0 : Fin 2) 1)) =
    (-(1 / 2) : ℂ) :=
  (tasaki_problem_2_2_b_upDown_average.1 (basisSwap upDown (0 : Fin 2) 1)).trans (by
    simp [basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown])

/-- Pin: full signature of eq. (2.2.15) — the SU(2)-averaged `|↑↑⟩` state equals the
unnormalised `Φ_{1,0}` combination times `π/8`, which in turn equals a `twoSiteTripletZero`
multiple, and `twoSiteTripletZero` is not SU(2)-invariant (Tasaki §2.2, eq. (2.2.15), p. 23,
second display of Problem 2.2.b; App. A.3.3, eq. (A.3.22), p. 474; invariance witness at axis 2,
θ = π). Distinguishes `π/8` from `π/4` and the non-invariance predicate's negation
from an unnegated (false) universal claim. -/
example :
    (∀ τ : Fin 2 → Fin 2, (1 / (4 * (Real.pi : ℂ))) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..Real.pi,
        ((Real.sin θ : ℂ) *
          ((NormedSpace.exp ((-(Complex.I * (φ : ℂ))) • totalSpinHalfOp3 (Fin 2)) *
              NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp2 (Fin 2))).mulVec
            (basisVec (fun _ : Fin 2 => (0 : Fin 2)))) τ) =
        (((Real.pi : ℂ) / 8) • (basisVec upDown + basisVec (basisSwap upDown (0 : Fin 2) 1))) τ) ∧
    ((Real.pi : ℂ) / 8) • (basisVec upDown + basisVec (basisSwap upDown (0 : Fin 2) 1)) =
      ((Real.pi : ℂ) / (4 * ((Real.sqrt 2 : ℝ) : ℂ))) • twoSiteTripletZero ∧
    ¬ ∀ (α : Fin 3) (θ : ℝ),
      (NormedSpace.exp ((-(Complex.I * (θ : ℂ))) •
          ![totalSpinHalfOp1 (Fin 2), totalSpinHalfOp2 (Fin 2), totalSpinHalfOp3 (Fin 2)] α)).mulVec
        twoSiteTripletZero = twoSiteTripletZero :=
  tasaki_problem_2_2_b_upUp_average

/-- Pin: positive control instantiating the eq. (2.2.15) component chain at `τ = upDown`:
the averaged coefficient is `+π/8` (distinguishes from `0`, the value at `τ = fun _ => 0` below,
and from the `-1/2` value of eq. (2.2.14) at the swapped configuration above). -/
example :
    (1 / (4 * (Real.pi : ℂ))) * ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..Real.pi,
      ((Real.sin θ : ℂ) *
        ((NormedSpace.exp ((-(Complex.I * (φ : ℂ))) • totalSpinHalfOp3 (Fin 2)) *
            NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp2 (Fin 2))).mulVec
          (basisVec (fun _ : Fin 2 => (0 : Fin 2)))) upDown) =
    ((Real.pi : ℂ) / 8) :=
  (tasaki_problem_2_2_b_upUp_average.1 upDown).trans (by
    simp [basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown])

/-- Pin: positive control instantiating the eq. (2.2.15) component chain at
`τ = fun _ => 0`, i.e. `|↑↑⟩` itself: the averaged coefficient is `0` (distinguishes the vanishing
diagonal component from the off-diagonal `π/8` value pinned above). -/
example :
    (1 / (4 * (Real.pi : ℂ))) * ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..Real.pi,
      ((Real.sin θ : ℂ) *
        ((NormedSpace.exp ((-(Complex.I * (φ : ℂ))) • totalSpinHalfOp3 (Fin 2)) *
            NormedSpace.exp ((-(Complex.I * (θ : ℂ))) • totalSpinHalfOp2 (Fin 2))).mulVec
          (basisVec (fun _ : Fin 2 => (0 : Fin 2)))) (fun _ : Fin 2 => (0 : Fin 2))) =
    (0 : ℂ) :=
  (tasaki_problem_2_2_b_upUp_average.1 (fun _ : Fin 2 => (0 : Fin 2))).trans (by
    simp [basisVec, basisSwap_upDown, funext_iff, Fin.forall_fin_two, upDown])

/-- Pin (θ = 0 control on the non-invariance predicate, all three axes): at `θ = 0` every
axis rotation acts as the identity on `twoSiteTripletZero`. This is what the non-invariance
conjunct guards against: it must not be trivially true because `NormedSpace.exp` at the zero
exponent fails to reduce to `1`. This positive control shows the θ = 0 instance holds
unconditionally for every axis, so the theorem's non-invariance must come from a genuine
non-identity instance. -/
example (α : Fin 3) :
    (NormedSpace.exp ((-(Complex.I * ((0 : ℝ) : ℂ))) •
        ![totalSpinHalfOp1 (Fin 2), totalSpinHalfOp2 (Fin 2), totalSpinHalfOp3 (Fin 2)] α)).mulVec
      twoSiteTripletZero = twoSiteTripletZero := by
  simp

/-! ## D. Characterization pins for the global spin-1/2 rotation family

These pins fix the public surface of the `totalSpinHalfRot*` constructors of
`Quantum/TotalSpin/Rotation.lean`: the literal site-wise shape of the six constructors, the
definitional agreement of the π family with the general-θ family at `θ = π`, and the cyclic,
boundary and two-site laws. They are green on the current source and are recorded to localise
any future change of the underlying construction. -/

/-- Literal-shape pin: `Û^(1)_π_tot` is the site-wise `noncommProd` of `onSite x (Û^(1)_π)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot1Pi Λ =
      ((Finset.univ : Finset Λ).noncommProd (fun x => onSite x (spinHalfRot1 Real.pi))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _) : ManyBodyOp Λ) := rfl

/-- Literal-shape pin: `Û^(2)_π_tot` is the site-wise `noncommProd` of `onSite x (Û^(2)_π)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot2Pi Λ =
      ((Finset.univ : Finset Λ).noncommProd (fun x => onSite x (spinHalfRot2 Real.pi))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _) : ManyBodyOp Λ) := rfl

/-- Literal-shape pin: `Û^(3)_π_tot` is the site-wise `noncommProd` of `onSite x (Û^(3)_π)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot3Pi Λ =
      ((Finset.univ : Finset Λ).noncommProd (fun x => onSite x (spinHalfRot3 Real.pi))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _) : ManyBodyOp Λ) := rfl

/-- Literal-shape pin: `Û^(1)_θ_tot` is the site-wise `noncommProd` of `onSite x (Û^(1)_θ)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (θ : ℝ) :
    totalSpinHalfRot1 Λ θ =
      ((Finset.univ : Finset Λ).noncommProd (fun x => onSite x (spinHalfRot1 θ))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _) : ManyBodyOp Λ) := rfl

/-- Literal-shape pin: `Û^(2)_θ_tot` is the site-wise `noncommProd` of `onSite x (Û^(2)_θ)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (θ : ℝ) :
    totalSpinHalfRot2 Λ θ =
      ((Finset.univ : Finset Λ).noncommProd (fun x => onSite x (spinHalfRot2 θ))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _) : ManyBodyOp Λ) := rfl

/-- Literal-shape pin: `Û^(3)_θ_tot` is the site-wise `noncommProd` of `onSite x (Û^(3)_θ)`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (θ : ℝ) :
    totalSpinHalfRot3 Λ θ =
      ((Finset.univ : Finset Λ).noncommProd (fun x => onSite x (spinHalfRot3 θ))
        (fun _ _ _ _ hxy => onSite_mul_onSite_of_ne hxy _ _) : ManyBodyOp Λ) := rfl

/-- Pin: `Û^(1)_π_tot = Û^(1)_θ_tot` at `θ = π`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot1Pi Λ = totalSpinHalfRot1 Λ Real.pi :=
  totalSpinHalfRot1Pi_eq Λ

/-- Pin: `Û^(2)_π_tot = Û^(2)_θ_tot` at `θ = π`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot2Pi Λ = totalSpinHalfRot2 Λ Real.pi :=
  totalSpinHalfRot2Pi_eq Λ

/-- Pin: `Û^(3)_π_tot = Û^(3)_θ_tot` at `θ = π`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot3Pi Λ = totalSpinHalfRot3 Λ Real.pi :=
  totalSpinHalfRot3Pi_eq Λ

/-- Pin (Tasaki eq. (2.1.29), p. 19, lifted site-wise):
`Û^(1)_π_tot · Û^(2)_π_tot = Û^(3)_π_tot`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot1Pi Λ * totalSpinHalfRot2Pi Λ = totalSpinHalfRot3Pi Λ :=
  totalSpinHalfRot1Pi_mul_totalSpinHalfRot2Pi Λ

/-- Pin (Tasaki eq. (2.1.29), p. 19, lifted site-wise):
`Û^(2)_π_tot · Û^(3)_π_tot = Û^(1)_π_tot`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot2Pi Λ * totalSpinHalfRot3Pi Λ = totalSpinHalfRot1Pi Λ :=
  totalSpinHalfRot2Pi_mul_totalSpinHalfRot3Pi Λ

/-- Pin (Tasaki eq. (2.1.29), p. 19, lifted site-wise):
`Û^(3)_π_tot · Û^(1)_π_tot = Û^(2)_π_tot`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot3Pi Λ * totalSpinHalfRot1Pi Λ = totalSpinHalfRot2Pi Λ :=
  totalSpinHalfRot3Pi_mul_totalSpinHalfRot1Pi Λ

/-- Pin: `Û^(1)_0_tot = 1`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] : totalSpinHalfRot1 Λ 0 = 1 :=
  totalSpinHalfRot1_zero Λ

/-- Pin: `Û^(2)_0_tot = 1`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] : totalSpinHalfRot2 Λ 0 = 1 :=
  totalSpinHalfRot2_zero Λ

/-- Pin: `Û^(3)_0_tot = 1`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] : totalSpinHalfRot3 Λ 0 = 1 :=
  totalSpinHalfRot3_zero Λ

/-- Pin (the `|Λ| = 2` case of Tasaki eq. (2.2.11), p. 22, not Problem 2.2.b): the two-site
factorisation of `Û^(1)_π_tot`. -/
example :
    totalSpinHalfRot1Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot1 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot1 Real.pi) :=
  totalSpinHalfRot1Pi_two_site

/-- Pin (the `|Λ| = 2` case of Tasaki eq. (2.2.11), p. 22, not Problem 2.2.b): the two-site
factorisation of `Û^(2)_π_tot`. -/
example :
    totalSpinHalfRot2Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot2 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot2 Real.pi) :=
  totalSpinHalfRot2Pi_two_site

/-- Pin (the `|Λ| = 2` case of Tasaki eq. (2.2.11), p. 22, not Problem 2.2.b): the two-site
factorisation of `Û^(3)_π_tot`. -/
example :
    totalSpinHalfRot3Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot3 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot3 Real.pi) :=
  totalSpinHalfRot3Pi_two_site

/-- Pin: the two-site factorisation of `Û^(1)_θ_tot`. -/
example (θ : ℝ) :
    totalSpinHalfRot1 (Fin 2) θ =
      onSite (0 : Fin 2) (spinHalfRot1 θ) * onSite (1 : Fin 2) (spinHalfRot1 θ) :=
  totalSpinHalfRot1_two_site θ

/-- Pin: the two-site factorisation of `Û^(2)_θ_tot` (consumed by `Quantum/SU2Integral.lean`). -/
example (θ : ℝ) :
    totalSpinHalfRot2 (Fin 2) θ =
      onSite (0 : Fin 2) (spinHalfRot2 θ) * onSite (1 : Fin 2) (spinHalfRot2 θ) :=
  totalSpinHalfRot2_two_site θ

/-- Pin: the two-site factorisation of `Û^(3)_θ_tot` (consumed by `Quantum/SU2Integral.lean`). -/
example (θ : ℝ) :
    totalSpinHalfRot3 (Fin 2) θ =
      onSite (0 : Fin 2) (spinHalfRot3 θ) * onSite (1 : Fin 2) (spinHalfRot3 θ) :=
  totalSpinHalfRot3_two_site θ

end LatticeSystem.Tests.SU2Family
