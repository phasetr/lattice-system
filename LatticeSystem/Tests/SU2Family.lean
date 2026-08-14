import LatticeSystem.Quantum.SU2
import LatticeSystem.Quantum.SU2Integral

/-!
# Test coverage for the SU2 cluster

D coverage for `Quantum/SU2.lean` and `Quantum/SU2Integral.lean`
(per refactor plan v4 §9 mapping table; refactor Phase 1 PR 12,
#281).

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

/-! ## D. Half-angle / complex-exp helper integrals (codex audit Item 8)

These power the SU(2)-averaged singlet computation
(`problem_2_2_c`); previously only the three easiest base
integrals above were pinned. -/

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

/-! ## D. Tasaki Problem 2.2.c — full SU(2)-averaged singlet identity -/

example (τ : Fin 2 → Fin 2) :
    (1 / (4 * (Real.pi : ℂ))) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∫ θ in (0 : ℝ)..Real.pi,
          ((Real.sin θ : ℂ) *
            ((totalSpinHalfRot3 (Fin 2) φ * totalSpinHalfRot2 (Fin 2) θ).mulVec
              (basisVec upDown)) τ) =
    (1 / 2 : ℂ) * (basisVec upDown τ - basisVec (basisSwap upDown (0 : Fin 2) 1) τ) :=
  problem_2_2_c τ

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

/-- Pin (Tasaki Problem 2.2.a): `Û^(1)_π_tot · Û^(2)_π_tot = Û^(3)_π_tot`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot1Pi Λ * totalSpinHalfRot2Pi Λ = totalSpinHalfRot3Pi Λ :=
  totalSpinHalfRot1Pi_mul_totalSpinHalfRot2Pi Λ

/-- Pin (Tasaki Problem 2.2.a): `Û^(2)_π_tot · Û^(3)_π_tot = Û^(1)_π_tot`. -/
example (Λ : Type*) [Fintype Λ] [DecidableEq Λ] :
    totalSpinHalfRot2Pi Λ * totalSpinHalfRot3Pi Λ = totalSpinHalfRot1Pi Λ :=
  totalSpinHalfRot2Pi_mul_totalSpinHalfRot3Pi Λ

/-- Pin (Tasaki Problem 2.2.a): `Û^(3)_π_tot · Û^(1)_π_tot = Û^(2)_π_tot`. -/
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

/-- Pin (Tasaki Problem 2.2.b): the two-site factorisation of `Û^(1)_π_tot`. -/
example :
    totalSpinHalfRot1Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot1 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot1 Real.pi) :=
  totalSpinHalfRot1Pi_two_site

/-- Pin (Tasaki Problem 2.2.b): the two-site factorisation of `Û^(2)_π_tot`. -/
example :
    totalSpinHalfRot2Pi (Fin 2) =
      onSite (0 : Fin 2) (spinHalfRot2 Real.pi) *
        onSite (1 : Fin 2) (spinHalfRot2 Real.pi) :=
  totalSpinHalfRot2Pi_two_site

/-- Pin (Tasaki Problem 2.2.b): the two-site factorisation of `Û^(3)_π_tot`. -/
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
