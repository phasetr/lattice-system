/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.SU2
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.TotalSpin
import LatticeSystem.Quantum.SpinDot
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Trig-integral helpers for Tasaki §2.2 Problem 2.2.c

Concrete trig-integral evaluations needed for the SU(2)-averaged-state
computation (Tasaki §2.2, Problem 2.2.c, eq. (2.2.15)). These are
proved using mathlib's `intervalIntegral` and
`SpecialFunctions.Integrals`. Each is a thin wrapper around mathlib's
`integral_sin`, `integral_cos`, or `integral_sin_sq`/`integral_cos_sq`.

The full integral statement (Problem 2.2.c itself) will be assembled
from these helpers in a follow-up work item (B-3c).
-/

namespace LatticeSystem.Quantum

open MeasureTheory Real

/-! ## Standard trig integrals over one full period or half period -/

/-- `∫ φ in 0..2π, cos φ = 0`. -/
theorem integral_cos_zero_two_pi :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.cos φ = 0 := by
  rw [integral_cos]
  simp [Real.sin_two_pi, Real.sin_zero]

/-- `∫ φ in 0..2π, sin φ = 0`. -/
theorem integral_sin_zero_two_pi :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Real.sin φ = 0 := by
  rw [integral_sin]
  simp [Real.cos_two_pi, Real.cos_zero]

/-- `∫ θ in 0..π, sin θ = 2`. -/
theorem integral_sin_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 2 := by
  rw [integral_sin]
  simp [Real.cos_pi, Real.cos_zero]; ring

/-! ## Combined 2D integral: SU(2) volume in Euler angles -/

/-- `∫ φ in 0..2π, ∫ θ in 0..π, sin θ = 4π`. This is the total volume
of the SU(2) parameter space in Euler-angle coordinates. -/
theorem integral_sin_two_pi_pi :
    ∫ _φ in (0 : ℝ)..(2 * Real.pi),
      ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ = 4 * Real.pi := by
  simp only [integral_sin_zero_pi]
  rw [intervalIntegral.integral_const]
  simp [smul_eq_mul]; ring

/-! ## Half-angle integrals for the θ component of Problem 2.2.c

`sin θ cos²(θ/2) = (sin θ + sin θ cos θ) / 2 = (sin θ) / 2 + (sin 2θ) / 4`
and similarly for `sin²(θ/2)`. Integrated over `[0, π]`, the `sin 2θ`
term vanishes and the `sin θ` term gives 1 for each. -/

/-- `∫ θ in 0..π, sin θ · cos θ = 0`. Antiderivative: `sin²(θ)/2`. -/
theorem integral_sin_mul_cos_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * Real.cos θ = 0 := by
  have key : ∀ x ∈ Set.uIcc (0 : ℝ) Real.pi,
      HasDerivAt (fun x => (Real.sin x) ^ 2 / 2) (Real.sin x * Real.cos x) x := by
    intros x _
    have h := (Real.hasDerivAt_sin x).pow 2
    convert h.div_const 2 using 1
    ring
  have hint : IntervalIntegrable (fun x => Real.sin x * Real.cos x)
      MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key hint]
  simp [Real.sin_pi, Real.sin_zero]

/-- `∫ θ in 0..π, sin θ · cos²(θ/2) = 1`. Uses the half-angle identity
`cos²(θ/2) = (1 + cos θ) / 2` and the vanishing of `∫ sin θ cos θ`. -/
theorem integral_sin_mul_cos_sq_half_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ * Real.cos (θ / 2) ^ 2 = 1 := by
  have hid : ∀ θ : ℝ, Real.sin θ * Real.cos (θ / 2) ^ 2 =
      (1 / 2) * Real.sin θ + (1 / 2) * (Real.sin θ * Real.cos θ) := by
    intro θ
    have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
      have h := Real.cos_two_mul (θ / 2)
      rwa [show 2 * (θ / 2) = θ from by ring] at h
    linear_combination -(1 / 2) * Real.sin θ * hcos
  conv_lhs => arg 1; ext θ; rw [hid θ]
  have h1 : IntervalIntegrable (fun θ => (1/2 : ℝ) * Real.sin θ) MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_sin.const_mul _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => (1/2 : ℝ) * (Real.sin θ * Real.cos θ))
      MeasureTheory.volume 0 Real.pi :=
    ((Real.continuous_sin.mul Real.continuous_cos).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_sin_zero_pi, integral_sin_mul_cos_zero_pi]
  ring

/-- `∫ θ in 0..π, sin θ · sin²(θ/2) = 1`. Uses the half-angle identity
`sin²(θ/2) = (1 - cos θ) / 2`. -/
theorem integral_sin_mul_sin_sq_half_zero_pi :
    ∫ θ in (0 : ℝ)..Real.pi,
      Real.sin θ * Real.sin (θ / 2) ^ 2 = 1 := by
  have hid : ∀ θ : ℝ, Real.sin θ * Real.sin (θ / 2) ^ 2 =
      (1 / 2) * Real.sin θ - (1 / 2) * (Real.sin θ * Real.cos θ) := by
    intro θ
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h := Real.cos_two_mul' (θ / 2)
      rw [show 2 * (θ / 2) = θ from by ring] at h
      linear_combination h + Real.sin_sq_add_cos_sq (θ / 2)
    linear_combination (1 / 2) * Real.sin θ * hcos
  conv_lhs => arg 1; ext θ; rw [hid θ]
  have h1 : IntervalIntegrable (fun θ => (1/2 : ℝ) * Real.sin θ) MeasureTheory.volume 0 Real.pi :=
    (Real.continuous_sin.const_mul _).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => (1/2 : ℝ) * (Real.sin θ * Real.cos θ))
      MeasureTheory.volume 0 Real.pi :=
    ((Real.continuous_sin.mul Real.continuous_cos).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_sin_zero_pi, integral_sin_mul_cos_zero_pi]
  ring

/-! ## Complex exponential integrals for the φ component of Problem 2.2.c

`∫₀²π e^{±iφ} dφ = 0` follows from `e^{iφ} = cos φ + i sin φ` and the
vanishing of `∫ cos` and `∫ sin` over one full period. -/

/-- `∫ φ in 0..2π, e^{iφ} = 0`. -/
theorem integral_cexp_I_mul_zero_two_pi :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (Complex.I * (φ : ℂ)) = 0 := by
  have hid : ∀ φ : ℝ, Complex.exp (Complex.I * (φ : ℂ)) =
      (Real.cos φ : ℂ) + Complex.I * (Real.sin φ : ℂ) := by
    intro φ
    rw [show Complex.I * (φ : ℂ) = (φ : ℂ) * Complex.I from by ring,
      Complex.exp_mul_I]
    push_cast; ring
  conv_lhs => arg 1; ext φ; rw [hid φ]
  have h1 : IntervalIntegrable (fun φ => (Real.cos φ : ℂ))
      MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
    (Complex.continuous_ofReal.comp Real.continuous_cos).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun φ => Complex.I * (Real.sin φ : ℂ))
      MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
    ((Complex.continuous_ofReal.comp Real.continuous_sin).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_add h1 h2]
  have hcos : ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.cos φ : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal, integral_cos_zero_two_pi]; simp
  have hsin : ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.I * (Real.sin φ : ℂ) = 0 := by
    have : ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.sin φ : ℂ) = 0 := by
      rw [intervalIntegral.integral_ofReal, integral_sin_zero_two_pi]; simp
    calc ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.I * (Real.sin φ : ℂ)
        = Complex.I * ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.sin φ : ℂ) :=
          intervalIntegral.integral_const_mul ..
        _ = 0 := by rw [this, mul_zero]
  rw [hcos, hsin, add_zero]

/-- `∫ φ in 0..2π, e^{-iφ} = 0`. -/
theorem integral_cexp_neg_I_mul_zero_two_pi :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(Complex.I * (φ : ℂ))) = 0 := by
  have hid : ∀ φ : ℝ, Complex.exp (-(Complex.I * (φ : ℂ))) =
      (Real.cos φ : ℂ) - Complex.I * (Real.sin φ : ℂ) := by
    intro φ
    rw [show -(Complex.I * (φ : ℂ)) = (-(φ : ℂ)) * Complex.I from by ring,
      Complex.exp_mul_I]
    simp only [Complex.cos_neg, Complex.sin_neg, neg_mul]
    push_cast; ring
  conv_lhs => arg 1; ext φ; rw [hid φ]
  have h1 : IntervalIntegrable (fun φ => (Real.cos φ : ℂ))
      MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
    (Complex.continuous_ofReal.comp Real.continuous_cos).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun φ => Complex.I * (Real.sin φ : ℂ))
      MeasureTheory.volume (0 : ℝ) (2 * Real.pi) :=
    ((Complex.continuous_ofReal.comp Real.continuous_sin).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2]
  have hcos : ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.cos φ : ℂ) = 0 := by
    rw [intervalIntegral.integral_ofReal, integral_cos_zero_two_pi]; simp
  have hsin : ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.I * (Real.sin φ : ℂ) = 0 := by
    have : ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.sin φ : ℂ) = 0 := by
      rw [intervalIntegral.integral_ofReal, integral_sin_zero_two_pi]; simp
    calc ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.I * (Real.sin φ : ℂ)
        = Complex.I * ∫ φ in (0 : ℝ)..(2 * Real.pi), (Real.sin φ : ℂ) :=
          intervalIntegral.integral_const_mul ..
        _ = 0 := by rw [this, mul_zero]
  rw [hcos, hsin, sub_zero]

/-! ## Two-site factorization of total rotation product

Tasaki §2.2 eq (2.2.11): the product `Û^(3)_φ_tot · Û^(2)_θ_tot` factors
as a product of single-site combined rotations
`∏_x onSite x (Û^(3)_φ · Û^(2)_θ)`. -/

/-- Total rotation `Û^(3)_φ · Û^(2)_θ` on two sites factors into per-site
combined rotations. -/
theorem totalRot32_two_site (θ φ : ℝ) :
    totalSpinHalfRot3 (Fin 2) φ * totalSpinHalfRot2 (Fin 2) θ =
      onSite (0 : Fin 2) (spinHalfRot3 φ * spinHalfRot2 θ) *
        onSite (1 : Fin 2) (spinHalfRot3 φ * spinHalfRot2 θ) := by
  rw [totalSpinHalfRot3_two_site, totalSpinHalfRot2_two_site]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  set R3₀ := onSite (0 : Fin 2) (spinHalfRot3 φ)
  set R3₁ := onSite (1 : Fin 2) (spinHalfRot3 φ)
  set R2₀ := onSite (0 : Fin 2) (spinHalfRot2 θ)
  set R2₁ := onSite (1 : Fin 2) (spinHalfRot2 θ)
  change R3₀ * R3₁ * (R2₀ * R2₁) = _
  have : R3₁ * R2₀ = R2₀ * R3₁ :=
    onSite_mul_onSite_of_ne h10 (spinHalfRot3 φ) (spinHalfRot2 θ)
  rw [mul_assoc R3₀, ← mul_assoc R3₁, this, mul_assoc R2₀, ← mul_assoc R3₀]
  rw [onSite_mul_onSite_same, onSite_mul_onSite_same]

/-! ## Tensor product action on a two-site basis vector

For `Λ = Fin 2`, the product `onSite 0 M * onSite 1 N` acts on a basis
vector `|σ⟩` as the Kronecker product: the coefficient of `|τ⟩` is
`M (τ 0) (σ 0) * N (τ 1) (σ 1)`. -/

/-- On `Fin 2`, agreement away from `0` is equivalent to agreement at `1`. -/
private lemma fin2_forall_ne_zero (τ κ : Fin 2 → Fin 2) :
    (∀ k, k ≠ (0 : Fin 2) → τ k = κ k) ↔ τ 1 = κ 1 := by
  constructor
  · intro h; exact h 1 (by decide)
  · intro h k hk; fin_cases k <;> simp_all

/-- On `Fin 2`, agreement away from `1` is equivalent to agreement at `0`. -/
private lemma fin2_forall_ne_one (τ κ : Fin 2 → Fin 2) :
    (∀ k, k ≠ (1 : Fin 2) → τ k = κ k) ↔ τ 0 = κ 0 := by
  constructor
  · intro h; exact h 0 (by decide)
  · intro h k hk; fin_cases k <;> simp_all

/-- Equality of functions `Fin 2 → Fin 2` reduces to pointwise equality at `0` and `1`. -/
private lemma fin2_eq_iff (σ τ : Fin 2 → Fin 2) :
    σ = τ ↔ σ 0 = τ 0 ∧ σ 1 = τ 1 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · intro ⟨h0, h1⟩; funext i; fin_cases i <;> assumption

/-- Two-site tensor product action on a basis vector. -/
theorem onSite_zero_mul_one_mulVec_basisVec
    (M N : Matrix (Fin 2) (Fin 2) ℂ) (σ τ : Fin 2 → Fin 2) :
    ((onSite (0 : Fin 2) M * onSite (1 : Fin 2) N).mulVec (basisVec σ)) τ =
      M (τ 0) (σ 0) * N (τ 1) (σ 1) := by
  conv_lhs =>
    rw [show (onSite (0 : Fin 2) M * onSite (1 : Fin 2) N).mulVec (basisVec σ) =
      (onSite (0 : Fin 2) M).mulVec ((onSite (1 : Fin 2) N).mulVec (basisVec σ)) from
      (Matrix.mulVec_mulVec ..).symm]
  rw [onSite_mulVec_basisVec 1 N σ]
  simp only [Matrix.mulVec, dotProduct, onSite_apply, fin2_forall_ne_zero, Fin.sum_univ_two]
  have hupd0 : (Function.update σ 1 (0 : Fin 2)) 0 = σ 0 := by
    rw [Function.update_apply]; simp
  have hupd1 : (Function.update σ 1 (1 : Fin 2)) 0 = σ 0 := by
    rw [Function.update_apply]; simp
  simp only [basisVec, fin2_eq_iff, Function.update_self, hupd0, hupd1]
  simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Fintype.sum_eq_single (fun i : Fin 2 => if i = 0 then σ 0 else τ 1) (fun x hx => by
    by_cases h1 : τ 1 = x 1
    · rw [if_pos h1]
      have h0 : x 0 ≠ σ 0 := by
        intro h0; apply hx; funext i; fin_cases i <;> simp_all
      simp [h0]
    · simp [h1])]
  have : τ 1 = 0 ∨ τ 1 = 1 := by rcases τ 1 with ⟨v, hv⟩; omega
  rcases this with h | h <;> simp [h]

/-! ## Matrix entry ↔ mulVec connection -/

/-- Column 0 of `M` equals `M · |↑⟩` entry-wise. -/
private lemma matrix_col0_eq_mulVec_up (M : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 2) :
    M k 0 = (M.mulVec spinHalfUp) k := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, spinHalfUp]

/-- Column 1 of `M` equals `M · |↓⟩` entry-wise. -/
private lemma matrix_col1_eq_mulVec_down (M : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 2) :
    M k 1 = (M.mulVec spinHalfDown) k := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, spinHalfDown]

/-! ## Tasaki Problem 2.2.c: SU(2)-averaged state is the singlet

The SU(2)-averaged state `(1/4π) ∫₀²π dφ ∫₀π dθ sin θ · Û(φ,θ)|↑↓⟩`
equals `(1/2)(|↑↓⟩ - |↓↑⟩)`, the spin singlet. This is Tasaki
*Physics and Mathematics of Quantum Many-Body Systems*, §2.2,
Problem 2.2.c, eq. (2.2.15). -/

/-- Expand the integrand: the component of the rotated state at configuration `τ`
is a product of single-site rotation entries. -/
private theorem totalRot_mulVec_upDown_component (θ φ : ℝ) (τ : Fin 2 → Fin 2) :
    ((totalSpinHalfRot3 (Fin 2) φ * totalSpinHalfRot2 (Fin 2) θ).mulVec
      (basisVec upDown)) τ =
    (![Complex.exp (-(Complex.I * (φ : ℂ) / 2)) * (Real.cos (θ / 2) : ℂ),
       Complex.exp (Complex.I * (φ : ℂ) / 2) * (Real.sin (θ / 2) : ℂ)] (τ 0)) *
    (![-(Complex.exp (-(Complex.I * (φ : ℂ) / 2))) * (Real.sin (θ / 2) : ℂ),
       Complex.exp (Complex.I * (φ : ℂ) / 2) * (Real.cos (θ / 2) : ℂ)] (τ 1)) := by
  rw [totalRot32_two_site, onSite_zero_mul_one_mulVec_basisVec]
  unfold upDown
  conv_lhs =>
    rw [show (spinHalfRot3 φ * spinHalfRot2 θ) (τ 0) 0 =
      ((spinHalfRot3 φ * spinHalfRot2 θ).mulVec spinHalfUp) (τ 0) from
        (matrix_col0_eq_mulVec_up _ _).symm ▸ rfl,
      show (spinHalfRot3 φ * spinHalfRot2 θ) (τ 1) 1 =
      ((spinHalfRot3 φ * spinHalfRot2 θ).mulVec spinHalfDown) (τ 1) from
        (matrix_col1_eq_mulVec_down _ _).symm ▸ rfl,
      spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfUp,
      spinHalfRot3_mul_spinHalfRot2_mulVec_spinHalfDown]

set_option maxHeartbeats 1600000 in
-- The 16-case row-by-column analysis on `Fin 2 → Fin 2` together with
-- the Euler-angle integrals exceeds the default 200k budget.
/-- Tasaki Problem 2.2.c: the SU(2)-averaged two-site state is the singlet.
Stated component-wise for each configuration `τ : Fin 2 → Fin 2`.
Tasaki *Physics and Mathematics of Quantum Many-Body Systems*,
§2.2 eq. (2.2.15). -/
theorem problem_2_2_c (τ : Fin 2 → Fin 2) :
    (1 / (4 * (Real.pi : ℂ))) *
      ∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∫ θ in (0 : ℝ)..Real.pi,
          ((Real.sin θ : ℂ) *
            ((totalSpinHalfRot3 (Fin 2) φ * totalSpinHalfRot2 (Fin 2) θ).mulVec
              (basisVec upDown)) τ) =
    (1 / 2 : ℂ) * (basisVec upDown τ - basisVec (basisSwap upDown (0 : Fin 2) 1) τ) := by
  -- Expand integrand to explicit trig/exp products
  conv_lhs => arg 2; arg 1; ext φ; arg 1; ext θ; rw [totalRot_mulVec_upDown_component]
  -- Simplify RHS
  have hbs : basisSwap upDown (0 : Fin 2) 1 = fun i : Fin 2 =>
      match i with | 0 => 1 | 1 => 0 := by
    funext i; simp only [basisSwap, upDown, Function.update]; fin_cases i <;> simp
  -- Case split on τ 0 and τ 1
  have ht0 : τ 0 = 0 ∨ τ 0 = 1 := by rcases τ 0 with ⟨v, hv⟩; omega
  have ht1 : τ 1 = 0 ∨ τ 1 = 1 := by rcases τ 1 with ⟨v, hv⟩; omega
  rcases ht0 with h0 | h0 <;> rcases ht1 with h1 | h1 <;>
    simp only [h0, h1, Matrix.cons_val_zero, Matrix.cons_val_one,
      basisVec, hbs, upDown, fin2_eq_iff]
  -- 4 cases: (0,0), (0,1), (1,0), (1,1). Each needs integral computation.
  -- Common exp-cancellation helper
  · -- τ = (0, 0): exp(-iφ) integrates to 0 over [0,2π]
    norm_num
    have hfactor : (fun x : ℝ => ∫ x₁ in (0 : ℝ)..Real.pi,
        Complex.sin ↑x₁ * (Complex.exp (-(Complex.I * ↑x / 2)) * Complex.cos (↑x₁ / 2) *
          (Complex.exp (-(Complex.I * ↑x / 2)) * Complex.sin (↑x₁ / 2)))) =
      fun x : ℝ => Complex.exp (-(Complex.I * (x : ℂ))) *
        ∫ x₁ in (0 : ℝ)..Real.pi,
          Complex.sin ↑x₁ * Complex.cos (↑x₁ / 2) * Complex.sin (↑x₁ / 2) := by
      ext x
      have : ∀ x₁ : ℝ, Complex.sin ↑x₁ *
          (Complex.exp (-(Complex.I * ↑x / 2)) * Complex.cos (↑x₁ / 2) *
            (Complex.exp (-(Complex.I * ↑x / 2)) * Complex.sin (↑x₁ / 2))) =
          Complex.exp (-(Complex.I * (x : ℂ))) *
            (Complex.sin ↑x₁ * Complex.cos (↑x₁ / 2) * Complex.sin (↑x₁ / 2)) := by
        intro x₁
        have hexp : Complex.exp (-(Complex.I * ↑x / 2)) * Complex.exp (-(Complex.I * ↑x / 2)) =
            Complex.exp (-(Complex.I * (x : ℂ))) := by
          rw [← Complex.exp_add]; ring
        calc Complex.sin ↑x₁ *
            (Complex.exp (-(Complex.I * ↑x / 2)) * Complex.cos (↑x₁ / 2) *
              (Complex.exp (-(Complex.I * ↑x / 2)) * Complex.sin (↑x₁ / 2)))
            = Complex.exp (-(Complex.I * ↑x / 2)) * Complex.exp (-(Complex.I * ↑x / 2)) *
              (Complex.sin ↑x₁ * Complex.cos (↑x₁ / 2) * Complex.sin (↑x₁ / 2)) := by ring
          _ = _ := by rw [hexp]
      simp_rw [this]; exact intervalIntegral.integral_const_mul _ _
    rw [hfactor]
    set C := ∫ x₁ in (0 : ℝ)..Real.pi,
      Complex.sin ↑x₁ * Complex.cos (↑x₁ / 2) * Complex.sin (↑x₁ / 2)
    change ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(Complex.I * ↑x)) * C = 0
    rw [show (fun x : ℝ => Complex.exp (-(Complex.I * ↑x)) * C) =
      fun x : ℝ => C * Complex.exp (-(Complex.I * ↑x)) from by ext; ring]
    have : ∫ x in (0 : ℝ)..(2 * Real.pi), C * Complex.exp (-(Complex.I * (x : ℂ))) =
        C * ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(Complex.I * (x : ℂ))) :=
      intervalIntegral.integral_const_mul _ _
    rw [this, integral_cexp_neg_I_mul_zero_two_pi, mul_zero]
  · -- τ = (0, 1) = upDown: cos²(θ/2) integral gives 1/2
    have key : ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..Real.pi,
        ↑(Real.sin θ) * (Complex.exp (-(Complex.I * ↑φ / 2)) * ↑(Real.cos (θ / 2)) *
          (Complex.exp (Complex.I * ↑φ / 2) * ↑(Real.cos (θ / 2)))) =
        2 * (Real.pi : ℂ) := by
      have hsimp : ∀ (φ θ : ℝ),
          ↑(Real.sin θ) * (Complex.exp (-(Complex.I * ↑φ / 2)) * ↑(Real.cos (θ / 2)) *
            (Complex.exp (Complex.I * ↑φ / 2) * ↑(Real.cos (θ / 2)))) =
          (↑(Real.sin θ * Real.cos (θ / 2) ^ 2) : ℂ) := by
        intros φ' θ'
        have hexp : Complex.exp (-(Complex.I * ↑φ' / 2)) *
            Complex.exp (Complex.I * ↑φ' / 2) = 1 := by
          rw [← Complex.exp_add]; ring_nf; simp
        rw [show Complex.exp (-(Complex.I * ↑φ' / 2)) * ↑(Real.cos (θ' / 2)) *
          (Complex.exp (Complex.I * ↑φ' / 2) * ↑(Real.cos (θ' / 2))) =
          Complex.exp (-(Complex.I * ↑φ' / 2)) * Complex.exp (Complex.I * ↑φ' / 2) *
          (↑(Real.cos (θ' / 2)) * ↑(Real.cos (θ' / 2))) from by ring, hexp]
        push_cast; ring
      simp_rw [hsimp, intervalIntegral.integral_ofReal, integral_sin_mul_cos_sq_half_zero_pi]
      simp [intervalIntegral.integral_const, smul_eq_mul]
    rw [key]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    field_simp; simp; ring
  · -- τ = (1, 0) = swap: -sin²(θ/2) integral gives -1/2
    have key : ∫ φ in (0 : ℝ)..(2 * Real.pi), ∫ θ in (0 : ℝ)..Real.pi,
        ↑(Real.sin θ) * (Complex.exp (Complex.I * ↑φ / 2) * ↑(Real.sin (θ / 2)) *
          (-(Complex.exp (-(Complex.I * ↑φ / 2))) * ↑(Real.sin (θ / 2)))) =
        -(2 * (Real.pi : ℂ)) := by
      have hsimp : ∀ (φ θ : ℝ),
          ↑(Real.sin θ) * (Complex.exp (Complex.I * ↑φ / 2) * ↑(Real.sin (θ / 2)) *
            (-(Complex.exp (-(Complex.I * ↑φ / 2))) * ↑(Real.sin (θ / 2)))) =
          (↑(-(Real.sin θ * Real.sin (θ / 2) ^ 2)) : ℂ) := by
        intros φ' θ'
        have hexp : Complex.exp (Complex.I * ↑φ' / 2) *
            Complex.exp (-(Complex.I * ↑φ' / 2)) = 1 := by
          rw [← Complex.exp_add]; ring_nf; simp
        rw [show Complex.exp (Complex.I * ↑φ' / 2) * ↑(Real.sin (θ' / 2)) *
          (-(Complex.exp (-(Complex.I * ↑φ' / 2))) * ↑(Real.sin (θ' / 2))) =
          -(Complex.exp (Complex.I * ↑φ' / 2) * Complex.exp (-(Complex.I * ↑φ' / 2)) *
          (↑(Real.sin (θ' / 2)) * ↑(Real.sin (θ' / 2)))) from by ring, hexp]
        push_cast; ring
      simp_rw [hsimp, intervalIntegral.integral_ofReal,
        show ∫ θ in (0 : ℝ)..Real.pi, -(Real.sin θ * Real.sin (θ / 2) ^ 2) = -1 from by
          rw [intervalIntegral.integral_neg, integral_sin_mul_sin_sq_half_zero_pi]]
      simp [intervalIntegral.integral_const, smul_eq_mul]
    rw [key]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    field_simp; simp; ring
  · -- τ = (1, 1): exp(iφ) integrates to 0 over [0,2π]
    norm_num
    have hfactor : (fun φ : ℝ => ∫ θ in (0 : ℝ)..Real.pi,
        Complex.sin ↑θ * (Complex.exp (Complex.I * ↑φ / 2) * Complex.sin (↑θ / 2) *
          (Complex.exp (Complex.I * ↑φ / 2) * Complex.cos (↑θ / 2)))) =
      fun φ : ℝ => Complex.exp (Complex.I * (φ : ℂ)) *
        ∫ θ in (0 : ℝ)..Real.pi,
          Complex.sin ↑θ * Complex.sin (↑θ / 2) * Complex.cos (↑θ / 2) := by
      ext φ
      have : ∀ θ : ℝ, Complex.sin ↑θ *
          (Complex.exp (Complex.I * ↑φ / 2) * Complex.sin (↑θ / 2) *
            (Complex.exp (Complex.I * ↑φ / 2) * Complex.cos (↑θ / 2))) =
          Complex.exp (Complex.I * (φ : ℂ)) *
            (Complex.sin ↑θ * Complex.sin (↑θ / 2) * Complex.cos (↑θ / 2)) := by
        intro θ
        have hexp : Complex.exp (Complex.I * ↑φ / 2) * Complex.exp (Complex.I * ↑φ / 2) =
            Complex.exp (Complex.I * (φ : ℂ)) := by
          rw [← Complex.exp_add]; ring
        calc Complex.sin ↑θ *
            (Complex.exp (Complex.I * ↑φ / 2) * Complex.sin (↑θ / 2) *
              (Complex.exp (Complex.I * ↑φ / 2) * Complex.cos (↑θ / 2)))
            = Complex.exp (Complex.I * ↑φ / 2) * Complex.exp (Complex.I * ↑φ / 2) *
              (Complex.sin ↑θ * Complex.sin (↑θ / 2) * Complex.cos (↑θ / 2)) := by ring
          _ = _ := by rw [hexp]
      simp_rw [this]; exact intervalIntegral.integral_const_mul _ _
    rw [hfactor]
    set C := ∫ θ in (0 : ℝ)..Real.pi,
      Complex.sin ↑θ * Complex.sin (↑θ / 2) * Complex.cos (↑θ / 2)
    change ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (Complex.I * ↑φ) * C = 0
    rw [show (fun φ : ℝ => Complex.exp (Complex.I * ↑φ) * C) =
      fun φ : ℝ => C * Complex.exp (Complex.I * ↑φ) from by ext; ring]
    have : ∫ φ in (0 : ℝ)..(2 * Real.pi), C * Complex.exp (Complex.I * (φ : ℂ)) =
        C * ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (Complex.I * (φ : ℂ)) :=
      intervalIntegral.integral_const_mul _ _
    rw [this, integral_cexp_I_mul_zero_two_pi, mul_zero]

end LatticeSystem.Quantum
