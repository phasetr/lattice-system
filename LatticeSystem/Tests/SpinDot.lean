import LatticeSystem.Quantum.SpinDot

/-!
# Test coverage for Quantum/SpinDot

A+C+G+D coverage for `spinHalfDot`, `basisSwap`, and the
inner-product family from #272-#278 (refactor plan v4 §9 mapping
table; refactor Phase 1 PR 6, #281).
-/

namespace LatticeSystem.Tests.SpinDot

open LatticeSystem.Quantum

/-! ## D. signature shims for core `spinHalfDot` / `basisSwap` -/

/-- `spinHalfDot` is symmetric in its arguments. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (x y : Λ) :
    (spinHalfDot x y : ManyBodyOp Λ) = spinHalfDot y x :=
  spinHalfDot_comm x y

/-- `spinHalfDot` is Hermitian. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (x y : Λ) :
    (spinHalfDot x y : ManyBodyOp Λ).IsHermitian :=
  spinHalfDot_isHermitian x y

/-- Antiparallel-pair eigenvalue equation. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    (spinHalfDot x y).mulVec (basisVec σ) =
      (1 / 2 : ℂ) • basisVec (basisSwap σ x y) -
        (1 / 4 : ℂ) • basisVec σ :=
  spinHalfDot_mulVec_basisVec_antiparallel hxy σ h

/-- Parallel-pair eigenvalue equation. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x = σ y) :
    (spinHalfDot x y).mulVec (basisVec σ) = (1 / 4 : ℂ) • basisVec σ :=
  spinHalfDot_mulVec_basisVec_parallel hxy σ h

/-- `basisSwap` is involutive. -/
example {Λ : Type*} [DecidableEq Λ] {x y : Λ} (hxy : x ≠ y)
    (σ : Λ → Fin 2) :
    basisSwap (basisSwap σ x y) x y = σ :=
  basisSwap_involutive hxy σ

/-- `basisSwap` of antiparallel changes the configuration. -/
example {Λ : Type*} [DecidableEq Λ] {x y : Λ} (hxy : x ≠ y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    basisSwap σ x y ≠ σ :=
  basisSwap_ne_self hxy h

/-! ## D: inner-product family (#272-#278) -/

/-- Antiparallel `⟨σ, S·S σ⟩ = -1/4`. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    ∑ τ : Λ → Fin 2,
        basisVec σ τ *
          ((spinHalfDot x y).mulVec (basisVec σ)) τ = -(1 / 4 : ℂ) :=
  inner_basisVec_spinHalfDot_basisVec_antiparallel hxy σ h

/-- Parallel `⟨σ, S·S σ⟩ = +1/4`. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x = σ y) :
    ∑ τ : Λ → Fin 2,
        basisVec σ τ *
          ((spinHalfDot x y).mulVec (basisVec σ)) τ = (1 / 4 : ℂ) :=
  inner_basisVec_spinHalfDot_basisVec_parallel hxy σ h

/-- `S^z·S^z` eigenvalue on basis vectors. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (x y : Λ)
    (σ : Λ → Fin 2) :
    (onSite x spinHalfOp3 * onSite y spinHalfOp3 :
        ManyBodyOp Λ).mulVec (basisVec σ) =
      (spinHalfSign (σ x) * spinHalfSign (σ y)) • basisVec σ :=
  onSite_spinHalfOp3_mul_onSite_spinHalfOp3_mulVec_basisVec x y σ

/-- Off-diagonal correlator vanishes on antiparallel basis vectors. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin 2) (h : σ x ≠ σ y) :
    ∑ τ : Λ → Fin 2,
        basisVec σ τ *
          ((spinHalfDot x y -
              (onSite x spinHalfOp3 * onSite y spinHalfOp3) :
              ManyBodyOp Λ).mulVec (basisVec σ)) τ = 0 :=
  inner_basisVec_spinHalfDot_sub_szsz_basisVec_antiparallel hxy σ h

/-! ## A. decide-based universal: `basisSwap` properties on `Fin 2`
of `Fin 2 → Fin 2` -/

/-- `basisSwap σ 0 1` is involutive on every `σ : Fin 2 → Fin 2`
(universally over the 4 configurations). -/
example :
    ∀ σ : Fin 2 → Fin 2,
        basisSwap (basisSwap σ (0 : Fin 2) 1) 0 1 = σ := by
  intro σ; exact basisSwap_involutive (by decide) σ

/-! ## C + G: `spinHalfDot 0 1` raising/lowering decomposition pin -/

/-- `spinHalfDot x y = (1/2)(S^+S^- + S^-S^+) + S^z S^z`
(reaffirmed; refactor-resilience pin via the named lemma). -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (x y : Λ) :
    (spinHalfDot x y : ManyBodyOp Λ) =
      (1 / 2 : ℂ) •
        (onSite x spinHalfOpPlus * onSite y spinHalfOpMinus +
          onSite x spinHalfOpMinus * onSite y spinHalfOpPlus) +
        onSite x spinHalfOp3 * onSite y spinHalfOp3 :=
  spinHalfDot_eq_plus_minus x y

end LatticeSystem.Tests.SpinDot
