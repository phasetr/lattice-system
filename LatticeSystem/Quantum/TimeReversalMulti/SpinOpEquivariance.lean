/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TimeReversalMulti

/-!
# Time-reversal per-axis spin-operator equivariance (Tasaki §2.3 (2.3.14))

The per-axis sign-flip lemmas
`Θ̂_tot Ŝ^(α)_x = -Ŝ^(α)_x Θ̂_tot` for α = 1, 2, 3, including
the σ^x / σ^y / σ^z (Pauli) variants.

(Refactor Phase 2 PR 24 — second TimeReversalMulti extraction,
plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Multi-site spin sign flip: `Θ̂_tot σ^z_x = -σ^z_x Θ̂_tot`

Tasaki §2.3 eq. (2.3.14) lifted to many-body operators: each
single-site Pauli `σ^(α)_x = onSite x σ^(α)` anticommutes (under
the antilinear conjugation) with the multi-spin time-reversal,

  `Θ̂_tot ((onSite x A) v) = (-(onSite x A))(Θ̂_tot v)`

for `A ∈ {σ^x, σ^y, σ^z}`. We start with the diagonal case
`A = σ^z`, where the action on a vector reduces to a pointwise
sign multiplication. The off-diagonal cases (`σ^x`, `σ^y`) are
deferred and require a `siteFlipAt` swap analysis. -/

/-- Pointwise unfolding of `(onSite x pauliZ).mulVec v`: since
`σ^z` is diagonal, the action is multiplication by
`if τ x = 0 then 1 else -1` at every configuration `τ`. -/
private theorem onSite_pauliZ_mulVec_apply
    (x : Λ) (v : (Λ → Fin 2) → ℂ) (τ : Λ → Fin 2) :
    ((onSite x pauliZ).mulVec v) τ =
      (if τ x = 0 then (1 : ℂ) else -1) * v τ := by
  unfold Matrix.mulVec dotProduct
  rw [show (∑ σ : Λ → Fin 2, (onSite x pauliZ) τ σ * v σ) =
      ∑ σ : Λ → Fin 2,
        (if σ = τ then (if τ x = 0 then (1 : ℂ) else -1) * v σ else 0)
    from ?_]
  · rw [Finset.sum_ite_eq']
    simp
  · apply Finset.sum_congr rfl
    intro σ _
    simp only [onSite_apply]
    by_cases hagree : ∀ k, k ≠ x → τ k = σ k
    · -- τ and σ agree off site x
      rw [if_pos hagree]
      by_cases hx : τ x = σ x
      · -- τ x = σ x ⇒ τ = σ
        have hτσ : τ = σ := by
          funext k
          by_cases hk : k = x
          · rw [hk]; exact hx
          · exact hagree k hk
        rw [if_pos hτσ.symm]
        rw [hτσ]
        match h : σ x with
        | 0 => simp [pauliZ]
        | 1 => simp [pauliZ]
      · -- τ x ≠ σ x ⇒ τ ≠ σ; pauliZ off-diagonal = 0
        have hτσ : σ ≠ τ := by
          intro h
          apply hx
          rw [h]
        rw [if_neg hτσ]
        match hτ : τ x, hσ : σ x with
        | 0, 0 => exact absurd (hτ.trans hσ.symm) hx
        | 0, 1 => simp [pauliZ]
        | 1, 0 => simp [pauliZ]
        | 1, 1 => exact absurd (hτ.trans hσ.symm) hx
    · rw [if_neg hagree]
      have hστ : σ ≠ τ := by
        intro h
        apply hagree
        intro k _
        rw [h]
      rw [if_neg hστ, zero_mul]

/-- Multi-site sign-flip equivariance for `σ^z` (Tasaki §2.3
(2.3.14) at `α = 3`): for every `x : Λ` and every state `v`,

  `Θ̂_tot ((onSite x σ^z) v) = (-(onSite x σ^z))(Θ̂_tot v)`.

Proof: both sides reduce via `onSite_pauliZ_mulVec_apply` to a
sign-multiplication on `v`. The two sign factors `(if τ x = 0)`
and `(if (flip τ) x = 0)` are swapped, and the explicit minus on
the RHS exactly compensates. -/
theorem timeReversalSpinHalfMulti_onSite_pauliZ_mulVec
    (x : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x pauliZ).mulVec v) =
      (-(onSite x pauliZ)).mulVec
        (timeReversalSpinHalfMulti v) := by
  funext τ
  rw [Matrix.neg_mulVec, Pi.neg_apply,
    onSite_pauliZ_mulVec_apply,
    timeReversalSpinHalfMulti_apply,
    timeReversalSpinHalfMulti_apply,
    onSite_pauliZ_mulVec_apply]
  by_cases hτx : τ x = 0
  · have hflipτx : (flipConfig τ) x = 1 := by simp [flipConfig, hτx]
    rw [hτx, hflipτx]
    simp
  · have hτx1 : τ x = 1 := by
      match hτ : τ x with
      | 0 => exact absurd hτ hτx
      | 1 => rfl
    have hflipτx : (flipConfig τ) x = 0 := by simp [flipConfig, hτx1]
    rw [hτx1, hflipτx]
    simp

/-! ## Per-site flip helpers (`siteFlipAt`)

The `siteFlipAt` operation flips a single slot `x` of a
configuration, leaving every other slot fixed. This is the
combinatorial primitive underlying the action of off-diagonal
single-site Pauli operators (`σ^x_x`, `σ^y_x`) which swap the
spin at site `x`.

These helpers package the basic identities; the actual
multi-site sign-flip equivariance for `σ^x`/`σ^y` (extending the
`σ^z` lemma above) is deferred. -/

/-- Per-site spin flip of a configuration: swap slot `x` only,
leaving other slots fixed.

  `siteFlipAt τ x y = if y = x then 1 - τ y else τ y`. -/
def siteFlipAt (τ : Λ → Fin 2) (x : Λ) : Λ → Fin 2 :=
  Function.update τ x (1 - τ x)

omit [Fintype Λ] in
@[simp] theorem siteFlipAt_self (τ : Λ → Fin 2) (x : Λ) :
    siteFlipAt τ x x = 1 - τ x := by
  unfold siteFlipAt
  rw [Function.update_self]

omit [Fintype Λ] in
/-- `siteFlipAt τ x` leaves site `y ≠ x` unchanged. -/
theorem siteFlipAt_of_ne (τ : Λ → Fin 2) {x y : Λ} (h : y ≠ x) :
    siteFlipAt τ x y = τ y := by
  unfold siteFlipAt
  rw [Function.update_of_ne h]

omit [Fintype Λ] in
/-- `flipConfig` and `siteFlipAt` commute: flipping every site and
then flipping site `x` again equals flipping site `x` first then
every site. -/
theorem flipConfig_siteFlipAt_comm (τ : Λ → Fin 2) (x : Λ) :
    flipConfig (siteFlipAt τ x) = siteFlipAt (flipConfig τ) x := by
  funext y
  by_cases hy : y = x
  · rw [hy, flipConfig_apply, siteFlipAt_self, siteFlipAt_self,
        flipConfig_apply]
  · rw [flipConfig_apply, siteFlipAt_of_ne _ hy,
        siteFlipAt_of_ne _ hy, flipConfig_apply]

omit [Fintype Λ] in
/-- `siteFlipAt` is involutive: flipping the same site twice
returns the original configuration. -/
theorem siteFlipAt_involutive (τ : Λ → Fin 2) (x : Λ) :
    siteFlipAt (siteFlipAt τ x) x = τ := by
  funext y
  by_cases hy : y = x
  · rw [hy, siteFlipAt_self, siteFlipAt_self]
    match h : τ x with
    | 0 => simp
    | 1 => simp
  · rw [siteFlipAt_of_ne _ hy, siteFlipAt_of_ne _ hy]

/-- Action of `(onSite x σ^x)` on a basis vector: it swaps the
spin at site `x`. Tasaki §2.2-style identity for the off-diagonal
Pauli `σ^x`:

  `(onSite x σ^x).mulVec (basisVec σ) = basisVec (siteFlipAt σ x)`.

Direct corollary of `onSite_mulVec_basisVec` together with the
single-site `pauliX` matrix entries: `pauliX k (σ x) = 1` iff
`k = 1 - σ x`, else `0`. -/
theorem onSite_pauliX_mulVec_basisVec (x : Λ) (σ : Λ → Fin 2) :
    ((onSite x pauliX).mulVec (basisVec σ) : (Λ → Fin 2) → ℂ) =
      basisVec (siteFlipAt σ x) := by
  rw [onSite_mulVec_basisVec]
  funext τ
  rw [Fin.sum_univ_two]
  unfold basisVec siteFlipAt
  match h : σ x with
  | 0 =>
    -- pauliX 0 0 = 0, pauliX 1 0 = 1; updated value 1 = 1 - 0
    simp [pauliX]
  | 1 =>
    -- pauliX 0 1 = 1, pauliX 1 1 = 0; updated value 0 = 1 - 1
    simp [pauliX]

/-- Closed-form indicator for `pauliX`: `pauliX a b = 1` iff
`b = 1 - a`, else `0`. The off-diagonal Pauli matrix viewed as a
spin-flip indicator. -/
private theorem pauliX_eq_indicator (a b : Fin 2) :
    pauliX a b = (if b = 1 - a then (1 : ℂ) else 0) := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Pointwise unfolding of `(onSite x pauliX).mulVec v`: the
off-diagonal action sends `v τ` to `v (siteFlipAt τ x)`.

  `((onSite x σ^x).mulVec v) τ = v (siteFlipAt τ x)`. -/
theorem onSite_pauliX_mulVec_apply
    (x : Λ) (v : (Λ → Fin 2) → ℂ) (τ : Λ → Fin 2) :
    ((onSite x pauliX).mulVec v) τ = v (siteFlipAt τ x) := by
  unfold Matrix.mulVec dotProduct
  -- Replace each summand by an indicator-shaped expression, then
  -- reduce via `Fintype.sum_eq_single`.
  rw [show (∑ σ : Λ → Fin 2, (onSite x pauliX) τ σ * v σ)
        = ∑ σ : Λ → Fin 2,
            (if σ = siteFlipAt τ x then v σ else 0) from ?_]
  · rw [Finset.sum_ite_eq']
    simp
  · apply Finset.sum_congr rfl
    intro σ _
    simp only [onSite_apply]
    by_cases hagree : ∀ k, k ≠ x → τ k = σ k
    · -- agree off x: matrix entry = pauliX (τ x) (σ x) = indicator [σ x = 1 - τ x]
      rw [if_pos hagree, pauliX_eq_indicator]
      by_cases hsx : σ x = 1 - τ x
      · -- σ = siteFlipAt τ x
        have hσ : σ = siteFlipAt τ x := by
          funext k
          by_cases hk : k = x
          · rw [hk, siteFlipAt_self]; exact hsx
          · rw [siteFlipAt_of_ne _ hk]; exact (hagree k hk).symm
        rw [if_pos hsx, if_pos hσ, one_mul]
      · -- σ ≠ siteFlipAt τ x (since they differ at x)
        have hσ : σ ≠ siteFlipAt τ x := by
          intro h
          apply hsx
          rw [h, siteFlipAt_self]
        rw [if_neg hsx, if_neg hσ, zero_mul]
    · -- disagree off x: matrix entry = 0; also σ ≠ siteFlipAt τ x
      have hσ : σ ≠ siteFlipAt τ x := by
        intro h
        apply hagree
        intro k hk
        rw [h, siteFlipAt_of_ne _ hk]
      rw [if_neg hagree, if_neg hσ, zero_mul]

/-- The sign-product flips by `-1` under `siteFlipAt`: for any
configuration `τ` and site `x`,

  `∏_y ε((siteFlipAt τ x) y) = -(∏_y ε(τ y))`.

(One factor `ε(τ x)` is replaced by `ε(1 - τ x) = -ε(τ x)`.) -/
theorem timeReversalSign_prod_siteFlipAt (τ : Λ → Fin 2) (x : Λ) :
    (∏ y : Λ, timeReversalSign ((siteFlipAt τ x) y)) =
      -(∏ y : Λ, timeReversalSign (τ y)) := by
  have h_at : timeReversalSign ((siteFlipAt τ x) x)
      = -timeReversalSign (τ x) := by
    rw [siteFlipAt_self]
    match h : τ x with
    | 0 => simp [timeReversalSign]
    | 1 => simp [timeReversalSign]
  have h_off : (∏ y ∈ Finset.univ.erase x,
        timeReversalSign ((siteFlipAt τ x) y)) =
      ∏ y ∈ Finset.univ.erase x, timeReversalSign (τ y) := by
    apply Finset.prod_congr rfl
    intro y hy
    rw [Finset.mem_erase] at hy
    rw [siteFlipAt_of_ne _ hy.1]
  calc (∏ y : Λ, timeReversalSign ((siteFlipAt τ x) y))
      = timeReversalSign ((siteFlipAt τ x) x)
          * ∏ y ∈ Finset.univ.erase x,
              timeReversalSign ((siteFlipAt τ x) y) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x)]
    _ = (-timeReversalSign (τ x))
          * ∏ y ∈ Finset.univ.erase x, timeReversalSign (τ y) := by
        rw [h_at, h_off]
    _ = -(timeReversalSign (τ x)
          * ∏ y ∈ Finset.univ.erase x, timeReversalSign (τ y)) := by
        ring
    _ = -(∏ y : Λ, timeReversalSign (τ y)) := by
        congr 1
        exact Finset.mul_prod_erase Finset.univ
          (fun y => timeReversalSign (τ y)) (Finset.mem_univ x)

/-! ### `σ^y` analogue (`α = 2`) -/

/-- Per-site sign factor for the `σ^y` action: `s ↦ -i` if
`s = 0` (down ← up), `s ↦ +i` if `s = 1` (up ← down). -/
private def pauliY_sign (s : Fin 2) : ℂ :=
  if s = 0 then -Complex.I else Complex.I

/-- Closed-form indicator for `pauliY`:
`pauliY a b = if b = 1 - a then pauliY_sign(a) else 0`. -/
private theorem pauliY_eq_indicator (a b : Fin 2) :
    pauliY a b =
      (if b = 1 - a then pauliY_sign a else 0) := by
  fin_cases a <;> fin_cases b <;> rfl

/-- Pointwise unfolding of `(onSite x pauliY).mulVec v`:

  `((onSite x σ^y).mulVec v) τ = pauliY_sign(τ x) · v (siteFlipAt τ x)`. -/
private theorem onSite_pauliY_mulVec_apply
    (x : Λ) (v : (Λ → Fin 2) → ℂ) (τ : Λ → Fin 2) :
    ((onSite x pauliY).mulVec v) τ =
      pauliY_sign (τ x) * v (siteFlipAt τ x) := by
  unfold Matrix.mulVec dotProduct
  rw [show (∑ σ : Λ → Fin 2, (onSite x pauliY) τ σ * v σ)
        = ∑ σ : Λ → Fin 2,
            (if σ = siteFlipAt τ x then pauliY_sign (τ x) * v σ
              else 0) from ?_]
  · rw [Finset.sum_ite_eq']
    simp
  · apply Finset.sum_congr rfl
    intro σ _
    simp only [onSite_apply]
    by_cases hagree : ∀ k, k ≠ x → τ k = σ k
    · rw [if_pos hagree, pauliY_eq_indicator]
      by_cases hsx : σ x = 1 - τ x
      · have hσ : σ = siteFlipAt τ x := by
          funext k
          by_cases hk : k = x
          · rw [hk, siteFlipAt_self]; exact hsx
          · rw [siteFlipAt_of_ne _ hk]; exact (hagree k hk).symm
        rw [if_pos hsx, if_pos hσ]
      · have hσ : σ ≠ siteFlipAt τ x := by
          intro h
          apply hsx
          rw [h, siteFlipAt_self]
        rw [if_neg hsx, if_neg hσ, zero_mul]
    · have hσ : σ ≠ siteFlipAt τ x := by
        intro h
        apply hagree
        intro k hk
        rw [h, siteFlipAt_of_ne _ hk]
      rw [if_neg hagree, if_neg hσ, zero_mul]

/-- Conjugation flips `pauliY_sign`: `conj(pauliY_sign(1 - s)) = pauliY_sign(s)`. -/
private theorem conj_pauliY_sign_flip (s : Fin 2) :
    starRingEnd ℂ (pauliY_sign (1 - s)) = pauliY_sign s := by
  match s with
  | 0 => simp [pauliY_sign]
  | 1 => simp [pauliY_sign]

/-- Multi-site sign-flip equivariance for `σ^y` (Tasaki §2.3
(2.3.14) at `α = 2`):

  `Θ̂_tot ((onSite x σ^y) v) = (-(onSite x σ^y))(Θ̂_tot v)`.

The proof structure mirrors the `σ^x` case but uses
`pauliY_sign` (the per-site `±i` factor) instead of `1`. The
extra `conj` cancellation `conj(pauliY_sign(1 - s)) = pauliY_sign(s)`
ensures the two factors-of-`i` line up. -/
theorem timeReversalSpinHalfMulti_onSite_pauliY_mulVec
    (x : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x pauliY).mulVec v) =
      (-(onSite x pauliY)).mulVec
        (timeReversalSpinHalfMulti v) := by
  funext τ
  rw [Matrix.neg_mulVec, Pi.neg_apply,
    onSite_pauliY_mulVec_apply,
    timeReversalSpinHalfMulti_apply,
    timeReversalSpinHalfMulti_apply,
    onSite_pauliY_mulVec_apply,
    ← flipConfig_siteFlipAt_comm,
    timeReversalSign_prod_siteFlipAt]
  -- LHS: (∏ ε(τ y)) · conj(pauliY_sign((flip τ) x) · v(siteFlipAt(flip τ) x))
  -- RHS: -(pauliY_sign(τ x) · (-(∏ ε(τ y))) · conj(v(flip(siteFlipAt τ x))))
  --    = pauliY_sign(τ x) · (∏ ε(τ y)) · conj(v(siteFlipAt(flip τ) x))
  -- Need: conj(pauliY_sign((flip τ) x)) = pauliY_sign(τ x).
  rw [show ((flipConfig τ) x) = 1 - τ x from rfl,
      map_mul, conj_pauliY_sign_flip]
  ring

/-- Multi-site sign-flip equivariance for `σ^x` (Tasaki §2.3
(2.3.14) at `α = 1`):

  `Θ̂_tot ((onSite x σ^x) v) = (-(onSite x σ^x))(Θ̂_tot v)`.

Proof: both sides reduce via `onSite_pauliX_mulVec_apply` to a
`v` evaluated at `siteFlipAt _ x` (after using
`flipConfig_siteFlipAt_comm` to identify `flip(siteFlipAt τ x)`
with `siteFlipAt(flip τ) x`). The sign-product factors differ by
`-1` (one `ε(τ x)` becomes `ε(1 - τ x)`), exactly cancelling the
explicit minus on the right. -/
theorem timeReversalSpinHalfMulti_onSite_pauliX_mulVec
    (x : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((onSite x pauliX).mulVec v) =
      (-(onSite x pauliX)).mulVec
        (timeReversalSpinHalfMulti v) := by
  funext τ
  rw [Matrix.neg_mulVec, Pi.neg_apply,
    onSite_pauliX_mulVec_apply,
    timeReversalSpinHalfMulti_apply,
    timeReversalSpinHalfMulti_apply,
    onSite_pauliX_mulVec_apply,
    ← flipConfig_siteFlipAt_comm,
    timeReversalSign_prod_siteFlipAt]
  ring

/-! ### `Ŝ^(α)` analogues — Tasaki eq. (2.3.14) for spin-1/2 ops

These are direct corollaries of the corresponding `σ^(α)` Pauli
versions via `Ŝ^(α) = (1/2) • σ^(α)`. -/

/-- Multi-site sign-flip equivariance for `Ŝ^(1) = σ^x / 2`:

  `Θ̂_tot ((onSite x Ŝ^(1)) v) = (-(onSite x Ŝ^(1)))(Θ̂_tot v)`.

Direct corollary of the `σ^x` version
(`timeReversalSpinHalfMulti_onSite_pauliX_mulVec`) by scalar
multiplication. -/
theorem timeReversalSpinHalfMulti_onSite_spinHalfOp1_mulVec
    (x : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((onSite x spinHalfOp1).mulVec v) =
      (-(onSite x spinHalfOp1)).mulVec
        (timeReversalSpinHalfMulti v) := by
  unfold spinHalfOp1
  rw [onSite_smul, Matrix.smul_mulVec,
    timeReversalSpinHalfMulti_smul,
    show starRingEnd ℂ ((1 : ℂ) / 2) = 1 / 2 from by
      rw [map_div₀]; simp [Complex.conj_ofNat],
    timeReversalSpinHalfMulti_onSite_pauliX_mulVec]
  rw [← smul_neg, Matrix.smul_mulVec]

/-- Multi-site sign-flip equivariance for `Ŝ^(2) = σ^y / 2`. -/
theorem timeReversalSpinHalfMulti_onSite_spinHalfOp2_mulVec
    (x : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((onSite x spinHalfOp2).mulVec v) =
      (-(onSite x spinHalfOp2)).mulVec
        (timeReversalSpinHalfMulti v) := by
  unfold spinHalfOp2
  rw [onSite_smul, Matrix.smul_mulVec,
    timeReversalSpinHalfMulti_smul,
    show starRingEnd ℂ ((1 : ℂ) / 2) = 1 / 2 from by
      rw [map_div₀]; simp [Complex.conj_ofNat],
    timeReversalSpinHalfMulti_onSite_pauliY_mulVec]
  rw [← smul_neg, Matrix.smul_mulVec]

/-- Multi-site sign-flip equivariance for `Ŝ^(3) = σ^z / 2`. -/
theorem timeReversalSpinHalfMulti_onSite_spinHalfOp3_mulVec
    (x : Λ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti
        ((onSite x spinHalfOp3).mulVec v) =
      (-(onSite x spinHalfOp3)).mulVec
        (timeReversalSpinHalfMulti v) := by
  unfold spinHalfOp3
  rw [onSite_smul, Matrix.smul_mulVec,
    timeReversalSpinHalfMulti_smul,
    show starRingEnd ℂ ((1 : ℂ) / 2) = 1 / 2 from by
      rw [map_div₀]; simp [Complex.conj_ofNat],
    timeReversalSpinHalfMulti_onSite_pauliZ_mulVec]
  rw [← smul_neg, Matrix.smul_mulVec]


end LatticeSystem.Quantum
