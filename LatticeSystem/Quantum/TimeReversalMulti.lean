/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.TimeReversalSpinHalf

/-!
# Multi-spin time-reversal map (Tasaki §2.3, lattice extension, S = 1/2)

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
§2.3 (pp. 26–29) extends the single-spin time-reversal map
`Θ̂ := û_2 · K̂` to a many-body system as the tensor product

  `Θ̂_tot := ⊗_{x ∈ Λ} Θ̂_x`.

For `S = 1/2` and `Λ` finite, this acts on the many-body Hilbert
space `(Λ → Fin 2) → ℂ` by

  `(Θ̂_tot v) τ = (∏_{x ∈ Λ} ε(τ x)) · conj(v (flip τ))`

where `flip τ x := 1 - τ x` is the spin-flipped configuration and
`ε(0) := 1`, `ε(1) := -1` is the single-site sign factor coming
from `Θ̂_x |↑⟩ = |↓⟩` (no sign), `Θ̂_x |↓⟩ = -|↑⟩` (sign `-1`).

This module formalises the multi-site map and proves the
**Kramers degeneracy** (Tasaki §2.3 (2.3.8) extension):

  `Θ̂_tot² = (-1)^|Λ| · 1̂`,

so the action squares to `+1̂` when `|Λ|` is even and to `-1̂` when
`|Λ|` is odd. This is the explicit `S = 1/2` instance of Tasaki's
half-odd-integer-spin Kramers result `Θ̂² = (-1)^(2 S |Λ|)`.

For finiteness reasons we work with `[Fintype Λ] [DecidableEq Λ]`.
The map is implemented as a plain function on the many-body
state vector (antilinearity prevents a `Matrix` representation).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace LatticeSystem.Quantum

open Complex

/-- The spin-flip on a configuration: `flipConfig σ x := 1 - σ x`.
For `σ x : Fin 2`, this swaps `0 ↔ 1`. -/
def flipConfig {Λ : Type*} (σ : Λ → Fin 2) : Λ → Fin 2 :=
  fun x => 1 - σ x

@[simp] theorem flipConfig_apply {Λ : Type*}
    (σ : Λ → Fin 2) (x : Λ) :
    flipConfig σ x = 1 - σ x := rfl

/-- `flipConfig` is involutive: flipping twice returns the original. -/
theorem flipConfig_involutive {Λ : Type*} (σ : Λ → Fin 2) :
    flipConfig (flipConfig σ) = σ := by
  funext x
  match h : σ x with
  | 0 => simp [flipConfig, h]
  | 1 => simp [flipConfig, h]

/-- The single-site sign factor `ε : Fin 2 → ℂ` from
`Θ̂_x |↑⟩ = |↓⟩` (`ε(0) = 1`) and `Θ̂_x |↓⟩ = -|↑⟩`
(`ε(1) = -1`). -/
def timeReversalSign (s : Fin 2) : ℂ :=
  if s = 0 then 1 else -1

@[simp] theorem timeReversalSign_zero :
    timeReversalSign (0 : Fin 2) = 1 := by simp [timeReversalSign]

@[simp] theorem timeReversalSign_one :
    timeReversalSign (1 : Fin 2) = -1 := by simp [timeReversalSign]

/-- `ε(s) · ε(1 - s) = -1`: the two opposite-spin signs cancel
into a single `-1` (the `S = 1/2` Kramers minus sign at one
site). -/
theorem timeReversalSign_mul_flip (s : Fin 2) :
    timeReversalSign s * timeReversalSign (1 - s) = -1 := by
  match s with
  | 0 => simp [timeReversalSign]
  | 1 => simp [timeReversalSign]

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Multi-spin time-reversal map for `S = 1/2` (Tasaki §2.3
lattice extension):

  `(Θ̂_tot v) τ := (∏_{x ∈ Λ} ε(τ x)) · conj(v (flip τ))`.

For finite `Λ` this is the tensor product `⊗_{x ∈ Λ} Θ̂_x` of the
single-spin `timeReversalSpinHalf`. -/
noncomputable def timeReversalSpinHalfMulti
    (v : (Λ → Fin 2) → ℂ) : (Λ → Fin 2) → ℂ :=
  fun τ =>
    (∏ x : Λ, timeReversalSign (τ x)) * starRingEnd ℂ (v (flipConfig τ))

/-- Pointwise unfolding of `Θ̂_tot`. -/
theorem timeReversalSpinHalfMulti_apply
    (v : (Λ → Fin 2) → ℂ) (τ : Λ → Fin 2) :
    timeReversalSpinHalfMulti v τ =
      (∏ x : Λ, timeReversalSign (τ x)) *
        starRingEnd ℂ (v (flipConfig τ)) := rfl

/-- The product of `ε(τ x)` over `Λ` is real: it is either `+1` or
`-1` depending on parity. -/
theorem timeReversalSign_prod_conj (τ : Λ → Fin 2) :
    starRingEnd ℂ (∏ x : Λ, timeReversalSign (τ x)) =
      ∏ x : Λ, timeReversalSign (τ x) := by
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro x _
  match τ x with
  | 0 => simp [timeReversalSign]
  | 1 => simp [timeReversalSign]

/-- The product of `ε(τ x) · ε((flip τ) x)` over `x ∈ Λ` equals
`(-1)^|Λ|`. Combines the per-site `timeReversalSign_mul_flip`
identity with `Finset.prod_mul_distrib`. -/
theorem timeReversalSign_prod_mul_flip (τ : Λ → Fin 2) :
    (∏ x : Λ, timeReversalSign (τ x)) *
      (∏ x : Λ, timeReversalSign ((flipConfig τ) x)) =
      (-1 : ℂ) ^ (Fintype.card Λ) := by
  rw [← Finset.prod_mul_distrib]
  have h : (∀ x ∈ (Finset.univ : Finset Λ),
      timeReversalSign (τ x) * timeReversalSign ((flipConfig τ) x)
        = -1) := by
    intro x _
    simpa [flipConfig] using timeReversalSign_mul_flip (τ x)
  rw [Finset.prod_congr rfl h]
  simp [Finset.card_univ]

/-- **Kramers degeneracy at `S = 1/2`, multi-spin** (Tasaki §2.3
half-odd-integer extension): for finite `Λ`,

  `Θ̂_tot² = (-1)^|Λ| · 1̂`,

i.e. for every state `v : (Λ → Fin 2) → ℂ`,

  `Θ̂_tot (Θ̂_tot v) = (-1)^|Λ| • v`.

Specialises to `Θ̂² = -1̂` when `|Λ|` is odd and to `Θ̂² = +1̂`
when `|Λ|` is even (so the single-site `Θ̂² = -1̂` of
`timeReversalSpinHalf_sq` is the `|Λ| = 1` case via the obvious
`Fin 1 → Fin 2 ≃ Fin 2` identification). -/
theorem timeReversalSpinHalfMulti_sq (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (timeReversalSpinHalfMulti v) =
      ((-1 : ℂ) ^ (Fintype.card Λ)) • v := by
  funext τ
  simp only [timeReversalSpinHalfMulti_apply, Pi.smul_apply,
    smul_eq_mul, map_mul, timeReversalSign_prod_conj,
    flipConfig_involutive]
  rw [Complex.conj_conj]
  rw [show (∏ x : Λ, timeReversalSign (τ x)) *
        ((∏ x : Λ, timeReversalSign ((flipConfig τ) x)) * v τ) =
      ((∏ x : Λ, timeReversalSign (τ x)) *
        (∏ x : Λ, timeReversalSign ((flipConfig τ) x))) * v τ from by
        ring]
  rw [timeReversalSign_prod_mul_flip]

/-- Action of `Θ̂_tot` on a many-body basis state
`|Ψ_σ⟩ = basisVec σ`:

  `Θ̂_tot (basisVec σ) = (∏_x ε(flip σ x)) · basisVec (flip σ)`.

This is the natural generalisation of the single-spin
`Θ̂|↑⟩ = |↓⟩`, `Θ̂|↓⟩ = -|↑⟩` to many sites: each "down" spin
in the *flipped* configuration contributes a sign `-1`, so the
total sign is `(-1)^|{x : (flip σ) x = 1}| = (-1)^|{x : σ x = 0}|`.
At a single site (`|Λ| = 1`), this recovers
`Θ̂|↑⟩ = (-1)^0 · |↓⟩ = |↓⟩` and
`Θ̂|↓⟩ = (-1)^1 · |↑⟩ = -|↑⟩`. -/
theorem timeReversalSpinHalfMulti_basisVec (σ : Λ → Fin 2) :
    timeReversalSpinHalfMulti (basisVec σ) =
      (∏ x : Λ, timeReversalSign (flipConfig σ x)) •
        basisVec (flipConfig σ) := by
  funext τ
  simp only [timeReversalSpinHalfMulti_apply, basisVec, Pi.smul_apply,
    smul_eq_mul]
  by_cases hτ : τ = flipConfig σ
  · -- τ = flip σ: both sides reduce to ∏ ε(τ x).
    rw [if_pos hτ]
    have hflip : flipConfig τ = σ := by
      rw [hτ, flipConfig_involutive]
    rw [hflip, if_pos rfl]
    simp [hτ]
  · -- τ ≠ flip σ: both sides vanish.
    rw [if_neg hτ]
    have hflip : flipConfig τ ≠ σ := by
      intro h
      apply hτ
      rw [← h, flipConfig_involutive]
    rw [if_neg hflip]
    simp

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
        | 0 => simp [pauliZ, h]
        | 1 => simp [pauliZ, h]
      · -- τ x ≠ σ x ⇒ τ ≠ σ; pauliZ off-diagonal = 0
        have hτσ : σ ≠ τ := by
          intro h
          apply hx
          rw [h]
        rw [if_neg hτσ]
        match hτ : τ x, hσ : σ x with
        | 0, 0 => exact absurd (hτ.trans hσ.symm) hx
        | 0, 1 => simp [pauliZ, hτ, hσ]
        | 1, 0 => simp [pauliZ, hτ, hσ]
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

@[simp] theorem siteFlipAt_self (τ : Λ → Fin 2) (x : Λ) :
    siteFlipAt τ x x = 1 - τ x := by
  unfold siteFlipAt
  rw [Function.update_self]

theorem siteFlipAt_of_ne (τ : Λ → Fin 2) {x y : Λ} (h : y ≠ x) :
    siteFlipAt τ x y = τ y := by
  unfold siteFlipAt
  rw [Function.update_of_ne h]

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

/-- `siteFlipAt` is involutive: flipping the same site twice
returns the original configuration. -/
theorem siteFlipAt_involutive (τ : Λ → Fin 2) (x : Λ) :
    siteFlipAt (siteFlipAt τ x) x = τ := by
  funext y
  by_cases hy : y = x
  · rw [hy, siteFlipAt_self, siteFlipAt_self]
    match h : τ x with
    | 0 => simp [h]
    | 1 => simp [h]
  · rw [siteFlipAt_of_ne _ hy, siteFlipAt_of_ne _ hy]

end LatticeSystem.Quantum
