/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.ManyBody
import LatticeSystem.Quantum.Pauli
import LatticeSystem.Quantum.SpinHalf
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.HeisenbergLattice
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

Sub-files extending this module (Phase 2 PR 24 split, plan v4
§3.1):

| sub-file | content |
|---|---|
| `TimeReversalMulti/SpinOpEquivariance.lean` | per-axis `Θ̂_tot Ŝ^(α)_x = |
|                                             | -Ŝ^(α)_x Θ̂_tot` (Tasaki eq. |
|                                             | (2.3.14) lattice extension), |
|                                             | site-flip predicates |
| `TimeReversalMulti/Heisenberg.lean` | `Θ̂_tot · H_Heisenberg = H · Θ̂_tot` |
|                                     | for chain (open / periodic), |
|                                     | 2D / 3D Heisenberg (concrete |
|                                     | mulVec lemmas), and the two-site |
|                                     | singlet / triplet `Θ̂_tot` action |

Downstream code wanting the equivariance / Heisenberg-invariance
companion family should import the sub-modules directly (this
file is content + extensions, not a façade).
-/

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

omit [DecidableEq Λ] in
/-- Pointwise unfolding of `Θ̂_tot`. -/
theorem timeReversalSpinHalfMulti_apply
    (v : (Λ → Fin 2) → ℂ) (τ : Λ → Fin 2) :
    timeReversalSpinHalfMulti v τ =
      (∏ x : Λ, timeReversalSign (τ x)) *
        starRingEnd ℂ (v (flipConfig τ)) := rfl

omit [DecidableEq Λ] in
/-- Multi-spin `Θ̂_tot` is additive: `Θ̂_tot (v + w) = Θ̂_tot v + Θ̂_tot w`. -/
theorem timeReversalSpinHalfMulti_add
    (v w : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (v + w) =
      timeReversalSpinHalfMulti v + timeReversalSpinHalfMulti w := by
  funext τ
  simp only [timeReversalSpinHalfMulti_apply, Pi.add_apply, map_add]
  ring

omit [DecidableEq Λ] in
/-- Multi-spin `Θ̂_tot` is **antilinear** in the scalar:
`Θ̂_tot (c • v) = (conj c) • Θ̂_tot v`. -/
theorem timeReversalSpinHalfMulti_smul
    (c : ℂ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti (c • v) =
      (starRingEnd ℂ c) • timeReversalSpinHalfMulti v := by
  funext τ
  simp only [timeReversalSpinHalfMulti_apply, Pi.smul_apply,
    smul_eq_mul, map_mul]
  ring

omit [DecidableEq Λ] in
/-- Multi-spin `Θ̂_tot` is real-linear in the scalar (special case
of antilinearity at real `r`). -/
theorem timeReversalSpinHalfMulti_real_smul
    (r : ℝ) (v : (Λ → Fin 2) → ℂ) :
    timeReversalSpinHalfMulti ((r : ℂ) • v) =
      (r : ℂ) • timeReversalSpinHalfMulti v := by
  rw [timeReversalSpinHalfMulti_smul]
  congr 1
  exact (Complex.conj_ofReal r).symm ▸ Complex.conj_ofReal r

omit [DecidableEq Λ] in
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

omit [DecidableEq Λ] in
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

omit [DecidableEq Λ] in
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

omit [DecidableEq Λ] in
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

end LatticeSystem.Quantum
