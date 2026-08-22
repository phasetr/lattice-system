import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel

/-!
# Tasaki §10.1: the superexchange operator identity (eq. (10.1.9)/(10.1.10))

Towards Theorem 10.4 (Lieb's repulsive-Hubbard half-filling theorem, Issue #5320, PR-7 of the
`theorem_10_4_lieb_repulsive_half_filling` discharge arc): the **model-independent** algebraic
identity underlying the strong-coupling second-order effective Hamiltonian (superexchange). For
two *distinct* sites `x ≠ y` on the spinful Jordan–Wigner backbone, the round-trip hopping sum

`Σ_{σ,τ} ĉ†_{y,τ} ĉ_{x,τ} ĉ†_{x,σ} ĉ_{y,σ}`

(a fermion hops `x → y` with spin `σ`, then a — possibly different-spin — fermion hops `y → x`
with spin `τ`, landing back on the original pair of sites) equals

`n̂_y − 2 Ŝ_x·Ŝ_y − ½ n̂_x n̂_y`.

This is Tasaki's eq. (10.1.9)/(10.1.10) (p. 344), the algebraic core from which the
strong-coupling perturbative reduction to the Heisenberg exchange term is built. Nothing here
depends on the half-filling sector, the hard-core projection, or the bipartite endpoint graph of
the Lieb-repulsive arc (PR-6, `LiebRepulsiveSuperexchangeReducedInverse.lean`); those enter only
at PR-8 (`LiebRepulsiveSuperexchange.lean`), which sandwiches this identity between the
kernel-projection `P₀` on the half-filled hard-core sector.

The proof route is via CAR (canonical anticommutation relations), not Jordan–Wigner sign
combinatorics: three anticommutation swaps move `ĉ†_{x,σ}` past `ĉ_{x,τ}` and `ĉ†_{y,τ}`, turning
the opposite-spin summand into `−Ŝ^{±}_y Ŝ^{∓}_x`, while the same-spin summand collapses via the
ordinary `n̂ = c†c` algebra to `n̂_{y,σ} − n̂_{x,σ} n̂_{y,σ}`. This route was chosen over
`HopSignBetween`'s Jordan–Wigner string-sign lemmas to avoid the four-way `x ≶ y`, `σ, τ`
case split on two different configurations, which is exactly where a silent overall-sign error
would hide.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §10.1, eq. (10.1.9)/(10.1.10), p. 344.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The hop-return operator** `Σ_{σ,τ} ĉ†_{y,τ} ĉ_{x,τ} ĉ†_{x,σ} ĉ_{y,σ}` (Tasaki eq. (10.1.9)):
a fermion hops `x → y` carrying spin `σ`, then a (possibly different-spin) fermion hops back
`y → x` carrying spin `τ`. Summed over both spin labels of the outgoing and returning hop, this
is the round-trip operator whose value between the two intermediate (singly-occupied-`x`,
doubly-occupied-`y`)  hard-core Fock states supplies the second-order strong-coupling
superexchange coefficient (PR-8). No hypothesis on `x, y` is built into the definition; the
identity below requires `x ≠ y`. -/
noncomputable def fermionHopReturn (N : ℕ) (x y : Fin (N + 1)) : ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ σ : Fin 2, ∑ τ : Fin 2,
    fermionMultiCreation (2 * N + 1) (spinfulIndex N y τ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x τ) *
        fermionMultiCreation (2 * N + 1) (spinfulIndex N x σ) *
      fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y σ)

/-- **Same-spin summand** (`σ = τ`). For a fixed spin label `σ` and `x ≠ y`,
`ĉ†_{y,σ} ĉ_{x,σ} ĉ†_{x,σ} ĉ_{y,σ} = n̂_{y,σ} − n̂_{x,σ} n̂_{y,σ}`: inserting
`ĉ_{x,σ} ĉ†_{x,σ} = 1 − n̂_{x,σ}` at the middle pair (both operators live at the same mode
`spinfulIndex N x σ`) and using `ĉ†_{y,σ} ĉ_{y,σ} = n̂_{y,σ}` at the outer pair. -/
theorem fermionHopReturn_same_spin_eq (N : ℕ) (x y : Fin (N + 1)) (hxy : x ≠ y) (σ : Fin 2) :
    fermionMultiCreation (2 * N + 1) (spinfulIndex N y σ) *
          fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x σ) *
          fermionMultiCreation (2 * N + 1) (spinfulIndex N x σ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y σ) =
      fermionMultiNumber (2 * N + 1) (spinfulIndex N y σ) -
        fermionMultiNumber (2 * N + 1) (spinfulIndex N x σ) *
          fermionMultiNumber (2 * N + 1) (spinfulIndex N y σ) := by
  sorry

/-- **Opposite-spin summand** (`σ ≠ τ`, hence `{σ, τ} = {0, 1}` in `Fin 2`). For `x ≠ y`,
`ĉ†_{y,τ} ĉ_{x,τ} ĉ†_{x,σ} ĉ_{y,σ} = − (ĉ†_{y,τ} ĉ_{y,σ}) (ĉ†_{x,σ} ĉ_{x,τ})`: three CAR
anticommutation swaps (`{ĉ_{x,τ}, ĉ†_{x,σ}} = 0` since `τ ≠ σ` are distinct modes at the same
site, `{ĉ_{x,τ}, ĉ_{y,σ}} = 0` and `{ĉ†_{x,σ}, ĉ_{y,σ}} = 0` since `x ≠ y`) move `ĉ†_{x,σ}` past
`ĉ_{x,τ}` and past `ĉ†_{y,τ}`, regrouping the four operators around the two sites `y` and `x`.
The right-hand-side factors are (up to sign) the spin ladder operators
`Ŝ^{(τσ)}_y := ĉ†_{y,τ} ĉ_{y,σ}` and `Ŝ^{(στ)}_x := ĉ†_{x,σ} ĉ_{x,τ}`. -/
theorem fermionHopReturn_opposite_spin_eq (N : ℕ) (x y : Fin (N + 1)) (hxy : x ≠ y)
    (σ τ : Fin 2) (hστ : σ ≠ τ) :
    fermionMultiCreation (2 * N + 1) (spinfulIndex N y τ) *
          fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x τ) *
          fermionMultiCreation (2 * N + 1) (spinfulIndex N x σ) *
        fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y σ) =
      -((fermionMultiCreation (2 * N + 1) (spinfulIndex N y τ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y σ)) *
          (fermionMultiCreation (2 * N + 1) (spinfulIndex N x σ) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N x τ))) := by
  sorry

/-- **Charge decomposition of the same-spin density-density sum.**
`Σ_σ n̂_{x,σ} n̂_{y,σ} = 2 (Ŝ^z_x Ŝ^z_y + ¼ n̂_x n̂_y)`: expand both sides into the four spin-label
products `n̂_{x,↑} n̂_{y,↑}`, `n̂_{x,↑} n̂_{y,↓}`, `n̂_{x,↓} n̂_{y,↑}`, `n̂_{x,↓} n̂_{y,↓}` and match
coefficients (no hypothesis on `x, y` is needed — this is a purely local algebraic rearrangement
of commuting number operators). -/
theorem sum_fermionMultiNumber_spinfulIndex_mul_eq (N : ℕ) (x y : Fin (N + 1)) :
    ∑ σ : Fin 2,
        fermionMultiNumber (2 * N + 1) (spinfulIndex N x σ) *
          fermionMultiNumber (2 * N + 1) (spinfulIndex N y σ) =
      (2 : ℂ) •
        (fermionSiteSpinZ N x * fermionSiteSpinZ N y +
          (1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)) := by
  sorry

/-- **Ladder decomposition of the two-site spin dot.** For `x ≠ y`,
`Ŝ⁺_y Ŝ⁻_x + Ŝ⁻_y Ŝ⁺_x = 2 (Ŝ_x·Ŝ_y − Ŝ^z_x Ŝ^z_y)`: the two-site ladder bilinears at `x` and
`y` commute (each is even in the fermion operators, and `x ≠ y` makes the underlying modes
disjoint), which lets the `y`-first pairing on the left be rewritten into the `x`-first pairing of
`fermionSpinDot`'s definition. -/
theorem fermionSiteSpinPlus_mul_Minus_add_fermionSiteSpinMinus_mul_Plus_eq
    (N : ℕ) (x y : Fin (N + 1)) (hxy : x ≠ y) :
    fermionSiteSpinPlus N y * fermionSiteSpinMinus N x +
        fermionSiteSpinMinus N y * fermionSiteSpinPlus N x =
      (2 : ℂ) • (fermionSpinDot N x y - fermionSiteSpinZ N x * fermionSiteSpinZ N y) := by
  sorry

/-- **The superexchange operator identity** (Tasaki eq. (10.1.9)/(10.1.10), p. 344), the PR-7
capstone. For `x ≠ y`:

`Σ_{σ,τ} ĉ†_{y,τ} ĉ_{x,τ} ĉ†_{x,σ} ĉ_{y,σ} = n̂_y − 2 Ŝ_x·Ŝ_y − ½ n̂_x n̂_y`.

Model-independent: no sector, half-filling, or bipartiteness hypothesis enters. Proof: split the
defining double sum of `fermionHopReturn` into the `σ = τ` diagonal (two same-spin summands,
`fermionHopReturn_same_spin_eq`) and the `σ ≠ τ` off-diagonal (two opposite-spin summands,
`fermionHopReturn_opposite_spin_eq`), then assemble via
`sum_fermionMultiNumber_spinfulIndex_mul_eq` and
`fermionSiteSpinPlus_mul_Minus_add_fermionSiteSpinMinus_mul_Plus_eq`. The hypothesis `x ≠ y` is
essential: at `x = y` every summand of `fermionHopReturn` degenerates to a same-site
number-operator expression and the stated right-hand side is false (e.g. `fermionSpinDot N x x`
is not `¼ n̂_x` in general). -/
theorem fermionHopReturn_eq (N : ℕ) (x y : Fin (N + 1)) (hxy : x ≠ y) :
    fermionHopReturn N x y =
      fermionSiteNumber N y - (2 : ℂ) • fermionSpinDot N x y -
        (1 / 2 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) := by
  sorry

end LatticeSystem.Fermion
