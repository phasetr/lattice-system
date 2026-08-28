import LatticeSystem.Quantum.IsingChainMatrixElements

/-!
# Test coverage for Tasaki Problem 3.3.a — the low-energy `2L` matrix (TSK-005)

Fixtures for the low-energy analysis of the open-chain quantum Ising Hamiltonian
(`quantumIsingHamiltonian N (1/4) (lam/2)`, `S = σ/2` convention), Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, Problem 3.3.a, statement p. 59, solution pp. 498-501,
eqs. (S.24)-(S.41). This module grows with each PR of the TSK-005 arc; the current PR (PR-005a)
covers only the configuration-basis matrix-element API of `quantumIsingHamiltonian` itself
(`LatticeSystem/Quantum/IsingChainMatrixElements.lean`), not yet the `2L`-dimensional
low-energy space of the problem.

The fixtures come in two layers. The signature pins state each of
`quantumIsingHamiltonian_mulVec_apply`, `quantumIsingHamiltonian_apply_diag`,
`quantumIsingHamiltonian_apply_siteFlip` and `quantumIsingHamiltonian_apply_eq_zero` in full and
discharge it by the lemma itself, so a change of statement (index range, sign, argument order)
breaks the module. The numeric fixtures evaluate the diagonal and single-flip entries at `L = 2`
and `L = 3` through those lemmas, pinning the concrete values `-(L-1)/4` (aligned), `0`
(single kink) and `-h`, so a bond-counting or sign error that happens to be invisible on a single
bond is still caught.
-/

namespace LatticeSystem.Tests.Problem33aLowEnergy

open LatticeSystem.Quantum
open Matrix

/-! ## Signature pins for the four matrix-element lemmas -/

/-- **A1 signature pin.** `quantumIsingHamiltonian_mulVec_apply` expands `(H *ᵥ v) τ` into the
signed bond sum (`+1` on an aligned bond, `-1` across a domain wall) times `v τ`, plus the field
term summed over `siteFlipAt`. This is the base identity A2-A4 are derived from; a wrong bond-sum
range (`Fin (N+1)` instead of `Fin N`, the periodic-ring trap) or a wrong sign on either term
breaks this fixture before it ever reaches the numeric fixtures below. -/
example (N : ℕ) (J h : ℝ) (v : (Fin (N + 1) → Fin 2) → ℂ) (τ : Fin (N + 1) → Fin 2) :
    (quantumIsingHamiltonian N J h *ᵥ v) τ =
      -(J : ℂ) * (∑ i : Fin N, if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) * v τ
        - (h : ℂ) * ∑ i : Fin (N + 1), v (siteFlipAt τ i) :=
  quantumIsingHamiltonian_mulVec_apply N J h v τ

/-- **A2 signature pin.** `quantumIsingHamiltonian_apply_diag` gives the diagonal entry
`⟨Φ_τ|H|Φ_τ⟩` as `-J` times the signed bond sum (`+1` on an aligned bond, `-1` across a domain
wall), with no field-term contribution (a flipped configuration never equals the original). -/
example (N : ℕ) (J h : ℝ) (τ : Fin (N + 1) → Fin 2) :
    quantumIsingHamiltonian N J h τ τ =
      -(J : ℂ) * ∑ i : Fin N, (if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) :=
  quantumIsingHamiltonian_apply_diag N J h τ

/-- **A3 signature pin.** `quantumIsingHamiltonian_apply_siteFlip` gives the matrix element
between a configuration and its single-site flip: exactly `-h`, independent of `J` and of the
flipped site. -/
example (N : ℕ) (J h : ℝ) (τ : Fin (N + 1) → Fin 2) (x : Fin (N + 1)) :
    quantumIsingHamiltonian N J h (siteFlipAt τ x) τ = -(h : ℂ) :=
  quantumIsingHamiltonian_apply_siteFlip N J h τ x

/-- **A4 signature pin (this PR's capstone).** `quantumIsingHamiltonian_apply_eq_zero` is the
source's "all other matrix elements are vanishing": distinct configurations that are also not a
single-site flip of one another have a zero matrix element. -/
example (N : ℕ) (J h : ℝ) (σ τ : Fin (N + 1) → Fin 2) (h₁ : σ ≠ τ)
    (h₂ : ∀ x, σ ≠ siteFlipAt τ x) :
    quantumIsingHamiltonian N J h σ τ = 0 :=
  quantumIsingHamiltonian_apply_eq_zero N J h σ τ h₁ h₂

/-! ## Numeric fixtures at `L = 2` (`N = 1`) -/

/-- **Open-boundary trap detector (A2 at `L = 2`).** The all-down configuration is aligned across
the single bond of the two-site *open* chain — one aligned bond and no domain wall — so the
signed bond sum is `+1` and the diagonal entry is `-J = -1/4 = -(L-1)/4`, Tasaki eq. (S.24). Had
the bond sum instead run over `Fin (N + 1)` (as the physically periodic `isingCycleHamiltonian`
would force, counting the wrap-around bond a second time), the sum would be `+2` and this value
would be `-1/2`; this fixture is exactly the guard against that mis-instantiation (design §8
fixture 3, adapted to the matrix-element API). -/
example :
    quantumIsingHamiltonian 1 (1 / 4 : ℝ) (1 : ℝ) (fun _ => (1 : Fin 2)) (fun _ => (1 : Fin 2))
      = -1 / 4 := by
  rw [quantumIsingHamiltonian_apply_diag 1 (1 / 4) 1 (fun _ => 1)]
  norm_num

/-- **Field-term value (A3 at `L = 2`).** The matrix element between the all-down configuration
and its site-`0` flip is exactly `-h`; here `h = 1`. A wrong sign, a stray factor of `J`, or a
doubled field term (counting the flipped site twice) would each change this numeric value. -/
example :
    quantumIsingHamiltonian 1 (1 / 4 : ℝ) (1 : ℝ) (siteFlipAt (fun _ => (1 : Fin 2)) 0)
        (fun _ => (1 : Fin 2))
      = -1 :=
  quantumIsingHamiltonian_apply_siteFlip 1 (1 / 4) 1 (fun _ => 1) 0

/-- **Vanishing at distance `2` (A4 at `L = 2`).** The all-up and all-down configurations differ
at both sites of the two-site chain, so neither is the other nor a single-site flip of the other;
their matrix element is `0`. Matches design §8 fixture 5's second clause
(`lowEnergyMatrix 1 lam 0 2 = 0`) at the matrix-element level, one PR earlier. -/
example :
    quantumIsingHamiltonian 1 (1 / 4 : ℝ) (1 : ℝ) (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2))
      = 0 :=
  quantumIsingHamiltonian_apply_eq_zero 1 (1 / 4) 1 (fun _ => 0) (fun _ => 1) (by decide)
    (by decide)

/-! ## Numeric fixtures at `L = 3` (`N = 2`) -/

/-- **Bond counting (A2 at `L = 3`).** The all-down configuration is aligned across both bonds of
the three-site open chain, so the signed bond sum is `+2` and the diagonal entry is
`-2J = -1/2 = -(L-1)/4`, Tasaki eq. (S.24). Together with the `L = 2` fixture above this pins
`-(L-1)/4` as a formula in `L` rather than at a single bond: an off-by-one bond range agreeing
with `Fin N` at `N = 1` is caught here. -/
example :
    quantumIsingHamiltonian 2 (1 / 4 : ℝ) (1 : ℝ) (fun _ => (1 : Fin 2)) (fun _ => (1 : Fin 2))
      = -1 / 2 := by
  rw [quantumIsingHamiltonian_apply_diag 2 (1 / 4) 1 (fun _ => 1)]
  norm_num

/-- **Single kink (A2 at `L = 3`).** Flipping site `0` of the all-down configuration creates one
domain wall and leaves one aligned bond, so the signed bond sum is `-1 + 1 = 0` and the diagonal
entry is `0`. This is Tasaki eq. (S.25), whose value `E_GS^(0) + 1/2 = -(L-1)/4 + 1/2` is `0`
exactly at `L = 3`. The cancelling pair of bonds is what rules out an unsigned bond sum, be it
over domain walls or over aligned bonds only: either would give `-J` here. (The overall sign of
the bond sum is pinned by the aligned fixtures, not by this one, whose value is its own
negation.) -/
example :
    quantumIsingHamiltonian 2 (1 / 4 : ℝ) (1 : ℝ) (siteFlipAt (fun _ => (1 : Fin 2)) 0)
        (siteFlipAt (fun _ => (1 : Fin 2)) 0)
      = 0 := by
  rw [quantumIsingHamiltonian_apply_diag 2 (1 / 4) 1 (siteFlipAt (fun _ => (1 : Fin 2)) 0),
    Fin.sum_univ_two]
  norm_num [siteFlipAt, Function.update_apply, Fin.ext_iff]

end LatticeSystem.Tests.Problem33aLowEnergy
