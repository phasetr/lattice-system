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

**TDD status: Red.** `IsingChainMatrixElements.lean` currently contains only its imports; none of
`quantumIsingHamiltonian_mulVec_apply`, `quantumIsingHamiltonian_apply_diag`,
`quantumIsingHamiltonian_apply_siteFlip`, `quantumIsingHamiltonian_apply_eq_zero` exist yet, so
every fixture below fails to elaborate with `unknown identifier`. Each `example`'s *type* is
nonetheless already the concrete claim it will discharge once the four lemmas are implemented, so
the Red pins the exact statements and the exact numeric error modes they must rule out.
-/

namespace LatticeSystem.Tests.Problem33aLowEnergy

open LatticeSystem.Quantum
open Matrix

/-! ## Signature pins for the four matrix-element lemmas -/

/-- **A1 signature pin.** `quantumIsingHamiltonian_mulVec_apply` expands `(H *ᵥ v) τ` into the
domain-wall bond sum times `v τ` plus the field term summed over `siteFlipAt`. This is the base
identity A2-A4 are derived from; a wrong bond-sum range (`Fin (N+1)` instead of `Fin N`, the
periodic-ring trap) or a wrong sign on either term breaks this fixture before it ever reaches the
numeric fixtures below. -/
example (N : ℕ) (J h : ℝ) (v : (Fin (N + 1) → Fin 2) → ℂ) (τ : Fin (N + 1) → Fin 2) :
    (quantumIsingHamiltonian N J h *ᵥ v) τ =
      -(J : ℂ) * (∑ i : Fin N, if τ i.castSucc = τ i.succ then (1 : ℂ) else -1) * v τ
        - (h : ℂ) * ∑ i : Fin (N + 1), v (siteFlipAt τ i) :=
  quantumIsingHamiltonian_mulVec_apply N J h v τ

/-- **A2 signature pin.** `quantumIsingHamiltonian_apply_diag` gives the diagonal entry
`⟨Φ_τ|H|Φ_τ⟩` as `-J` times the domain-wall bond count, with no field-term contribution (a
flipped configuration never equals the original). -/
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

/-- **Open-boundary trap detector (A2 at `L = 2`).** The all-down configuration has exactly one
domain-wall bond on the two-site *open* chain, so the diagonal entry is `-1/4 = -(L-1)/4`. Had
the bond sum instead run over `Fin (N + 1)` (as the physically periodic `isingCycleHamiltonian`
would force, counting the wrap-around bond a second time), this value would be `-1/2`; this
fixture is exactly the guard against that mis-instantiation (design §8 fixture 3, adapted to the
matrix-element API). -/
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

end LatticeSystem.Tests.Problem33aLowEnergy
