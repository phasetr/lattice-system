import LatticeSystem.Quantum.HorschVonderLindenTrialState
import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound

/-!
# The two-sided energy bound for the Horsch–von der Linden trial state (Tasaki eq. (3.4.12))

Tasaki's printed two-sided bound

`0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS ≤ 8 d h₀ (o₀)² / (q₀ L^d)` (eq. (3.4.12), p. 67)

is assembled here out of the basic variational estimate `hvlTrialState_energy_sub_eq` (eq. (3.4.8),
`HorschVonderLindenTrialState.lean`) and the locality numerator bound
`doubleCommutator_bondLocal_expectation_le` (eq. (3.4.11), `LocalDoubleCommutatorBound.lean`).

The abstract upper half is stated first, with the system size entering only as a positive real
parameter `Ld` and the long-range-order input of eq. (3.4.3), p. 65, as the lower bound `q₀` on the
normalised second moment.  In that form it applies to `Ô_L` and to its mirror `−Ô_L` alike, and it
uses no ground-state property of the reference vector.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, "Setting and assumptions" p. 65, eqs. (3.4.3), (3.4.8), pp. 65–66, eqs. (3.4.11)–
(3.4.12), p. 67.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ### The abstract upper bound -/

/-- **Tasaki eq. (3.4.12), p. 67, upper half, abstract form.**  For an eigenvector `Φ_GS` of a
Hermitian `Ĥ` with eigenvalue `E_GS`, a Hermitian order operator `Ô_L`, and a size parameter `Ld`,
long-range order in the form of eq. (3.4.3), p. 65 (`q₀ ≤ ⟨Φ_GS|(Ô_L)²|Φ_GS⟩ / Ld²` with `q₀ > 0`)
turns any bound `K` on the double-commutator expectation into

`⟨Γ|Ĥ|Γ⟩ − E_GS ≤ K / (2 q₀ Ld²)`.

The bound is eq. (3.4.8), p. 66, followed by monotonicity first in the numerator and then in the
denominator; splitting the comparison that way needs only `0 ≤ K` and no sign information about the
double-commutator expectation, so the ground-state property of `Φ_GS` — which is what the left half
of eq. (3.4.12) rests on — is not used here.  Keeping `Ld` an abstract positive real, rather than
`L^d`, makes the statement apply unchanged at `Ô_L` and at its mirror `−Ô_L`. -/
theorem hvlTrialState_energy_sub_le_of_lro {n : Type*} [Fintype n] [DecidableEq n]
    {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ q₀ Ld K : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian)
    (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hq₀ : 0 < q₀) (hLd : 0 < Ld)
    (hLRO : q₀ ≤ rayleighOnVec (O ^ 2) Φ / Ld ^ 2)
    (hK : 0 ≤ K)
    (hnum : rayleighOnVec (O * (H * O - O * H) - (H * O - O * H) * O) Φ ≤ K) :
    rayleighOnVec H (hvlTrialState O Φ) - E₀ ≤ K / (2 * q₀ * Ld ^ 2) := by
  have hLd2 : (0 : ℝ) < Ld ^ 2 := pow_pos hLd 2
  have hlow : q₀ * Ld ^ 2 ≤ rayleighOnVec (O ^ 2) Φ := (le_div_iff₀ hLd2).mp hLRO
  have hm2 : 0 < rayleighOnVec (O ^ 2) Φ := lt_of_lt_of_le (mul_pos hq₀ hLd2) hlow
  have hden : 2 * q₀ * Ld ^ 2 ≤ 2 * rayleighOnVec (O ^ 2) Φ := by linarith
  have hdpos : (0 : ℝ) < 2 * q₀ * Ld ^ 2 := by positivity
  have hnum' : (star Φ ⬝ᵥ ((O * (H * O - O * H) - (H * O - O * H) * O) *ᵥ Φ)).re ≤ K := hnum
  rw [hvlTrialState_energy_sub_eq hH hO hΦE hm2]
  exact div_le_div₀ hK hnum' hdpos hden

end LatticeSystem.Quantum
