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
uses no ground-state property of the reference vector.  The capstone then specialises it at
`Ld = L^d` to the bond-local spin-`S` setting of eqs. (3.4.1)–(3.4.2), p. 65, where eq. (3.4.11)
supplies the numerator bound `16 d h₀ (o₀)² L^d` and `16/(2 q₀) = 8/q₀`, `L^d/(L^d)² = L^{-d}`
produce the printed constant `C = 8 d h₀ (o₀)² / q₀`.

The left half `0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS` is the one place where `E_GS` must be a *ground-state* energy
rather than an arbitrary eigenvalue: it is the "Setting and assumptions" hypothesis of p. 65, taken
here as the variational hypothesis `hmin` and applied to the unit vector `Γ`.  It cannot be
dropped — at `Ĥ = σ³`, `Ô_L = σ¹`, `Φ_GS = (2, 0)` the eigenvalue `E_GS = 1` is not the ground
energy and both sides of eq. (3.4.8) equal `−2`.  Only eq. (3.4.3) is consumed here; the no-SSB
condition (3.4.4), p. 65, is not used.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, "Setting and assumptions" p. 65, eqs. (3.4.3), (3.4.8), pp. 65–66, eqs. (3.4.11)–
(3.4.12), p. 67.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

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

/-! ### The bond-local capstone (eq. (3.4.12)) -/

/-- **Tasaki eq. (3.4.12), p. 67.**  For a bond-local Hamiltonian `Ĥ = Σ_{b∈B} ĥ_b` and an order
operator `Ô_L = Σ_{x∈Λ} ô_x` obeying the locality and norm hypotheses of eqs. (3.4.1)–(3.4.2),
p. 65, at a normalised ground state `Φ_GS` with energy `E_GS`, long-range order (eq. (3.4.3),
p. 65) gives the printed two-sided bound

`0 ≤ ⟨Γ|Ĥ|Γ⟩ − E_GS ≤ C L^{-d}` with `C = 8 d h₀ (o₀)² / q₀`.

The left half is the variational hypothesis `hmin` applied to the unit vector `Γ`; the right half
is the abstract bound above at `Ld = L^d`, fed by eq. (3.4.11), p. 67.  The no-SSB condition
(3.4.4), p. 65, is not used in this derivation; the only declarations that take it as a named
hypothesis are the odd-moment hypotheses of `HorschVonderLindenProblem34b.lean`. -/
theorem tasaki_eq_3_4_12_trialState_energy_bound {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (d L : ℕ) (q₀ h₀ o₀ : ℝ) {Φ : (Λ → Fin (N + 1)) → ℂ} {E₀ : ℝ}
    (hH : (∑ b ∈ B, hb b).IsHermitian) (hO : (∑ x : Λ, o x).IsHermitian)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (hh₀ : 0 ≤ h₀) (ho₀ : 0 ≤ o₀)
    (hbond : ∀ b ∈ B, (W b).card ≤ 2)
    (hB : (B.card : ℝ) ≤ (d : ℝ) * (L : ℝ) ^ d)
    (hΦ : star Φ ⬝ᵥ Φ = 1)
    (hΦE : (∑ b ∈ B, hb b) *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hmin : ∀ v : (Λ → Fin (N + 1)) → ℂ, star v ⬝ᵥ v = 1 →
      E₀ ≤ rayleighOnVec (∑ b ∈ B, hb b) v)
    (hq₀ : 0 < q₀) (hL : 1 ≤ L)
    (hLRO : q₀ ≤ rayleighOnVec ((∑ x : Λ, o x) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) :
    0 ≤ rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ) - E₀
      ∧ rayleighOnVec (∑ b ∈ B, hb b) (hvlTrialState (∑ x : Λ, o x) Φ) - E₀
          ≤ 8 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d := by
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (lt_of_lt_of_le zero_lt_one hL') d
  have hLd2 : (0 : ℝ) < ((L : ℝ) ^ d) ^ 2 := pow_pos hLd 2
  have hm2 : 0 < rayleighOnVec ((∑ x : Λ, o x) ^ 2) Φ :=
    lt_of_lt_of_le (mul_pos hq₀ hLd2) ((le_div_iff₀ hLd2).mp hLRO)
  refine ⟨sub_nonneg.mpr (hmin _ (trialState_dotProduct_self hO Φ hm2)), ?_⟩
  have hnum := doubleCommutator_bondLocal_expectation_le B hb o W d L h₀ o₀ hW hoo hnh hno
    hh₀ ho₀ hbond hB hΦ
  have hK : (0 : ℝ) ≤ 16 * (d : ℝ) * h₀ * o₀ ^ 2 * (L : ℝ) ^ d :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hh₀) (sq_nonneg o₀)) hLd.le
  have hbound := hvlTrialState_energy_sub_le_of_lro
    (K := 16 * (d : ℝ) * h₀ * o₀ ^ 2 * (L : ℝ) ^ d) hH hO hΦE hq₀ hLd hLRO hK
    (le_trans hnum.1 hnum.2)
  have hq₀' : q₀ ≠ 0 := hq₀.ne'
  have hLd' : (L : ℝ) ^ d ≠ 0 := hLd.ne'
  have harith : 16 * (d : ℝ) * h₀ * o₀ ^ 2 * (L : ℝ) ^ d / (2 * q₀ * ((L : ℝ) ^ d) ^ 2)
      = 8 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d := by
    field_simp
    ring
  rwa [harith] at hbound

end LatticeSystem.Quantum
