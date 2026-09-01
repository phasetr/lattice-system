import LatticeSystem.Quantum.HorschVonderLindenProblem34b
import LatticeSystem.Quantum.HorschVonderLindenEnergyBound

/-!
# The low-lying state `Ξ₊` with LRO and SSB (Tasaki §3.4, eqs. (3.4.16)-(3.4.17))

Tasaki's statement that `|Ξ₊⟩ = (1/√2)(|Φ_GS⟩ + |Γ⟩)` (eq. (3.4.14)) "is a low-lying state" which
"exhibits symmetry breaking" (p. 68) unfolds into the normalisation `⟨Ξ₊|Ξ₊⟩ = 1`, the energy
bound `⟨Ξ₊|Ĥ|Ξ₊⟩ ≤ E_GS + (C/2) L^{-d}`, and the order-parameter bound
`⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀` (eq. (3.4.16)).

The energy bound rests on the exact identity `⟨Ξ₊|Ĥ|Ξ₊⟩ = (E_GS + ⟨Γ|Ĥ|Γ⟩)/2`, which is where the
factor `C/2` of the printed sentence comes from: the two cross terms `⟨Φ_GS|Ĥ|Γ⟩` and `⟨Γ|Ĥ|Φ_GS⟩`
vanish because `Φ_GS` is an eigenvector of the Hermitian `Ĥ` and `⟨Φ_GS|Γ⟩ = 0` by the no-SSB
assumption (3.4.4), p. 65, while `⟨Φ_GS|Ĥ|Φ_GS⟩ = E_GS` by normalisation.  The word "obviously" in
the source covers this cancellation.  The identity carries no positivity assumption on the
order-square Rayleigh quotient, and it degenerates gracefully where that quotient vanishes, since
`Γ` is then the zero vector and both sides read `E_GS/2`.  Halving the two-sided bound of
eq. (3.4.12) (`HorschVonderLindenEnergyBound.lean`) gives the printed display.

Eq. (3.4.16) is eq. (3.4.15) (`HorschVonderLindenProblem34b.lean`) read against the long-range-order
assumption (3.4.3), p. 65, through monotonicity of `Real.sqrt`; the volume enters only as a positive
real parameter, which the capstone instantiates at `L^d`.

The Schwarz remark eq. (3.4.17), p. 69, `|⟨Φ|Ô_L/L^d|Φ⟩| ≤ √(⟨Φ|(Ô_L/L^d)²|Φ⟩)`, holds for every
normalised vector and every Hermitian order operator; it is the source's reason why symmetry
breaking forces long-range order, and the derivation of eq. (3.4.16) here does not use it.
Hermiticity is essential rather than cosmetic: at the nilpotent `Ô_L = !![0,1;0,0]` with
`Φ = (1/√2, 1/√2)` and `Ld = 1` the right-hand side vanishes while the left-hand side is `1/2`.

Every statement here is at a single finite volume.  The `L ↑ ∞` and `h ↓ 0` limits of Theorem 3.2
(eq. (3.4.22), p. 70) are not taken; the variational core of that theorem is
`kaplan_horsch_vonderLinden_order_lower_bound` in `Quantum/KaplanHorschVonderLinden.lean`, whose
trial-state input is supplied by the declarations below.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, "Setting and assumptions" p. 65, eqs. (3.4.3), (3.4.4), (3.4.7), (3.4.12), (3.4.14)-
(3.4.17), pp. 65-69.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### The energy identity for `Ξ₊` -/

/-- **The energy identity for `Ξ₊`** (behind Tasaki eq. (3.4.14), p. 68):
`⟨Ξ₊|Ĥ|Ξ₊⟩ = (E_GS + ⟨Γ|Ĥ|Γ⟩)/2` for a normalised eigenvector `Φ_GS` of a Hermitian `Ĥ` at
eigenvalue `E_GS`, under the first odd-moment assumption (3.4.4), p. 65.

Both cross terms `⟨Φ_GS|Ĥ|Γ⟩` and `⟨Γ|Ĥ|Φ_GS⟩` vanish: `⟨Φ_GS|Γ⟩ = 0` by (3.4.4), and Hermiticity
of `Ĥ` moves it onto the eigenvector on either side.  Hermiticity enters only there, through the
bra-side pairing `⟨Φ_GS|Ĥ = ⟨ĤΦ_GS|`.  No positivity of the order-square Rayleigh quotient
`rayleighOnVec (O ^ 2) Φ` is assumed; where that quotient vanishes, `Γ` is the zero vector and both
sides read `E_GS/2`.  Halving turns the two-sided bound of eq. (3.4.12) into the printed
`⟨Ξ₊|Ĥ|Ξ₊⟩ ≤ E_GS + (C/2) L^{-d}` of p. 68. -/
theorem hvlPlusState_energy_eq {n : Type*} [Fintype n]
    {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0) :
    rayleighOnVec H (hvlPlusState O Φ)
      = (E₀ + rayleighOnVec H (hvlTrialState O Φ)) / 2 := by
  classical
  have hΦΓ : star Φ ⬝ᵥ hvlTrialState O Φ = 0 := by
    simpa [hodd1] using dotProduct_mulVec_trialState hO Φ 0
  have hΓΦ : star (hvlTrialState O Φ) ⬝ᵥ Φ = 0 := by
    simpa [hodd1] using trialState_dotProduct_mulVec hO Φ 0
  have hΦHΦ : star Φ ⬝ᵥ (H *ᵥ Φ) = (E₀ : ℂ) := by
    rw [hΦE, dotProduct_smul, smul_eq_mul, hΦ, mul_one]
  have hΓHΦ : star (hvlTrialState O Φ) ⬝ᵥ (H *ᵥ Φ) = 0 := by
    rw [hΦE, dotProduct_smul, smul_eq_mul, hΓΦ, mul_zero]
  have hbra : star Φ ᵥ* H = star (H *ᵥ Φ) := by rw [Matrix.star_mulVec, hH.eq]
  have hΦHΓ : star Φ ⬝ᵥ (H *ᵥ hvlTrialState O Φ) = 0 := by
    rw [Matrix.dotProduct_mulVec, hbra, hΦE, star_smul, smul_dotProduct, smul_eq_mul,
      hΦΓ, mul_zero]
  have hkey : star (hvlPlusState O Φ) ⬝ᵥ (H *ᵥ hvlPlusState O Φ)
      = (1 / 2 : ℂ) * ((E₀ : ℂ)
          + star (hvlTrialState O Φ) ⬝ᵥ (H *ᵥ hvlTrialState O Φ)) := by
    rw [hvlPlusState, smul_add_dotProduct_mulVec, hΦHΦ, hΦHΓ, hΓHΦ, Complex.star_def, map_inv₀,
      Complex.conj_ofReal, sqrt2_inv_mul_sqrt2_inv]
    ring
  have hdef : rayleighOnVec H (hvlPlusState O Φ)
      = (star (hvlPlusState O Φ) ⬝ᵥ (H *ᵥ hvlPlusState O Φ)).re := rfl
  rw [hdef, hkey]
  simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.add_im,
    Complex.ofReal_im, Complex.div_re, Complex.div_im]
  norm_num
  have hΓdef : rayleighOnVec H (hvlTrialState O Φ)
      = (star (hvlTrialState O Φ) ⬝ᵥ (H *ᵥ hvlTrialState O Φ)).re := rfl
  rw [hΓdef]
  ring

end LatticeSystem.Quantum
