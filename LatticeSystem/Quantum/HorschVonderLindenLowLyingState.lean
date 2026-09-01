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
trial-state input at `Ξ = Ξ₊` the capstone below (`tasaki_eq_3_4_16_lowLyingState_ssb`) supplies;
composing the two and taking the double limit is not carried out here.

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
of `Ĥ` moves it onto the eigenvector on either side, through the bra-side pairing
`⟨Φ_GS|Ĥ = ⟨ĤΦ_GS|`.  No positivity of the order-square Rayleigh quotient
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

/-! ### Eq. (3.4.16), the order parameter of `Ξ₊` -/

/-- **Tasaki eq. (3.4.16), p. 68, abstract form**: `√q₀ ≤ ⟨Ξ₊|Ô_L|Ξ₊⟩ / Ld` for a Hermitian order
operator `Ô_L` whose first and third moments at `Φ_GS` vanish (assumption (3.4.4), p. 65), under
long-range order (eq. (3.4.3), p. 65) in the form `q₀ ≤ ⟨Φ_GS|(Ô_L)²|Φ_GS⟩ / Ld²` with `q₀ > 0`.

It is eq. (3.4.15) followed by monotonicity of `Real.sqrt`, the size parameter moving under the
root by `√m₂ / Ld = √(m₂ / Ld²)`.  Normalisation of `Φ_GS` is not assumed, since eq. (3.4.15) does
not use it.  The hypothesis `0 < Ld` is load-bearing at negative values rather than at zero: at
`Ld = 0` the long-range-order hypothesis reads `q₀ ≤ 0` and contradicts `0 < q₀`, whereas at
`Ld = -2` with `q₀ = 1` there is data satisfying every hypothesis and failing the conclusion.  `Ld`
is an abstract positive real, which the capstone instantiates at `L^d`. -/
theorem hvlPlusState_order_mean_ge_sqrt {n : Type*} [Fintype n] [DecidableEq n]
    (O : Matrix n n ℂ) (Φ : n → ℂ) {q₀ Ld : ℝ}
    (hO : O.IsHermitian) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hq₀ : 0 < q₀) (hLd : 0 < Ld)
    (hLRO : q₀ ≤ rayleighOnVec (O ^ 2) Φ / Ld ^ 2) :
    Real.sqrt q₀ ≤ rayleighOnVec O (hvlPlusState O Φ) / Ld := by
  have hLd2 : (0 : ℝ) < Ld ^ 2 := pow_pos hLd 2
  have hm2 : 0 < rayleighOnVec (O ^ 2) Φ :=
    lt_of_lt_of_le (mul_pos hq₀ hLd2) ((le_div_iff₀ hLd2).mp hLRO)
  have hrw : Real.sqrt (rayleighOnVec (O ^ 2) Φ) / Ld
      = Real.sqrt (rayleighOnVec (O ^ 2) Φ / Ld ^ 2) := by
    rw [Real.sqrt_div' _ (sq_nonneg Ld), Real.sqrt_sq hLd.le]
  rw [hvlPlusState_order_mean O Φ hO hodd1 hodd3 hm2, hrw]
  exact Real.sqrt_le_sqrt hLRO

/-! ### Eq. (3.4.17), the Schwarz remark -/

open scoped ComplexOrder in
/-- **Tasaki eq. (3.4.17), p. 69** (the Schwarz remark):
`|⟨Φ|Ô_L/Ld|Φ⟩| ≤ √(⟨Φ|(Ô_L/Ld)²|Φ⟩)` for a normalised `Φ` and a Hermitian `Ô_L`.  This is the
source's reason why symmetry breaking forces long-range order; the derivation of eq. (3.4.16) above
does not use it.

Real Cauchy–Schwarz at the identity matrix, applied to `Φ` and `Ô_L Φ` and combined with
`⟨Ô_L Φ|Ô_L Φ⟩ = ⟨Φ|(Ô_L)²|Φ⟩`, gives `(⟨Φ|Ô_L|Φ⟩)² ≤ ⟨Φ|(Ô_L)²|Φ⟩`; taking square roots produces
the absolute value.  Hermiticity of `Ô_L` is load-bearing rather than cosmetic: at the nilpotent
`Ô_L = !![0,1;0,0]` with `Φ = (1/√2, 1/√2)` and `Ld = 1` the right-hand side is `0` while the
left-hand side is `1/2`, so the inequality fails there.  The hypothesis `0 < Ld` supports moving
the size parameter under the root; at `Ld = 0` both sides of the conclusion are `0`. -/
theorem tasaki_eq_3_4_17_order_mean_abs_le_sqrt {n : Type*} [Fintype n] [DecidableEq n]
    {O : Matrix n n ℂ} {Φ : n → ℂ} {Ld : ℝ}
    (hO : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hLd : 0 < Ld) :
    |rayleighOnVec O Φ / Ld| ≤ Real.sqrt (rayleighOnVec (O ^ 2) Φ / Ld ^ 2) := by
  have hsplit : star ((O ^ 1) *ᵥ Φ) ⬝ᵥ ((O ^ 1) *ᵥ Φ) = star Φ ⬝ᵥ ((O ^ (1 + 1)) *ᵥ Φ) :=
    hermitian_pow_dotProduct_split hO 1 1 Φ
  rw [pow_one, show (1 : ℕ) + 1 = 2 from rfl] at hsplit
  have hcs := posSemidef_re_dotProduct_mulVec_sq_le (M := (1 : Matrix n n ℂ))
    Matrix.PosSemidef.one Φ (O *ᵥ Φ)
  simp only [Matrix.one_mulVec] at hcs
  rw [hΦ, hsplit] at hcs
  have hsq : (rayleighOnVec O Φ) ^ 2 ≤ rayleighOnVec (O ^ 2) Φ := by
    simpa [rayleighOnVec] using hcs
  have hdiv : (rayleighOnVec O Φ / Ld) ^ 2 ≤ rayleighOnVec (O ^ 2) Φ / Ld ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hsq (pow_pos hLd 2).le
  calc |rayleighOnVec O Φ / Ld|
      = Real.sqrt ((rayleighOnVec O Φ / Ld) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (rayleighOnVec (O ^ 2) Φ / Ld ^ 2) := Real.sqrt_le_sqrt hdiv

/-! ### The bond-local low-lying state (eq. (3.4.16)) -/

/-- **Tasaki eq. (3.4.16), p. 68, together with the low-lying-state sentence of the same page.**
In the bond-local spin-`S` setting of eqs. (3.4.1)-(3.4.2), p. 65, at a normalised ground state
`Φ_GS` with energy `E_GS` obeying long-range order (eq. (3.4.3)) and the no-SSB condition (3.4.4)
in its first- and third-moment forms, the state `Ξ₊` of eq. (3.4.14) is normalised, sits within
`(C/2) L^{-d}` above the ground-state energy with `C = 8 d h₀ (o₀)² / q₀` the constant of
eq. (3.4.12), p. 67, and carries the order parameter `⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀`.

The energy conjuncts are eq. (3.4.12) transported through `hvlPlusState_energy_eq`, which halves
both sides of the bracket `⟨Γ|Ĥ|Γ⟩ − E_GS`; the order conjunct is
`hvlPlusState_order_mean_ge_sqrt` at `Ld = L^d`.  The hypothesis block is that of
`tasaki_eq_3_4_12_trialState_energy_bound` together with the two odd-moment hypotheses, which
eq. (3.4.12) does not take.  At `d = 0` the bond-set hypothesis forces the bond set empty and the
printed constant to `0`, leaving the energy conjuncts energy-trivial while the normalisation and
eq. (3.4.16) conjuncts keep their content. -/
theorem tasaki_eq_3_4_16_lowLyingState_ssb {ι : Type*} (B : Finset ι)
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
    (hodd1 : star Φ ⬝ᵥ ((∑ x : Λ, o x) *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ (((∑ x : Λ, o x) ^ 3) *ᵥ Φ) = 0)
    (hq₀ : 0 < q₀) (hL : 1 ≤ L)
    (hLRO : q₀ ≤ rayleighOnVec ((∑ x : Λ, o x) ^ 2) Φ / ((L : ℝ) ^ d) ^ 2) :
    star (hvlPlusState (∑ x : Λ, o x) Φ) ⬝ᵥ hvlPlusState (∑ x : Λ, o x) Φ = 1
    ∧ 0 ≤ rayleighOnVec (∑ b ∈ B, hb b) (hvlPlusState (∑ x : Λ, o x) Φ) - E₀
    ∧ rayleighOnVec (∑ b ∈ B, hb b) (hvlPlusState (∑ x : Λ, o x) Φ) - E₀
        ≤ 4 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d
    ∧ Real.sqrt q₀
        ≤ rayleighOnVec (∑ x : Λ, o x) (hvlPlusState (∑ x : Λ, o x) Φ) / (L : ℝ) ^ d := by
  have hL' : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLd : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (lt_of_lt_of_le zero_lt_one hL') d
  have hLd2 : (0 : ℝ) < ((L : ℝ) ^ d) ^ 2 := pow_pos hLd 2
  have hm2 : 0 < rayleighOnVec ((∑ x : Λ, o x) ^ 2) Φ :=
    lt_of_lt_of_le (mul_pos hq₀ hLd2) ((le_div_iff₀ hLd2).mp hLRO)
  have hgamma := tasaki_eq_3_4_12_trialState_energy_bound B hb o W d L q₀ h₀ o₀ hH hO hW hoo
    hnh hno hh₀ ho₀ hbond hB hΦ hΦE hmin hq₀ hL hLRO
  have hid := hvlPlusState_energy_eq hH hO hΦE hΦ hodd1
  have harith : 4 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d
      = (8 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d) / 2 := by ring
  refine ⟨hvlPlusState_dotProduct_self _ Φ hO hΦ hodd1 hm2, ?_, ?_, ?_⟩
  · rw [hid]; linarith [hgamma.1]
  · rw [hid, harith]; linarith [hgamma.2]
  · exact hvlPlusState_order_mean_ge_sqrt _ Φ hO hodd1 hodd3 hq₀ hLd hLRO

end LatticeSystem.Quantum
