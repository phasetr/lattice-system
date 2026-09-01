import LatticeSystem.Quantum.HorschVonderLindenLowLyingState
import LatticeSystem.Quantum.SpinS.ClusterState

/-!
# Test coverage for eqs. (3.4.16)/(3.4.17), the `Ξ₊`/`Ξ₋` low-lying states

Fixtures for `LatticeSystem/Quantum/HorschVonderLindenLowLyingState.lean`: the `Ξ₊` energy
identity, eq. (3.4.16)'s abstract lower bound, the Schwarz remark eq. (3.4.17), the bond-local
low-lying-state capstone, and (below, "Signature pins — the mirror state") the mirror state `Ξ₋`
of p. 68-69: `hvlTrialState_neg`, `hvlMinusState`, its bridge to `hvlPlusState (-O)`, its
normalisation, energy identity, order mean and order bound, its cross-orthogonality to `Ξ₊`, and
the capstone `tasaki_mirrorLowLyingState_ssb`.

## Sign-error fixtures for the mirror state `Ξ₋`

`Ξ₋` differs from `Ξ₊` only by signs, so a fixture built for `Ξ₊` can pass for a wrongly-signed
`Ξ₋`. Fixtures F1-F8 (below the `Ξ₊` fixtures) each carry a value that differs under the sign
flip: F1 pins the state's four entries directly; F2 pins the energy identity together with the
sign-discriminating value `rayleighOnVec fO Ξ₋ = -2` (against `Ξ₊`'s `+2`), since the identity's
own right-hand side is even in the sign of `Γ` and would not itself catch a flipped sign; F3 pins
orthogonality and normalisation together, since substituting `Ξ₊` for `Ξ₋` reads `1 = 0`; F4 is
exactly tight at `q₀ = 1`, `Ld = 2`; F5 is a negative-`Ld` instance where the mirror bound's own
conclusion fails; F6/F7 are boundary instances at a vanishing order-square Rayleigh quotient.

## What each block pins

**Signature pins.** Each pin restates a declaration's own statement and is discharged only by
applying that identifier, so it breaks if the hypothesis list or the conclusion moves. The
energy-identity pin (`hvlPlusState_energy_eq`) fixes that the hypothesis list carries no positivity
of the order-square Rayleigh quotient. The eq. (3.4.16) pin (`hvlPlusState_order_mean_ge_sqrt`)
fixes that it carries no normalisation hypothesis `star Φ ⬝ᵥ Φ = 1`. The eq. (3.4.17) pin
(`tasaki_eq_3_4_17_order_mean_abs_le_sqrt`) fixes the Hermitian hypothesis on the order operator.
The capstone pin (`tasaki_eq_3_4_16_lowLyingState_ssb`) fixes its four conjuncts, the literal
constant `4 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d`, and the presence of the two odd-moment
hypotheses `hodd1`, `hodd3`, which eq. (3.4.12)'s capstone does not take.

**Numeric fixture (the two-spin `Ξ₊` instance).** On `Fin 4` with basis order
`(↑↑, ↑↓, ↓↑, ↓↓)`, `fH := diagonal ![-1, 3, 3, -1]` and the transverse order operator
`fO := !![0,1,1,0; 1,0,0,1; 1,0,0,1; 0,1,1,0]`, at `fPhi := ![c, 0, 0, c]` (`c = (√2)⁻¹`): `fPhi`
is an `fH`-eigenvector at `E₀ = -1`, `hvlTrialState fO fPhi = ![0, c, c, 0]` (`Γ`),
`hvlPlusState fO fPhi = ![1/2, 1/2, 1/2, 1/2]` (`Ξ₊`), and the Rayleigh quotients are
`rayleighOnVec fH (hvlPlusState fO fPhi) = 1`, `rayleighOnVec fH (hvlTrialState fO fPhi) = 3`,
`rayleighOnVec fO (hvlPlusState fO fPhi) = 2`.  A **diagonal** order operator would leave `Γ`
inside the ground eigenspace and collapse `rayleighOnVec fH Γ` to `E₀`, so `fO` is transverse
against the diagonal `fH` by construction, not incidentally.  The energy identity reads
`1 = (-1 + 3) / 2`, separating it from the un-halved `2`, the `E₀`-free `3/2`, and the
sign-flipped `-2`: since `E₀ ≠ 0` and `E₀ + rayleighOnVec fH Γ = 2 ≠ 0`, none of those variants
coincides with the correct value at this point. Eq. (3.4.16) is **tight** here at `q₀ = 1`,
`Ld = (2 : ℝ) = 2 ^ 1`: `rayleighOnVec (fO ^ 2) fPhi / Ld ^ 2 = 4 / 4 = 1 = q₀` and
`rayleighOnVec fO (hvlPlusState fO fPhi) / Ld = 2 / 2 = 1 = √q₀`, so a candidate whose right-hand
side is strictly smaller at this data — dividing by `Ld ^ 2` instead of `Ld`, say — is not
`≤`-provable here.

**Eq. (3.4.17) fixtures.** A strict rational instance
(`O' := diagonal ![2, 0, 0, -2]`, `v := ![3/5, 4/5, 0, 0]`, `Ld := 2`) gives
`|rayleighOnVec O' v / Ld| = 9/25` against `Real.sqrt (rayleighOnVec (O' ^ 2) v / Ld ^ 2) = 3/5`,
both rational and strict; the same `O'`, `v` at `Ld := -2` give the identical `9/25 ≤ 3/5`, proved
directly since the declaration's own hypothesis `0 < Ld` does not apply there; a tight instance at
`O := fO`, `v := hvlPlusState fO fPhi`, `Ld := 2` gives equality `1 = 1`.  Since a bare `≤` endpoint
cannot by itself exclude a wrongly *larger* right-hand side, the strict instance carries those two
values as their own conjuncts, spelling the radicand `rayleighOnVec (O' ^ 2) v / Ld ^ 2` out
syntactically.

**Capstone satisfiability witness.** The bundle in the `ManyBodyOpS Λ N` packaging is instantiated
at `Λ := Fin 1`, `N := 1`, `B := (∅ : Finset Unit)`, `o 0 := pauliXS (0 : Fin 1)` (the single-site
Pauli `X`, genuinely `Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ`-Hermitian and unitary via
`onSiteS_isHermitian`/`spinSOp1_isHermitian`/`manyBodyOperatorNormS_eq_one_of_unitary`),
`Φ := basisVecS (fun _ => (0 : Fin 2))`, `d = L = q₀ = o₀ = 1`, `h₀ = 0`, `E₀ = 0`. Every
hypothesis is **discharged by proof** against these declarations, not assumed: `hΦ` and `hΦE`
are direct computations; `hodd1`/`hodd3`/`hLRO` follow from `pauliXS_apply`'s explicit
basis-flip formula plus the involution `flipSite (flipSite σ x) x = σ`, which gives
`(∑ x, o x) ^ 2 = 1` at the matrix level and hence `rayleighOnVec ((∑ x, o x) ^ 2) Φ = 1`;
`hno` follows from that same square-to-`1` fact via the unitary-norm lemma. The capstone's
hypothesis bundle is therefore jointly satisfiable in the packaging it is stated in, so the
capstone is not vacuously true for every instance.

## Boundary facts

`hLd` in eq. (3.4.16) is load-bearing at *negative* `Ld`, not at `Ld = 0` (at `Ld = 0` the LRO
hypothesis becomes `q₀ ≤ 0`, so the statement is vacuous there, not false). `hLd` in eq. (3.4.17)
is not needed at `Ld = 0`, where both sides of its conclusion are `0`; the negative-`Ld` fixture
above additionally checks, at one concrete instance, that the conclusion also holds where `hLd`
supplies no proof at all. `hL : 1 ≤ L` in the capstone excludes nothing false. At `d = 0` the
capstone's two energy conjuncts read `0 ≤ 0 ≤ 0` — energy-trivial, neither vacuous nor false —
while its normalisation and eq. (3.4.16) conjuncts keep their content. The empty-carrier route to
vacuity differs per declaration: the energy identity and eq. (3.4.17) go vacuous through the
normalisation hypothesis, eq. (3.4.16) through the LRO-and-positivity pair; the capstone's own
carrier `Λ → Fin (N + 1)` is never empty, since it always contains the all-zero configuration.
-/

namespace LatticeSystem.Tests.HorschVonderLindenLowLyingState

open LatticeSystem
open LatticeSystem.Quantum
open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## Signature pin 1 — the `Ξ₊` energy identity, `hvlPlusState_energy_eq` -/

/-- **Signature pin.** Pins the energy identity of eq. (3.4.14)'s state: `Φ` a Hermitian-`H`
eigenvector, normalised, with the first odd moment `⟨Φ|O|Φ⟩ = 0`, and **no** positivity hypothesis
on the order-square Rayleigh quotient `rayleighOnVec (O ^ 2) Φ`, and no `DecidableEq` instance on
the index type. Discharged only by the identifier itself, so a move in the hypothesis list or the
conclusion breaks it. -/
example {n : Type*} [Fintype n] {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0) :
    rayleighOnVec H (hvlPlusState O Φ)
      = (E₀ + rayleighOnVec H (hvlTrialState O Φ)) / 2 :=
  hvlPlusState_energy_eq hH hO hΦE hΦ hodd1

/-! ## Signature pin 2 — eq. (3.4.16), `hvlPlusState_order_mean_ge_sqrt` -/

/-- **Signature pin.** Pins eq. (3.4.16) at the abstract size parameter `Ld`, and that the
hypothesis list carries **no** normalisation hypothesis `star Φ ⬝ᵥ Φ = 1`. Discharged only by the
identifier itself. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ) {q₀ Ld : ℝ}
    (hO : O.IsHermitian) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hq₀ : 0 < q₀) (hLd : 0 < Ld)
    (hLRO : q₀ ≤ rayleighOnVec (O ^ 2) Φ / Ld ^ 2) :
    Real.sqrt q₀ ≤ rayleighOnVec O (hvlPlusState O Φ) / Ld :=
  hvlPlusState_order_mean_ge_sqrt O Φ hO hodd1 hodd3 hq₀ hLd hLRO

/-! ## Signature pin 3 — eq. (3.4.17), `tasaki_eq_3_4_17_order_mean_abs_le_sqrt` -/

/-- **Signature pin.** Pins the Schwarz remark eq. (3.4.17), including the Hermitian hypothesis on
the order operator, without which the inequality fails at a nilpotent order operator. Discharged
only by the identifier itself. -/
example {n : Type*} [Fintype n] [DecidableEq n] {O : Matrix n n ℂ} {Φ : n → ℂ} {Ld : ℝ}
    (hO : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hLd : 0 < Ld) :
    |rayleighOnVec O Φ / Ld| ≤ Real.sqrt (rayleighOnVec (O ^ 2) Φ / Ld ^ 2) :=
  tasaki_eq_3_4_17_order_mean_abs_le_sqrt hO hΦ hLd

/-! ## Signature pin 4 — the capstone, `tasaki_eq_3_4_16_lowLyingState_ssb` -/

/-- **Signature pin (capstone).** Pins the four conjuncts of the conclusion (normalisation,
`0 ≤ ⟨Ξ₊|Ĥ|Ξ₊⟩ − E₀ ≤ 4 d h₀ o₀² / q₀ / L^d`, and eq. (3.4.16)), the literal constant, and that
the hypothesis list carries **both** odd-moment hypotheses `hodd1`/`hodd3` (unlike eq. (3.4.12)'s
capstone, which needs neither). Discharged only by the identifier itself. -/
example {ι : Type*} (B : Finset ι)
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
        ≤ rayleighOnVec (∑ x : Λ, o x) (hvlPlusState (∑ x : Λ, o x) Φ) / (L : ℝ) ^ d :=
  tasaki_eq_3_4_16_lowLyingState_ssb B hb o W d L q₀ h₀ o₀ hH hO hW hoo hnh hno hh₀ ho₀
    hbond hB hΦ hΦE hmin hodd1 hodd3 hq₀ hL hLRO

/-! ## Fixture data — the two-spin `Ξ₊` instance -/

/-- The normalisation constant `(√2)⁻¹` for the two-spin `fPhi`/`fXi` fixture data below. -/
private noncomputable def c2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- `c2 * c2 = 1 / 2`, reduced to the repo's `sqrt2_inv_mul_sqrt2_inv`. -/
private lemma c2_sq : c2 * c2 = 1 / 2 := sqrt2_inv_mul_sqrt2_inv

/-- `c2` has vanishing imaginary part (it is the coercion of a real number). -/
private lemma c2_im : c2.im = 0 := by
  unfold c2; rw [← Complex.ofReal_inv, Complex.ofReal_im]

/-- `c2.re * c2.re = 1 / 2`, the real-part form of `c2_sq` used by the `rayleighOnVec`
computations below. -/
private lemma c2_re_sq : c2.re * c2.re = 1 / 2 := by
  have h := congrArg Complex.re c2_sq
  simpa [Complex.mul_re, c2_im] using h

/-- `c2` is self-adjoint (it is real). -/
private lemma c2_star : star c2 = c2 := by
  unfold c2; rw [Complex.star_def, map_inv₀, Complex.conj_ofReal]

/-- The diagonal Ising-type Hamiltonian `diag(-1, 3, 3, -1)` on the two-spin basis
`(↑↑, ↑↓, ↓↑, ↓↓)`. -/
private noncomputable def fH : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![-1, 3, 3, -1]

/-- The transverse order operator on the same basis (off-diagonal, so `Γ = hvlTrialState fO fPhi`
leaves the ground eigenspace of `fH` — unlike a diagonal order operator, which would collapse the
fixture's discriminating power). -/
private def fO : Matrix (Fin 4) (Fin 4) ℂ := !![0,1,1,0; 1,0,0,1; 1,0,0,1; 0,1,1,0]

/-- The reference state `Φ_GS := (c2, 0, 0, c2)`, an `fH`-eigenvector at `E₀ = -1`. -/
private noncomputable def fPhi : Fin 4 → ℂ := ![c2, 0, 0, c2]

/-- `fPhi` is normalised. -/
private lemma fPhi_norm : star fPhi ⬝ᵥ fPhi = 1 := by
  unfold fPhi
  simp only [dotProduct, Fin.sum_univ_four, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, c2_star]
  rw [c2_sq]; norm_num

/-- `fO *ᵥ fPhi = (0, 2 c2, 2 c2, 0)`. -/
private lemma fO_mulVec_fPhi : fO *ᵥ fPhi = ![0, 2 * c2, 2 * c2, 0] := by
  unfold fO fPhi
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_four] <;> ring

/-- The order-square moment `m₂ = ⟨Φ|(fO)²|Φ⟩ = 4` in the un-normalised `vecNormSqRe` form used to
build `hvlTrialState`. -/
private lemma fPhi_vecNormSq : vecNormSqRe (fO *ᵥ fPhi) = 4 := by
  rw [fO_mulVec_fPhi]
  unfold vecNormSqRe
  simp only [dotProduct, Fin.sum_univ_four, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, star_mul', c2_star, star_ofNat]
  rw [show (2 : ℂ) * c2 * (2 * c2) = 4 * (c2 * c2) by ring, c2_sq]
  norm_num

/-- The trial state `Γ = hvlTrialState fO fPhi = (0, c2, c2, 0)` (eq. (3.4.7)). -/
private lemma fTrial : hvlTrialState fO fPhi = ![0, c2, c2, 0] := by
  unfold hvlTrialState unitNormalize
  rw [fPhi_vecNormSq, show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), fO_mulVec_fPhi]
  ext i
  fin_cases i <;> simp

/-- The state `Ξ₊ = hvlPlusState fO fPhi = (1/2, 1/2, 1/2, 1/2)` (eq. (3.4.14)). -/
private lemma fXi : hvlPlusState fO fPhi = ![1/2, 1/2, 1/2, 1/2] := by
  have hpre : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = c2 := rfl
  unfold hvlPlusState
  rw [fTrial, hpre]
  unfold fPhi
  ext i
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.add_cons, add_zero,
      Matrix.empty_add_empty, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, smul_eq_mul, one_div, zero_add, add_zero] <;>
    rw [c2_sq] <;> norm_num

/-- `fH` is Hermitian. -/
private lemma fH_herm : fH.IsHermitian := by
  unfold Matrix.IsHermitian fH
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- `fO` is Hermitian. -/
private lemma fO_herm : fO.IsHermitian := by
  unfold Matrix.IsHermitian fO
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- `fPhi` is an `fH`-eigenvector at `E₀ = -1`. -/
private lemma fH_eigen : fH *ᵥ fPhi = (((-1 : ℝ)) : ℂ) • fPhi := by
  unfold fH fPhi
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Matrix.diagonal]

/-- Assumption (3.4.4), first moment: `⟨Φ|fO|Φ⟩ = 0`. -/
private lemma f_odd1 : star fPhi ⬝ᵥ (fO *ᵥ fPhi) = 0 := by
  rw [fO_mulVec_fPhi]
  unfold fPhi
  simp only [dotProduct, Fin.sum_univ_four, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, star_zero, mul_zero, zero_mul, add_zero]

/-- Assumption (3.4.4), third moment: `⟨Φ|fO³|Φ⟩ = 0` (proved, not assumed, from
`fO³ = !![0,4,4,0; 4,0,0,4; 4,0,0,4; 0,4,4,0]`). -/
private lemma f_odd3 : star fPhi ⬝ᵥ ((fO ^ 3) *ᵥ fPhi) = 0 := by
  have h : (fO ^ 3 : Matrix (Fin 4) (Fin 4) ℂ) = !![0,4,4,0; 4,0,0,4; 4,0,0,4; 0,4,4,0] := by
    unfold fO
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  rw [h]
  unfold fPhi
  simp only [dotProduct, mulVec, Fin.sum_univ_four, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, c2_star,
    star_zero, Matrix.vecHead, mul_zero, zero_mul]
  ring

/-- `rayleighOnVec fH Ξ₊ = 1`. -/
private lemma fXiH : rayleighOnVec fH (hvlPlusState fO fPhi) = 1 := by
  rw [fXi]
  unfold rayleighOnVec fH
  simp [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal]
  norm_num

/-- `rayleighOnVec fO Ξ₊ = 2`. -/
private lemma fXiO : rayleighOnVec fO (hvlPlusState fO fPhi) = 2 := by
  rw [fXi]
  unfold rayleighOnVec fO
  simp [dotProduct, mulVec, Fin.sum_univ_four]
  norm_num

/-- `rayleighOnVec fH Γ = 3`. -/
private lemma fGammaH : rayleighOnVec fH (hvlTrialState fO fPhi) = 3 := by
  rw [fTrial]
  unfold rayleighOnVec fH
  simp only [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal, Pi.star_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, c2_star, Matrix.of_apply]
  simp [Complex.mul_re, c2_im]
  nlinarith [c2_re_sq]

/-- `rayleighOnVec (fO ^ 2) fPhi = 4` (the order-square moment `m₂`). -/
private lemma fPhi_orderSq : rayleighOnVec (fO ^ 2) fPhi = 4 := by
  have h : (fO ^ 2 : Matrix (Fin 4) (Fin 4) ℂ) = !![2,0,0,2; 0,2,2,0; 0,2,2,0; 2,0,0,2] := by
    unfold fO
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  rw [h]
  unfold rayleighOnVec fPhi
  simp only [dotProduct, mulVec, Fin.sum_univ_four, Pi.star_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, c2_star, Matrix.of_apply]
  simp [Complex.mul_re, c2_im]
  nlinarith [c2_re_sq]

/-! ## Fixture 1 — the energy identity is discriminating -/

/-- **Fixture (energy identity, discriminating).** At the two-spin instance the identity reads
`1 = (-1 + 3) / 2`, and the two Rayleigh quotients it relates are asserted alongside it. Because
`E₀ = -1 ≠ 0` and `E₀ + rayleighOnVec fH Γ = 2 ≠ 0`, the un-halved value `2`, the `E₀`-free value
`3 / 2`, and the sign-flipped value `-2` are pairwise distinct from `1`, so a candidate of any of
those shapes could not satisfy all three conjuncts here. -/
example :
    rayleighOnVec fH (hvlPlusState fO fPhi)
        = (((-1 : ℝ)) + rayleighOnVec fH (hvlTrialState fO fPhi)) / 2
    ∧ rayleighOnVec fH (hvlPlusState fO fPhi) = 1
    ∧ rayleighOnVec fH (hvlTrialState fO fPhi) = 3 :=
  ⟨hvlPlusState_energy_eq fH_herm fO_herm fH_eigen fPhi_norm f_odd1, fXiH, fGammaH⟩

/-! ## Fixture 2 — eq. (3.4.16) is tight -/

/-- **Fixture (eq. (3.4.16), tight).** At `q₀ = 1`, `Ld = 2` (`L = 2`, `d = 1`), the LRO
hypothesis `q₀ ≤ m₂ / Ld ^ 2 = 4 / 4 = 1` holds with equality, and the conclusion
`√q₀ = 1 ≤ rayleighOnVec fO Ξ₊ / Ld = 2 / 2 = 1` is likewise an equality, as the second conjunct
records. A candidate whose right-hand side is strictly smaller at this data — dividing by `Ld ^ 2`
instead of `Ld`, say — is not `≤`-provable here, since `1 ≤ 1` is the tightest possible bound. -/
example :
    Real.sqrt (1 : ℝ) ≤ rayleighOnVec fO (hvlPlusState fO fPhi) / (2 : ℝ)
    ∧ rayleighOnVec fO (hvlPlusState fO fPhi) / (2 : ℝ) = 1 := by
  have hLRO : (1 : ℝ) ≤ rayleighOnVec (fO ^ 2) fPhi / (2 : ℝ) ^ 2 := by
    rw [fPhi_orderSq]; norm_num
  refine ⟨hvlPlusState_order_mean_ge_sqrt fO fPhi fO_herm f_odd1 f_odd3
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2) hLRO, ?_⟩
  rw [fXiO]; norm_num

/-! ## Fixture 3 — eq. (3.4.17), rational and tight instances -/

/-- **Fixture (eq. (3.4.17), strict).** `O' = diagonal ![2,0,0,-2]`, `v = (3/5, 4/5, 0, 0)`,
`Ld = 2`: the declaration's conclusion holds, and the two sides evaluate to `9 / 25` and `3 / 5`,
so the instance is strict and both endpoints are rational. The two evaluation conjuncts spell the
radicand out syntactically, since the `≤` endpoint alone cannot exclude a wrongly *larger*
right-hand side such as one dividing the radicand by `Ld` instead of `Ld ^ 2`:
`Real.sqrt (rayleighOnVec (O' ^ 2) v / Ld) = Real.sqrt (18 / 25) ≈ 0.849 > 3 / 5`. -/
example :
    |rayleighOnVec (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ![3/5, 4/5, 0, 0] / (2 : ℝ)|
      ≤ Real.sqrt
          (rayleighOnVec ((Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ^ 2) ![3/5, 4/5, 0, 0]
            / (2 : ℝ) ^ 2)
    ∧ |rayleighOnVec (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ![3/5, 4/5, 0, 0] / (2 : ℝ)|
        = 9 / 25
    ∧ Real.sqrt
        (rayleighOnVec ((Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ^ 2) ![3/5, 4/5, 0, 0]
          / (2 : ℝ) ^ 2) = 3 / 5 := by
  have hO' : (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]).IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  have hv : star (![(3 : ℂ)/5, 4/5, 0, 0]) ⬝ᵥ ![(3 : ℂ)/5, 4/5, 0, 0] = 1 := by
    simp only [dotProduct, Fin.sum_univ_four, Pi.star_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    norm_num
  have hL : rayleighOnVec (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ![(3 : ℂ)/5, 4/5, 0, 0] / 2
      = (9 : ℝ) / 25 := by
    unfold rayleighOnVec
    simp [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal, Complex.div_re,
      Complex.normSq_apply]
    norm_num
  have hR : rayleighOnVec ((Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ^ 2) ![(3 : ℂ)/5, 4/5, 0, 0]
      / (2 : ℝ) ^ 2 = (36 : ℝ) / 100 := by
    have hsq : (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ^ 2
        = Matrix.diagonal ![(4 : ℂ), 0, 0, 4] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [pow_two, Matrix.mul_apply, Matrix.diagonal] <;> norm_num
    rw [hsq]
    unfold rayleighOnVec
    simp [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal, Complex.div_re,
      Complex.normSq_apply]
    norm_num
  have hc : Real.sqrt ((36 : ℝ) / 100) = 3 / 5 := by
    rw [show (36 : ℝ) / 100 = (3 / 5 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨tasaki_eq_3_4_17_order_mean_abs_le_sqrt hO' hv (by norm_num : (0 : ℝ) < 2), ?_, ?_⟩
  · rw [hL]; norm_num
  · rw [hR, hc]

/-- **Fixture (eq. (3.4.17), negative `Ld`).** Same `O'`, `v` as the strict instance above, at
`Ld = -2` instead of `2`: the conclusion still evaluates to `9 / 25 ≤ 3 / 5`, since `|x / Ld|` and
`Ld ^ 2` are both insensitive to the sign of `Ld`. The declaration itself does not apply here (its
hypothesis is `0 < Ld`), so this instance is proved directly. It is one witness, not an exhaustive
check over all negative `Ld`, but it is the machine-checked support for treating `0 < Ld` as proof
convenience rather than a truth condition at this data. -/
example :
    |rayleighOnVec (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ![3/5, 4/5, 0, 0] / (-2 : ℝ)|
      ≤ Real.sqrt
          (rayleighOnVec ((Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ^ 2) ![3/5, 4/5, 0, 0]
            / (-2 : ℝ) ^ 2) := by
  have hL : rayleighOnVec (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ![(3 : ℂ)/5, 4/5, 0, 0] / (-2)
      = -((9 : ℝ) / 25) := by
    unfold rayleighOnVec
    simp [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal, Complex.div_re,
      Complex.normSq_apply]
    norm_num
  have hR : rayleighOnVec ((Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ^ 2) ![(3 : ℂ)/5, 4/5, 0, 0]
      / (-2 : ℝ) ^ 2 = (36 : ℝ) / 100 := by
    have hsq : (Matrix.diagonal ![(2 : ℂ), 0, 0, -2]) ^ 2
        = Matrix.diagonal ![(4 : ℂ), 0, 0, 4] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [pow_two, Matrix.mul_apply, Matrix.diagonal] <;> norm_num
    rw [hsq]
    unfold rayleighOnVec
    simp [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal, Complex.div_re,
      Complex.normSq_apply]
    norm_num
  rw [hL, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 9 / 25), hR,
    show (36 : ℝ) / 100 = (3 / 5 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

/-- **Fixture (eq. (3.4.17), tight).** `O = fO`, `v = hvlPlusState fO fPhi`, `Ld = 2`: both sides
equal `1`. -/
example :
    |rayleighOnVec fO (hvlPlusState fO fPhi) / (2 : ℝ)|
      ≤ Real.sqrt (rayleighOnVec (fO ^ 2) (hvlPlusState fO fPhi) / (2 : ℝ) ^ 2) := by
  have hΞ_norm : star (hvlPlusState fO fPhi) ⬝ᵥ hvlPlusState fO fPhi = 1 := by
    rw [fXi]
    simp only [dotProduct, Fin.sum_univ_four, Pi.star_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    norm_num
  have h := tasaki_eq_3_4_17_order_mean_abs_le_sqrt fO_herm hΞ_norm (by norm_num : (0 : ℝ) < 2)
  exact h

/-! ## Capstone satisfiability witness (`Λ = Fin 1`, `N = 1`, `B = ∅`, `o 0 = pauliXS 0`) -/

/-- The all-`Fin1` carrier: `Λ = Fin 1`, `N = 1`. -/
private abbrev Λw := Fin 1

/-- Spin-`1/2`: `N = 1` gives the qubit configuration space `Fin 1 → Fin 2`. -/
private abbrev Nw : ℕ := 1

/-- The order-operator family: the single-site Pauli `X` at the unique site. -/
private noncomputable def ow : Λw → ManyBodyOpS Λw Nw := fun _ => pauliXS (0 : Fin 1)

/-- The reference state: the `σ = 0` computational basis vector. -/
private noncomputable def Φw : (Λw → Fin (Nw + 1)) → ℂ := basisVecS (fun _ => (0 : Fin 2))

/-- `flipSite` is an involution: flipping the same site twice is the identity. -/
private theorem flipSite_flipSite_self {L : ℕ} (σ : Fin L → Fin 2) (x : Fin L) :
    flipSite (flipSite σ x) x = σ := by
  funext y
  by_cases hy : y = x
  · subst hy
    rw [flipSite_self, flipSite_self]
    generalize σ y = a
    fin_cases a <;> decide
  · rw [flipSite_of_ne _ hy, flipSite_of_ne _ hy]

/-- `pauliXS 0` squares to `1` at the matrix level (used for `hno`/`hLRO`/`hodd3` below). -/
private theorem ow_sq : ow (0 : Fin 1) * ow (0 : Fin 1) = 1 := by
  unfold ow
  ext τ σ
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (flipSite σ (0 : Fin 1))]
  · rw [pauliXS_apply, pauliXS_apply, if_pos rfl, mul_one, flipSite_flipSite_self]
  · intro c _ hc
    simp only [pauliXS_apply, if_neg hc, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `ow 0` sends the `σ = 0` basis vector to the `σ = 1` basis vector (the Pauli `X` flip). -/
private theorem ow_mulVec_Φw :
    (ow (0 : Fin 1)) *ᵥ Φw = basisVecS (fun _ : Fin 1 => (1 : Fin 2)) := by
  unfold ow
  ext τ
  rw [mulVec, dotProduct]
  unfold Φw
  rw [Finset.sum_eq_single (fun _ : Λw => (0 : Fin 2))]
  · rw [pauliXS_apply]
    have hflip : flipSite (fun _ : Fin 1 => (0 : Fin 2)) (0 : Fin 1) = fun _ => (1 : Fin 2) := by
      funext y
      have hy : y = (0 : Fin 1) := Subsingleton.elim y 0
      rw [hy, flipSite_self]
      decide
    rw [hflip]
    simp [basisVecS_apply]
  · intro c _ hc
    simp [basisVecS_apply, hc]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `hΦ` : `Φw` is normalised. -/
private theorem hΦw_holds : star Φw ⬝ᵥ Φw = 1 := by
  unfold Φw dotProduct
  rw [Finset.sum_eq_single (fun _ : Λw => (0 : Fin 2))]
  · simp
  · intro c _ hc
    simp [Pi.star_apply, basisVecS_apply, hc]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `hodd1` : `Φw` is orthogonal to `ow 0 *ᵥ Φw` (assumption (3.4.4), first moment). -/
private theorem hodd1w_holds : star Φw ⬝ᵥ (ow (0 : Fin 1) *ᵥ Φw) = 0 := by
  rw [ow_mulVec_Φw]
  unfold Φw dotProduct
  rw [Finset.sum_eq_single (fun _ : Λw => (0 : Fin 2))]
  · have hne : ¬ (fun _ : Fin 1 => (0 : Fin 2)) = fun _ => (1 : Fin 2) := by decide
    simp [basisVecS_apply, hne]
  · intro c _ hc
    simp [Pi.star_apply, basisVecS_apply, hc]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `(ow 0) ^ 3 *ᵥ Φw = ow 0 *ᵥ Φw`, from `(ow 0) ^ 2 = 1`. -/
private theorem ow_cube_mulVec_Φw :
    ((ow (0 : Fin 1)) ^ 3) *ᵥ Φw = ow (0 : Fin 1) *ᵥ Φw := by
  have h2 : (ow (0 : Fin 1)) ^ 2 = 1 := by rw [sq]; exact ow_sq
  rw [pow_succ, h2, one_mul]

/-- `hodd3` : the third-moment orthogonality reduces to `hodd1w_holds`. -/
private theorem hodd3w_holds : star Φw ⬝ᵥ (((ow (0 : Fin 1)) ^ 3) *ᵥ Φw) = 0 := by
  rw [ow_cube_mulVec_Φw]; exact hodd1w_holds

/-- `hLRO` at `q₀ = 1`, `d = L = 1`: `(ow 0) ^ 2 = 1` makes the order-square Rayleigh quotient
exactly `⟨Φw|Φw⟩ = 1`. -/
private theorem hLROw_holds :
    (1 : ℝ) ≤ rayleighOnVec ((ow (0 : Fin 1)) ^ 2) Φw / (((1 : ℕ) : ℝ) ^ (1 : ℕ)) ^ 2 := by
  have h2 : (ow (0 : Fin 1)) ^ 2 = 1 := by rw [sq]; exact ow_sq
  rw [h2]
  unfold rayleighOnVec
  simp only [Matrix.one_mulVec]
  rw [hΦw_holds]
  norm_num

/-- `hno` : `manyBodyOperatorNormS (ow 0) ≤ 1`, from the unitarity `(ow 0)ᴴ (ow 0) = 1`. -/
private theorem hnow_holds : manyBodyOperatorNormS (ow (0 : Fin 1)) ≤ (1 : ℝ) := by
  have hH : (ow (0 : Fin 1)).IsHermitian := by
    unfold ow pauliXS spinSSiteOp1
    refine Matrix.IsHermitian.smul (onSiteS_isHermitian 0 (spinSOp1_isHermitian 1)) ?_
    change star (2 : ℂ) = 2
    simp
  have hU : Matrix.conjTranspose (ow (0 : Fin 1)) * ow (0 : Fin 1) = 1 := by
    rw [hH.eq]; exact ow_sq
  exact le_of_eq (manyBodyOperatorNormS_eq_one_of_unitary hU)

/-- `hΦE` at `B = ∅`, `E₀ = 0`: the zero Hamiltonian's eigen-equation is trivial. -/
private theorem hΦEw_holds :
    (∑ _b ∈ (∅ : Finset Unit), (0 : ManyBodyOpS Λw Nw)) *ᵥ Φw = ((0 : ℝ) : ℂ) • Φw := by
  simp

/-- `hmin` at `B = ∅`, `E₀ = 0`: the zero Hamiltonian's Rayleigh quotient vanishes identically. -/
private theorem hminw_holds : ∀ v : (Λw → Fin (Nw + 1)) → ℂ, star v ⬝ᵥ v = 1 →
    (0 : ℝ) ≤ rayleighOnVec (∑ _b ∈ (∅ : Finset Unit), (0 : ManyBodyOpS Λw Nw)) v := by
  intro v _
  simp [rayleighOnVec]

/-- **The capstone's hypothesis bundle is jointly satisfiable.** At `Λ = Fin 1`, `N = 1`, `B = ∅`,
`o 0 = pauliXS 0`, `Φ = basisVecS (fun _ => 0)`, `d = L = q₀ = o₀ = 1`, `h₀ = 0`, `E₀ = 0`, every
named hypothesis of the capstone `tasaki_eq_3_4_16_lowLyingState_ssb` holds — discharged above by
proof against genuine `ManyBodyOpS`/`rayleighOnVec` declarations, not assumed. It therefore rules
out that the capstone is vacuously true for every instance. -/
example :
    (∑ _b ∈ (∅ : Finset Unit), (0 : ManyBodyOpS Λw Nw)).IsHermitian
    ∧ (∑ _x : Λw, ow _x).IsHermitian
    ∧ (∀ b ∈ (∅ : Finset Unit), ∀ z ∉ (∅ : Finset Λw), Commute (0 : ManyBodyOpS Λw Nw) (ow z))
    ∧ (∀ x z : Λw, x ≠ z → Commute (ow x) (ow z))
    ∧ (∀ b ∈ (∅ : Finset Unit), manyBodyOperatorNormS (0 : ManyBodyOpS Λw Nw) ≤ (0 : ℝ))
    ∧ (∀ x : Λw, manyBodyOperatorNormS (ow x) ≤ (1 : ℝ))
    ∧ (0 : ℝ) ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ (1 : ℝ)
    ∧ (∀ b ∈ (∅ : Finset Unit), (∅ : Finset Λw).card ≤ 2)
    ∧ (((∅ : Finset Unit).card : ℝ) ≤ (1 : ℝ) * (1 : ℝ) ^ (1 : ℕ))
    ∧ star Φw ⬝ᵥ Φw = 1
    ∧ (∑ _b ∈ (∅ : Finset Unit), (0 : ManyBodyOpS Λw Nw)) *ᵥ Φw = ((0 : ℝ) : ℂ) • Φw
    ∧ (∀ v : (Λw → Fin (Nw + 1)) → ℂ, star v ⬝ᵥ v = 1 →
        (0 : ℝ) ≤ rayleighOnVec (∑ _b ∈ (∅ : Finset Unit), (0 : ManyBodyOpS Λw Nw)) v)
    ∧ star Φw ⬝ᵥ ((∑ x : Λw, ow x) *ᵥ Φw) = 0
    ∧ star Φw ⬝ᵥ (((∑ x : Λw, ow x) ^ 3) *ᵥ Φw) = 0
    ∧ (0 : ℝ) < (1 : ℝ) ∧ (1 : ℕ) ≤ (1 : ℕ)
    ∧ (1 : ℝ) ≤ rayleighOnVec ((∑ x : Λw, ow x) ^ 2) Φw / (((1 : ℕ) : ℝ) ^ (1 : ℕ)) ^ 2 := by
  have hox : (∑ x : Λw, ow x) = ow (0 : Fin 1) := by
    simp
  refine ⟨Matrix.isHermitian_zero, ?_, by simp, ?_, by simp, ?_, le_refl _, zero_le_one,
    by simp, by simp, hΦw_holds, hΦEw_holds, hminw_holds, ?_, ?_, one_pos, le_refl _, ?_⟩
  · rw [hox]
    unfold ow pauliXS spinSSiteOp1
    refine Matrix.IsHermitian.smul (onSiteS_isHermitian 0 (spinSOp1_isHermitian 1)) ?_
    change star (2 : ℂ) = 2
    simp
  · intro x z hxz
    exact absurd (Subsingleton.elim x z) hxz
  · intro x; rw [show ow x = ow (0 : Fin 1) from congrArg ow (Subsingleton.elim x 0)]
    exact hnow_holds
  · rw [hox]; exact hodd1w_holds
  · rw [hox]; exact hodd3w_holds
  · rw [hox]; exact hLROw_holds

/-! ## Signature pins — the mirror state `Ξ₋` (PR-6, destined for
`HorschVonderLindenTrialState.lean` and `HorschVonderLindenLowLyingState.lean`) -/

/-- **Signature pin.** Pins `hvlTrialState_neg`: `hvlTrialState (-O) Φ = -hvlTrialState O Φ`, with
no hypothesis at all. Discharged only by the identifier itself. -/
example {n : Type*} [Fintype n] (O : Matrix n n ℂ) (Φ : n → ℂ) :
    hvlTrialState (-O) Φ = -hvlTrialState O Φ :=
  hvlTrialState_neg O Φ

/-- **Signature pin (definition).** Pins that `hvlMinusState` takes the same parameter shape as
`hvlPlusState`: a matrix and a vector on a common finite index type, returning a vector on that
type. -/
noncomputable example {n : Type*} [Fintype n] (O : Matrix n n ℂ) (Φ : n → ℂ) : n → ℂ :=
  hvlMinusState O Φ

/-- **Signature pin.** Pins the bridge `hvlMinusState O Φ = hvlPlusState (-O) Φ`, with no
hypothesis. Discharged only by the identifier itself. -/
example {n : Type*} [Fintype n] (O : Matrix n n ℂ) (Φ : n → ℂ) :
    hvlMinusState O Φ = hvlPlusState (-O) Φ :=
  hvlMinusState_eq_hvlPlusState_neg O Φ

/-- **Signature pin.** Pins the mirror-state normalisation `⟨Ξ₋|Ξ₋⟩ = 1`, at the same hypothesis
shape as `hvlPlusState_dotProduct_self`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ)
    (hO : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlMinusState O Φ) ⬝ᵥ hvlMinusState O Φ = 1 :=
  hvlMinusState_dotProduct_self O Φ hO hΦ hodd1 hm2

/-- **Signature pin.** Pins the mirror-state energy identity
`⟨Ξ₋|Ĥ|Ξ₋⟩ = (E₀ + ⟨Γ|Ĥ|Γ⟩) / 2`, the same right-hand side as `hvlPlusState_energy_eq`. A wrongly
sign-flipped right-hand side `(E₀ - ⟨Γ|Ĥ|Γ⟩) / 2` is *even* in the sign of `Γ`, so it agrees with
this one on every `Ξ₊` fixture; the fixture below (F2) separates them by an explicit value. -/
example {n : Type*} [Fintype n] {H O : Matrix n n ℂ} {Φ : n → ℂ} {E₀ : ℝ}
    (hH : H.IsHermitian) (hO : O.IsHermitian) (hΦE : H *ᵥ Φ = (E₀ : ℂ) • Φ)
    (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0) :
    rayleighOnVec H (hvlMinusState O Φ)
      = (E₀ + rayleighOnVec H (hvlTrialState O Φ)) / 2 :=
  hvlMinusState_energy_eq hH hO hΦE hΦ hodd1

/-- **Signature pin.** Pins the mirror-state order mean
`⟨Ξ₋|Ô|Ξ₋⟩ = -√(⟨Φ|Ô²|Φ⟩)`, negative where `hvlPlusState_order_mean`'s right-hand side
`Real.sqrt (rayleighOnVec (O ^ 2) Φ)` is positive. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ)
    (hO : O.IsHermitian) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec O (hvlMinusState O Φ) = -Real.sqrt (rayleighOnVec (O ^ 2) Φ) :=
  hvlMinusState_order_mean O Φ hO hodd1 hodd3 hm2

/-- **Signature pin.** Pins the mirror order bound `⟨Ξ₋|Ô|Ξ₋⟩ / Ld ≤ -√q₀`, an upper bound in the
opposite direction from `hvlPlusState_order_mean_ge_sqrt`'s lower bound `√q₀ ≤ ⟨Ξ₊|Ô|Ξ₊⟩ / Ld`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ)
    {q₀ Ld : ℝ} (hO : O.IsHermitian) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hq₀ : 0 < q₀) (hLd : 0 < Ld)
    (hLRO : q₀ ≤ rayleighOnVec (O ^ 2) Φ / Ld ^ 2) :
    rayleighOnVec O (hvlMinusState O Φ) / Ld ≤ -Real.sqrt q₀ :=
  hvlMinusState_order_mean_le_neg_sqrt O Φ hO hodd1 hodd3 hq₀ hLd hLRO

/-- **Signature pin.** Pins the cross-orthogonality `⟨Ξ₋|Ξ₊⟩ = 0` between the two mirror states,
which has no `Ξ₊`-side counterpart obtainable by a sign substitution alone. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ)
    (hO : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlMinusState O Φ) ⬝ᵥ hvlPlusState O Φ = 0 :=
  hvlMinusState_dotProduct_hvlPlusState O Φ hO hΦ hodd1 hm2

/-- **Signature pin (capstone).** Pins the five conjuncts of `tasaki_mirrorLowLyingState_ssb`:
mirror-state normalisation, cross-orthogonality to `Ξ₊`, the same two-sided energy bound as
`tasaki_eq_3_4_16_lowLyingState_ssb`, and the mirror order bound `≤ -√q₀` in place of that
declaration's `√q₀ ≤ …`. Discharged only by the identifier itself. -/
example {ι : Type*} (B : Finset ι)
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
    star (hvlMinusState (∑ x : Λ, o x) Φ) ⬝ᵥ hvlMinusState (∑ x : Λ, o x) Φ = 1
    ∧ star (hvlMinusState (∑ x : Λ, o x) Φ) ⬝ᵥ hvlPlusState (∑ x : Λ, o x) Φ = 0
    ∧ 0 ≤ rayleighOnVec (∑ b ∈ B, hb b) (hvlMinusState (∑ x : Λ, o x) Φ) - E₀
    ∧ rayleighOnVec (∑ b ∈ B, hb b) (hvlMinusState (∑ x : Λ, o x) Φ) - E₀
        ≤ 4 * (d : ℝ) * h₀ * o₀ ^ 2 / q₀ / (L : ℝ) ^ d
    ∧ rayleighOnVec (∑ x : Λ, o x) (hvlMinusState (∑ x : Λ, o x) Φ) / (L : ℝ) ^ d
        ≤ -Real.sqrt q₀ :=
  tasaki_mirrorLowLyingState_ssb B hb o W d L q₀ h₀ o₀ hH hO hW hoo hnh hno hh₀ ho₀
    hbond hB hΦ hΦE hmin hodd1 hodd3 hq₀ hL hLRO

/-! ## Fixture F1 — the mirror state at the two-spin fixture, sign-discriminating -/

/-- **Fixture F1 (state-level, sign-discriminating).** `Ξ₋ = (1/2, -1/2, -1/2, 1/2)` at the
two-spin fixture `fO`, `fPhi` — differing from `Ξ₊ = fXi = (1/2, 1/2, 1/2, 1/2)` in the sign of
its middle two entries, so a copy-paste of the `Ξ₊` definition would fail this fixture. -/
private lemma fXiMinus : hvlMinusState fO fPhi = ![1/2, -(1/2), -(1/2), 1/2] := by
  have hpre : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = c2 := rfl
  unfold hvlMinusState
  rw [fTrial, hpre]
  unfold fPhi
  ext i
  fin_cases i <;>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.sub_cons, sub_zero, zero_sub,
      Matrix.empty_sub_empty, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.head_cons, Matrix.tail_cons, smul_eq_mul, one_div, mul_neg] <;>
    rw [c2_sq] <;> norm_num

/-! ## Fixture F2 — the energy identity, with sign discrimination -/

/-- `rayleighOnVec fH Ξ₋ = 1`, the same numeric value the `Ξ₊` fixture `fXiH` gives at `Ξ₊`. -/
private lemma fXiMinusH : rayleighOnVec fH (hvlMinusState fO fPhi) = 1 := by
  rw [fXiMinus]
  unfold rayleighOnVec fH
  simp [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal]
  norm_num

/-- `rayleighOnVec fO Ξ₋ = -2`, against `fXiO`'s `+2` at `Ξ₊`: the sign-discriminating value that
an erroneously un-mirrored order operator, or a direction error in `hvlMinusState` itself, would
fail to reproduce. -/
private lemma fXiMinusO : rayleighOnVec fO (hvlMinusState fO fPhi) = -2 := by
  rw [fXiMinus]
  unfold rayleighOnVec fO
  simp [dotProduct, mulVec, Fin.sum_univ_four]
  norm_num

/-- **Fixture F2 (energy identity, sign-discriminating).** The identity reads `1 = (-1 + 1) / 2`
at the two-spin fixture — the same right-hand-side *shape* as the `Ξ₊` energy identity, but at
`Γ`'s Ξ₋-side value, alongside the two sign-separating Rayleigh values `rayleighOnVec fH Ξ₋ = 1`
and `rayleighOnVec fO Ξ₋ = -2`. Since the energy identity's own right-hand side is even in the
sign of `Γ`, an erroneous minus sign there would still pass this and every `Ξ₊` fixture; the
`fO`-side conjunct is what would catch a wrongly-signed `hvlMinusState`. -/
example :
    rayleighOnVec fH (hvlMinusState fO fPhi)
        = (((-1 : ℝ)) + rayleighOnVec fH (hvlTrialState fO fPhi)) / 2
    ∧ rayleighOnVec fH (hvlMinusState fO fPhi) = 1
    ∧ rayleighOnVec fO (hvlMinusState fO fPhi) = -2 :=
  ⟨hvlMinusState_energy_eq fH_herm fO_herm fH_eigen fPhi_norm f_odd1, fXiMinusH, fXiMinusO⟩

/-! ## Fixture F3 — orthogonality and normalisation -/

/-- **Fixture F3 (orthogonality, normalisation).** `⟨Ξ₋|Ξ₊⟩ = 0` and `⟨Ξ₋|Ξ₋⟩ = 1` at the
two-spin fixture. Substituting `Ξ₊` for `Ξ₋` in the first conjunct would read `⟨Ξ₊|Ξ₊⟩ = 1`
against a claimed `= 0`, i.e. `1 = 0`, so this conjunct alone rules that substitution out. -/
example :
    star (hvlMinusState fO fPhi) ⬝ᵥ hvlPlusState fO fPhi = 0
    ∧ star (hvlMinusState fO fPhi) ⬝ᵥ hvlMinusState fO fPhi = 1 := by
  have hm2 : 0 < rayleighOnVec (fO ^ 2) fPhi := by rw [fPhi_orderSq]; norm_num
  exact ⟨hvlMinusState_dotProduct_hvlPlusState fO fPhi fO_herm fPhi_norm f_odd1 hm2,
    hvlMinusState_dotProduct_self fO fPhi fO_herm fPhi_norm f_odd1 hm2⟩

/-! ## Fixture F4 — the mirror order bound, exactly tight -/

/-- **Fixture F4 (mirror order bound, tight).** At `q₀ = 1`, `Ld = 2` (`L = 2`, `d = 1`), the LRO
hypothesis `q₀ ≤ m₂ / Ld ^ 2 = 4 / 4 = 1` holds with equality, and the conclusion
`⟨Ξ₋|Ô|Ξ₋⟩ / Ld = -2 / 2 = -1 = -√q₀` is likewise an equality, as the second conjunct records: both
the hypothesis and the conclusion are exactly tight, so neither a weakened nor a strengthened
right-hand side passes here. The third conjunct is the untruncated order-mean identity
`⟨Ξ₋|Ô|Ξ₋⟩ = -√(⟨Φ|Ô²|Φ⟩)` this bound is built from. -/
example :
    rayleighOnVec fO (hvlMinusState fO fPhi) / (2 : ℝ) ≤ -Real.sqrt (1 : ℝ)
    ∧ rayleighOnVec fO (hvlMinusState fO fPhi) / (2 : ℝ) = -1
    ∧ rayleighOnVec fO (hvlMinusState fO fPhi) = -Real.sqrt (rayleighOnVec (fO ^ 2) fPhi) := by
  have hm2 : 0 < rayleighOnVec (fO ^ 2) fPhi := by rw [fPhi_orderSq]; norm_num
  have hLRO : (1 : ℝ) ≤ rayleighOnVec (fO ^ 2) fPhi / (2 : ℝ) ^ 2 := by
    rw [fPhi_orderSq]; norm_num
  refine ⟨hvlMinusState_order_mean_le_neg_sqrt fO fPhi fO_herm f_odd1 f_odd3
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2) hLRO, ?_, ?_⟩
  · rw [fXiMinusO]; norm_num
  · exact hvlMinusState_order_mean fO fPhi fO_herm f_odd1 f_odd3 hm2

/-! ## Fixture F5 — negative size parameter falsifies the mirror bound's conclusion -/

/-- **Fixture F5 (negative `Ld`).** At `fO`, `Ξ₋`, `Ld = -2` the conclusion of
`hvlMinusState_order_mean_le_neg_sqrt` fails: `⟨Ξ₋|Ô|Ξ₋⟩ / (-2) = -2 / (-2) = 1`, which is not
`≤ -√1 = -1`. The declaration's own hypothesis `0 < Ld` is load-bearing at this data. -/
example : ¬ (rayleighOnVec fO (hvlMinusState fO fPhi) / (-2 : ℝ) ≤ -Real.sqrt (1 : ℝ)) := by
  rw [fXiMinusO, Real.sqrt_one]
  norm_num

/-! ## Fixtures F6/F7 — a vanishing order-square Rayleigh quotient -/

/-- The one-site reference vector for the vanishing-quotient fixtures F6/F7. -/
private noncomputable def bPhi : Fin 1 → ℂ := ![1]

/-- `bPhi` is normalised. -/
private lemma bPhi_norm : star bPhi ⬝ᵥ bPhi = 1 := by
  unfold bPhi
  simp [dotProduct]

/-- At the zero order operator the trial state is the zero vector. -/
private lemma bTrial : hvlTrialState (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi = 0 := by
  unfold hvlTrialState unitNormalize
  simp

/-- **Fixture F6 (vanishing order-square quotient).** At `O = 0`, `Φ = bPhi`, the trial state
collapses to the zero vector, so `Ξ₋` collapses onto `Ξ₊`: both `⟨Ξ₋|Ξ₋⟩` and `⟨Ξ₋|Ξ₊⟩` evaluate
to `1 / 2` rather than to `1` and `0` respectively. This is evidence that the positivity
hypothesis `0 < rayleighOnVec (O ^ 2) Φ` in `hvlMinusState_dotProduct_self` and
`hvlMinusState_dotProduct_hvlPlusState` is a genuine truth condition, not proof convenience: both
declarations' conclusions fail at this data, so they are not being invoked here. -/
example :
    star (hvlMinusState (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi)
        ⬝ᵥ hvlMinusState (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi = 1 / 2
    ∧ star (hvlMinusState (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi)
        ⬝ᵥ hvlPlusState (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi = 1 / 2
    ∧ rayleighOnVec (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi = 0 := by
  refine ⟨?_, ?_, by simp [rayleighOnVec]⟩
  · unfold hvlMinusState
    rw [bTrial]
    simp only [sub_zero, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, bPhi_norm, mul_one]
    rw [sqrt2_inv_mul_sqrt2_inv]
  · unfold hvlMinusState hvlPlusState
    rw [bTrial]
    simp only [sub_zero, add_zero, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      Complex.star_def, map_inv₀, Complex.conj_ofReal, bPhi_norm, mul_one]
    rw [sqrt2_inv_mul_sqrt2_inv]

/-- **Fixture F7 (energy identity at a vanishing order-square quotient).** The energy identity
carries no positivity hypothesis on the order-square Rayleigh quotient, and holds even where the
quotient vanishes: at `O = 0`, `H = diagonal ![5]`, both sides of the identity evaluate to `5 / 2`.
-/
example :
    rayleighOnVec (Matrix.diagonal ![(5 : ℂ)]) (hvlMinusState (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi)
      = ((5 : ℝ) + rayleighOnVec (Matrix.diagonal ![(5 : ℂ)])
          (hvlTrialState (0 : Matrix (Fin 1) (Fin 1) ℂ) bPhi)) / 2 := by
  have hH : (Matrix.diagonal ![(5 : ℂ)]).IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j; fin_cases i; fin_cases j; simp [Matrix.diagonal]
  have hE : (Matrix.diagonal ![(5 : ℂ)]) *ᵥ bPhi = ((5 : ℝ) : ℂ) • bPhi := by
    unfold bPhi
    ext i
    fin_cases i; simp [mulVec, dotProduct, Matrix.diagonal]
  exact hvlMinusState_energy_eq hH Matrix.isHermitian_zero hE bPhi_norm (by simp)

/-! ## Fixture F8 — capstone non-vacuity, mirror form -/

/-- **Fixture F8 (capstone non-vacuity, mirror form).** The mirror capstone
`tasaki_mirrorLowLyingState_ssb`, applied at the same witness data as the `Ξ₊` capstone's
non-vacuity fixture (`Λw = Fin 1`, `N = 1`, `B = ∅`, `o 0 = pauliXS 0`, `d = L = q₀ = o₀ = 1`,
`h₀ = 0`, `E₀ = 0`), produces its five conjuncts concretely. The hypothesis bundle is already
discharged above (`hΦw_holds`, `hΦEw_holds`, `hminw_holds`, `hodd1w_holds`, `hodd3w_holds`,
`hLROw_holds`, `hnow_holds`) for the `Ξ₊` capstone and is reused here rather than restated. -/
example :
    star (hvlMinusState (∑ x : Λw, ow x) Φw) ⬝ᵥ hvlMinusState (∑ x : Λw, ow x) Φw = 1
    ∧ star (hvlMinusState (∑ x : Λw, ow x) Φw) ⬝ᵥ hvlPlusState (∑ x : Λw, ow x) Φw = 0
    ∧ (0 : ℝ) ≤ rayleighOnVec (∑ _b ∈ (∅ : Finset Unit), (0 : ManyBodyOpS Λw Nw))
        (hvlMinusState (∑ x : Λw, ow x) Φw) - 0
    ∧ rayleighOnVec (∑ _b ∈ (∅ : Finset Unit), (0 : ManyBodyOpS Λw Nw))
        (hvlMinusState (∑ x : Λw, ow x) Φw) - 0
        ≤ 4 * ((1 : ℕ) : ℝ) * 0 * (1 : ℝ) ^ 2 / 1 / ((1 : ℕ) : ℝ) ^ (1 : ℕ)
    ∧ rayleighOnVec (∑ x : Λw, ow x) (hvlMinusState (∑ x : Λw, ow x) Φw)
        / ((1 : ℕ) : ℝ) ^ (1 : ℕ) ≤ -Real.sqrt 1 := by
  have hox : (∑ x : Λw, ow x) = ow (0 : Fin 1) := by simp
  have hOw : (∑ x : Λw, ow x).IsHermitian := by
    rw [hox]
    unfold ow pauliXS spinSSiteOp1
    refine Matrix.IsHermitian.smul (onSiteS_isHermitian 0 (spinSOp1_isHermitian 1)) ?_
    change star (2 : ℂ) = 2
    simp
  have hnoall : ∀ x : Λw, manyBodyOperatorNormS (ow x) ≤ (1 : ℝ) := by
    intro x
    rw [show ow x = ow (0 : Fin 1) from congrArg ow (Subsingleton.elim x 0)]
    exact hnow_holds
  exact tasaki_mirrorLowLyingState_ssb (∅ : Finset Unit) (fun _ => (0 : ManyBodyOpS Λw Nw)) ow
    (fun _ => (∅ : Finset Λw)) 1 1 1 0 1 Matrix.isHermitian_zero hOw (by simp)
    (fun x z hxz => absurd (Subsingleton.elim x z) hxz) (by simp)
    hnoall
    (le_refl _) zero_le_one (by simp) (by simp) hΦw_holds hΦEw_holds hminw_holds
    (by rw [hox]; exact hodd1w_holds) (by rw [hox]; exact hodd3w_holds) one_pos (le_refl _)
    (by rw [hox]; exact hLROw_holds)

end LatticeSystem.Tests.HorschVonderLindenLowLyingState
