import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiu
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveCorrelation
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismGroundTower

/-!
# §10.2.3 (Theorem 10.8): pair operator, ladder algebra, and the signed-sum comparison

Algebraic layer of **Tasaki Theorem 10.8** (Lieb–Shen–Qiu superconductivity; Hal Tasaki, *Physics
and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.3, p. 359,
eq. (10.2.22)).  The superconducting bound compares two double sums over pairs of sites: the
off-diagonal-long-range-order observable `b̂† b̂` of the **attractive** ground state `φ` and the
transverse ladder product `Ŝ⁺_tot Ŝ⁻_tot` of its Shiba image `ψ = Û φ`.  This file supplies the
identities and the two inequalities that make the comparison term-wise.

## Main results

* `totalPairCreationOperator_eq_conjTranspose` — `b̂† = b̂ᴴ`, so `b̂† b̂` is a positive observable
  (the degenerate `Ne = 2(N+1)` branch of the capstone rests on this alone).
* `totalPairCorrelationOperator_eq_sum` — `b̂† b̂ = Σ_{x,y} ĉ†_{x↑} ĉ†_{x↓} ĉ_{y↓} ĉ_{y↑}`, the
  double sum of the on-site pair-transfer operators of Theorem 10.3.
* `fermionTotalSpinPlusMinus_eq_sum` — `Ŝ⁺_tot Ŝ⁻_tot = Σ_{x,y} Ŝ⁺_x Ŝ⁻_y`, the matching double
  sum of per-site ladder products.
* `shiba_spinPlusMinus_expectation_eq_signed_sum` — Shiba transport (eq. (10.2.13)) turns the
  expectation of the ladder product in `ψ` into the **sublattice-signed** sum
  `Σ_{x,y} ε_x ε_y ⟨φ| ĉ†_{x↑} ĉ†_{x↓} ĉ_{y↓} ĉ_{y↑} |φ⟩`, `ε_x = ±1`.
* `gaugeSign_mul_re_mul_le_of_pos` — the term-wise sign comparison `ε_x ε_y p ≤ p` for `p > 0`,
  which bounds the signed sum by the unsigned one.  Tasaki argues the same step through
  Theorem 10.5's correlation sign (eq. (10.2.25)); in this development that sign is itself
  *derived* from the Shiba identity plus Theorem 10.3's strict positivity
  (`theorem_10_5_shen_qiu_tian_transverse_sign`), so the comparison is made directly from the two
  ingredients and Theorem 10.5 is not invoked as a lemma.
* `liebShenQiuPairLowerBound_le_casimir_gap` — the real arithmetic
  `(|A| − Ne/2)(Ne/2 − |B|) ≤ S₀(S₀+1) − m(m−1)` at `S₀ = ||A|−|B||/2` and `m = (Ne − (N+1))/2`,
  the step from the Casimir/weight data of `ψ` to eq. (10.2.22)'s bound.  The slack is exactly
  `Ne/2 − |B| ≥ 0`.
* `liebShenQiu_towerExponent_le_sublatticeImbalance` — `|A| − Ne/2 ≤ ||A| − |B||`, discharging the
  tower-exponent hypothesis of `liebShenQiu_sectorGround_mem_halfFillingGround` from Theorem
  10.8's own hypotheses `2|B| ≤ Ne ≤ 2|A|`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (eq. (10.2.13), p. 353) and §10.2.3 (Theorem 10.8, eqs. (10.2.22)/(10.2.25),
pp. 359–360); E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201; S.-Q. Shen, Z.-M. Qiu, G.-S. Tian,
*Phys. Rev. Lett.* **72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

variable {N : ℕ}

/-! ## The total pair operator -/

/-- **The total pair creation operator is the adjoint of the total pair annihilation operator**,
`b̂† = b̂ᴴ` with `b̂ = Σ_x ĉ_{x,↓} ĉ_{x,↑}` (Tasaki eq. (10.2.22)): the sum of the per-site adjoint
relations `(ĉ†_{x,↑} ĉ†_{x,↓})ᴴ = ĉ_{x,↓} ĉ_{x,↑}`. -/
theorem totalPairCreationOperator_eq_conjTranspose (N : ℕ) :
    totalPairCreationOperator N = Matrix.conjTranspose (totalPairAnnihilationOperator N) := by
  rw [totalPairAnnihilationOperator, Matrix.conjTranspose_sum, totalPairCreationOperator]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← fermionSitePairCreation_conjTranspose N x, Matrix.conjTranspose_conjTranspose]

/-- **The pair-correlation observable is the double sum of on-site pair-transfer operators**,
`b̂† b̂ = Σ_{x,y} ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑}` (Tasaki eq. (10.2.22) expanded through
eq. (10.2.4)): expand the product of the two sums and reassociate. -/
theorem totalPairCorrelationOperator_eq_sum (N : ℕ) :
    totalPairCorrelationOperator N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1), hubbardPairCorrelationOp N x y := by
  rw [totalPairCorrelationOperator, totalPairCreationOperator, totalPairAnnihilationOperator,
    Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [hubbardPairCorrelationOp]
  simp only [mul_assoc]

/-- **The total ladder product is the double sum of per-site ladder products**,
`Ŝ⁺_tot Ŝ⁻_tot = Σ_{x,y} Ŝ⁺_x Ŝ⁻_y`: the total ladder operators are the site sums of the per-site
ones, and the product of the two sums expands. -/
theorem fermionTotalSpinPlusMinus_eq_sum (N : ℕ) :
    fermionTotalSpinPlus N * fermionTotalSpinMinus N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          fermionSiteSpinPlus N x * fermionSiteSpinMinus N y := by
  rw [fermionTotalSpinPlus_eq_sum_siteSpinPlus, fermionTotalSpinMinus_eq_sum_siteSpinMinus,
    Finset.sum_mul_sum]

/-! ## Shiba transport of the ladder expectation -/

/-- **The transported ladder expectation is the sublattice-signed pair-correlation sum**
(Tasaki eq. (10.2.13), p. 353): for `ψ = Û φ` with the Shiba unitary `Û = shibaSignedUnitary N
(shibaSignFn A)`,
`⟨ψ| Ŝ⁺_tot Ŝ⁻_tot |ψ⟩ = Σ_{x,y} ε_x ε_y ⟨φ| ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑} |φ⟩`,
`ε_x = gaugeSign A x = ±1`.  Expand the ladder product into the double sum, distribute the
conjugation over it, and apply `shibaSignedUnitary_conj_spinPlusMinus` term by term. -/
theorem shiba_spinPlusMinus_expectation_eq_signed_sum (N : ℕ) (A : Finset (Fin (N + 1)))
    (φ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2))
    (hψ : ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp) :
    euclideanExpectation (fermionTotalSpinPlus N * fermionTotalSpinMinus N) ψ
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (gaugeSign A x * gaugeSign A y)
            * euclideanExpectation (hubbardPairCorrelationOp N x y) φ := by
  have hconj : Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * (fermionTotalSpinPlus N * fermionTotalSpinMinus N)
        * shibaSignedUnitary N (shibaSignFn A)
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (gaugeSign A x * gaugeSign A y) • hubbardPairCorrelationOp N x y := by
    rw [fermionTotalSpinPlusMinus_eq_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, shibaSignedUnitary_conj_spinPlusMinus]
  rw [euclideanExpectation_shiba_conj _ _ ψ φ hψ, hconj, euclideanExpectation_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [euclideanExpectation_sum]
  exact Finset.sum_congr rfl fun y _ => euclideanExpectation_smul _ _ _

/-! ## The two inequalities -/

/-- **The sublattice-gauge sign cannot increase a positive quantity**:
`(ε_x ε_y).re · p ≤ p` for `p > 0`, since `ε_x ε_y = ±1` (`+1` on a common sublattice, `−1`
across the bipartition).  Summed over `x, y` this bounds the signed sum of Tasaki
eq. (10.2.13) by the unsigned pair-correlation sum `⟨φ| b̂† b̂ |φ⟩`. -/
theorem gaugeSign_mul_re_mul_le_of_pos (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) {p : ℝ}
    (hp : 0 < p) : (gaugeSign A x * gaugeSign A y).re * p ≤ p := by
  by_cases h : SameSublattice A x y
  · rw [gaugeSign_mul_sameSublattice A x y h, Complex.one_re, one_mul]
  · rw [gaugeSign_mul_not_sameSublattice A x y h, Complex.neg_re, Complex.one_re]
    linarith

/-- **Theorem 10.8's lower bound is dominated by the Casimir/weight gap**:
`(|A| − Ne/2)(Ne/2 − |B|) ≤ S₀(S₀+1) − m(m−1)` at `S₀ = ||A| − |B||/2` and `m = (Ne − (N+1))/2`,
whenever `2|B| ≤ Ne ≤ 2|A|`.  With `|A| + |B| = N + 1` the two-sided bound forces `|B| ≤ |A|`,
hence `||A| − |B|| = |A| − |B|`, and then the difference of the two sides is exactly the slack
`Ne/2 − |B| ≥ 0`.  The right-hand side is the value of `⟨ψ| Ŝ⁺_tot Ŝ⁻_tot |ψ⟩` fixed by
`Ŝ² ψ = S₀(S₀+1) ψ` and `Ŝ³ ψ = m ψ`. -/
theorem liebShenQiuPairLowerBound_le_casimir_gap (N : ℕ) (A : Finset (Fin (N + 1))) (Ne : ℕ)
    (hb : 2 * (bipartitionComplement A).card ≤ Ne) (ha : Ne ≤ 2 * A.card) :
    liebShenQiuPairLowerBound A Ne
      ≤ (liebRepulsiveSpinCasimir A).re
        - (((Ne : ℝ) - ((N : ℝ) + 1)) / 2) * ((((Ne : ℝ) - ((N : ℝ) + 1)) / 2) - 1) := by
  have hLnat := sublatticeImbalance_add_bipartitionComplement_card A (by omega)
  have hcard := bipartitionComplement_card_add N A
  have hL : (sublatticeImbalance A : ℝ) + ((bipartitionComplement A).card : ℝ)
      = (A.card : ℝ) := by exact_mod_cast hLnat
  have hAB : (A.card : ℝ) + ((bipartitionComplement A).card : ℝ) = (N : ℝ) + 1 := by
    exact_mod_cast hcard
  have hbn : 2 * ((bipartitionComplement A).card : ℝ) ≤ (Ne : ℝ) := by exact_mod_cast hb
  have hLv : (sublatticeImbalance A : ℝ)
      = (A.card : ℝ) - ((bipartitionComplement A).card : ℝ) := by linarith
  rw [liebShenQiuPairLowerBound, liebRepulsiveSpinCasimir_eq_ofReal, Complex.ofReal_re, ← hAB,
    hLv]
  nlinarith [hbn]

/-- **The tower exponent never exceeds the sublattice imbalance**: `|A| − Ne/2 ≤ ||A| − |B||`
under Theorem 10.8's hypotheses `2|B| ≤ Ne ≤ 2|A|`.  The bounds give `|B| ≤ |A|`, so the
imbalance is `|A| − |B|`, and `2|B| ≤ Ne` gives `|B| ≤ Ne/2`.  This discharges the hypothesis
`hk` of `liebShenQiu_sectorGround_mem_halfFillingGround` at the tower exponent
`k = |A| − Ne/2`. -/
theorem liebShenQiu_towerExponent_le_sublatticeImbalance (N : ℕ) (A : Finset (Fin (N + 1)))
    (Ne : ℕ) (hb : 2 * (bipartitionComplement A).card ≤ Ne) (ha : Ne ≤ 2 * A.card) :
    A.card - Ne / 2 ≤ sublatticeImbalance A := by
  have hLnat := sublatticeImbalance_add_bipartitionComplement_card A (by omega)
  omega

end LatticeSystem.Fermion
