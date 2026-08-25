import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuShibaTransport
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuSectorCasimir
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuPairAlgebra

/-!
# Tasaki Theorem 10.8: the Lieb–Shen–Qiu superconducting bound (discharge)

This file **proves** Tasaki Theorem 10.8 (Lieb–Shen–Qiu superconductivity; Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.3, p. 359,
eq. (10.2.22)): for the symmetric attractive Hubbard Hamiltonian
`Ĥ^{attr,sym}(T,U) = Ĥhop(T) − Σ_x U_x (n̂_{x↑}−½)(n̂_{x↓}−½)` (eq. (10.2.21)) on a bipartite
connected lattice `Λ = A ⊔ B`, at even electron number `Ne` with `2|B| ≤ Ne ≤ 2|A|`, the unique
ground state `φ` satisfies the off-diagonal-long-range-order bound

  `⟨φ| b̂† b̂ |φ⟩ ≥ (|A| − Ne/2)(Ne/2 − |B|)`,   `b̂ = Σ_x ĉ_{x,↓} ĉ_{x,↑}`,

the expectation being real.  The declaration `theorem_10_8_lieb_shen_qiu_superconductivity` was
previously recorded as a faithful documented `axiom` (in `LiebShenQiu.lean`, which retains only the
definitions the statement is written with); it is now a fully proved theorem, discharged axiom-free
(modulo `propext`/`Classical.choice`/`Quot.sound`).

## The assembly

The imaginary part is branch-free: `b̂† b̂ = b̂ᴴ b̂` is a square, so its expectation is the
real cast of a sum of squared norms (`liebShenQiu_pairExpectation_eq_normSq`).  The lower bound
splits on whether the band `Ne ≤ 2|A| ≤ 2(N+1)` is saturated.

* `Ne < 2(N+1)`: shift the centred interaction away
  (`liebShenQiu_attractiveGround_of_symmetric`) so that `φ` is a plain-attractive ground state at
  the shifted hopping `T + diag(U/2)`; Theorem 10.2 then makes it a spin singlet
  (`liebShenQiu_ground_singlet`) and Theorem 10.3 makes all its pair-transfer correlations
  strictly positive.  The Shiba transport of §10.2.3 carries `φ` to a unique ground state
  `ψ = Û φ` of the symmetric **repulsive** model on the spin-`z` sector `Ŝ³ = (Ne − (N+1))/2` at
  half filling, where Theorem 10.4 fixes the Casimir value `Ŝ² ψ = S₀(S₀+1) ψ`, `S₀ = ||A|−|B||/2`.
  The ladder identity `Ŝ⁺Ŝ⁻ = Ŝ² − Ŝ³(Ŝ³−1)` evaluates `⟨ψ| Ŝ⁺Ŝ⁻ |ψ⟩ = S₀(S₀+1) − m(m−1)`
  (`liebShenQiu_spinPlusMinus_expectation_eq`), the Shiba identity rewrites that expectation as the
  sublattice-signed pair sum on `φ`, and the signs can only decrease a positive sum
  (`liebShenQiu_signedSum_re_le_pairExpectation_re`).  The real arithmetic
  `liebShenQiuPairLowerBound_le_casimir_gap` closes the chain.
* `Ne = 2(N+1)`: the band forces `|A| = N+1`, `|B| = 0` and hence a vanishing bound, which the
  positivity of `⟨φ| b̂ᴴ b̂ |φ⟩` meets with no reference to the ground-state hypothesis
  (`liebShenQiu_bound_of_full`).

Theorem 10.5 (`theorem_10_5_shen_qiu_tian_transverse_sign`) is **not** used: Tasaki argues the
sign step of eq. (10.2.25) through it, whereas here the sign is re-derived directly from the Shiba
identity plus Theorem 10.3's strict positivity, so the transverse-correlation layer of §10.2.2 does
not enter this route.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.3 (Theorem 10.8, eqs. (10.2.21)/(10.2.22)/(10.2.25), pp. 359–360) and §10.2.2
(eq. (10.2.13), p. 353); E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201; S.-Q. Shen, Z.-M. Qiu,
G.-S. Tian, *Phys. Rev. Lett.* **72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

/-! ## The pair observable is a square -/

/-- **The pair-correlation expectation is a nonnegative real number**,
`⟨φ| b̂† b̂ |φ⟩ = Σ_j |(b̂ φ)_j|²`: `b̂† = b̂ᴴ` (`totalPairCreationOperator_eq_conjTranspose`), so
the observable is `b̂ᴴ b̂` and its expectation is the squared norm of `b̂ φ`.  This supplies both
the vanishing imaginary part of eq. (10.2.22) — for **all** parameter values, no case split — and
the nonnegativity that settles the degenerate `Ne = 2(N+1)` branch. -/
private theorem liebShenQiu_pairExpectation_eq_normSq (N : ℕ)
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    euclideanExpectation (totalPairCorrelationOperator N) φ
      = ((∑ j, Complex.normSq ((totalPairAnnihilationOperator N).mulVec φ.ofLp j) : ℝ) : ℂ) := by
  rw [totalPairCorrelationOperator, totalPairCreationOperator_eq_conjTranspose,
    euclideanExpectation_conjTranspose_mul_self]

/-! ## From the symmetric attractive model to the plain one -/

/-- **The symmetric attractive ground state is a plain attractive ground state at shifted hopping**
(Tasaki eq. (10.2.11), read in the attractive direction).  The two Hamiltonians differ by the
constant `(¼ Σ_x U_x)·1` (`symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul`), which
shifts the ground energy and leaves every eigenvector untouched
(`IsUniqueGroundStateOn.sub_smul_one`).  This is what lets Theorems 10.2/10.3 — stated for the
plain attractive Hamiltonian — be applied to Theorem 10.8's ground state `φ`. -/
private theorem liebShenQiu_attractiveGround_of_symmetric (N Ne : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (symmetricAttractiveHubbardHamiltonian N T U) E φ) :
    IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U)
      (E + (∑ x : Fin (N + 1), U x) / 4) φ := by
  have hshift := hGS.sub_smul_one (c := -((∑ x : Fin (N + 1), U x) / 4))
  have hcast : ((-((∑ x : Fin (N + 1), U x) / 4) : ℝ) : ℂ)
      = -((∑ x : Fin (N + 1), (U x : ℂ)) / 4) := by push_cast; ring
  have hH : symmetricAttractiveHubbardHamiltonian N T U
        - ((-((∑ x : Fin (N + 1), U x) / 4) : ℝ) : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2)))
      = attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U := by
    rw [symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul, hcast, neg_smul]
    abel
  have hE : E - -((∑ x : Fin (N + 1), U x) / 4) = E + (∑ x : Fin (N + 1), U x) / 4 := by ring
  rw [hH, hE] at hshift
  exact hshift

/-- **Theorem 10.8's ground state is a spin singlet** (Tasaki Theorem 10.2, p. 348).  Theorem 10.2
produces *some* unique ground state `φ₀` of the plain attractive model on the `Ne`-electron sector
together with `Ŝ² φ₀ = 0`; uniqueness (`IsUniqueGroundStateOn.exists_smul_eq`) makes the ground
state at hand a scalar multiple of `φ₀`, and `Ŝ²` is linear, so the singlet property transfers. -/
private theorem liebShenQiu_ground_singlet (N Ne : ℕ) (hNe_even : Even Ne) (hNe_pos : 0 < Ne)
    (hNe_le : Ne ≤ 2 * (N + 1)) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U) E φ) :
    Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0 := by
  obtain ⟨E₀, φ₀, hGS₀, hsinglet₀⟩ :=
    theorem_10_2_lieb_attractive_unique_singlet N Ne hNe_even hNe_pos hNe_le
      (T + Matrix.diagonal (fun x => U x / 2))
      (hoppingSymm_add_diagonal T hT_symm (fun x => U x / 2))
      (by rw [hoppingSupportGraph_add_diagonal]; exact hT_conn) U hU_pos
  obtain ⟨c, -, rfl⟩ := hGS₀.exists_smul_eq hGS
  rw [map_smul, hsinglet₀, smul_zero]

/-! ## The ladder expectation of the transported state -/

/-- **The ladder expectation of a joint `Ŝ²`/`Ŝ³` eigenvector**,
`⟨ψ| Ŝ⁺_tot Ŝ⁻_tot |ψ⟩ = S(S+1) − m(m−1)` for a unit vector with `Ŝ² ψ = S(S+1) ψ` and
`Ŝ³ ψ = m ψ`.  The operator identity `Ŝ⁺_tot Ŝ⁻_tot = Ŝ² − Ŝ³(Ŝ³ − 1)`
(`fermionTotalSpinPlus_mul_fermionTotalSpinMinus`) turns the observable into a scalar on `ψ`, and
normalisation (`star_dotProduct_self_of_norm_one`) strips the remaining pairing. -/
private theorem liebShenQiu_spinPlusMinus_expectation_eq (N : ℕ)
    {ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)} (hnorm : ‖ψ‖ = 1) {cas m : ℂ}
    (hcas : (fermionTotalSpinSquared N).mulVec ψ.ofLp = cas • ψ.ofLp)
    (hz : (fermionTotalSpinZ N).mulVec ψ.ofLp = m • ψ.ofLp) :
    euclideanExpectation (fermionTotalSpinPlus N * fermionTotalSpinMinus N) ψ
      = cas - m * (m - 1) := by
  have hzsub : (fermionTotalSpinZ N - 1).mulVec ψ.ofLp = (m - 1) • ψ.ofLp := by
    rw [Matrix.sub_mulVec, hz, Matrix.one_mulVec, sub_smul, one_smul]
  have hmul : (fermionTotalSpinSquared N
        - fermionTotalSpinZ N * (fermionTotalSpinZ N - 1)).mulVec ψ.ofLp
      = (cas - m * (m - 1)) • ψ.ofLp := by
    rw [Matrix.sub_mulVec, hcas, ← Matrix.mulVec_mulVec, hzsub, Matrix.mulVec_smul, hz,
      smul_smul, sub_smul]
    ring_nf
  unfold euclideanExpectation
  rw [fermionTotalSpinPlus_mul_fermionTotalSpinMinus, hmul, dotProduct_smul,
    star_dotProduct_self_of_norm_one ψ hnorm, smul_eq_mul, mul_one]

/-! ## The signed sum is dominated by the plain one -/

/-- **The transported ladder expectation is bounded by the pair correlation** (Tasaki
eqs. (10.2.13)/(10.2.25)): if `ψ = Û φ` is the Shiba image of a state whose on-site pair-transfer
correlations are all strictly positive reals, then
`Re ⟨ψ| Ŝ⁺_tot Ŝ⁻_tot |ψ⟩ ≤ Re ⟨φ| b̂† b̂ |φ⟩`.  Both sides are the same double sum over pairs of
sites (`shiba_spinPlusMinus_expectation_eq_signed_sum`, `totalPairCorrelationOperator_eq_sum`), the
left one carrying the sublattice signs `ε_x ε_y = ±1`, which can only decrease a positive term
(`gaugeSign_mul_re_mul_le_of_pos`). -/
private theorem liebShenQiu_signedSum_re_le_pairExpectation_re (N : ℕ) (A : Finset (Fin (N + 1)))
    {φ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hψ : ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp)
    (hpos : ∀ x y : Fin (N + 1),
      0 < (euclideanExpectation (hubbardPairCorrelationOp N x y) φ).re ∧
        (euclideanExpectation (hubbardPairCorrelationOp N x y) φ).im = 0) :
    (euclideanExpectation (fermionTotalSpinPlus N * fermionTotalSpinMinus N) ψ).re
      ≤ (euclideanExpectation (totalPairCorrelationOperator N) φ).re := by
  have hrhs : euclideanExpectation (totalPairCorrelationOperator N) φ
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          euclideanExpectation (hubbardPairCorrelationOp N x y) φ := by
    rw [totalPairCorrelationOperator_eq_sum, euclideanExpectation_sum]
    exact Finset.sum_congr rfl fun x _ => euclideanExpectation_sum _ _ _
  rw [shiba_spinPlusMinus_expectation_eq_signed_sum N A φ ψ hψ, hrhs, Complex.re_sum,
    Complex.re_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Complex.re_sum, Complex.re_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  obtain ⟨hp, him⟩ := hpos x y
  rw [Complex.mul_re, him, mul_zero, sub_zero]
  exact gaugeSign_mul_re_mul_le_of_pos A x y hp

/-! ## The degenerate branch: a completely filled `A` sublattice -/

/-- **At the top of the band the bound is vacuous**: if `Ne = 2(N+1)` then `Ne ≤ 2|A|` and
`|A| + |B| = N + 1` force `|A| = N + 1` and `|B| = 0`, so
`liebShenQiuPairLowerBound A Ne = (|A| − Ne/2)(Ne/2 − |B|) = 0`, and the bound is met by the
nonnegativity of `⟨φ| b̂ᴴ b̂ |φ⟩` alone — no ground-state hypothesis is used.  This is the branch
Theorem 10.3 (which needs `Ne < 2(N+1)`) does not reach. -/
private theorem liebShenQiu_bound_of_full (N Ne : ℕ) (A : Finset (Fin (N + 1)))
    (hUpper : Ne ≤ 2 * A.card) (hfull : Ne = 2 * (N + 1))
    (φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    liebShenQiuPairLowerBound A Ne
      ≤ (euclideanExpectation (totalPairCorrelationOperator N) φ).re := by
  have hcard := bipartitionComplement_card_add N A
  have hA : A.card = N + 1 := by omega
  have hB : (bipartitionComplement A).card = 0 := by omega
  have hzero : liebShenQiuPairLowerBound A Ne = 0 := by
    rw [liebShenQiuPairLowerBound, hA, hB, hfull]
    push_cast
    ring
  rw [hzero, liebShenQiu_pairExpectation_eq_normSq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-! ## Theorem 10.8 -/

/-- **Tasaki Theorem 10.8** (Lieb–Shen–Qiu superconductivity, 1st ed., Springer 2020, §10.2.3,
p. 359, eq. (10.2.22); **PROVED**, no longer an axiom).  For the attractive Hubbard model with a
bipartite (`Λ = A ⊔ B`) real symmetric connected hopping matrix `T` and the symmetric
site-dependent attraction `−Σ_x U_x (n̂_↑ − ½)(n̂_↓ − ½)` (`U_x > 0`, eq. (10.2.21)), and an even
electron number `Ne` with `2|B| ≤ Ne ≤ 2|A|`, the unique ground state `φ` (Theorem 10.2) satisfies
the pair off-diagonal-long-range-order bound

  `⟨φ| b̂† b̂ |φ⟩ ≥ (|A| − Ne/2)(Ne/2 − |B|)`,

with `b̂ = Σ_x ĉ_{x,↓} ĉ_{x,↑}`, the expectation being real.  The strictly positive regime exhibits
condensation of fermion pairs (superconductivity).

Proof: the imaginary part vanishes because `b̂† b̂ = b̂ᴴ b̂` is a square.  Below the top of the band
(`Ne < 2(N+1)`) the constant shift of eq. (10.2.11) turns `φ` into a plain attractive ground state,
whose singlet property (Theorem 10.2) drives the Shiba transport onto the spin-`z` sector
`Ŝ³ = (Ne − (N+1))/2` of the symmetric repulsive model at half filling, where Theorem 10.4 fixes
`Ŝ² = S₀(S₀+1)`; the ladder identity converts that into the value `S₀(S₀+1) − m(m−1)` of
`⟨ψ| Ŝ⁺_tot Ŝ⁻_tot |ψ⟩`, the Shiba identity (eq. (10.2.13)) identifies it with the
sublattice-signed pair sum on `φ`, whose signs can only decrease the strictly positive terms
supplied by Theorem 10.3, and `liebShenQiuPairLowerBound_le_casimir_gap` supplies the remaining
real arithmetic.  At the top of the band the bound degenerates to `0` and follows from positivity
alone. -/
theorem theorem_10_8_lieb_shen_qiu_superconductivity (N Ne : ℕ)
    (A : Finset (Fin (N + 1)))
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne)
    (hLower : 2 * (bipartitionComplement A).card ≤ Ne) (hUpper : Ne ≤ 2 * A.card)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x)
    (hT_bip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (symmetricAttractiveHubbardHamiltonian N T U) E φ) :
    liebShenQiuPairLowerBound A Ne ≤
        (euclideanExpectation (totalPairCorrelationOperator N) φ).re ∧
      (euclideanExpectation (totalPairCorrelationOperator N) φ).im = 0 := by
  refine ⟨?_, by rw [liebShenQiu_pairExpectation_eq_normSq, Complex.ofReal_im]⟩
  by_cases hlt : Ne < 2 * (N + 1)
  · have hGS' := liebShenQiu_attractiveGround_of_symmetric N Ne T U hGS
    have hT'_symm := hoppingSymm_add_diagonal T hT_symm (fun x => U x / 2)
    have hT'_conn :
        (hoppingSupportGraph (T + Matrix.diagonal (fun x => U x / 2))).Preconnected := by
      rw [hoppingSupportGraph_add_diagonal]; exact hT_conn
    have hsinglet := liebShenQiu_ground_singlet N Ne hNe_even hNe_pos hlt.le T hT_symm hT_conn U
      hU_pos hGS'
    have hpos := theorem_10_3_tian_pair_correlation_positive N Ne hNe_even hNe_pos hlt
      (T + Matrix.diagonal (fun x => U x / 2)) hT'_symm hT'_conn U hU_pos hGS'
    obtain ⟨ψ, hψ, hGSψ, hψN⟩ :=
      shibaTransport_uniqueGroundStateOn_spinZSector_symmetricAttractive N Ne hT_symm hT_bip U
        hGS hsinglet
    have hcas := liebShenQiu_casimir_eq N A T hT_symm hT_bip hT_conn U hU_pos (A.card - Ne / 2)
      (liebShenQiu_towerExponent_le_sublatticeImbalance N A Ne hLower hUpper)
      (liebShenQiu_towerExponent_weight_eq N A Ne hLower hUpper hNe_even) hGSψ hψN
    obtain ⟨hmem, hnorm, -, -, -⟩ := hGSψ
    rw [spinZSectorEuclidean, Module.End.mem_eigenspace_iff] at hmem
    have hz : (fermionTotalSpinZ N).mulVec ψ.ofLp
        = ((((Ne : ℂ) - ((N : ℂ) + 1)) / 2)) • ψ.ofLp := by
      simpa using congrArg WithLp.ofLp hmem
    have hle := liebShenQiu_signedSum_re_le_pairExpectation_re N A hψ hpos
    rw [liebShenQiu_spinPlusMinus_expectation_eq N hnorm hcas hz] at hle
    refine le_trans ?_ hle
    have hprod : (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) * ((((Ne : ℂ) - ((N : ℂ) + 1)) / 2) - 1)
        = ((((((Ne : ℝ) - ((N : ℝ) + 1)) / 2)
            * ((((Ne : ℝ) - ((N : ℝ) + 1)) / 2) - 1) : ℝ)) : ℂ) := by
      push_cast
      ring
    have harith : (liebRepulsiveSpinCasimir A
          - (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) * ((((Ne : ℂ) - ((N : ℂ) + 1)) / 2) - 1)).re
        = (liebRepulsiveSpinCasimir A).re
          - (((Ne : ℝ) - ((N : ℝ) + 1)) / 2) * ((((Ne : ℝ) - ((N : ℝ) + 1)) / 2) - 1) := by
      rw [hprod, liebRepulsiveSpinCasimir_eq_ofReal, ← Complex.ofReal_sub, Complex.ofReal_re,
        Complex.ofReal_re]
    rw [harith]
    exact liebShenQiuPairLowerBound_le_casimir_gap N A Ne hLower hUpper
  · have hcard := bipartitionComplement_card_add N A
    exact liebShenQiu_bound_of_full N Ne A hUpper (by omega) φ

end LatticeSystem.Fermion
