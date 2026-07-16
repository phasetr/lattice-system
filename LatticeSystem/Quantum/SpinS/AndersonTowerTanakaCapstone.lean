/-
Tasaki §4.2.2 Theorem 4.8 (the Tanaka symmetry-breaking state is low-lying), capstone — discharging
the `tanakaSSB_lowLying_energy_bound` axiom to a proved theorem.

The 1-axis numerator estimate (`tanaka_numerator_bound`, in `AndersonTowerTanakaNumeratorAssembly`,
eqs. (4.2.68)/(4.2.71)), the denominator lower bound (`orderSum_pow_two_denom_lower`, in
`AndersonTowerTanakaDenominator`, eq. (4.2.67)), the scale-invariance bridge
(`tanakaTowerTerm_expectationRatioRe_eq`, eq. (4.2.70)) and the parity cross-term vanishing
(`tanakaTowerTerm_cross_energy_eq_zero`, eq. (4.2.69)) combine, through the **central-binomial
(Pascal) cancellation** `C(2(k-1), k-1) / C(2k, k) = k / (2(2k-1)) ≤ 1/2`, into a Rayleigh energy
bound for each Tanaka tower term `(Ô_L^{(1)})^k Φ`, hence for the Tanaka symmetry-breaking state
`Ξ_{(1,0,0)}` (a normalized sum of two adjacent, orthogonal, parity-opposite tower terms).

Combined with the proved Theorem 4.6 (`tower_lowLying_energy_bound`, `IsAndersonTowerConstants`) via
constant monotonicity, this yields one pair `(C₁, C₂)` satisfying both predicates, discharging the
former axiom.  This file is downstream of `AndersonTower.lean` (which only states the predicates),
so the proved theorem can refer to the numerator/denominator machinery without an import cycle.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTheorem46
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaNumeratorAssembly
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaDenominator
import LatticeSystem.Quantum.SpinS.AndersonTowerParityCrossTerm
import LatticeSystem.Quantum.SpinS.AndersonTowerOrderSumExpansion

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-! ### Scalar-multiple algebra of sesquilinear forms -/

/-- **Scalar bilinearity of the `L²` form**: `⟨a•p, b•q⟩ = (conj a · b) ⟨p, q⟩`. -/
theorem star_smul_dotProduct_smul {ι : Type*} [Fintype ι] (a b : ℂ) (p q : ι → ℂ) :
    star (a • p) ⬝ᵥ (b • q) = (star a * b) * (star p ⬝ᵥ q) := by
  rw [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, mul_assoc]

/-- **Scalar bilinearity of the sandwiched form**: `⟨a•p, M (b•q)⟩ = (conj a · b) ⟨p, M q⟩`. -/
theorem star_smul_dotProduct_mulVec_smul {ι : Type*} [Fintype ι] (a b : ℂ)
    (M : Matrix ι ι ℂ) (p q : ι → ℂ) :
    star (a • p) ⬝ᵥ M.mulVec (b • q) = (star a * b) * (star p ⬝ᵥ M.mulVec q) := by
  rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    mul_assoc]

/-! ### The summed order density is Hermitian -/

/-- **The summed order density `Ã = ô⁺ + ô⁻` is Hermitian** (`(ô⁺)ᴴ = ô⁻`,
`staggeredOrderDensityOpS_conjTranspose`).  This makes every power `Ã^k` Hermitian, which is what
lets the variational gap and the denominator identity apply to the 1-axis Tanaka term. -/
theorem orderDensitySum_isHermitian (d L N : ℕ) [NeZero L] :
    (staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false).IsHermitian := by
  change Matrix.conjTranspose (staggeredOrderDensityOpS d L N true
      + staggeredOrderDensityOpS d L N false)
    = staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false
  rw [Matrix.conjTranspose_add, staggeredOrderDensityOpS_conjTranspose,
    staggeredOrderDensityOpS_conjTranspose, Bool.not_true, Bool.not_false]
  exact add_comm _ _

/-! ### The central-binomial (Pascal) cancellation -/

/-- **Central-binomial doubling** `2·C(2(k-1), k-1) ≤ C(2k, k)` (for `k ≥ 1`): the ratio
`C(2k, k) / C(2(k-1), k-1) = 2(2k-1)/k ≥ 2`.  This is the arithmetic heart of Tanaka's 1-axis
cancellation (eq. (4.2.71)): it turns the naive `4^{k-1}` word count into the resonant central
binomial, which then cancels against the denominator's `C(2k, k)`.  Proved from
`Nat.succ_mul_centralBinom_succ`, `(n+1)·C(2n+2, n+1) = 2(2n+1)·C(2n, n)`. -/
private theorem two_mul_choose_two_mul_sub_one_le (k : ℕ) (hk : 1 ≤ k) :
    2 * (2 * (k - 1)).choose (k - 1) ≤ (2 * k).choose k := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [← Nat.centralBinom_eq_two_mul_choose, ← Nat.centralBinom_eq_two_mul_choose]
  have hmul := Nat.succ_mul_centralBinom_succ n
  have hle : (n + 1) * (2 * Nat.centralBinom n) ≤ (n + 1) * Nat.centralBinom (n + 1) := by
    rw [hmul]; nlinarith [Nat.centralBinom_pos n]
  exact Nat.le_of_mul_le_mul_left hle (Nat.succ_pos n)

/-! ### Orthogonality and normalization of the Tanaka tower terms -/

/-- **The two adjacent Tanaka tower terms are orthogonal**:
`⟨(Ô_L^{(1)})^M Φ, (Ô_L^{(1)})^{M+1} Φ⟩ = 0`.  They are `Û`-parity eigenvectors with eigenvalues
`(-1)^M ≠ (-1)^{M+1}` (`diagonal_magParitySignS_mulVec_tanakaTowerTerm`), hence disjointly
supported (`dotProduct_eq_zero_of_diagonal_eigen`).  The norm-space companion of the energy
cross-term vanishing (eq. (4.2.69)). -/
theorem tanakaTowerTerm_dotProduct_cross_eq_zero {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
    {N : ℕ} (A : Λ → Bool) (M : ℕ) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (tanakaTowerTerm A N M Φ) ⬝ᵥ tanakaTowerTerm A N (M + 1) Φ = 0 := by
  refine dotProduct_eq_zero_of_diagonal_eigen (lam := (-1) ^ M) (mu := (-1) ^ (M + 1))
    (diagonal_magParitySignS_mulVec_tanakaTowerTerm A M hsing)
    (diagonal_magParitySignS_mulVec_tanakaTowerTerm A (M + 1) hsing) ?_
  intro h
  have hne : ((-1 : ℂ)) ^ M ≠ 0 := pow_ne_zero M (by norm_num)
  apply hne
  rw [pow_succ] at h
  exact (mul_eq_zero.mp (by linear_combination h : (2 : ℂ) * (-1) ^ M = 0)).resolve_left two_ne_zero

/-- **Unit normalization has unit norm**: `⟨w/‖w‖, w/‖w‖⟩ = 1` when `‖w‖² = vecNormSqRe w > 0`. -/
theorem unitNormalize_dotProduct_self {ι : Type*} [Fintype ι] (w : ι → ℂ)
    (hw : 0 < vecNormSqRe w) : star (unitNormalize w) ⬝ᵥ unitNormalize w = 1 := by
  have him : (star w ⬝ᵥ w).im = 0 := ((Complex.le_def.mp (dotProduct_star_self_nonneg w)).2).symm
  have hself : star w ⬝ᵥ w = ((vecNormSqRe w : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; rfl
    · rw [Complex.ofReal_im]; exact him
  have hrc : ((Real.sqrt (vecNormSqRe w) : ℝ) : ℂ) ≠ 0 :=
    by exact_mod_cast (Real.sqrt_pos.mpr hw).ne'
  have hV : ((vecNormSqRe w : ℝ) : ℂ) = ((Real.sqrt (vecNormSqRe w) : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hw.le]
  rw [unitNormalize, star_smul_dotProduct_smul, hself, hV, Complex.star_def, map_inv₀,
    Complex.conj_ofReal]
  field_simp

/-- **Rayleigh quotient is normalization-invariant**: `expectationRatioRe H (w/‖w‖) =
expectationRatioRe H w` when `vecNormSqRe w > 0` (they differ by the nonzero real scalar). -/
theorem expectationRatioRe_unitNormalize {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (w : ι → ℂ)
    (hw : 0 < vecNormSqRe w) : expectationRatioRe H (unitNormalize w) = expectationRatioRe H w := by
  have hrpos : 0 < Real.sqrt (vecNormSqRe w) := Real.sqrt_pos.mpr hw
  have hc : ((Real.sqrt (vecNormSqRe w) : ℝ) : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast hrpos.ne')
  simp only [expectationRatioRe, unitNormalize]
  exact rayleigh_smul_invariant H _ hc w

/-! ### Rayleigh quotient of an orthonormal pair -/

/-- **Rayleigh bound for a normalized orthonormal pair.**  If `u`, `v` are orthonormal
(`⟨u,u⟩ = ⟨v,v⟩ = 1`, `⟨u,v⟩ = 0`) and energy-decoupled (`⟨u, H v⟩ = 0`) with Hermitian `H`, then
the normalized sum `Ξ = (1/√2)(u + v)` has Rayleigh energy `(⟨u,Hu⟩.re + ⟨v,Hv⟩.re)/2`, bounded by
`(a + b)/2` whenever `⟨u,Hu⟩.re ≤ a` and `⟨v,Hv⟩.re ≤ b`.  This packages the interference
cancellation of the Tanaka state's two adjacent tower terms (eq. (4.2.69)). -/
theorem expectationRatioRe_orthonormal_pair_le {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
    (hHerm : H.IsHermitian) (u v : ι → ℂ) (huu : star u ⬝ᵥ u = 1) (hvv : star v ⬝ᵥ v = 1)
    (huv : star u ⬝ᵥ v = 0) (huHv : star u ⬝ᵥ H.mulVec v = 0) {a b : ℝ}
    (ha : (star u ⬝ᵥ H.mulVec u).re ≤ a) (hb : (star v ⬝ᵥ H.mulVec v).re ≤ b) :
    expectationRatioRe H ((Real.sqrt 2 : ℂ)⁻¹ • (u + v)) ≤ (a + b) / 2 := by
  have hvu : star v ⬝ᵥ u = 0 := by rw [Matrix.star_dotProduct, huv, star_zero]
  have hvHu : star v ⬝ᵥ H.mulVec u = 0 := by
    rw [star_dotProduct_mulVec_conjTranspose, hHerm.eq, Matrix.star_dotProduct, huHv, star_zero]
  have hc : (Real.sqrt 2 : ℂ)⁻¹ ≠ 0 :=
    inv_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')
  simp only [expectationRatioRe]
  rw [rayleigh_smul_invariant H _ hc (u + v)]
  have hden : star (u + v) ⬝ᵥ (u + v) = 2 := by
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add, huu, hvv, huv, hvu]; ring
  have hnum : star (u + v) ⬝ᵥ H.mulVec (u + v)
      = star u ⬝ᵥ H.mulVec u + star v ⬝ᵥ H.mulVec v := by
    rw [Matrix.mulVec_add, star_add, add_dotProduct, dotProduct_add, dotProduct_add, huHv, hvHu]
    ring
  rw [hden, hnum, Complex.add_re, show ((2 : ℂ)).re = 2 from by norm_num]
  linarith

/-! ### Single Tanaka tower-term Rayleigh bound (the binomial cancellation) -/

set_option maxHeartbeats 800000 in -- large explicit-constant Rayleigh inequality (d, N, V, q₀)
/-- **Single-term energy bound for `(Ô_L^{(1)})^k Φ`** (Tasaki §4.2.2, the crux).  Via the
scale-invariance bridge (eq. (4.2.70)) the Rayleigh quotient of the Tanaka tower term equals that of
`Ã^k Φ` (`Ã = ô⁺ + ô⁻`, Hermitian).  The variational gap
(`variational_gap_le_double_commutator`) bounds `⟨Ã^k Φ, Ĥ Ã^k Φ⟩ − E₀⟨Ã^k Φ, Ã^k Φ⟩` by the
double commutator numerator (`tanaka_numerator_bound`, `≤ k²·C(2(k-1),k-1)·1152 dN⁴/V · P_{k-1}`);
the denominator (`orderSum_pow_two_denom_lower`) is `≥ C(2k,k)·½ P_k`.  The central-binomial
cancellation `2 C(2(k-1),k-1) ≤ C(2k,k)` (`two_mul_choose_two_mul_sub_one_le`) and the long-range
moment step `2 q₀ P_{k-1} ≤ P_k` collapse the ratio to `≤ E_GS + 576 dN⁴/q₀ · k²/V`. -/
theorem tanaka_term_energy_bound (d L N k : ℕ) [NeZero L] (hN : 1 ≤ N) (hL : 2 ≤ L) (hk : 1 ≤ k)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) (E₀ : ℂ)
    (hev : (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Φ = E₀ • Φ)
    (hmin : ∀ (E : ℂ) (Ψ : (HypercubicTorus d L → Fin (N + 1)) → ℂ), Ψ ≠ 0 →
      (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re)
    (hΦ : Φ ≠ 0) (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2))
    (hcondNum : 3 * (N : ℝ) * ((2 * (k - 1) : ℕ) : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hbudNum : ((2 * (k - 1) : ℕ) : ℝ)
        * ((2 * 2 * (N : ℝ)) / (L : ℝ) ^ d / Real.sqrt (2 * q₀)) ≤ 1 / 2)
    (hcondDen : 3 * (N : ℝ) * (k : ℝ) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d) :
    expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
        (tanakaTowerTerm (torusParitySublattice d L) N k Φ)
      ≤ E₀.re + 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hVne : (L : ℝ) ^ d ≠ 0 := hVpos.ne'
  have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hm0 : 0 < phatMoment d L N Φ 0 := by rw [phatMoment_zero]; exact hm0c
  have hratio : ∀ n, 2 * q₀ * phatMoment d L N Φ n ≤ phatMoment d L N Φ (n + 1) :=
    phatMoment_succ_two_q0_le d L N Φ hsing3 hsing1 q₀ hm0c hVpos hlro
  have hHh : (heisenbergHamiltonianS (torusNNCoupling d L) N).IsHermitian :=
    heisenbergHamiltonianS_torus_isHermitian d L N
  have hÃ : (staggeredOrderDensityOpS d L N true
      + staggeredOrderDensityOpS d L N false).IsHermitian := orderDensitySum_isHermitian d L N
  rw [tanakaTowerTerm_expectationRatioRe_eq]
  set Ã := staggeredOrderDensityOpS d L N true + staggeredOrderDensityOpS d L N false with hÃdef
  -- denominator lower bound and positivity
  have hPk : 0 < phatMoment d L N Φ k := phatMoment_pos_of_lro d L N Φ hq₀ hm0 (hratio 0) k
  have hDlbRaw := orderSum_pow_two_denom_lower d L N hN Φ hsing3 hm0 (hratio 0) hcondDen (M := k)
  rw [← hÃdef] at hDlbRaw
  have hDval : (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re
      = (star Φ ⬝ᵥ (Ã ^ (2 * k)).mulVec Φ).re := by
    rw [hermitian_pow_dotProduct_split hÃ k k, two_mul]
  have hDlb : ((2 * k).choose k : ℝ) * ((1 / 2) * phatMoment d L N Φ k)
      ≤ (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re := hDlbRaw.trans_eq hDval.symm
  have hDpos : 0 < (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re := by
    refine lt_of_lt_of_le ?_ hDlb
    have hchoose : (0 : ℝ) < ((2 * k).choose k : ℝ) := by
      exact_mod_cast Nat.choose_pos (by omega : k ≤ 2 * k)
    exact mul_pos hchoose (mul_pos (by norm_num) hPk)
  -- variational gap ≤ numerator bound
  have hgap0 := variational_gap_le_double_commutator (Ã ^ k)
    (heisenbergHamiltonianS (torusNNCoupling d L) N) hHh Φ E₀ hev hmin hΦ
  rw [(hÃ.pow k).eq] at hgap0
  have hnum := tanaka_numerator_bound d L N hL hN Φ hsing3 hq₀ hm0 hratio k hk hcondNum hbudNum
  rw [← hÃdef] at hnum
  have hgap : (star ((Ã ^ k).mulVec Φ) ⬝ᵥ
        (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec ((Ã ^ k).mulVec Φ)).re
      - E₀.re * (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re
      ≤ (k : ℝ) ^ 2 * ((2 * (k - 1)).choose (k - 1) : ℝ)
          * (12 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * phatMoment d L N Φ (k - 1)) :=
    hgap0.trans ((le_abs_self _).trans hnum)
  -- the Pascal + moment key inequality
  have hpascal : (2 : ℝ) * ((2 * (k - 1)).choose (k - 1) : ℝ) ≤ ((2 * k).choose k : ℝ) := by
    exact_mod_cast two_mul_choose_two_mul_sub_one_le k hk
  have hmomk : 2 * q₀ * phatMoment d L N Φ (k - 1) ≤ phatMoment d L N Φ k := by
    have h := hratio (k - 1); rwa [show k - 1 + 1 = k from by omega] at h
  have hPk1 : 0 ≤ phatMoment d L N Φ (k - 1) := phatMoment_nonneg d L N Φ (k - 1)
  have hCmnn : (0 : ℝ) ≤ ((2 * k).choose k : ℝ) := by positivity
  have h2q1nn : (0 : ℝ) ≤ 2 * q₀ * phatMoment d L N Φ (k - 1) :=
    mul_nonneg (by positivity) hPk1
  have hprod := mul_le_mul hpascal hmomk h2q1nn hCmnn
  have hkey : 4 * q₀ * ((2 * (k - 1)).choose (k - 1) : ℝ) * phatMoment d L N Φ (k - 1)
      ≤ ((2 * k).choose k : ℝ) * phatMoment d L N Φ k := by
    calc 4 * q₀ * ((2 * (k - 1)).choose (k - 1) : ℝ) * phatMoment d L N Φ (k - 1)
        = 2 * ((2 * (k - 1)).choose (k - 1) : ℝ) * (2 * q₀ * phatMoment d L N Φ (k - 1)) := by ring
      _ ≤ ((2 * k).choose k : ℝ) * phatMoment d L N Φ k := hprod
  -- the numerator upper bound is ≤ (coefficient)·(denominator lower bound)
  have hcoeffnn : (0 : ℝ) ≤ 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d := by
    positivity
  have hND : (k : ℝ) ^ 2 * ((2 * (k - 1)).choose (k - 1) : ℝ)
        * (12 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * phatMoment d L N Φ (k - 1))
      ≤ 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d
        * (((2 * k).choose k : ℝ) * ((1 / 2) * phatMoment d L N Φ k)) := by
    rw [show (k : ℝ) ^ 2 * ((2 * (k - 1)).choose (k - 1) : ℝ)
          * (12 * (96 * (d : ℝ) * (N : ℝ) ^ 4 / (L : ℝ) ^ d) * phatMoment d L N Φ (k - 1))
        = (1152 * (d : ℝ) * (N : ℝ) ^ 4 * (k : ℝ) ^ 2 * ((2 * (k - 1)).choose (k - 1) : ℝ)
            * phatMoment d L N Φ (k - 1)) / (L : ℝ) ^ d from by field_simp; ring,
      show 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d
          * (((2 * k).choose k : ℝ) * ((1 / 2) * phatMoment d L N Φ k))
        = (288 * (d : ℝ) * (N : ℝ) ^ 4 * (k : ℝ) ^ 2 * ((2 * k).choose k : ℝ)
            * phatMoment d L N Φ k) / (q₀ * (L : ℝ) ^ d) from by field_simp; ring,
      div_le_div_iff₀ hVpos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkey
      (show (0 : ℝ) ≤ 288 * (d : ℝ) * (N : ℝ) ^ 4 * (k : ℝ) ^ 2 * (L : ℝ) ^ d from by positivity)]
  -- assemble the Rayleigh bound
  rw [expectationRatioRe, div_le_iff₀ hDpos,
    show (E₀.re + 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d)
        * (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re
      = E₀.re * (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re
        + 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d
          * (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re from by ring]
  have hcoeffD : 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d
        * (((2 * k).choose k : ℝ) * ((1 / 2) * phatMoment d L N Φ k))
      ≤ 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (k : ℝ) ^ 2 / (L : ℝ) ^ d
        * (star ((Ã ^ k).mulVec Φ) ⬝ᵥ (Ã ^ k).mulVec Φ).re :=
    mul_le_mul_of_nonneg_left hDlb hcoeffnn
  linarith [hgap, hND, hcoeffD]

/-! ### Rayleigh bound for the Tanaka symmetry-breaking state -/

/-- **Energy bound for the Tanaka state `Ξ_{(1,0,0)}` from the two tower-term bounds.**  The Tanaka
state is the normalized sum `(1/√2)(u_M + u_{M+1})` of the two unit-normalized adjacent tower terms,
which are orthonormal (`tanakaTowerTerm_dotProduct_cross_eq_zero`) and energy-decoupled
(`tanakaTowerTerm_cross_energy_eq_zero`, eq. (4.2.69)).  Its Rayleigh energy is the average of the
two per-term Rayleigh energies (`expectationRatioRe_orthonormal_pair_le`), so given per-term bounds
`a_M`, `a_{M+1}` the state energy is `≤ (a_M + a_{M+1})/2`. -/
theorem tanakaSSBState_expectationRatioRe_le (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hnormM : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
    (hnormM1 : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))
    {aM aM1 : ℝ}
    (heM : expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
        (tanakaTowerTerm (torusParitySublattice d L) N M Φ) ≤ aM)
    (heM1 : expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
        (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ) ≤ aM1) :
    expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
        (tanakaSSBState (torusParitySublattice d L) N M Φ) ≤ (aM + aM1) / 2 := by
  have hHerm : (heisenbergHamiltonianS (torusNNCoupling d L) N).IsHermitian :=
    heisenbergHamiltonianS_torus_isHermitian d L N
  have huu := unitNormalize_dotProduct_self
    (tanakaTowerTerm (torusParitySublattice d L) N M Φ) hnormM
  have hvv := unitNormalize_dotProduct_self
    (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ) hnormM1
  have huv : star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
      ⬝ᵥ unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ) = 0 := by
    rw [unitNormalize, unitNormalize, star_smul_dotProduct_smul,
      tanakaTowerTerm_dotProduct_cross_eq_zero _ M hsing3, mul_zero]
  have huHv : star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
      ⬝ᵥ (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
        (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) = 0 := by
    rw [unitNormalize, unitNormalize, star_smul_dotProduct_mulVec_smul,
      tanakaTowerTerm_cross_energy_eq_zero _ (torusNNCoupling d L) M hsing3, mul_zero]
  have ha : (star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
      ⬝ᵥ (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
        (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))).re ≤ aM := by
    have h1 : (star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
        ⬝ᵥ (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))).re
        = expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
          (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ)) := by
      rw [expectationRatioRe, huu, Complex.one_re, div_one]
    rw [h1, expectationRatioRe_unitNormalize _ _ hnormM]; exact heM
  have hb : (star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))
      ⬝ᵥ (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
        (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))).re ≤ aM1 := by
    have h1 : (star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))
        ⬝ᵥ (heisenbergHamiltonianS (torusNNCoupling d L) N).mulVec
          (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))).re
        = expectationRatioRe (heisenbergHamiltonianS (torusNNCoupling d L) N)
          (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) := by
      rw [expectationRatioRe, hvv, Complex.one_re, div_one]
    rw [h1, expectationRatioRe_unitNormalize _ _ hnormM1]; exact heM1
  rw [tanakaSSBState]
  exact expectationRatioRe_orthonormal_pair_le (heisenbergHamiltonianS (torusNNCoupling d L) N)
    hHerm _ _ huu hvv huv huHv ha hb

/-! ### Monotonicity of the constant predicates -/

/-- **Constant monotonicity of `IsAndersonTowerConstants`**: shrinking `C₁` (`0 < C₁' ≤ C₁`,
tightening the `|M|`-bound premise) and enlarging `C₂` (`C₂ ≤ C₂'`, weakening the energy bound)
preserve the predicate.  Used to merge the Theorem 4.6 and Theorem 4.8 constants into one pair. -/
theorem IsAndersonTowerConstants.mono {d N : ℕ} {q₀ C₁ C₂ C₁' C₂' : ℝ}
    (h : IsAndersonTowerConstants d N q₀ C₁ C₂) (hC1' : 0 < C₁') (hle1 : C₁' ≤ C₁)
    (hle2 : C₂ ≤ C₂') : IsAndersonTowerConstants d N q₀ C₁' C₂' := by
  obtain ⟨_, hC2, hbound⟩ := h
  refine ⟨hC1', lt_of_lt_of_le hC2 hle2, ?_⟩
  intro L _ hL hLeven Φ E₀ M hev hmin hΦ hs3 hs1 hlro hMbound htower
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hrpow : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have hMb : (M.natAbs : ℝ) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) :=
    hMbound.trans (mul_le_mul_of_nonneg_right hle1 hrpow)
  refine (hbound L hL hLeven Φ E₀ M hev hmin hΦ hs3 hs1 hlro hMb htower).trans ?_
  gcongr

/-- **Constant monotonicity of `IsTanakaSSBConstants`**: shrinking `C₁` and enlarging `C₂` preserve
the predicate (same mechanism as `IsAndersonTowerConstants.mono`, with the `M + 1 ≤ C₁ L^{d/2}`
premise and the `(M+1)²` energy bound). -/
theorem IsTanakaSSBConstants.mono {d N : ℕ} {q₀ C₁ C₂ C₁' C₂' : ℝ}
    (h : IsTanakaSSBConstants d N q₀ C₁ C₂) (hC1' : 0 < C₁') (hle1 : C₁' ≤ C₁)
    (hle2 : C₂ ≤ C₂') : IsTanakaSSBConstants d N q₀ C₁' C₂' := by
  obtain ⟨_, hC2, hbound⟩ := h
  refine ⟨hC1', lt_of_lt_of_le hC2 hle2, ?_⟩
  intro L _ hL hLeven Φ E₀ M hev hmin hΦ hs3 hs1 hlro hMpos hMbound hn1 hn2 hn3
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hrpow : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg L) _
  have hMb : ((M : ℝ) + 1) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) :=
    hMbound.trans (mul_le_mul_of_nonneg_right hle1 hrpow)
  refine (hbound L hL hLeven Φ E₀ M hev hmin hΦ hs3 hs1 hlro hMpos hMb hn1 hn2 hn3).trans ?_
  gcongr

/-! ### Existence of the Tanaka constants and the discharge -/

/-- **The Tanaka symmetry-breaking constants exist.**  For `N ≥ 1`, with `C₁ = min(√(q₀/6N),
√(2^d)√(2q₀)/16N)` (the Theorem 4.6 size constant, feeding the numerator/denominator conditions via
`tower_conditions_of_le`) and `C₂ = 576 dN⁴/q₀`, every Tanaka state on an even torus obeys the
Rayleigh bound (eq. (4.2.11)): apply `tanaka_term_energy_bound` to the two adjacent tower terms and
average (`tanakaSSBState_expectationRatioRe_le`).  For `N = 0` the order operator vanishes, so the
long-range-order premise is unsatisfiable and the statement is vacuous. -/
theorem exists_isTanakaSSBConstants (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsTanakaSSBConstants d N q₀ C₁ C₂ := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro L _ hL hLeven Φ E₀ M hev hmin hΦ hsing3 hsing1 hlro hMpos hMbound hn1 hn2 hn3
    exfalso
    have hO0 : staggeredOrderOpS (torusParitySublattice d L) 0 = 0 := by
      rw [staggeredOrderOpS]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      rw [spinSSiteOp3, show spinSOp3 0 = 0 from by
        ext i j; rw [spinSOp3, Matrix.diagonal_apply]
        rcases eq_or_ne i j with h | h
        · subst h; simp
        · simp [h], onSiteS_zero, smul_zero]
    have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
      (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
    rw [hO0] at hlro
    simp only [zero_mul, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re, zero_div] at hlro
    linarith [hlro]
  · have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    set C₁ := min (Real.sqrt (q₀ / (6 * N)))
      (Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / (16 * N)) with hC1
    have ha : 0 < Real.sqrt (q₀ / (6 * N)) := Real.sqrt_pos.mpr (by positivity)
    have hb : 0 < Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / (16 * N) := by positivity
    have hC1pos : 0 < C₁ := lt_min ha hb
    have hsq2q : 0 < Real.sqrt (2 * q₀) := Real.sqrt_pos.mpr (by positivity)
    have hC1cond : 6 * (N : ℝ) * C₁ ^ 2 ≤ q₀ := by
      have h1 : C₁ ≤ Real.sqrt (q₀ / (6 * N)) := min_le_left _ _
      have h2 : C₁ ^ 2 ≤ q₀ / (6 * N) := by
        calc C₁ ^ 2 ≤ (Real.sqrt (q₀ / (6 * N))) ^ 2 := by nlinarith [h1, hC1pos.le]
          _ = q₀ / (6 * N) := Real.sq_sqrt (by positivity)
      have h3 : 6 * (N : ℝ) * (q₀ / (6 * N)) = q₀ := by field_simp
      nlinarith [h2, hNR]
    have hC1bud : 16 * (N : ℝ) * C₁ ≤ Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) := by
      have h1 : C₁ ≤ Real.sqrt ((2 : ℝ) ^ d) * Real.sqrt (2 * q₀) / (16 * N) := min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h1
      linarith [h1]
    refine ⟨C₁, 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀, hC1pos, by positivity, ?_⟩
    intro L _ hL hLeven Φ E₀ M hev hmin hΦ hsing3 hsing1 hlro hMpos hMbound hn1 hn2 hn3
    have hbridge := LatticeSystem.Math.Ldhalf_bridge d L
    rw [hbridge] at hMbound
    have hmM : (M : ℝ) ≤ C₁ * Real.sqrt ((L : ℝ) ^ d) := le_trans (by linarith) hMbound
    have hmM1 : ((M + 1 : ℕ) : ℝ) ≤ C₁ * Real.sqrt ((L : ℝ) ^ d) := by push_cast; exact hMbound
    obtain ⟨hc2M, hb2M, _, _, hcDM⟩ :=
      tower_conditions_of_le d L N M hN hL hq₀ hC1cond hC1bud hmM
    obtain ⟨hc2M1, hb2M1, _, _, hcDM1⟩ :=
      tower_conditions_of_le d L N (M + 1) hN hL hq₀ hC1cond hC1bud hmM1
    rw [show 2 * M - 2 = 2 * (M - 1) from by omega] at hc2M hb2M
    rw [show 2 * (M + 1) - 2 = 2 * (M + 1 - 1) from by omega] at hc2M1 hb2M1
    have heM := tanaka_term_energy_bound d L N M hN hL hMpos Φ E₀ hev hmin hΦ hsing3 hsing1 hq₀
      hlro hc2M hb2M hcDM
    have heM1 := tanaka_term_energy_bound d L N (M + 1) hN hL (by omega) Φ E₀ hev hmin hΦ hsing3
      hsing1 hq₀ hlro hc2M1 hb2M1 hcDM1
    have hstate := tanakaSSBState_expectationRatioRe_le d L N M Φ hsing3 hn1 hn2 heM heM1
    refine hstate.trans ?_
    have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
    push_cast at heM1 ⊢
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have ht : 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * (M : ℝ) ^ 2 / (L : ℝ) ^ d
        ≤ 576 * (d : ℝ) * (N : ℝ) ^ 4 / q₀ * ((M : ℝ) + 1) ^ 2 / (L : ℝ) ^ d := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    linarith [ht]

/-- **Tasaki Theorem 4.8 (the Tanaka symmetry-breaking state is low-lying), PROVED.**  Discharges
the former `tanakaSSB_lowLying_energy_bound` axiom: there exists one pair of positive constants
`C₁`, `C₂` (depending only on `d`, `S = N/2`, `q₀`) satisfying **both** `IsAndersonTowerConstants`
(Theorem 4.6) and `IsTanakaSSBConstants` (Theorem 4.8, `exists_isTanakaSSBConstants`).  The two
existentials are merged with `C₁ = min` (tightening both `M`-bounds) and `C₂ = max` (weakening both
energy bounds), via `IsAndersonTowerConstants.mono` / `IsTanakaSSBConstants.mono`.  Conditional on
long-range order, hence vacuous in one dimension by Corollary 4.3. -/
theorem tanakaSSB_lowLying_energy_bound (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂ ∧ IsTanakaSSBConstants d N q₀ C₁ C₂ := by
  obtain ⟨C1A, C2A, hA⟩ := tower_lowLying_energy_bound d N hd q₀ hq₀
  obtain ⟨C1T, C2T, hT⟩ := exists_isTanakaSSBConstants d N hd q₀ hq₀
  refine ⟨min C1A C1T, max C2A C2T, ?_, ?_⟩
  · exact hA.mono (lt_min hA.1 hT.1) (min_le_left _ _) (le_max_left _ _)
  · exact hT.mono (lt_min hA.1 hT.1) (min_le_right _ _) (le_max_right _ _)

end LatticeSystem.Quantum
