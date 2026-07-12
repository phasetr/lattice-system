/-
Tasaki §4.2.2 Theorem 4.9 (the Tanaka state exhibits full symmetry breaking), arc PR3 — the axis-1
order-parameter lower bounds (4.2.12)/(4.2.13).

With `m∗ := √q₀` the Tanaka state `|Ξ_{(1,0,0)}⟩ = (1/√2)(u_M + u_{M+1})` (with
`u_k = (Ô_L^{(1)})^k Φ / ‖·‖`) has, at every admissible finite volume,
`⟨Ξ| Ô_L^{(1)}/L^d |Ξ⟩ ≥ √q₀`  (eq. (4.2.12)) and `⟨Ξ| (Ô_L^{(1)}/L^d)² |Ξ⟩ ≥ q₀`  (eq. (4.2.13)).
Both are the `liminf` lower bounds of Tasaki's footnote 21 (they hold for *every* `L`, so their
`liminf` is bounded below by the same value).

The mechanism, with `R_k := ⟨(ô^{(1)})^{2k+2}⟩ / ⟨(ô^{(1)})^{2k}⟩` (`ô^{(1)} = Ô_L^{(1)}/L^d`):
* the even bare moments `B_k := ‖(Ô_L^{(1)})^k Φ‖²` are log-convex (Cauchy–Schwarz,
  `B_{k+1}² ≤ B_k B_{k+2}`, eq. (4.2.35)), so `R_k` is non-decreasing in `k`;
* `R_0 = ⟨(ô^{(1)})²⟩ = ⟨p̂⟩/2 ≥ q₀` from the charge selection `⟨(Ô^{(1)})²⟩ = ⟨(Ô^{(2)})²⟩` and the
  proved long-range-order bridge `⟨p̂⟩ ≥ 2 q₀ ‖Φ‖²` (`phatMoment_succ_two_q0_le`);
* hence `R_M ≥ R_0 ≥ q₀`, and through the Ξ sandwich (`tanakaSSBState_dotProduct_mulVec_re_eq`) with
  the parity structure (odd 1-axis moments vanish on the diagonal, so
  `⟨Ξ| ô^{(1)} |Ξ⟩ = √R_M ≥ √q₀`; the squared operator conserves charge, so its cross term vanishes
  and `⟨Ξ| (ô^{(1)})² |Ξ⟩ = (R_M + R_{M+1})/2 ≥ q₀`).

No central-binomial cancellation is needed — only the ratio monotonicity — so this is lighter than
Theorem 4.8 (eqs. (4.2.34)–(4.2.44) collapse to a one-shot lower bound).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.12)/(4.2.13)/(4.2.35)/(4.2.45)–(4.2.47), footnote 21, pp. 98/104–106
(Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaMoments
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaCapstone
import LatticeSystem.Math.Analysis.RealLogConvexSequence

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Hermiticity of the 1-axis staggered order operator and the tower recursion -/

/-- **The `1`-axis staggered order operator is Hermitian**: `Ô_L^{(1)} = Σ_x ε_x Ŝ_x^{(1)}` is a
real (`±1`) linear combination of the Hermitian single-site operators `Ŝ_x^{(1)}` (the `α = 1`
companion of `staggeredOrderOpS_isHermitian`). -/
theorem staggeredOrderOp1S_isHermitian (A : Λ → Bool) (N : ℕ) :
    (staggeredOrderOp1S (Λ := Λ) A N).IsHermitian := by
  refine Matrix.isHermitian_sum Finset.univ (fun x _ => ?_)
  refine Matrix.IsHermitian.smul ?_ ?_
  · exact onSiteS_isHermitian x (spinSOp1_isHermitian N)
  · by_cases h : A x
    · simp [h, IsSelfAdjoint, star_one]
    · simp [h, IsSelfAdjoint]

/-- **Tanaka tower recursion**: `Ô_L^{(1)} (Ô_L^{(1)})^k Φ = (Ô_L^{(1)})^{k+1} Φ`, i.e. one more
application of the `1`-axis order operator advances the tower term. -/
private theorem staggeredOrderOp1S_mulVec_tanakaTowerTerm (A : Λ → Bool) (k : ℕ)
    (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (staggeredOrderOp1S A N).mulVec (tanakaTowerTerm A N k Φ) = tanakaTowerTerm A N (k + 1) Φ := by
  rw [tanakaTowerTerm, tanakaTowerTerm, pow_succ', Matrix.mulVec_mulVec]

/-! ### The renormalized moment ratio `R_k ≥ q₀` -/

/-- **The renormalized `1`-axis moment ratio is `≥ q₀`** (eqs. (4.2.36)/(4.2.37) for `ô^{(1)}`):
`q₀ · ‖(Ô_L^{(1)})^k Φ‖² · V² ≤ ‖(Ô_L^{(1)})^{k+1} Φ‖²` for every `k`, i.e. `R_k ≥ q₀`.  The base
case `R_0 ≥ q₀` is the charge-selection identity `⟨(Ô^{(1)})²⟩ = ⟨p̂⟩ V²/2` combined with the proved
long-range-order bridge `⟨p̂⟩ ≥ 2 q₀ ‖Φ‖²` (`phatMoment_succ_two_q0_le`); the monotonicity
`R_k ≥ R_0` comes from the Cauchy–Schwarz log-convexity of the even bare moments. -/
theorem orderOp1_evenMoment_ratio_ge_q0 (d L N k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hΦ : Φ ≠ 0) {q₀ : ℝ}
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) :
    q₀ * vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N k Φ) * ((L : ℝ) ^ d) ^ 2
      ≤ vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (k + 1) Φ) := by
  have hHh : (staggeredOrderOp1S (torusParitySublattice d L) N).IsHermitian :=
    staggeredOrderOp1S_isHermitian (torusParitySublattice d L) N
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set B : ℕ → ℝ := fun j => vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N j Φ)
    with hBdef
  have hBnn : ∀ j, 0 ≤ B j := fun j => (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
  -- Cauchy–Schwarz log-convexity of the even moments `B_{j+1}² ≤ B_j B_{j+2}`.
  have hone : (1 : Matrix (HypercubicTorus d L → Fin (N + 1))
      (HypercubicTorus d L → Fin (N + 1)) ℂ).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg Matrix.isHermitian_one
      (fun x => by rw [Matrix.one_mulVec]; exact dotProduct_star_self_nonneg x)
  have hmid : ∀ j, (star (tanakaTowerTerm (torusParitySublattice d L) N j Φ)
      ⬝ᵥ tanakaTowerTerm (torusParitySublattice d L) N (j + 2) Φ).re = B (j + 1) := by
    intro j
    rw [tanakaTowerTerm, tanakaTowerTerm, hermitian_pow_dotProduct_split hHh j (j + 2) Φ,
      show j + (j + 2) = (j + 1) + (j + 1) from by omega,
      ← hermitian_pow_dotProduct_split hHh (j + 1) (j + 1) Φ]
    simp only [hBdef, vecNormSqRe, tanakaTowerTerm]
  have hsq : ∀ j, B (j + 1) ^ 2 ≤ B j * B (j + 2) := by
    intro j
    have hcs := posSemidef_re_dotProduct_mulVec_sq_le hone
      (tanakaTowerTerm (torusParitySublattice d L) N j Φ)
      (tanakaTowerTerm (torusParitySublattice d L) N (j + 2) Φ)
    simp only [Matrix.one_mulVec] at hcs
    rw [hmid j] at hcs
    exact hcs
  have hcross := LatticeSystem.Math.real_logConvex_cross hBnn hsq
  -- `B 0 = ‖Φ‖² > 0`.
  have hB0 : B 0 = (star Φ ⬝ᵥ Φ).re := by
    simp only [hBdef, vecNormSqRe, tanakaTowerTerm, pow_zero, Matrix.one_mulVec]
  have hB0pos : 0 < B 0 := by
    rw [hB0]; exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  -- `R_0 ≥ q₀` in product form: `q₀ · B 0 · V² ≤ B 1`.
  have hB1' : B 1 = (star Φ ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N
      * staggeredOrderOp1S (torusParitySublattice d L) N).mulVec Φ).re := by
    simp only [hBdef, vecNormSqRe, tanakaTowerTerm]
    rw [hermitian_pow_dotProduct_split hHh 1 1 Φ,
      show (staggeredOrderOp1S (torusParitySublattice d L) N) ^ (1 + 1)
        = staggeredOrderOp1S (torusParitySublattice d L) N
          * staggeredOrderOp1S (torusParitySublattice d L) N from by rw [pow_succ, pow_one]]
  have hcast : (((L : ℂ) ^ d) ^ 2)⁻¹ = ((((L : ℝ) ^ d) ^ 2)⁻¹ : ℝ) := by push_cast; ring
  have hz12 := staggeredOrder_sq_expectation_eq_12 (torusParitySublattice d L) Φ hsing3
  have hV2ne : ((L : ℝ) ^ d) ^ 2 ≠ 0 := by positivity
  have hP1 : ((L : ℝ) ^ d) ^ 2 * phatMoment d L N Φ 1 = 2 * B 1 := by
    rw [phatMoment, pow_one, staggeredPhatS_dotProduct_cartesian, hcast, ← hz12, hB1',
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re]
    field_simp
    ring
  have hm0c : 0 < (star Φ ⬝ᵥ Φ).re :=
    (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  have hphat := phatMoment_succ_two_q0_le d L N Φ hsing3 hsing1 q₀ hm0c hVpos hlro 0
  have e1 : phatMoment d L N Φ (0 + 1) = phatMoment d L N Φ 1 := rfl
  rw [phatMoment_zero, e1] at hphat
  have hR0 : q₀ * B 0 * ((L : ℝ) ^ d) ^ 2 ≤ B 1 := by
    rw [hB0]
    nlinarith [mul_le_mul_of_nonneg_left hphat (le_of_lt (pow_pos hVpos 2)), hP1]
  -- Chain `R_0 ≤ R_k`: `q₀ · B k · V² ≤ B (k+1)`.
  have hkey : q₀ * B 0 * ((L : ℝ) ^ d) ^ 2 * B k ≤ B 0 * B (k + 1) :=
    calc q₀ * B 0 * ((L : ℝ) ^ d) ^ 2 * B k
        ≤ B 1 * B k := mul_le_mul_of_nonneg_right hR0 (hBnn k)
      _ ≤ B 0 * B (k + 1) := hcross k
  have hfin : B 0 * (q₀ * B k * ((L : ℝ) ^ d) ^ 2) ≤ B 0 * B (k + 1) := by
    rw [show B 0 * (q₀ * B k * ((L : ℝ) ^ d) ^ 2)
      = q₀ * B 0 * ((L : ℝ) ^ d) ^ 2 * B k from by ring]
    exact hkey
  exact le_of_mul_le_mul_left hfin hB0pos

/-! ### The Tanaka state is unit-normalized -/

/-- **The Tanaka state has unit norm** (`⟨Ξ, Ξ⟩ = 1`): the two adjacent tower terms are individually
unit-normalized and mutually orthogonal (opposite magnetization parity,
`tanakaTowerTerm_dotProduct_cross_eq_zero`), so `Ξ = (1/√2)(u_M + u_{M+1})` has squared norm
`½(1 + 1) + 0 = 1`. -/
theorem tanakaSSBState_vecNormSqRe_eq_one (A : Λ → Bool) (M : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing3 : (totalSpinSOp3 Λ N).mulVec Φ = 0)
    (hM : 0 < vecNormSqRe (tanakaTowerTerm A N M Φ))
    (hM1 : 0 < vecNormSqRe (tanakaTowerTerm A N (M + 1) Φ)) :
    vecNormSqRe (tanakaSSBState A N M Φ) = 1 := by
  have hsand := tanakaSSBState_dotProduct_mulVec_re_eq A M (1 : ManyBodyOpS Λ N)
    Matrix.isHermitian_one Φ
  simp only [Matrix.one_mulVec] at hsand
  have hdM : (star (unitNormalize (tanakaTowerTerm A N M Φ))
      ⬝ᵥ unitNormalize (tanakaTowerTerm A N M Φ)).re = 1 := by
    rw [unitNormalize_dotProduct_self _ hM, Complex.one_re]
  have hdM1 : (star (unitNormalize (tanakaTowerTerm A N (M + 1) Φ))
      ⬝ᵥ unitNormalize (tanakaTowerTerm A N (M + 1) Φ)).re = 1 := by
    rw [unitNormalize_dotProduct_self _ hM1, Complex.one_re]
  have hcr : (star (unitNormalize (tanakaTowerTerm A N M Φ))
      ⬝ᵥ unitNormalize (tanakaTowerTerm A N (M + 1) Φ)).re = 0 := by
    rw [unitNormalize, unitNormalize, star_smul_dotProduct_smul,
      tanakaTowerTerm_dotProduct_cross_eq_zero _ M hsing3, mul_zero, Complex.zero_re]
  rw [vecNormSqRe, hsand, hdM, hdM1, hcr]
  norm_num

/-! ### Diagonal and cross matrix elements of the unit-normalized tower terms -/

/-- **`⟨w, w⟩ = ‖w‖²` as a complex number** (the real squared norm cast to `ℂ`). -/
private theorem dotProduct_star_self_eq_ofReal {ι : Type*} [Fintype ι] (w : ι → ℂ) :
    star w ⬝ᵥ w = ((vecNormSqRe w : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; rfl
  · rw [Complex.ofReal_im]
    exact ((Complex.le_def.mp (dotProduct_star_self_nonneg w)).2).symm

/-- **The `1`-axis diagonal element vanishes**: `⟨û_j, Ô^{(1)} û_j⟩ = 0` for the unit-normalized
tower term `û_j` (a total-`Ŝ³` singlet `Φ`).  The odd bare moment
`⟨u_j, Ô^{(1)} u_j⟩ = ⟨u_j, u_{j+1}⟩` vanishes by the opposite-parity orthogonality
(`tanakaTowerTerm_dotProduct_cross_eq_zero`). -/
private theorem staggeredOrderOp1S_unitNormalize_diag_eq_zero (A : Λ → Bool) (j : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing3 : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (unitNormalize (tanakaTowerTerm A N j Φ))
      ⬝ᵥ (staggeredOrderOp1S A N).mulVec (unitNormalize (tanakaTowerTerm A N j Φ)) = 0 := by
  simp only [unitNormalize]
  rw [star_smul_dotProduct_mulVec_smul, staggeredOrderOp1S_mulVec_tanakaTowerTerm A j Φ,
    tanakaTowerTerm_dotProduct_cross_eq_zero A j hsing3, mul_zero]

/-- **The `1`-axis cross element**: `⟨û_M, Ô^{(1)} û_{M+1}⟩ = √B_{M+1} / √B_M` (a positive real),
where `B_k = ‖u_k‖²`.  The single application of `Ô^{(1)}` advances `u_{M+1}` to `u_{M+2}`, whose
overlap with `u_M` is the even moment `B_{M+1}`; the normalizations contribute `(√B_M √B_{M+1})⁻¹`,
and `B_{M+1} = (√B_{M+1})²` collapses this to `√B_{M+1}/√B_M`. -/
private theorem staggeredOrderOp1S_unitNormalize_cross_eq (A : Λ → Bool) (M : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hM : 0 < vecNormSqRe (tanakaTowerTerm A N M Φ))
    (hM1 : 0 < vecNormSqRe (tanakaTowerTerm A N (M + 1) Φ)) :
    star (unitNormalize (tanakaTowerTerm A N M Φ))
        ⬝ᵥ (staggeredOrderOp1S A N).mulVec (unitNormalize (tanakaTowerTerm A N (M + 1) Φ))
      = ((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N (M + 1) Φ))
          / Real.sqrt (vecNormSqRe (tanakaTowerTerm A N M Φ)) : ℝ) : ℂ) := by
  have hHh := staggeredOrderOp1S_isHermitian A N
  have hmid2 : star (tanakaTowerTerm A N M Φ) ⬝ᵥ tanakaTowerTerm A N (M + 2) Φ
      = ((vecNormSqRe (tanakaTowerTerm A N (M + 1) Φ) : ℝ) : ℂ) := by
    rw [← dotProduct_star_self_eq_ofReal (tanakaTowerTerm A N (M + 1) Φ)]
    simp only [tanakaTowerTerm]
    rw [hermitian_pow_dotProduct_split hHh M (M + 2) Φ,
      hermitian_pow_dotProduct_split hHh (M + 1) (M + 1) Φ,
      show M + (M + 2) = (M + 1) + (M + 1) from by omega]
  have h0 : ((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N M Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM).ne'
  have h1 : ((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N (M + 1) Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hM1).ne'
  simp only [unitNormalize]
  rw [star_smul_dotProduct_mulVec_smul, staggeredOrderOp1S_mulVec_tanakaTowerTerm A (M + 1) Φ,
    hmid2, show (((vecNormSqRe (tanakaTowerTerm A N (M + 1) Φ) : ℝ) : ℂ))
        = ((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N (M + 1) Φ)) : ℝ) : ℂ) ^ 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hM1.le],
    Complex.star_def, map_inv₀, Complex.conj_ofReal, Complex.ofReal_div]
  field_simp

/-- **The `(Ô^{(1)})²` diagonal element**: `⟨û_j, (Ô^{(1)})² û_j⟩ = B_{j+1}/B_j` for
`B_k = ‖u_k‖² > 0`.  Two applications of `Ô^{(1)}` advance `u_j` to `u_{j+2}`, whose overlap with
`u_j` is `B_{j+1}`; the normalization contributes `B_j⁻¹`. -/
private theorem staggeredOrderOp1Ssq_unitNormalize_diag (A : Λ → Bool) (j : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hj : 0 < vecNormSqRe (tanakaTowerTerm A N j Φ)) :
    star (unitNormalize (tanakaTowerTerm A N j Φ))
        ⬝ᵥ (staggeredOrderOp1S A N * staggeredOrderOp1S A N).mulVec
          (unitNormalize (tanakaTowerTerm A N j Φ))
      = ((vecNormSqRe (tanakaTowerTerm A N (j + 1) Φ)
          / vecNormSqRe (tanakaTowerTerm A N j Φ) : ℝ) : ℂ) := by
  have hHh := staggeredOrderOp1S_isHermitian A N
  have hmid : star (tanakaTowerTerm A N j Φ)
      ⬝ᵥ (staggeredOrderOp1S A N * staggeredOrderOp1S A N).mulVec (tanakaTowerTerm A N j Φ)
      = ((vecNormSqRe (tanakaTowerTerm A N (j + 1) Φ) : ℝ) : ℂ) := by
    rw [← Matrix.mulVec_mulVec, staggeredOrderOp1S_mulVec_tanakaTowerTerm A j Φ,
      staggeredOrderOp1S_mulVec_tanakaTowerTerm A (j + 1) Φ,
      ← dotProduct_star_self_eq_ofReal (tanakaTowerTerm A N (j + 1) Φ)]
    simp only [tanakaTowerTerm]
    rw [hermitian_pow_dotProduct_split hHh j (j + 2) Φ,
      hermitian_pow_dotProduct_split hHh (j + 1) (j + 1) Φ,
      show j + (j + 2) = (j + 1) + (j + 1) from by omega]
  have h0 : ((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N j Φ)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hj).ne'
  simp only [unitNormalize]
  rw [star_smul_dotProduct_mulVec_smul, hmid, Complex.star_def, map_inv₀, Complex.conj_ofReal,
    Complex.ofReal_div,
    show (((vecNormSqRe (tanakaTowerTerm A N j Φ) : ℝ) : ℂ))
        = ((Real.sqrt (vecNormSqRe (tanakaTowerTerm A N j Φ)) : ℝ) : ℂ) ^ 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hj.le]]
  field_simp

/-- **`(Ô^{(1)})²` commutes with the parity operator** `Û = diag(magParitySignS)`: `Ô^{(1)}`
anticommutes with `Û` (`diagonal_magParitySignS_mul_staggeredOrderOp1S`), so its square commutes. -/
private theorem staggeredOrderOp1S_sq_comm_diagonal_magParitySignS (A : Λ → Bool) :
    (staggeredOrderOp1S A N * staggeredOrderOp1S A N)
        * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
      = Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
        * (staggeredOrderOp1S A N * staggeredOrderOp1S A N) := by
  have hDH : Matrix.diagonal (magParitySignS (Λ := Λ) (N := N)) * staggeredOrderOp1S A N
      = -(staggeredOrderOp1S A N * Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))) :=
    diagonal_magParitySignS_mul_staggeredOrderOp1S A
  set H := staggeredOrderOp1S A N
  set D := Matrix.diagonal (magParitySignS (Λ := Λ) (N := N))
  have hHD : H * D = -(D * H) := by rw [hDH]; exact (neg_neg _).symm
  calc H * H * D = H * (H * D) := mul_assoc H H D
    _ = H * -(D * H) := by rw [hHD]
    _ = -(H * (D * H)) := by rw [mul_neg]
    _ = -(H * D * H) := by rw [mul_assoc]
    _ = -(-(D * H) * H) := by rw [hHD]
    _ = D * H * H := by rw [neg_mul]; exact neg_neg _
    _ = D * (H * H) := mul_assoc D H H

/-! ### (4.2.12): the axis-1 order-parameter lower bound `⟨Ξ| Ô^{(1)}/L^d |Ξ⟩ ≥ √q₀` -/

/-- **Tasaki eq. (4.2.12), lower bound (footnote 21 `liminf` form).**  With `m∗ = √q₀`, the Tanaka
state's axis-1 staggered moment per site satisfies `⟨Ξ| Ô_L^{(1)}/L^d |Ξ⟩ ≥ √q₀` at every admissible
finite volume.  The diagonal (odd-moment) contributions vanish and the surviving cross term equals
`√R_M` with `R_M = B_{M+1}/(B_M V²) ≥ q₀` (`orderOp1_evenMoment_ratio_ge_q0`), so the per-site
moment is `√R_M ≥ √q₀`. -/
theorem sqrt_q0_le_tanakaOrderMean1 (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hΦ : Φ ≠ 0) {q₀ : ℝ}
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2))
    (hBM : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
    (hBM1 : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) :
    Real.sqrt q₀ ≤ tanakaOrderMean1 d L N M Φ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hHh : (staggeredOrderOp1S (torusParitySublattice d L) N).IsHermitian :=
    staggeredOrderOp1S_isHermitian _ _
  have hden : vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N M Φ) = 1 :=
    tanakaSSBState_vecNormSqRe_eq_one _ M hsing3 hBM hBM1
  have hnum : (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N).mulVec
        (tanakaSSBState (torusParitySublattice d L) N M Φ)).re
      = Real.sqrt (vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))
        / Real.sqrt (vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ)) := by
    rw [tanakaSSBState_dotProduct_mulVec_re_eq (torusParitySublattice d L) M
        (staggeredOrderOp1S (torusParitySublattice d L) N) hHh Φ,
      staggeredOrderOp1S_unitNormalize_diag_eq_zero (torusParitySublattice d L) M hsing3,
      staggeredOrderOp1S_unitNormalize_diag_eq_zero (torusParitySublattice d L) (M + 1) hsing3,
      staggeredOrderOp1S_unitNormalize_cross_eq (torusParitySublattice d L) M hBM hBM1,
      Complex.zero_re, Complex.ofReal_re]
    ring
  have hmean1 : tanakaOrderMean1 d L N M Φ
      = Real.sqrt (vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))
        / (Real.sqrt (vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
          * (L : ℝ) ^ d) := by
    rw [tanakaOrderMean1, expectationRatioRe, hnum,
      show (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
        ⬝ᵥ tanakaSSBState (torusParitySublattice d L) N M Φ).re = 1 from hden, div_one]
    rw [div_div]
  have hmean1nn : 0 ≤ tanakaOrderMean1 d L N M Φ := by
    rw [hmean1]; positivity
  have hRk := orderOp1_evenMoment_ratio_ge_q0 d L N M Φ hsing3 hsing1 hΦ hlro
  have hmean1sq : q₀ ≤ (tanakaOrderMean1 d L N M Φ) ^ 2 := by
    rw [hmean1, div_pow, mul_pow, Real.sq_sqrt hBM1.le, Real.sq_sqrt hBM.le,
      le_div_iff₀ (by positivity)]
    nlinarith [hRk]
  calc Real.sqrt q₀ ≤ Real.sqrt ((tanakaOrderMean1 d L N M Φ) ^ 2) := Real.sqrt_le_sqrt hmean1sq
    _ = tanakaOrderMean1 d L N M Φ := Real.sqrt_sq hmean1nn

/-! ### (4.2.13): the axis-1 squared order-parameter lower bound `⟨Ξ| (Ô^{(1)}/L^d)² |Ξ⟩ ≥ q₀` -/

/-- **Tasaki eq. (4.2.13), lower bound (footnote 21 `liminf` form).**  With `m∗ = √q₀` (so
`m∗² = q₀`), the Tanaka state's axis-1 squared staggered moment per site satisfies
`⟨Ξ| (Ô_L^{(1)}/L^d)² |Ξ⟩ ≥ q₀`.  The squared order operator conserves the magnetization parity, so
the cross term vanishes (`tanakaTowerTerm_cross_charge_conserving_eq_zero`); the two diagonal terms
are `R_M` and `R_{M+1}`, both `≥ q₀` (`orderOp1_evenMoment_ratio_ge_q0`), so the average
`(R_M+R_{M+1})/2` is `≥ q₀`. -/
theorem q0_le_tanakaOrderSecond1 (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hΦ : Φ ≠ 0) {q₀ : ℝ}
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2))
    (hBM : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
    (hBM1 : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) :
    q₀ ≤ tanakaOrderSecond1 d L N M Φ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hHHh : (staggeredOrderOp1S (torusParitySublattice d L) N
      * staggeredOrderOp1S (torusParitySublattice d L) N).IsHermitian :=
    (staggeredOrderOp1S_isHermitian _ _).mul_of_commute (staggeredOrderOp1S_isHermitian _ _) rfl
  have hden : vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N M Φ) = 1 :=
    tanakaSSBState_vecNormSqRe_eq_one _ M hsing3 hBM hBM1
  have hcross0 : star (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N M Φ))
      ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N
        * staggeredOrderOp1S (torusParitySublattice d L) N).mulVec
        (unitNormalize (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) = 0 := by
    simp only [unitNormalize]
    rw [star_smul_dotProduct_mulVec_smul,
      tanakaTowerTerm_cross_charge_conserving_eq_zero (torusParitySublattice d L) _ M hsing3
        (staggeredOrderOp1S_sq_comm_diagonal_magParitySignS (torusParitySublattice d L)),
      mul_zero]
  have hnum : (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ (staggeredOrderOp1S (torusParitySublattice d L) N
        * staggeredOrderOp1S (torusParitySublattice d L) N).mulVec
        (tanakaSSBState (torusParitySublattice d L) N M Φ)).re
      = (1 / 2) * (vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ)
          + vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 2) Φ)
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)) := by
    rw [tanakaSSBState_dotProduct_mulVec_re_eq (torusParitySublattice d L) M
        (staggeredOrderOp1S (torusParitySublattice d L) N
          * staggeredOrderOp1S (torusParitySublattice d L) N) hHHh Φ,
      staggeredOrderOp1Ssq_unitNormalize_diag (torusParitySublattice d L) M hBM,
      staggeredOrderOp1Ssq_unitNormalize_diag (torusParitySublattice d L) (M + 1) hBM1,
      hcross0, Complex.ofReal_re, Complex.ofReal_re, Complex.zero_re, add_zero]
  have hsecond1 : tanakaOrderSecond1 d L N M Φ
      = (1 / 2) * (vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ)
          + vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 2) Φ)
            / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ))
        / ((L : ℝ) ^ d) ^ 2 := by
    rw [tanakaOrderSecond1, expectationRatioRe, hnum,
      show (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
        ⬝ᵥ tanakaSSBState (torusParitySublattice d L) N M Φ).re = 1 from hden, div_one]
  have hRkM := orderOp1_evenMoment_ratio_ge_q0 d L N M Φ hsing3 hsing1 hΦ hlro
  have hRkM1 := orderOp1_evenMoment_ratio_ge_q0 d L N (M + 1) Φ hsing3 hsing1 hΦ hlro
  have hr1 : q₀ * ((L : ℝ) ^ d) ^ 2
      ≤ vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ)
        / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N M Φ) := by
    rw [le_div_iff₀ hBM]; nlinarith [hRkM]
  have hr2 : q₀ * ((L : ℝ) ^ d) ^ 2
      ≤ vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 2) Φ)
        / vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M + 1) Φ) := by
    rw [le_div_iff₀ hBM1]; nlinarith [hRkM1]
  rw [hsecond1, le_div_iff₀ (by positivity)]
  linarith [hr1, hr2]

end LatticeSystem.Quantum
