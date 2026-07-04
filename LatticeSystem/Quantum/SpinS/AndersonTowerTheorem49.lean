/-
Tasaki §4.2.2 Theorem 4.9 (the Tanaka state exhibits full symmetry breaking), arc capstone PR5 —
discharges the `tanakaSSB_full_symmetry_breaking` axiom into a proved theorem.

Assembly of the four symmetry-breaking relations (eqs. (4.2.12)–(4.2.15)) for the explicit
slowly-diverging sequence `M(L) := ⌊L^{d/4}⌋`:

* **(a) axis-3 = axis-2 (eq. (4.2.56)).**  On a `Ŝ_tot^{(1)}`-singlet family the `1`-axis order
  operator `Ô^{(1)}` commutes with `Ŝ_tot^{(1)}`, so `Ŝ_tot^{(1)} Ξ = 0` for the Tanaka state,
  and the singlet component equality `staggeredOrder_sq_expectation_eq_23` applied at `Ξ` gives
  `second3 = second2` exactly (no asymptotics needed).
* **(b) tower-term positivity.**  The renormalized ratchet `orderOp1_evenMoment_ratio_ge_q0`
  propagates `‖Φ‖² > 0` to `‖(Ô^{(1)})^k Φ‖² > 0` for all `k`.
* **(c) clean fluctuation bound [F5].**  `deltaFluctBound ≤ N²/(2(j+2)) + K(j+2)²/V` with
  `K = 6N + 3N³/(4q₀)`, using the central-binomial ratio `≤ 4` (`pascal_real`) and the
  `p̂`-moment ratio `P_j/P_{j+1} ≤ 1/(2q₀)` (`phatMoment_succ_ratio`).
* **(d) `M(L)` and confluence.**  `M(L) = ⌊L^{d/4}⌋` diverges with `M+1 ≤ C₁ L^{d/2}` and
  `M²/V → 0`, so `second2 → 0`; the lower bounds (4.2.12)/(4.2.13) come from
  `sqrt_q0_le_tanakaOrderMean1`/`q0_le_tanakaOrderSecond1` with `m∗ = √q₀`, and (4.2.14) from
  `tanakaOrderMean2_eq_zero`/`tanakaOrderMean3_eq_zero`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eqs. (4.2.12)–(4.2.15)/(4.2.56)/footnote 21, pp. 98/104–108 (Tanaka [62]).
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaFluctuation
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaMoments

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### (a) axis-3 = axis-2: `[Ŝ_tot^{(1)}, Ô^{(1)}] = 0` and `Ŝ_tot^{(1)} Ξ = 0` -/

/-- **Self-commutator** `[Ŝ_tot^{(1)}, Ô_L^{(1)}] = 0`: the axis-1 order operator commutes with
the total axis-1 spin.  Both are sums of the single-axis on-site operators `onSiteS x (Ŝ^{(1)})`,
which pairwise commute (equal on the same site, disjoint support otherwise). -/
theorem totalSpinSOp1_commute_staggeredOrderOp1S (A : Λ → Bool) :
    Commute (totalSpinSOp1 Λ N) (staggeredOrderOp1S A N) := by
  rw [totalSpinSOp1, staggeredOrderOp1S]
  simp only [spinSSiteOp1]
  refine Commute.sum_left _ _ _ (fun x _ => Commute.sum_right _ _ _ (fun y _ => ?_))
  refine Commute.smul_right ?_ _
  rcases eq_or_ne x y with h | h
  · subst h; exact Commute.refl _
  · exact onSiteS_commute_of_ne h (spinSOp1 N) (spinSOp1 N)

/-- `Ŝ_tot^{(1)}` annihilates every Tanaka tower term `(Ô^{(1)})^k Φ` when it kills `Φ`. -/
theorem totalSpinSOp1_mulVec_tanakaTowerTerm (A : Λ → Bool) (k : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (totalSpinSOp1 Λ N).mulVec (tanakaTowerTerm A N k Φ) = 0 := by
  rw [tanakaTowerTerm, Matrix.mulVec_mulVec,
    ((totalSpinSOp1_commute_staggeredOrderOp1S A).pow_right k).eq, ← Matrix.mulVec_mulVec, hsing1,
    Matrix.mulVec_zero]

/-- `Ŝ_tot^{(1)}` annihilates the Tanaka symmetry-breaking state `Ξ` when it annihilates `Φ`. -/
theorem totalSpinSOp1_mulVec_tanakaSSBState (A : Λ → Bool) (M : ℕ)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hsing1 : (totalSpinSOp1 Λ N).mulVec Φ = 0) :
    (totalSpinSOp1 Λ N).mulVec (tanakaSSBState A N M Φ) = 0 := by
  rw [tanakaSSBState, Matrix.mulVec_smul, unitNormalize, unitNormalize, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, totalSpinSOp1_mulVec_tanakaTowerTerm A M hsing1,
    totalSpinSOp1_mulVec_tanakaTowerTerm A (M + 1) hsing1, smul_zero, smul_zero, add_zero,
    smul_zero]

/-- **Tasaki eq. (4.2.56): `second3 = second2`.**  For a `Ŝ_tot^{(1)}`-singlet ground state, the
axis-2 and axis-3 squared per-site moments of the Tanaka state coincide (the transverse directions
`2, 3` are equivalent), via `staggeredOrder_sq_expectation_eq_23` applied at `Ξ`. -/
theorem tanakaOrderSecond3_eq_tanakaOrderSecond2 (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0) :
    tanakaOrderSecond3 d L N M Φ = tanakaOrderSecond2 d L N M Φ := by
  have hΞ : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec
      (tanakaSSBState (torusParitySublattice d L) N M Φ) = 0 :=
    totalSpinSOp1_mulVec_tanakaSSBState (torusParitySublattice d L) M hsing1
  have heq := staggeredOrder_sq_expectation_eq_23 (torusParitySublattice d L)
    (tanakaSSBState (torusParitySublattice d L) N M Φ) hΞ
  rw [tanakaOrderSecond3, tanakaOrderSecond2, expectationRatioRe, expectationRatioRe, ← heq]

/-! ### (b) tower-term positivity -/

/-- **Tanaka tower-term positivity.**  Under long-range order, every tower term
`(Ô_L^{(1)})^k Φ` has strictly positive squared norm: the base `‖Φ‖² > 0` (as `Φ ≠ 0`) is
propagated by the renormalized ratchet `q₀ ‖·‖² V² ≤ ‖Ô^{(1)}·‖²`
(`orderOp1_evenMoment_ratio_ge_q0`). -/
theorem tanakaTowerTerm_vecNormSqRe_pos (d L N k : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hsing1 : (totalSpinSOp1 (HypercubicTorus d L) N).mulVec Φ = 0)
    (hΦ : Φ ≠ 0) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hlro : q₀ ≤ (star Φ ⬝ᵥ (staggeredOrderOpS (torusParitySublattice d L) N
        * staggeredOrderOpS (torusParitySublattice d L) N).mulVec Φ).re
        / ((star Φ ⬝ᵥ Φ).re * ((L : ℝ) ^ d) ^ 2)) :
    0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N k Φ) := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  induction k with
  | zero =>
      rw [tanakaTowerTerm, pow_zero, Matrix.one_mulVec, vecNormSqRe]
      exact (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
  | succ n ih =>
      have hr := orderOp1_evenMoment_ratio_ge_q0 d L N n Φ hsing3 hsing1 hΦ hlro
      exact lt_of_lt_of_le (mul_pos (mul_pos hq₀ ih) (pow_pos hVpos 2)) hr

/-! ### (c) axis-2 second moment is nonnegative -/

/-- The axis-2 squared per-site moment is nonnegative: `Ô^{(2)}` is Hermitian so
`⟨Ξ, (Ô^{(2)})² Ξ⟩ = ‖Ô^{(2)} Ξ‖² ≥ 0`, and the Rayleigh denominator is `> 0`. -/
theorem tanakaOrderSecond2_nonneg (d L N M : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hden : 0 < vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N M Φ)) :
    0 ≤ tanakaOrderSecond2 d L N M Φ := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hH := staggeredOrderOp2S_isHermitian (torusParitySublattice d L) N
  have hnum : 0 ≤ (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ (staggeredOrderOp2S (torusParitySublattice d L) N
        * staggeredOrderOp2S (torusParitySublattice d L) N).mulVec
        (tanakaSSBState (torusParitySublattice d L) N M Φ)).re := by
    rw [hermitian_dotProduct_shift hH]
    exact (Complex.le_def.mp (dotProduct_star_self_nonneg _)).1
  rw [tanakaOrderSecond2, expectationRatioRe]
  have hden' : 0 < (star (tanakaSSBState (torusParitySublattice d L) N M Φ)
      ⬝ᵥ tanakaSSBState (torusParitySublattice d L) N M Φ).re := hden
  positivity

/-! ### (c) [F5] clean fluctuation bound `deltaFluctBound ≤ N²/(2(j+2)) + K(j+2)²/V` -/

set_option maxHeartbeats 2000000 in
-- The clean bound clears several nested `field_simp` fractions over the large central-binomial and
-- `p̂`-moment atoms, exceeding the default heartbeat budget.
/-- **[F5] Clean fluctuation bound.**  The finite-`L` fluctuation bound `deltaFluctBound` is at most
`N²/(2(j+2)) + (6N + 3N³/(4q₀)) (j+2)²/V`: the `p̂`-moment `P_{j+1}` cancels in the lead term,
the central-binomial ratio bounded by `4`, and the moment ratio
`P_j/P_{j+1} ≤ 1/(2q₀)` (`phatMoment_succ_ratio`).  Reference: Tasaki §4.2.2, eqs.
(4.2.42)/(4.2.55), pp. 106–108. -/
theorem deltaFluctBound_le_clean (d L N j : ℕ) [NeZero L]
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1) :
    deltaFluctBound d L N j Φ
      ≤ (N : ℝ) ^ 2 / (2 * ((j : ℝ) + 1 + 1))
        + (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((j : ℝ) + 1 + 1) ^ 2
          / (L : ℝ) ^ d := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hCa : (0 : ℝ) < ((2 * (j + 1)).choose (j + 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hCb : (0 : ℝ) ≤ ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ) := by positivity
  have hP1 : 0 < phatMoment d L N Φ (j + 1) := by
    have hge := phatMoment_ge_of_lro d L N Φ hq₀.le hm0 hlro j
    exact lt_of_lt_of_le (mul_pos (pow_pos (by linarith) _) hm0) hge
  have hP0 : 0 ≤ phatMoment d L N Φ j := phatMoment_nonneg d L N Φ j
  have hratio : 2 * q₀ * phatMoment d L N Φ j ≤ phatMoment d L N Φ (j + 1) :=
    phatMoment_succ_ratio d L N Φ hm0 hlro j
  have hCble : ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ)
      ≤ 4 * ((2 * (j + 1)).choose (j + 1) : ℝ) := by
    have h := Nat.succ_mul_centralBinom_succ (j + 1)
    rw [Nat.centralBinom_eq_two_mul_choose, Nat.centralBinom_eq_two_mul_choose] at h
    have hr : ((j + 1 + 1 : ℕ) * (2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ)
        = (2 * (2 * (j + 1) + 1) * (2 * (j + 1)).choose (j + 1) : ℝ) := by exact_mod_cast h
    push_cast at hr
    nlinarith [hr, hCa, Nat.cast_nonneg (α := ℝ) j]
  have hP1ne : phatMoment d L N Φ (j + 1) ≠ 0 := ne_of_gt hP1
  have hVne : (L : ℝ) ^ d ≠ 0 := ne_of_gt hVpos
  have hCane : ((2 * (j + 1)).choose (j + 1) : ℝ) ≠ 0 := ne_of_gt hCa
  have hq₀ne : q₀ ≠ 0 := ne_of_gt hq₀
  rw [deltaFluctBound]
  set Ca : ℝ := ((2 * (j + 1)).choose (j + 1) : ℝ) with hCadef
  set Cb : ℝ := ((2 * (j + 1 + 1)).choose (j + 1 + 1) : ℝ) with hCbdef
  set P1 : ℝ := phatMoment d L N Φ (j + 1) with hP1def
  set P0 : ℝ := phatMoment d L N Φ j with hP0def
  set V : ℝ := (L : ℝ) ^ d with hVdef
  -- Term 2 bound: the `P₁` cancels, central-binomial ratio ≤ 4.
  have hT2 : (4 * Ca + Cb) * (((j : ℝ) + 1 + 1) ^ 2 * ((N : ℝ) / V * (3 / 2 * P1)))
        / (2 * Ca * P1) ≤ 6 * (N : ℝ) * ((j : ℝ) + 1 + 1) ^ 2 / V := by
    have key2 : (4 * Ca + Cb) * (((j : ℝ) + 1 + 1) ^ 2 * ((N : ℝ) / V * (3 / 2 * P1)))
          / (2 * Ca * P1)
        = (4 * Ca + Cb) / (2 * Ca) * (((j : ℝ) + 1 + 1) ^ 2 * (3 * (N : ℝ) / (2 * V))) := by
      field_simp
    rw [key2]
    have hb2 : (4 * Ca + Cb) / (2 * Ca) ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith [hCble]
    calc (4 * Ca + Cb) / (2 * Ca) * (((j : ℝ) + 1 + 1) ^ 2 * (3 * (N : ℝ) / (2 * V)))
        ≤ 4 * (((j : ℝ) + 1 + 1) ^ 2 * (3 * (N : ℝ) / (2 * V))) :=
          mul_le_mul_of_nonneg_right hb2 (by positivity)
      _ = 6 * (N : ℝ) * ((j : ℝ) + 1 + 1) ^ 2 / V := by field_simp; ring
  -- Term 3 bound: `P₀/P₁ ≤ 1/(2q₀)`, `(j+1)²/(j+2) ≤ (j+2)`.
  have hT3 : (N : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ((N : ℝ) / V * (3 / 2 * P0)))
        / (((j : ℝ) + 1 + 1) * P1)
      ≤ 3 * (N : ℝ) ^ 3 / (4 * q₀) * ((j : ℝ) + 1 + 1) ^ 2 / V := by
    have key3 : (N : ℝ) ^ 2 * (((j : ℝ) + 1) ^ 2 * ((N : ℝ) / V * (3 / 2 * P0)))
          / (((j : ℝ) + 1 + 1) * P1)
        = 3 * (N : ℝ) ^ 3 / 2 * (((j : ℝ) + 1) ^ 2 / ((j : ℝ) + 1 + 1) * (P0 / P1)) / V := by
      field_simp
    rw [key3]
    have hX : ((j : ℝ) + 1) ^ 2 / ((j : ℝ) + 1 + 1) ≤ (j : ℝ) + 1 + 1 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Nat.cast_nonneg (α := ℝ) j]
    have hY : P0 / P1 ≤ 1 / (2 * q₀) := by
      rw [div_le_div_iff₀ hP1 (by positivity)]; linarith [hratio]
    have hXY : ((j : ℝ) + 1) ^ 2 / ((j : ℝ) + 1 + 1) * (P0 / P1)
        ≤ ((j : ℝ) + 1 + 1) ^ 2 / (2 * q₀) := by
      calc ((j : ℝ) + 1) ^ 2 / ((j : ℝ) + 1 + 1) * (P0 / P1)
          ≤ ((j : ℝ) + 1 + 1) * (1 / (2 * q₀)) :=
            mul_le_mul hX hY (by positivity) (by positivity)
        _ ≤ ((j : ℝ) + 1 + 1) ^ 2 / (2 * q₀) := by
            rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [Nat.cast_nonneg (α := ℝ) j, hq₀]
    have hnum : 3 * (N : ℝ) ^ 3 / 2 * (((j : ℝ) + 1) ^ 2 / ((j : ℝ) + 1 + 1) * (P0 / P1))
        ≤ 3 * (N : ℝ) ^ 3 / (4 * q₀) * ((j : ℝ) + 1 + 1) ^ 2 := by
      refine (mul_le_mul_of_nonneg_left hXY (by positivity)).trans (le_of_eq ?_)
      field_simp
      ring
    rw [div_le_div_iff₀ hVpos hVpos]
    exact mul_le_mul_of_nonneg_right hnum hVpos.le
  have hKdecomp : (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((j : ℝ) + 1 + 1) ^ 2 / V
      = 6 * (N : ℝ) * ((j : ℝ) + 1 + 1) ^ 2 / V
        + 3 * (N : ℝ) ^ 3 / (4 * q₀) * ((j : ℝ) + 1 + 1) ^ 2 / V := by
    ring
  linarith [hT2, hT3, hKdecomp]

/-- **Clean axis-2 second-moment bound.**  For `M = i+1`, the Tanaka state's axis-2 squared per-site
moment is bounded by `N²/(2(i+2)) + K(i+3)²/V` (via `tanakaOrderSecond2_le` and two clean
`deltaFluctBound_le_clean` bounds, averaging and dominating). -/
theorem tanakaOrderSecond2_le_clean (d L N i : ℕ) [NeZero L] (hN : 1 ≤ N)
    (Φ : (HypercubicTorus d L → Fin (N + 1)) → ℂ)
    (hsing3 : (totalSpinSOp3 (HypercubicTorus d L) N).mulVec Φ = 0) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (hm0 : 0 < phatMoment d L N Φ 0)
    (hlro : 2 * q₀ * phatMoment d L N Φ 0 ≤ phatMoment d L N Φ 1)
    (hcond : 3 * (N : ℝ) * ((i : ℝ) + 1 + 1 + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d)
    (hBM : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (i + 1) Φ))
    (hBM1 : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (i + 1 + 1) Φ)) :
    tanakaOrderSecond2 d L N (i + 1) Φ
      ≤ (N : ℝ) ^ 2 / (2 * ((i : ℝ) + 1 + 1))
        + (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((i : ℝ) + 1 + 1 + 1) ^ 2
          / (L : ℝ) ^ d := by
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
  have hbase := tanakaOrderSecond2_le d L N i hN Φ hsing3 hq₀ hm0 hlro hcond hBM hBM1
  have hc1 := deltaFluctBound_le_clean d L N i Φ hq₀ hm0 hlro
  have hc2 := deltaFluctBound_le_clean d L N (i + 1) Φ hq₀ hm0 hlro
  have hcast : ((i + 1 : ℕ) : ℝ) + 1 + 1 = (i : ℝ) + 1 + 1 + 1 := by push_cast; ring
  rw [hcast] at hc2
  have hK : (0 : ℝ) ≤ 6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀) := by positivity
  have hA'leA : (N : ℝ) ^ 2 / (2 * ((i : ℝ) + 1 + 1 + 1))
      ≤ (N : ℝ) ^ 2 / (2 * ((i : ℝ) + 1 + 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Nat.cast_nonneg (α := ℝ) i, sq_nonneg (N : ℝ)]
  have hBleB' :
      (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((i : ℝ) + 1 + 1) ^ 2 / (L : ℝ) ^ d
        ≤ (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((i : ℝ) + 1 + 1 + 1) ^ 2
          / (L : ℝ) ^ d := by
    rw [div_le_div_iff₀ hVpos hVpos]
    have hsq : ((i : ℝ) + 1 + 1) ^ 2 ≤ ((i : ℝ) + 1 + 1 + 1) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) i]
    nlinarith [mul_le_mul_of_nonneg_left hsq hK, hVpos.le]
  linarith [hbase, hc1, hc2, hA'leA, hBleB']

/-! ### (d) `M(L) = ⌊L^{d/4}⌋` and the confluence / discharge -/

set_option maxHeartbeats 1600000 in
-- The confluence assembles many per-`L` facts (positivity, growth, size, lower bounds, decay) into
-- one bundle, and the `M(L)` real-analysis limits, exceeding the default heartbeat budget.
/-- **Tasaki Theorem 4.9 (the Tanaka state exhibits full symmetry breaking), PROVED.**  Discharges
the former `tanakaSSB_full_symmetry_breaking` axiom.  With the constants `C₁`, `C₂` of Theorems
4.6/4.8 and order parameter `mStar = √q₀`, the Tanaka state `Ξ_{(1,0,0)}` for the explicit slowly
diverging sequence `M(L) = ⌊L^{d/4}⌋` realizes full `SU(2)` symmetry breaking in the `(1,0,0)`
direction (eqs. (4.2.12)–(4.2.15)): the axis-1 staggered moment per site has `liminf ≥ √q₀` and its
square `liminf ≥ q₀` (footnote 21 `liminf` forms), while both transverse axes `2, 3` have vanishing
moment (exactly, eq. (4.2.14)) and vanishing squared fluctuation (eq. (4.2.15)).  Conditional on
long-range order (`q₀ > 0`), hence vacuous in `d = 1` by Corollary 4.3.  Reference: Hal Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §4.2.2,
eqs. (4.2.12)–(4.2.15), pp. 98/104–108 (Tanaka [62]). -/
theorem tanakaSSB_full_symmetry_breaking (d N : ℕ) (hd : 1 ≤ d) (q₀ : ℝ) (hq₀ : 0 < q₀) :
    ∃ C₁ C₂ mStar : ℝ, IsAndersonTowerConstants d N q₀ C₁ C₂ ∧
      IsTanakaSSBConstants d N q₀ C₁ C₂ ∧ IsTanakaFullSSBConstants d N q₀ C₁ mStar := by
  obtain ⟨C₁, C₂, hAnd, hSSB⟩ := tanakaSSB_lowLying_energy_bound d N hd q₀ hq₀
  refine ⟨C₁, C₂, Real.sqrt q₀, hAnd, hSSB, hAnd.1, Real.sqrt_pos.mpr hq₀, ?_⟩
  intro Φ E₀ hfam
  obtain ⟨L₁, hbody⟩ := hfam
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- `N = 0`: the order operator vanishes, so the long-range-order premise is unsatisfiable.
    exfalso
    subst hN0
    set L := 2 * (L₁ + 1) with hLdef
    haveI : NeZero L := ⟨by omega⟩
    obtain ⟨_, _, hΦ, _, _, _, hlroΦ⟩ := hbody L (by omega) (by omega) ⟨L₁ + 1, by omega⟩
    have hO0 : staggeredOrderOpS (torusParitySublattice d L) 0 = 0 := by
      rw [staggeredOrderOpS]
      refine Finset.sum_eq_zero (fun x _ => ?_)
      rw [spinSSiteOp3, show spinSOp3 0 = 0 from by
        ext a b; rw [spinSOp3, Matrix.diagonal_apply]
        rcases eq_or_ne a b with h | h
        · subst h; simp
        · simp [h], onSiteS_zero, smul_zero]
    have hm0c : 0 < (star (Φ L) ⬝ᵥ Φ L).re :=
      (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
    rw [hO0] at hlroΦ
    simp only [zero_mul, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re, zero_div] at hlroΦ
    linarith [hlroΦ]
  · -- `N ≥ 1`: the main construction.
    set M : ℕ → ℕ := fun L => ⌊(L : ℝ) ^ ((d : ℝ) / 4)⌋₊ with hMdef
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hd4 : (0 : ℝ) < (d : ℝ) / 4 := by positivity
    have hd2 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
    have htL : Tendsto (fun L : ℕ => (L : ℝ) ^ ((d : ℝ) / 4)) atTop atTop :=
      (tendsto_rpow_atTop hd4).comp tendsto_natCast_atTop_atTop
    have htM : Tendsto M atTop atTop := by
      rw [hMdef]; exact tendsto_nat_floor_atTop.comp htL
    have hMle : ∀ L : ℕ, (M L : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) / 4) := by
      intro L; simp only [hMdef]; exact Nat.floor_le (by positivity)
    have hev_t : ∀ b : ℝ, ∃ a : ℕ, ∀ L : ℕ, a ≤ L → b ≤ (L : ℝ) ^ ((d : ℝ) / 4) := fun b =>
      Filter.eventually_atTop.mp (htL.eventually_ge_atTop b)
    obtain ⟨a1, ha1⟩ := hev_t 1
    obtain ⟨a2, ha2⟩ := hev_t (2 / C₁)
    obtain ⟨a3, ha3⟩ := hev_t 2
    obtain ⟨a4, ha4⟩ := hev_t (Real.sqrt (6 * (N : ℝ) / q₀))
    set Lstar := max L₁ (max a1 (max a2 (max a3 a4))) with hLstardef
    -- The upper-bound sequence `U(L)` converges to `0`.
    have hU1 : Tendsto (fun L => (N : ℝ) ^ 2 / (2 * ((M L : ℝ) + 1))) atTop (𝓝 0) := by
      have hj : Tendsto (fun k : ℕ => (N : ℝ) ^ 2 / (2 * ((k : ℝ) + 1))) atTop (𝓝 0) := by
        apply tendsto_const_nhds.div_atTop
        apply Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
        exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      exact hj.comp htM
    have hU2 : Tendsto (fun L => (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀))
        * ((M L : ℝ) + 2) ^ 2 / (L : ℝ) ^ d) atTop (𝓝 0) := by
      have hg : Tendsto (fun L : ℕ => (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * 4
          * (L : ℝ) ^ (-((d : ℝ) / 2))) atTop (𝓝 0) := by
        have h0 : Tendsto (fun L : ℕ => (L : ℝ) ^ (-((d : ℝ) / 2))) atTop (𝓝 0) :=
          (tendsto_rpow_neg_atTop hd2).comp tendsto_natCast_atTop_atTop
        simpa using h0.const_mul ((6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * 4)
      refine squeeze_zero' ?_ ?_ hg
      · filter_upwards [eventually_ge_atTop 1] with L hL1
        have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
        positivity
      · filter_upwards [htL.eventually_ge_atTop 2, eventually_ge_atTop 1] with L hLt hL1
        have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL1
        have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
        have ht2 : ((L : ℝ) ^ ((d : ℝ) / 4)) ^ 2 = (L : ℝ) ^ ((d : ℝ) / 2) := by
          rw [sq, ← Real.rpow_add hLR]; congr 1; ring
        have hdiv : (L : ℝ) ^ ((d : ℝ) / 2) / (L : ℝ) ^ d = (L : ℝ) ^ (-((d : ℝ) / 2)) := by
          rw [← Real.rpow_natCast (L : ℝ) d, ← Real.rpow_sub hLR]; congr 1; ring
        have hM2 : (M L : ℝ) + 2 ≤ 2 * (L : ℝ) ^ ((d : ℝ) / 4) := by
          have := hMle L; linarith [hLt]
        have hsq : ((M L : ℝ) + 2) ^ 2 ≤ 4 * (L : ℝ) ^ ((d : ℝ) / 2) := by
          rw [← ht2]; nlinarith [hM2, hMle L]
        have hK : (0 : ℝ) ≤ 6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀) := by positivity
        calc (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((M L : ℝ) + 2) ^ 2 / (L : ℝ) ^ d
            ≤ (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * (4 * (L : ℝ) ^ ((d : ℝ) / 2))
              / (L : ℝ) ^ d := by
              rw [div_le_div_iff₀ hVpos hVpos]
              nlinarith [mul_le_mul_of_nonneg_left hsq hK, hVpos.le]
          _ = (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * 4 * (L : ℝ) ^ (-((d : ℝ) / 2)) := by
              rw [show (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * (4 * (L : ℝ) ^ ((d : ℝ) / 2))
                    / (L : ℝ) ^ d
                  = (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * 4
                    * ((L : ℝ) ^ ((d : ℝ) / 2) / (L : ℝ) ^ d) from by ring, hdiv]
    have hU : Tendsto (fun L => (N : ℝ) ^ 2 / (2 * ((M L : ℝ) + 1))
        + (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((M L : ℝ) + 2) ^ 2 / (L : ℝ) ^ d)
        atTop (𝓝 0) := by simpa using hU1.add hU2
    -- The per-`L` bundle: for `L ≥ Lstar` (with `2 ≤ L`, `Even L`), all six relations hold.
    have hallL : ∀ (L : ℕ) [NeZero L], Lstar ≤ L → 2 ≤ L → Even L →
        0 < M L
        ∧ ((M L : ℝ) + 1) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2)
        ∧ 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L) (Φ L))
        ∧ 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L + 1) (Φ L))
        ∧ 0 < vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L))
        ∧ Real.sqrt q₀ ≤ tanakaOrderMean1 d L N (M L) (Φ L)
        ∧ q₀ ≤ tanakaOrderSecond1 d L N (M L) (Φ L)
        ∧ tanakaOrderMean2 d L N (M L) (Φ L) = 0
        ∧ tanakaOrderMean3 d L N (M L) (Φ L) = 0
        ∧ tanakaOrderSecond2 d L N (M L) (Φ L)
            ≤ (N : ℝ) ^ 2 / (2 * ((M L : ℝ) + 1))
              + (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((M L : ℝ) + 2) ^ 2 / (L : ℝ) ^ d
        ∧ 0 ≤ tanakaOrderSecond2 d L N (M L) (Φ L)
        ∧ tanakaOrderSecond3 d L N (M L) (Φ L) = tanakaOrderSecond2 d L N (M L) (Φ L) := by
      intro L _ hLL hL2 hLeven
      obtain ⟨hev, hmin, hΦ, hs3, hs1, hΘ, hlroΦ⟩ :=
        hbody L (le_trans (le_max_left _ _) hLL) hL2 hLeven
      have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by positivity
      have hm0c : 0 < (star (Φ L) ⬝ᵥ Φ L).re :=
        (Complex.lt_def.mp (Matrix.dotProduct_star_self_pos_iff.mpr hΦ)).1
      have hm0 : 0 < phatMoment d L N (Φ L) 0 := by rw [phatMoment_zero]; exact hm0c
      have hlrophat : 2 * q₀ * phatMoment d L N (Φ L) 0 ≤ phatMoment d L N (Φ L) 1 :=
        phatMoment_succ_two_q0_le d L N (Φ L) hs3 hs1 q₀ hm0c hVpos hlroΦ 0
      have ht1 : (1 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) / 4) := ha1 L (by omega)
      have ht2eq : ((L : ℝ) ^ ((d : ℝ) / 4)) ^ 2 = (L : ℝ) ^ ((d : ℝ) / 2) := by
        rw [sq, ← Real.rpow_add hLR]; congr 1; ring
      have hs_eq : (L : ℝ) ^ d = ((L : ℝ) ^ ((d : ℝ) / 2)) ^ 2 := by
        rw [sq, ← Real.rpow_add hLR, ← Real.rpow_natCast (L : ℝ) d]; congr 1; ring
      have hgrow : ((M L : ℝ) + 1) ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 2) := by
        have htC : 2 / C₁ ≤ (L : ℝ) ^ ((d : ℝ) / 4) := ha2 L (by omega)
        have hC1t : 2 ≤ C₁ * (L : ℝ) ^ ((d : ℝ) / 4) := by
          rw [mul_comm]; exact (div_le_iff₀ hAnd.1).mp htC
        rw [← ht2eq]
        nlinarith [hMle L, ht1, mul_le_mul_of_nonneg_right hC1t
          (by linarith [ht1] : (0 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) / 4))]
      have hs_ge : 6 * (N : ℝ) / q₀ ≤ (L : ℝ) ^ ((d : ℝ) / 2) := by
        have ht : Real.sqrt (6 * (N : ℝ) / q₀) ≤ (L : ℝ) ^ ((d : ℝ) / 4) := ha4 L (by omega)
        rw [← ht2eq]
        calc 6 * (N : ℝ) / q₀ = (Real.sqrt (6 * (N : ℝ) / q₀)) ^ 2 :=
              (Real.sq_sqrt (by positivity)).symm
          _ ≤ ((L : ℝ) ^ ((d : ℝ) / 4)) ^ 2 := by
              nlinarith [ht, Real.sqrt_nonneg (6 * (N : ℝ) / q₀)]
      have h6N : 6 * (N : ℝ) ≤ q₀ * (L : ℝ) ^ ((d : ℝ) / 2) := by
        have h := hs_ge; rw [div_le_iff₀ hq₀] at h; linarith [h]
      have hsize : 3 * (N : ℝ) * ((M L : ℝ) + 2) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
        have ht3 : (2 : ℝ) ≤ (L : ℝ) ^ ((d : ℝ) / 4) := ha3 L (by omega)
        have hsq : ((M L : ℝ) + 2) ^ 2 ≤ 4 * (L : ℝ) ^ ((d : ℝ) / 2) := by
          rw [← ht2eq]; nlinarith [hMle L, ht3]
        rw [hs_eq]
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 3 * (N : ℝ)),
          mul_le_mul_of_nonneg_left h6N (by positivity : (0 : ℝ) ≤ 2 * (L : ℝ) ^ ((d : ℝ) / 2))]
      have hMpos : 0 < M L := by simp only [hMdef]; exact Nat.floor_pos.mpr ht1
      have hBM : 0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L) (Φ L)) :=
        tanakaTowerTerm_vecNormSqRe_pos d L N (M L) (Φ L) hs3 hs1 hΦ hq₀ hlroΦ
      have hBM1 :
          0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (M L + 1) (Φ L)) :=
        tanakaTowerTerm_vecNormSqRe_pos d L N (M L + 1) (Φ L) hs3 hs1 hΦ hq₀ hlroΦ
      have hstate : 0 < vecNormSqRe (tanakaSSBState (torusParitySublattice d L) N (M L) (Φ L)) := by
        rw [tanakaSSBState_vecNormSqRe_eq_one (torusParitySublattice d L) (M L) hs3 hBM hBM1]
        norm_num
      have hmean1 : Real.sqrt q₀ ≤ tanakaOrderMean1 d L N (M L) (Φ L) :=
        sqrt_q0_le_tanakaOrderMean1 d L N (M L) (Φ L) hs3 hs1 hΦ hlroΦ hBM hBM1
      have hsecond1 : q₀ ≤ tanakaOrderSecond1 d L N (M L) (Φ L) :=
        q0_le_tanakaOrderSecond1 d L N (M L) (Φ L) hs3 hs1 hΦ hlroΦ hBM hBM1
      have hmean2 : tanakaOrderMean2 d L N (M L) (Φ L) = 0 :=
        tanakaOrderMean2_eq_zero d L N (M L) (Φ L) hΘ
      have hmean3 : tanakaOrderMean3 d L N (M L) (Φ L) = 0 :=
        tanakaOrderMean3_eq_zero d L N (M L) (Φ L) hΘ
      have hsecond2nn : 0 ≤ tanakaOrderSecond2 d L N (M L) (Φ L) :=
        tanakaOrderSecond2_nonneg d L N (M L) (Φ L) hstate
      have hsecond3 :
          tanakaOrderSecond3 d L N (M L) (Φ L) = tanakaOrderSecond2 d L N (M L) (Φ L) :=
        tanakaOrderSecond3_eq_tanakaOrderSecond2 d L N (M L) (Φ L) hs1
      obtain ⟨i, hi⟩ : ∃ i, M L = i + 1 := ⟨M L - 1, (Nat.succ_pred_eq_of_pos hMpos).symm⟩
      have hcond_i : 3 * (N : ℝ) * ((i : ℝ) + 1 + 1 + 1) ^ 2 ≤ 2 * q₀ * (L : ℝ) ^ d := by
        have heq : ((i : ℝ) + 1 + 1 + 1) = (M L : ℝ) + 2 := by rw [hi]; push_cast; ring
        rw [heq]; exact hsize
      have hBMi :
          0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (i + 1) (Φ L)) := by
        rw [← hi]; exact hBM
      have hBM1i :
          0 < vecNormSqRe (tanakaTowerTerm (torusParitySublattice d L) N (i + 1 + 1) (Φ L)) := by
        rw [show i + 1 + 1 = M L + 1 from by rw [hi]]; exact hBM1
      have hcl :=
        tanakaOrderSecond2_le_clean d L N i hN (Φ L) hs3 hq₀ hm0 hlrophat hcond_i hBMi hBM1i
      have hMcast : (M L : ℝ) = (i : ℝ) + 1 := by rw [hi]; push_cast; ring
      have h10 : tanakaOrderSecond2 d L N (M L) (Φ L)
          ≤ (N : ℝ) ^ 2 / (2 * ((M L : ℝ) + 1))
            + (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((M L : ℝ) + 2) ^ 2 / (L : ℝ) ^ d := by
        rw [show tanakaOrderSecond2 d L N (M L) (Φ L) = tanakaOrderSecond2 d L N (i + 1) (Φ L)
              from by rw [hi]]
        refine hcl.trans (le_of_eq ?_)
        rw [hMcast]; ring
      exact ⟨hMpos, hgrow, hBM, hBM1, hstate, hmean1, hsecond1, hmean2, hmean3, h10, hsecond2nn,
        hsecond3⟩
    refine ⟨M, htM, ⟨Lstar, ?_⟩, ?_, ?_, ?_, ?_⟩
    · intro L _ hLL hL2 hLeven
      obtain ⟨hMpos, hgrow, hBM, hBM1, hstate, _, _, _, _, _, _, _⟩ := hallL L hLL hL2 hLeven
      exact ⟨hMpos, hgrow, hBM, hBM1, hstate⟩
    · -- (4.2.12): `liminf ≥ √q₀`
      intro ε hε
      refine ⟨Lstar, fun L _ hLL hL2 hLeven => ?_⟩
      obtain ⟨_, _, _, _, _, hmean1, _, _, _, _, _, _⟩ := hallL L hLL hL2 hLeven
      linarith [hmean1]
    · -- (4.2.13): `liminf ≥ q₀ = (√q₀)²`
      intro ε hε
      refine ⟨Lstar, fun L _ hLL hL2 hLeven => ?_⟩
      obtain ⟨_, _, _, _, _, _, hsecond1, _, _, _, _, _⟩ := hallL L hLL hL2 hLeven
      rw [Real.sq_sqrt hq₀.le]; linarith [hsecond1]
    · -- (4.2.14): the transverse moments vanish
      refine ⟨Lstar, fun L _ hLL hL2 hLeven => ?_⟩
      obtain ⟨_, _, _, _, _, _, _, hmean2, hmean3, _, _, _⟩ := hallL L hLL hL2 hLeven
      exact ⟨hmean2, hmean3⟩
    · -- (4.2.15): the transverse fluctuations vanish
      intro ε hε
      obtain ⟨La, hLa⟩ := Metric.tendsto_atTop.mp hU ε hε
      refine ⟨max Lstar La, fun L _ hLL hL2 hLeven => ?_⟩
      have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      obtain ⟨_, _, _, _, _, _, _, _, _, h10, hsecond2nn, hsecond3⟩ :=
        hallL L (le_trans (le_max_left _ _) hLL) hL2 hLeven
      have hUlt : (N : ℝ) ^ 2 / (2 * ((M L : ℝ) + 1))
          + (6 * (N : ℝ) + 3 * (N : ℝ) ^ 3 / (4 * q₀)) * ((M L : ℝ) + 2) ^ 2 / (L : ℝ) ^ d < ε := by
        have hd := hLa L (le_trans (le_max_right _ _) hLL)
        rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hd
        exact hd
      refine ⟨?_, ?_⟩
      · rw [abs_of_nonneg hsecond2nn]; linarith [h10, hUlt]
      · rw [hsecond3, abs_of_nonneg hsecond2nn]; linarith [h10, hUlt]

end LatticeSystem.Quantum
