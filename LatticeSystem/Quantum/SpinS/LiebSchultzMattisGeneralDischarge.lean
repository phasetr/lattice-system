import LatticeSystem.Quantum.SpinS.LiebSchultzMattisTaylorBound
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality

/-!
# Tasaki §6.2: discharge of the generalized Lieb–Schultz–Mattis variational bound (Lemma 6.4)

This file assembles the crux pieces of the Lemma 6.4 arc into the final `C/L` variational bound
(Tasaki eq. (6.2.24)), turning the former documented axiom
`tasaki_lemma_6_4_general_trial_energy_bound` into a proved theorem.

The assembly combines:
* the abstract symmetrised-sum reduction `lsm_energy_diff_symm_sum_general` and variational lower
  bound `groundEnergy_le_expectationRatioRe_general` (Rayleigh form of eq. (6.2.25));
* the global→local twist reductions `twistConj_eq_localGen` / `twistConj'_eq_localGen`
  (eq. (6.2.27), CRUX A);
* the second-order symmetric-difference twist bound `symmetricDifference_conj_norm_le`
  (eqs. (6.2.28)–(6.2.30), CRUX B), `‖Û†ĥ_xÛ + Ûĥ_xÛ† − 2ĥ_x‖ ≤ 8‖M̂_x‖²‖ĥ_x‖`;
* the centered-generator norm bound `localTwistGen_manyBodyOperatorNormS_le`, `‖M̂_x‖ ≤ B/L` with
  `B = π r(2r+1)N`.

Summing the per-site bound `8(B/L)²h₀` over the `L` sites gives `8B²h₀/L`, the operator norm of the
symmetrised Hamiltonian, which bounds the twisted-state Rayleigh quotient above the ground energy.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, Lemma 6.4, eqs. (6.2.23)–(6.2.30), pp. 162–165.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Rayleigh quotient bounded by the operator norm.**  For any many-body operator `S` and any
nonzero vector `Φ`, the real Rayleigh quotient `⟨Φ, S Φ⟩.re / ⟨Φ, Φ⟩.re` is bounded above by the
`L²` operator norm `‖S‖` (operator Cauchy–Schwarz `|Re⟨Φ, S Φ⟩| ≤ ‖S‖ ‖Φ‖²`).  Consumed by the
Lemma 6.4 discharge to bound the symmetrised twist expectation. -/
theorem expectationRatioRe_le_manyBodyOperatorNormS (S : ManyBodyOpS Λ N)
    {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦ : Φ ≠ 0) :
    expectationRatioRe S Φ ≤ manyBodyOperatorNormS S := by
  rw [expectationRatioRe, div_le_iff₀ (dotProduct_star_self_re_pos hΦ)]
  have hcs := abs_re_dotProduct_mulVec_le_norm_mul S Φ Φ
  have hnorm : ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
      * ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ = (star Φ ⬝ᵥ Φ).re := by
    rw [← sqrt_vecNormSqRe_eq_toLp_norm,
      Real.mul_self_sqrt (x := vecNormSqRe Φ) (dotProduct_star_self_re_pos hΦ).le]
    rfl
  calc (star Φ ⬝ᵥ S.mulVec Φ).re
      ≤ |(star Φ ⬝ᵥ S.mulVec Φ).re| := le_abs_self _
    _ ≤ manyBodyOperatorNormS S
          * ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖
          * ‖(WithLp.toLp 2 Φ : EuclideanSpace ℂ (Λ → Fin (N + 1)))‖ := hcs
    _ = manyBodyOperatorNormS S * (star Φ ⬝ᵥ Φ).re := by rw [mul_assoc, hnorm]

/-- **Tasaki Lemma 6.4 (generalized LSM variational bound).**  For the class of short-ranged
`U(1)`-invariant chain Hamiltonians `Ĥ = Σ_x ĥ_x` (`IsShortRangeU1Chain`, range `r`, bound `h₀`,
spin `S = N/2`), there is a constant `C > 0` — depending only on `N`, `r` and `h₀` — such that for
**any** ground state `Φ_GS` (a nonzero eigenvector at the minimal energy `E_GS`; uniqueness is *not*
assumed) the Lieb–Schultz–Mattis trial state has energy bounded by `C/L` above the ground state
(eq. (6.2.24)):
`⟨Φ_LSM, Ĥ Φ_LSM⟩ / ⟨Φ_LSM, Φ_LSM⟩ − E_GS ≤ C/L`, for any `L`.

The constant `C = 8 B² |h₀| + 1` with `B = π r(2r+1)N` is uniform over the volume `L`, the local
terms `ĥ`, and the ground state — it depends only on `S`, `r`, `h₀`.  Proof: `Δ₊ ≤ Δ₊ + Δ₋`
(the back-twist difference `Δ₋ ≥ 0` by the variational principle), and the `±θ`-symmetrised sum
equals the Rayleigh quotient of `Û†ĤÛ + ÛĤÛ† − 2Ĥ = Σ_x (Û†ĥ_xÛ + Ûĥ_xÛ† − 2ĥ_x)`; each summand
reduces
(CRUX A) to a local-generator conjugation and is bounded (CRUX B) by `8‖M̂_x‖²‖ĥ_x‖ ≤ 8(B/L)²h₀`,
summing to `8B²h₀/L ≤ C/L`. -/
theorem tasaki_lemma_6_4_general_trial_energy_bound (N r : ℕ) (h₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {L : ℕ} (h : Fin L → ManyBodyOpS (Fin L) N)
      (Φ_GS : (Fin L → Fin (N + 1)) → ℂ) (E_GS : ℝ), 0 < L →
      IsShortRangeU1Chain L N r h₀ h →
      (∑ x : Fin L, h x).mulVec Φ_GS = (E_GS : ℂ) • Φ_GS → Φ_GS ≠ 0 →
      IsGroundEnergy (∑ x : Fin L, h x) E_GS →
      expectationRatioRe (∑ x : Fin L, h x) (lsmTrialState L N Φ_GS) - E_GS ≤ C / (L : ℝ) := by
  set B : ℝ := Real.pi * (r : ℝ) * (2 * (r : ℝ) + 1) * (N : ℝ) with hB
  refine ⟨8 * B ^ 2 * |h₀| + 1, by positivity, ?_⟩
  intro L h Φ_GS E_GS hL chain heig hne hmin
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hL0 : (L : ℝ) ≠ 0 := ne_of_gt hLpos
  set H : ManyBodyOpS (Fin L) N := ∑ x : Fin L, h x with hH
  have hHherm : H.IsHermitian :=
    Matrix.isHermitian_sum Finset.univ (fun x _ => chain.hermitian x)
  -- Δ₋ ≥ 0: the back-twisted state is nonzero (unitarity) and its Rayleigh quotient ≥ E_GS.
  have hΦ' : (lsmTwistOperator L N).conjTranspose.mulVec Φ_GS ≠ 0 := by
    intro hcon
    apply hne
    have hu := lsmTwistOperator_unitary' L N
    calc Φ_GS = (1 : ManyBodyOpS (Fin L) N).mulVec Φ_GS := (Matrix.one_mulVec _).symm
      _ = (lsmTwistOperator L N * (lsmTwistOperator L N).conjTranspose).mulVec Φ_GS := by rw [hu]
      _ = (lsmTwistOperator L N).mulVec
            ((lsmTwistOperator L N).conjTranspose.mulVec Φ_GS) := by rw [Matrix.mulVec_mulVec]
      _ = (lsmTwistOperator L N).mulVec 0 := by rw [hcon]
      _ = 0 := Matrix.mulVec_zero _
  have hΔm : 0 ≤
      expectationRatioRe H ((lsmTwistOperator L N).conjTranspose.mulVec Φ_GS) - E_GS := by
    have := groundEnergy_le_expectationRatioRe_general L N H hHherm E_GS hmin hΦ'
    linarith
  -- The ±θ-symmetrised energy difference as a Rayleigh quotient (eq. (6.2.25)).
  have hsum := lsm_energy_diff_symm_sum_general L N H Φ_GS E_GS hne heig
  set Ssym : ManyBodyOpS (Fin L) N :=
    (lsmTwistOperator L N).conjTranspose * H * lsmTwistOperator L N
      + lsmTwistOperator L N * H * (lsmTwistOperator L N).conjTranspose - 2 • H with hSsymdef
  -- The symmetrised Hamiltonian is the site-sum of the symmetrised local terms.
  have hSsum : Ssym = ∑ x : Fin L,
      ((lsmTwistOperator L N).conjTranspose * h x * lsmTwistOperator L N
        + lsmTwistOperator L N * h x * (lsmTwistOperator L N).conjTranspose - 2 • h x) := by
    rw [hSsymdef, hH, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
    simp only [Finset.mul_sum, Finset.sum_mul]
  -- Per-site second-order bound: `‖Û†ĥ_xÛ + Ûĥ_xÛ† − 2ĥ_x‖ ≤ 8(B/L)²h₀`.
  have hterm : ∀ x ∈ (Finset.univ : Finset (Fin L)),
      manyBodyOperatorNormS
          ((lsmTwistOperator L N).conjTranspose * h x * lsmTwistOperator L N
            + lsmTwistOperator L N * h x * (lsmTwistOperator L N).conjTranspose - 2 • h x)
        ≤ 8 * (B / (L : ℝ)) ^ 2 * h₀ := by
    intro x _
    rw [twistConj_eq_localGen chain x, twistConj'_eq_localGen chain x]
    refine le_trans (symmetricDifference_conj_norm_le (localTwistGen L N r x) (h x)
      (localTwistGen_isHermitian L N r x)) ?_
    have hMnn := manyBodyOperatorNormS_nonneg (localTwistGen L N r x)
    have hM' : manyBodyOperatorNormS (localTwistGen L N r x) ≤ B / (L : ℝ) := by
      rw [hB]; exact localTwistGen_manyBodyOperatorNormS_le L N r x hL
    have hMsq : manyBodyOperatorNormS (localTwistGen L N r x) ^ 2 ≤ (B / (L : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hMnn hM' 2
    have hh := chain.norm_le x
    calc 8 * manyBodyOperatorNormS (localTwistGen L N r x) ^ 2 * manyBodyOperatorNormS (h x)
        ≤ 8 * (B / (L : ℝ)) ^ 2 * manyBodyOperatorNormS (h x) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hMsq (by norm_num)) (manyBodyOperatorNormS_nonneg _)
      _ ≤ 8 * (B / (L : ℝ)) ^ 2 * h₀ := mul_le_mul_of_nonneg_left hh (by positivity)
  -- Sum the per-site bounds over the `L` sites: `‖Ssym‖ ≤ 8B²h₀/L`.
  have hnorm_le : manyBodyOperatorNormS Ssym ≤ 8 * B ^ 2 * h₀ / (L : ℝ) := by
    rw [hSsum]
    refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum hterm) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  -- Assemble: `Δ₊ ≤ Δ₊ + Δ₋ = ⟨Ssym⟩ ≤ ‖Ssym‖ ≤ 8B²h₀/L ≤ C/L`.
  have hq : expectationRatioRe Ssym Φ_GS ≤ manyBodyOperatorNormS Ssym :=
    expectationRatioRe_le_manyBodyOperatorNormS Ssym hne
  have hsum2 : (expectationRatioRe H (lsmTrialState L N Φ_GS) - E_GS)
      + (expectationRatioRe H ((lsmTwistOperator L N).conjTranspose.mulVec Φ_GS) - E_GS)
      = expectationRatioRe Ssym Φ_GS := hsum
  have hnum : 8 * B ^ 2 * h₀ ≤ 8 * B ^ 2 * |h₀| + 1 := by
    have : 8 * B ^ 2 * h₀ ≤ 8 * B ^ 2 * |h₀| :=
      mul_le_mul_of_nonneg_left (le_abs_self h₀) (by positivity)
    linarith
  have hCL : 8 * B ^ 2 * h₀ / (L : ℝ) ≤ (8 * B ^ 2 * |h₀| + 1) / (L : ℝ) :=
    (div_le_div_iff_of_pos_right hLpos).mpr hnum
  linarith [hΔm, hq, hnorm_le, hsum2, hCL]

end LatticeSystem.Quantum
