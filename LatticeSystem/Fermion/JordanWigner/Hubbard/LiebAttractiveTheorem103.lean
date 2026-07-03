import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePairCorrelationTrace
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveTheorem102
import LatticeSystem.Math.PosSemidef.TraceProductPos

/-!
# Tian's pair-correlation positivity for the attractive Hubbard model (Tasaki §10.2, Theorem 10.3)

This file **proves** Tasaki Theorem 10.3 (Tian's pair-correlation positivity): under the hypotheses
of Theorem 10.2 (even electron number `Ne`, connected real symmetric hopping `T`, site-dependent
attraction `U_x > 0`), the unique ground state `|ΦGS⟩` of the attractive Hubbard model has strictly
positive on-site pair-transfer correlation for all sites `x, y`:
`⟨ΦGS| ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑} |ΦGS⟩ > 0`.

The declaration `theorem_10_3_tian_pair_correlation_positive` was previously recorded as a faithful
documented `axiom` (in `LiebAttractive.lean`).  It is now a fully proved theorem, discharged
axiom-free (modulo `propext`/`Classical.choice`/`Quot.sound`).

## The assembly (Tasaki eq. (10.2.50)/(10.2.51), p. 372)

Write `P = ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑}` for the pair-transfer operator and
`S = hubbardBlockKineticUpFixedMatrix (single x y 1)` for the single-hop transfer matrix.

* `euclideanExpectation_pairCorrelation_eq_trace` gives `⟨φ| P |φ⟩ = Tr(Wᴴ · S · W · Sᵀ)` with
  `W = blockWCoeff φ`.
* The unique ground `φ` is collinear (`IsUniqueGroundStateOn` uniqueness at the ground energy
  `E = E_bal = E_full`) with the balanced positive-definite ground state `φ_bal`
  (`exists_posDefCompress_ground_in_balanced_sector`), so `W = c⁻¹ • W_bal` with
  `W_bal = J · R · Jᴴ` and `R = Jᴴ · W_bal · J` positive definite
  (`blockWCoeff_eq_embed_compress_of_balanced`).
* Hence `⟨φ| P |φ⟩ = |c⁻¹|² · Tr(R · (S_cᴴ · R · S_c))` with `S_c = Jᴴ · S · J` the sector
  compression of `S`; `S_c ≠ 0` (`hubbardCountSectorEmbedding_pairFixed_compress_ne_zero`), so
  `S_cᴴ · R · S_c` is a nonzero positive-semidefinite matrix, and `trace_mul_posSemidef_pos` gives
  `0 < Tr(R · (S_cᴴ · R · S_c))`.  As `|c⁻¹|² > 0`, the expectation is strictly positive.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2, Theorem 10.3 (Tian), pp. 349, 372; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201;
G.-S. Tian, *J. Phys. A* **27** (1994).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

/-- **Tasaki Theorem 10.3** (Tian's pair-correlation positivity, 1st ed., Springer 2020, §10.2,
p. 349, eq. (10.2.4); **PROVED**, no longer an axiom).  Under the hypotheses of Theorem 10.2, the
unique ground state `|ΦGS⟩` of the attractive Hubbard model has strictly positive on-site
pair-transfer correlation for all sites `x, y`:
`⟨ΦGS| ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑} |ΦGS⟩ > 0`. -/
theorem theorem_10_3_tian_pair_correlation_positive (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x)
    {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N T U) E φ) :
    ∀ x y : Fin (N + 1),
      0 < (euclideanExpectation (hubbardPairCorrelationOp N x y) φ).re ∧
        (euclideanExpectation (hubbardPairCorrelationOp N x y) φ).im = 0 := by
  classical
  obtain ⟨k, hk⟩ := id hNe_even
  have hNe : Ne = 2 * k := by omega
  have hk1 : 1 ≤ k := by omega
  have hkN : k ≤ N := by omega
  have hk_le : k ≤ N + 1 := by omega
  haveI := nonempty_hubbardSpinCountSector_of_le (N := N) hk_le
  haveI := nonempty_hubbardBalancedConfig_of_le (N := N) hk_le
  haveI : Nonempty (hubbardSectorConfig N Ne) := by
    rw [hNe]; exact nonempty_hubbardSectorConfig_of_le (N := N) hk_le
  obtain ⟨hφmemK, hnorm, hφeig, hground, huniq⟩ := hGS
  have hφne : φ ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; exact one_ne_zero hnorm.symm
  -- Bridges between plain `mulVec` and `toEuclideanLin` eigenvector relations (as in Theorem 10.2).
  have bridgeBack : ∀ (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ) (e : ℂ)
      (v : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      Matrix.toEuclideanLin M v = e • v → M.mulVec v.ofLp = e • v.ofLp := by
    intro M e v hv; simpa using congrArg WithLp.ofLp hv
  have toEuc : ∀ (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ) (e : ℂ)
      (v : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)),
      M.mulVec v.ofLp = e • v.ofLp → Matrix.toEuclideanLin M v = e • v := by
    intro M e v hv
    apply WithLp.ofLp_injective (p := 2) (V := (Fin (2 * N + 2) → Fin 2) → ℂ)
    simpa using hv
  -- The balanced positive-definite ground state and its embedding data.
  obtain ⟨φbal, hφbal0, hφbalUp, hφbalDn, hRposdef, hφbalEig⟩ :=
    exists_posDefCompress_ground_in_balanced_sector k T U hT_symm hU_pos hT_conn
  set Ebal : ℝ := hermitianMinEigenvalue (configSectorCompress_isHermitian
    (hubbardBalancedSectorPred N k)
    (attractiveHubbardHamiltonian_isHermitian T U hT_symm)) with hEbaldef
  set J := hubbardCountSectorEmbedding N k with hJdef
  set R := Jᴴ * blockWCoeff N φbal * J with hRdef
  -- Euclidean lift of the balanced ground; its number and energy eigenvalues.
  set ψbal : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2) := WithLp.toLp 2 φbal with hψbaldef
  have hψofLp : ψbal.ofLp = φbal := rfl
  have hψbal0 : ψbal ≠ 0 := by rw [hψbaldef, ne_eq, WithLp.toLp_eq_zero]; exact hφbal0
  have hφbalN : (fermionTotalNumber (2 * N + 1)).mulVec φbal = (Ne : ℂ) • φbal := by
    rw [fermionTotalNumber_eq_up_add_down, Matrix.add_mulVec, hφbalUp, hφbalDn, ← add_smul,
      show (k : ℂ) + (k : ℂ) = (Ne : ℂ) by rw [hNe]; push_cast; ring]
  have hψbalMem : ψbal ∈ electronNumberSectorEuclidean N Ne := by
    rw [electronNumberSectorEuclidean, Module.End.mem_eigenspace_iff]
    exact toEuc _ _ _ (by rw [hψofLp]; exact hφbalN)
  have hψbalH : Matrix.toEuclideanLin (attractiveHubbardHamiltonian N T U) ψbal
      = (Ebal : ℂ) • ψbal :=
    toEuc _ _ _ (by rw [hψofLp]; exact hφbalEig)
  -- The ground energy `E` equals the balanced minimum `Ebal`.
  have hφofLp0 : φ.ofLp ≠ 0 := by
    simp only [ne_eq, WithLp.ofLp_eq_zero]; exact hφne
  have hφN : (fermionTotalNumber (2 * N + 1)).mulVec φ.ofLp = (Ne : ℂ) • φ.ofLp :=
    bridgeBack _ _ _ ((Module.End.mem_eigenspace_iff).mp hφmemK)
  have hφH : (attractiveHubbardHamiltonian N T U).mulVec φ.ofLp = (E : ℂ) • φ.ofLp :=
    bridgeBack _ _ _ hφeig
  have hE_le : E ≤ Ebal := hground.2 Ebal ⟨ψbal, hψbalMem, hψbal0, hψbalH⟩
  have hEbal_le : Ebal ≤ E := by
    rw [hEbaldef, attractiveHubbard_balanced_energy_eq_number_sector k Ne hNe hNe_even T U hT_symm]
    exact configSector_minEnergy_le_of_eigenvector (hubbardNumberSectorPred N Ne)
      (attractiveHubbardHamiltonian_isHermitian T U hT_symm)
      (hubbardNumberSector_supported_of_mem Ne ((mem_hubbardSectorWSubmodule_iff Ne).mpr hφN))
      hφofLp0 hφH
  have hEeq : E = Ebal := le_antisymm hE_le hEbal_le
  -- Collinearity: `φbal = c • φ.ofLp` for some `c ≠ 0`.
  obtain ⟨c, hc⟩ := huniq ψbal hψbalMem (by rw [hEeq]; exact hψbalH)
  have hcne : c ≠ 0 := by
    intro h; rw [h, zero_smul] at hc; exact hψbal0 hc
  have hφbal_eq : φbal = c • φ.ofLp := by
    have := congrArg WithLp.ofLp hc; simpa [hψofLp] using this
  -- `W = c⁻¹ • W_bal` and `W_bal = J · R · Jᴴ` with `R` positive definite.
  set W := blockWCoeff N φ.ofLp with hWdef
  have hWbal : blockWCoeff N φbal = c • W := by rw [hφbal_eq, blockWCoeff_smul]
  have hWembed : blockWCoeff N φbal = J * R * Jᴴ := by
    rw [hRdef, hJdef]; exact blockWCoeff_eq_embed_compress_of_balanced k φbal hφbalUp hφbalDn
  have hRherm : Rᴴ = R := hRposdef.isHermitian
  intro x y
  set S := hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1) with hSdef
  set Sc := Jᴴ * S * J with hScdef
  -- `S` is entrywise real (`Sᴴ = Sᵀ`), so `Jᴴ · Sᵀ · J = S_cᴴ`.
  have hSreal : ∀ i j, star ((Matrix.single x y (1 : ℂ)) i j) = (Matrix.single x y 1) i j := by
    intro i j; rw [Matrix.single_apply]; split <;> simp
  have hStrans : Sᵀ = Sᴴ := by
    rw [hSdef, ← hubbardBlockKineticUpFixedMatrix_conjTranspose_eq_transpose N hSreal]
  have hScH : Jᴴ * Sᵀ * J = Scᴴ := by
    rw [hStrans, hScdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  -- The positive-semidefinite nonzero second factor `B = S_cᴴ · R · S_c`.
  have hScne : Sc ≠ 0 := by
    rw [hScdef, hSdef, hJdef]
    exact hubbardCountSectorEmbedding_pairFixed_compress_ne_zero k hk1 hkN x y
  have hBpsd : (Scᴴ * R * Sc).PosSemidef := hRposdef.posSemidef.conjTranspose_mul_mul_same Sc
  have hBne : Scᴴ * R * Sc ≠ 0 := Matrix.PosDef.conjTranspose_mul_mul_ne_zero hRposdef hScne
  have hBtrace : 0 < (R * (Scᴴ * R * Sc)).trace :=
    Matrix.PosDef.trace_mul_posSemidef_pos hRposdef hBpsd hBne
  -- The Hermitian embedded balanced coefficient and the trace reduction.
  have hWbalH : (J * R * Jᴴ)ᴴ = J * R * Jᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hRherm,
      Matrix.mul_assoc]
  have hWSW : (J * R * Jᴴ) * S * (J * R * Jᴴ) = J * (R * Sc * R) * Jᴴ := by
    rw [hScdef]; simp only [Matrix.mul_assoc]
  have step : (R * Sc * R * Scᴴ).trace = (R * (Scᴴ * R * Sc)).trace := by
    rw [show R * Sc * R * Scᴴ = (R * Sc) * (R * Scᴴ) from by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm (R * Sc) (R * Scᴴ),
      show (R * Scᴴ) * (R * Sc) = R * (Scᴴ * R * Sc) from by simp only [Matrix.mul_assoc]]
  have htr : ((blockWCoeff N φbal)ᴴ * (S * blockWCoeff N φbal * Sᵀ)).trace
      = (R * (Scᴴ * R * Sc)).trace := by
    rw [hWembed, hWbalH,
      show (J * R * Jᴴ) * (S * (J * R * Jᴴ) * Sᵀ)
        = ((J * R * Jᴴ) * S * (J * R * Jᴴ)) * Sᵀ from by simp only [Matrix.mul_assoc],
      hWSW,
      show J * (R * Sc * R) * Jᴴ * Sᵀ = J * (R * Sc * R * Jᴴ * Sᵀ) from by
        simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm J (R * Sc * R * Jᴴ * Sᵀ),
      show R * Sc * R * Jᴴ * Sᵀ * J = R * Sc * R * (Jᴴ * Sᵀ * J) from by
        simp only [Matrix.mul_assoc],
      hScH, step]
  -- Assemble: `⟨φ| P |φ⟩ = |c⁻¹|² · Tr(R · B)`.
  have hcinv : c⁻¹ * star c⁻¹ = (Complex.normSq c⁻¹ : ℂ) := by
    rw [← starRingEnd_apply, Complex.mul_conj]
  have hWinv : W = c⁻¹ • blockWCoeff N φbal := by
    rw [hWbal, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  have hexp : euclideanExpectation (hubbardPairCorrelationOp N x y) φ
      = (Complex.normSq c⁻¹ : ℂ) * (R * (Scᴴ * R * Sc)).trace := by
    rw [euclideanExpectation_pairCorrelation_eq_trace, ← hSdef, ← hWdef, hWinv]
    simp only [Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
      Matrix.trace_smul, smul_eq_mul]
    rw [hcinv, htr]
  have hnormSqPos : (0 : ℂ) < (Complex.normSq c⁻¹ : ℂ) := by
    rw [Complex.pos_iff, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨Complex.normSq_pos.mpr (inv_ne_zero hcne), rfl⟩
  have hfinal : (0 : ℂ) < euclideanExpectation (hubbardPairCorrelationOp N x y) φ := by
    rw [hexp]; exact mul_pos hnormSqPos hBtrace
  exact ⟨(Complex.pos_iff.mp hfinal).1, (Complex.pos_iff.mp hfinal).2.symm⟩

end LatticeSystem.Fermion
