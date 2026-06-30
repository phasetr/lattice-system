import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveHermitianGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorSupport

/-!
# The Γ-reflection preserves the electron-number sector (Tasaki §10.2.4)

Layer PR40e-pre2a2 toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity construction of a Hermitian-`W` ground state symmetrises an eigenvector
by the Γ-reflection `Θ` (`gammaThetaVec`). For the sector argument this must stay inside the
`Ne`-electron sector. Since `Θ = gammaWState ∘ conjTranspose ∘ blockWCoeff`, and conjugate
transpose preserves the `blockWCoeff` band support `|u| + |h| = Ne` (it swaps `(u, h) ↦ (h, u)`),
`Θ` preserves the `N̂ = Ne` eigenspace.

## Main results

* `mulVec_eq_smul_number_of_apply_eq_zero` — the converse of the band support: a vector supported on
  count-`Ne` configurations is an `N̂`-eigenvector at `Ne`.
* `gammaWState_mem_numberSector_of_band_supported` — a band-supported `W` gives a sector state.
* `gammaThetaVec_preserves_fermionTotalNumber` — `Θ` preserves the `Ne`-electron sector.
* `exists_hermitianW_ground_in_sector` — the Hermitian-`W` ground representative, in the sector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- **Converse of the band support.** A vector vanishing off the count-`k` configurations is an
`N̂`-eigenvector at `k` (the total number operator is diagonal with entry the occupation count). -/
theorem mulVec_eq_smul_number_of_apply_eq_zero (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (h : ∀ w, (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) ≠ k → v w = 0) :
    (fermionTotalNumber (2 * N + 1)).mulVec v = k • v := by
  funext w
  rw [fermionTotalNumber_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hc : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = k
  · rw [hc]
  · rw [h w hc, mul_zero, mul_zero]

/-- **A band-supported coefficient matrix gives a sector state.** If `W u h = 0` whenever
`|u| + |h| ≠ Ne`, then `gammaWState N W` lies in the `Ne`-electron sector. The entrywise value
`(gammaWState N W) c = ±W (upConfig (c∘π)) (downConfig (c∘π))` vanishes unless the orbital-permuted
count `|c∘π| = |c|` equals `Ne`. -/
theorem gammaWState_mem_numberSector_of_band_supported (Ne : ℕ)
    (W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ)
    (hW : ∀ u h : hubbardSpinConfig N, (∑ x : Fin (N + 1), ((u x).val : ℂ))
        + ∑ x : Fin (N + 1), ((h x).val : ℂ) ≠ (Ne : ℂ) → W u h = 0) :
    (fermionTotalNumber (2 * N + 1)).mulVec (gammaWState N W) = (Ne : ℂ) • gammaWState N W := by
  refine mulVec_eq_smul_number_of_apply_eq_zero (gammaWState N W) (Ne : ℂ) (fun c hc => ?_)
  rw [gammaWState, hubbardBlockToSpinfulPermutationOperator, permutationOperator_mulVec_apply]
  set π := hubbardBlockToSpinfulOrbitalEquiv N with hπ
  -- The orbital-permuted count `|c∘π|` equals `|c|`, hence `≠ Ne`.
  have hperm : (∑ j : Fin (2 * N + 2), (((c ∘ π) j).val : ℂ))
      = ∑ j : Fin (2 * N + 2), ((c j).val : ℂ) := by
    simp only [Function.comp_apply]
    exact Equiv.sum_comp π (fun j => ((c j).val : ℂ))
  have hcount : (∑ x : Fin (N + 1), ((hubbardBlockUpConfig N (c ∘ π) x).val : ℂ))
      + ∑ x : Fin (N + 1), ((hubbardBlockDownConfig N (c ∘ π) x).val : ℂ) ≠ (Ne : ℂ) := by
    rw [← hubbardBlockMergeConfig_count, hubbardBlockMergeConfig_up_down, hperm]
    exact hc
  -- `(LE.symm W) (c∘π) = W (upConfig (c∘π)) (downConfig (c∘π)) = 0` by band support.
  have hWzero : ((hubbardBlockCoeffLinearEquiv N).symm W) (c ∘ π) = 0 :=
    hW (hubbardBlockUpConfig N (c ∘ π)) (hubbardBlockDownConfig N (c ∘ π)) hcount
  rw [hWzero, mul_zero]

/-- **Conjugate transpose preserves the band support.** If `W` vanishes off `|u| + |h| = Ne`, so
does `Wᴴ` (it swaps `(u, h) ↦ (h, u)`, preserving `|u| + |h|`). -/
theorem band_supported_conjTranspose (Ne : ℕ)
    {W : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ}
    (hW : ∀ u h : hubbardSpinConfig N, (∑ x : Fin (N + 1), ((u x).val : ℂ))
        + ∑ x : Fin (N + 1), ((h x).val : ℂ) ≠ (Ne : ℂ) → W u h = 0)
    (u h : hubbardSpinConfig N) (huh : (∑ x : Fin (N + 1), ((u x).val : ℂ))
        + ∑ x : Fin (N + 1), ((h x).val : ℂ) ≠ (Ne : ℂ)) :
    Wᴴ u h = 0 := by
  rw [Matrix.conjTranspose_apply, hW h u (by rw [add_comm]; exact huh), star_zero]

/-- **The Γ-reflection preserves the `Ne`-electron sector.** If `N̂ ψ = Ne·ψ`, then
`N̂ (Θψ) = Ne·(Θψ)`. -/
theorem gammaThetaVec_preserves_fermionTotalNumber (Ne : ℕ)
    {ψ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hψ : (fermionTotalNumber (2 * N + 1)).mulVec ψ = (Ne : ℂ) • ψ) :
    (fermionTotalNumber (2 * N + 1)).mulVec (gammaThetaVec N ψ)
      = (Ne : ℂ) • gammaThetaVec N ψ := by
  rw [gammaThetaVec]
  refine gammaWState_mem_numberSector_of_band_supported Ne _ (fun u h huh => ?_)
  exact band_supported_conjTranspose Ne
    (fun u' h' hc => blockWCoeff_apply_eq_zero_of_count_ne Ne ψ hψ u' h' hc) u h huh

/-- **A Hermitian-`W` ground representative, in the sector.** The sector-tracking strengthening of
`exists_hermitianW_ground`: given a nonzero `Ĥ`-eigenvector `ψ₀` at a real eigenvalue `E` in the
`Ne`-electron sector, there is a nonzero eigenvector `φ` at the same eigenvalue, still in the
`Ne`-electron sector, whose reconciliation coefficient `blockWCoeff φ` is Hermitian. The
`Θ`-symmetrization stays in the sector by `gammaThetaVec_preserves_fermionTotalNumber`. -/
theorem exists_hermitianW_ground_in_sector (Ne : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (ψ₀ : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℝ) (hψ₀ : ψ₀ ≠ 0)
    (hNe : (fermionTotalNumber (2 * N + 1)).mulVec ψ₀ = (Ne : ℂ) • ψ₀)
    (hE : (attractiveHubbardHamiltonian N T U).mulVec ψ₀ = (E : ℂ) • ψ₀) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0
      ∧ (fermionTotalNumber (2 * N + 1)).mulVec φ = (Ne : ℂ) • φ
      ∧ (blockWCoeff N φ).IsHermitian
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ = (E : ℂ) • φ := by
  -- `N̂` is preserved by the `Θ`-symmetrization `x ↦ x + Θx`.
  have hsector : ∀ x : (Fin (2 * N + 2) → Fin 2) → ℂ,
      (fermionTotalNumber (2 * N + 1)).mulVec x = (Ne : ℂ) • x →
      (fermionTotalNumber (2 * N + 1)).mulVec (x + gammaThetaVec N x)
        = (Ne : ℂ) • (x + gammaThetaVec N x) := fun x hx => by
    rw [Matrix.mulVec_add, hx, gammaThetaVec_preserves_fermionTotalNumber Ne hx, smul_add]
  have hIE : (attractiveHubbardHamiltonian N T U).mulVec (Complex.I • ψ₀)
      = (E : ℂ) • (Complex.I • ψ₀) := by rw [Matrix.mulVec_smul, hE, smul_comm]
  have hINe : (fermionTotalNumber (2 * N + 1)).mulVec (Complex.I • ψ₀)
      = (Ne : ℂ) • (Complex.I • ψ₀) := by rw [Matrix.mulVec_smul, hNe, smul_comm]
  by_cases h0 : ψ₀ + gammaThetaVec N ψ₀ = 0
  · refine ⟨Complex.I • ψ₀ + gammaThetaVec N (Complex.I • ψ₀), ?_, hsector _ hINe,
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr (gammaThetaSymm_fixed _),
      gammaThetaSymm_eigenvector T U _ E hIE⟩
    have hθ : gammaThetaVec N ψ₀ = -ψ₀ := by
      rw [eq_neg_iff_add_eq_zero, add_comm (gammaThetaVec N ψ₀) ψ₀]; exact h0
    have hθI : gammaThetaVec N (Complex.I • ψ₀) = Complex.I • ψ₀ := by
      rw [gammaThetaVec_smul, Complex.conj_I, hθ, neg_smul, smul_neg, neg_neg]
    have hval : Complex.I • ψ₀ + gammaThetaVec N (Complex.I • ψ₀)
        = (2 : ℂ) • (Complex.I • ψ₀) := by rw [hθI, ← two_smul ℂ]
    rw [hval]
    exact smul_ne_zero (by norm_num) (smul_ne_zero Complex.I_ne_zero hψ₀)
  · exact ⟨ψ₀ + gammaThetaVec N ψ₀, h0, hsector _ hNe,
      (blockWCoeff_isHermitian_iff_gammaThetaFixed _).mpr (gammaThetaSymm_fixed _),
      gammaThetaSymm_eigenvector T U ψ₀ E hE⟩

end LatticeSystem.Fermion
