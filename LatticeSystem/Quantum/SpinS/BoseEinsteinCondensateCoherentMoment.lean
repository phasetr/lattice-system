import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensate
import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentMatrixElement

/-!
# Tasaki §5.3 Theorem 5.3: Cesàro window average of the coherent complex moment (eq. (5.3.6))

The `U(1)` symmetry-breaking coherent state `Ξ_θ` (`becCoherentState`, eq. (5.3.5)) has, for the
raising order operator `Ô⁺ = staggeredRaisingOpS`, the sesquilinear form
`⟨Ξ_θ, Ô⁺ Ξ_θ⟩ = (2 M_max + 1)^{-1} Σ_{M',M} conj(e^{−iM'θ}) e^{−iMθ} ⟨Γ_{M'}, Ô⁺ Γ_M⟩`
(`becCoherentState_dotProduct_mulVec`, PR-1).  At half filling (`Ŝ³_tot Φ = 0`) the sector
orthogonality of the tower states collapses the double sum: `Ô⁺ Γ_M` lives in the total-`Ŝ³`
sector `M + 1`, so only the adjacent band `M' = M + 1` survives
(`becOffDiagonal_ne_adjacent_eq_zero`, PR-3).  On that band the phase telescopes to the common
factor `conj(e^{−i(M+1)θ}) e^{−iMθ} = e^{iθ}`, independent of the sign of `M`, giving the exact
finite-`L` Cesàro window representation

* `becCoherent_complexMoment_raising`: `⟨Ξ_θ, Ô⁺ Ξ_θ⟩ = e^{iθ} (2 M_max + 1)^{-1}
  Σ_{M=−M_max}^{M_max−1} ⟨Γ_{M+1}, Ô⁺ Γ_M⟩`, where each summand `⟨Γ_{M+1}, Ô⁺ Γ_M⟩` is the real,
  nonnegative off-diagonal element (the norm ratio `√(D_{M+1}/D_M)` on the raising side `M ≥ 0`,
  the inverse ratio `√(D_M/D_{M+1})` on the lowering side `M ≤ −1`; `becOffDiagonal_eq_norm_ratio`
  and `becOffDiagonal_eq_norm_ratio_neg`, both from PR-3).

The window mean of these off-diagonal elements is the `r_M` average of eq. (5.3.6); its convergence
to `m∗` (the concentration input) is deferred to the assembly PR.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.3, eq. (5.3.6), pp. 141–142 (Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Cesàro window representation of the raising coherent moment** (Tasaki §5.3, eq. (5.3.6)): at
half filling (`Ŝ³_tot Φ = 0`) the coherent-state expectation of `Ô⁺` collapses to the phase factor
`e^{iθ}` times the window average of the adjacent off-diagonal elements,
`⟨Ξ_θ, Ô⁺ Ξ_θ⟩ = e^{iθ} (2 M_max + 1)^{-1} Σ_{M=−M_max}^{M_max−1} ⟨Γ_{M+1}, Ô⁺ Γ_M⟩`.

The double sum of `becCoherentState_dotProduct_mulVec` is collapsed to the adjacent band
`M' = M + 1` by the sector orthogonality `becOffDiagonal_ne_adjacent_eq_zero` (`Ô⁺ Γ_M` sits in
sector `M + 1`); the surviving phase `conj(e^{−i(M+1)θ}) e^{−iMθ}` telescopes to `e^{iθ}`,
independent of the sign of `M`, and the `M = M_max` term drops because `M_max + 1` lies outside the
window.  Each surviving off-diagonal element is real and nonnegative (`becOffDiagonal_eq_norm_ratio`
on `M ≥ 0`, `becOffDiagonal_eq_norm_ratio_neg` on `M ≤ −1`). -/
theorem becCoherent_complexMoment_raising (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = Complex.exp (θ * Complex.I) * ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) Φ)) ⬝ᵥ
              (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  -- the telescoped phase on the adjacent band `M' = M + 1`, common to both signs of `M`.
  have hphase : ∀ M : ℤ,
      (starRingEnd ℂ) (Complex.exp (-((M + 1 : ℤ) : ℝ) * θ * Complex.I))
          * Complex.exp (-(M : ℝ) * θ * Complex.I) = Complex.exp (θ * Complex.I) := by
    intro M
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- the `M = M_max` outer term vanishes: `M_max + 1` is outside the window.
  have hf : ∀ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
      M ∉ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ) →
      (∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
            * Complex.exp (-(M : ℝ) * θ * Complex.I)
            * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
                (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                  (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)))) = 0 := by
    intro M hMicc hMnico
    rw [Finset.mem_Icc] at hMicc
    rw [Finset.mem_Ico] at hMnico
    refine Finset.sum_eq_zero fun M' hM' => ?_
    rw [Finset.mem_Icc] at hM'
    have hne : M' ≠ M + 1 := by omega
    rw [becOffDiagonal_ne_adjacent_eq_zero (torusParitySublattice d L) hne hsing, mul_zero]
  -- for each interior `M`, the inner sum collapses to the single band term `M' = M + 1`.
  have hinner : ∀ M ∈ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ),
      (∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
            * Complex.exp (-(M : ℝ) * θ * Complex.I)
            * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
                (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                  (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))))
        = Complex.exp (θ * Complex.I) *
            (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) Φ)) ⬝ᵥ
              (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))) := by
    intro M hM
    rw [Finset.mem_Ico] at hM
    have hmem : (M + 1) ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ) := by
      rw [Finset.mem_Icc]; omega
    rw [Finset.sum_eq_single_of_mem (M + 1) hmem ?_, hphase M]
    intro M' _ hM'ne
    rw [becOffDiagonal_ne_adjacent_eq_zero (torusParitySublattice d L) hM'ne hsing, mul_zero]
  rw [becCoherentState_dotProduct_mulVec, Finset.sum_comm,
    ← Finset.sum_subset Finset.Ico_subset_Icc_self hf, Finset.sum_congr rfl hinner,
    ← Finset.mul_sum]
  ring

/-- **Cesàro window representation of the lowering coherent moment** (Tasaki §5.3, eq. (5.3.6);
mirror of `becCoherent_complexMoment_raising`): at half filling (`Ŝ³_tot Φ = 0`) the coherent-state
expectation of `Ô⁻` collapses to the phase factor `e^{−iθ}` times the window average of the adjacent
off-diagonal elements,
`⟨Ξ_θ, Ô⁻ Ξ_θ⟩ = e^{−iθ} (2 M_max + 1)^{-1} Σ_{M=−M_max+1}^{M_max} ⟨Γ_{M−1}, Ô⁻ Γ_M⟩`.

The double sum of `becCoherentState_dotProduct_mulVec` is collapsed to the adjacent band
`M' = M − 1` by the sector orthogonality `becOffDiagonal_lowering_ne_adjacent_eq_zero` (`Ô⁻ Γ_M` is
in sector
`M − 1`); the surviving phase `conj(e^{−i(M−1)θ}) e^{−iMθ}` telescopes to `e^{−iθ}`, independent of
the sign of `M`, and the `M = −M_max` term drops because `M_max` is symmetric and `−M_max − 1` lies
outside the window.  Each surviving off-diagonal element is real and nonnegative
(`becOffDiagonal_lowering_eq_norm_ratio` on `M ≤ 0`, `becOffDiagonal_lowering_eq_norm_ratio_pos` on
`M ≥ 1`). -/
theorem becCoherent_complexMoment_lowering (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = Complex.exp (-θ * Complex.I) * ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Ioc (-(Mmax : ℤ)) (Mmax : ℤ),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 (M - 1) Φ)) ⬝ᵥ
              (staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  -- the telescoped phase on the adjacent band `M' = M − 1`, common to both signs of `M`.
  have hphase : ∀ M : ℤ,
      (starRingEnd ℂ) (Complex.exp (-((M - 1 : ℤ) : ℝ) * θ * Complex.I))
          * Complex.exp (-(M : ℝ) * θ * Complex.I) = Complex.exp (-θ * Complex.I) := by
    intro M
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  -- the `M = −M_max` outer term vanishes: `−M_max − 1` is outside the window.
  have hf : ∀ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
      M ∉ Finset.Ioc (-(Mmax : ℤ)) (Mmax : ℤ) →
      (∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
            * Complex.exp (-(M : ℝ) * θ * Complex.I)
            * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
                (staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
                  (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)))) = 0 := by
    intro M hMicc hMnioc
    rw [Finset.mem_Icc] at hMicc
    rw [Finset.mem_Ioc] at hMnioc
    refine Finset.sum_eq_zero fun M' hM' => ?_
    rw [Finset.mem_Icc] at hM'
    have hne : M' ≠ M - 1 := by omega
    rw [becOffDiagonal_lowering_ne_adjacent_eq_zero (torusParitySublattice d L) hne hsing, mul_zero]
  -- for each interior `M`, the inner sum collapses to the single band term `M' = M − 1`.
  have hinner : ∀ M ∈ Finset.Ioc (-(Mmax : ℤ)) (Mmax : ℤ),
      (∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
            * Complex.exp (-(M : ℝ) * θ * Complex.I)
            * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
                (staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
                  (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))))
        = Complex.exp (-θ * Complex.I) *
            (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M - 1) Φ)) ⬝ᵥ
              (staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))) := by
    intro M hM
    rw [Finset.mem_Ioc] at hM
    have hmem : (M - 1) ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ) := by
      rw [Finset.mem_Icc]; omega
    rw [Finset.sum_eq_single_of_mem (M - 1) hmem ?_, hphase M]
    intro M' _ hM'ne
    rw [becOffDiagonal_lowering_ne_adjacent_eq_zero (torusParitySublattice d L) hM'ne hsing,
      mul_zero]
  rw [becCoherentState_dotProduct_mulVec, Finset.sum_comm,
    ← Finset.sum_subset Finset.Ioc_subset_Icc_self hf, Finset.sum_congr rfl hinner,
    ← Finset.mul_sum]
  ring

/-- **Adjacent lowering element equals the shifted raising element** (Tasaki §5.3, eq. (5.3.3)): for
nonzero neighbouring tower states the lowering off-diagonal element `⟨Γ_{M−1}, Ô⁻ Γ_M⟩` equals the
raising element `⟨Γ_{(M−1)+1}, Ô⁺ Γ_{M−1}⟩` one step down the tower.  Both evaluate to the same
real norm ratio (`√(D_{M−1}/D_M)` for `M ≤ 0`, `√(D_M/D_{M−1})` for `M ≥ 1`); this is the per-term
identity that symmetrises the lowering window sum onto the raising window in
`becCoherent_mean1`/`becCoherent_mean2`. -/
private theorem becOffDiagonal_lowering_shift_eq {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (A : Λ → Bool) {M : ℤ} {Φ : (Λ → Fin (N + 1)) → ℂ}
    (htM : towerState A N M Φ ≠ 0) (htMm1 : towerState A N (M - 1) Φ ≠ 0) :
    star (unitNormalize (towerState A N (M - 1) Φ)) ⬝ᵥ
        (staggeredLoweringOpS A N).mulVec (unitNormalize (towerState A N M Φ))
      = star (unitNormalize (towerState A N (M - 1 + 1) Φ)) ⬝ᵥ
        (staggeredRaisingOpS A N).mulVec (unitNormalize (towerState A N (M - 1) Φ)) := by
  have hshift : M - 1 + 1 = M := by ring
  have htMm1' : towerState A N (M - 1 + 1) Φ ≠ 0 := by rw [hshift]; exact htM
  by_cases hM : M ≤ 0
  · rw [becOffDiagonal_lowering_eq_norm_ratio A hM htM htMm1,
      becOffDiagonal_eq_norm_ratio_neg A (show M - 1 ≤ -1 by omega) htMm1 htMm1', hshift]
  · rw [becOffDiagonal_lowering_eq_norm_ratio_pos A (show (1 : ℤ) ≤ M by omega) htM htMm1,
      becOffDiagonal_eq_norm_ratio A (show (0 : ℤ) ≤ M - 1 by omega) htMm1 htMm1', hshift]

/-- **Lowering window sum equals the raising window sum** (Tasaki §5.3, eq. (5.3.7) symmetrisation):
reindexing `M ↦ M − 1` maps the lowering window `Ioc(−M_max, M_max)` bijectively onto the raising
window `Ico(−M_max, M_max)`, and each lowering element equals the raising element one step down
(`becOffDiagonal_lowering_shift_eq`).  This lets the coherent means `becCoherent_mean1`/`mean2`
express both `Ô⁺` and `Ô⁻` contributions over the single raising window sum, so their phase factors
combine to `cos θ`/`sin θ`. -/
theorem becCoherent_loweringWindow_eq_raisingWindow (d L : ℕ) [NeZero L] (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hne : ∀ M : ℤ, -(Mmax : ℤ) ≤ M → M ≤ (Mmax : ℤ) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0) :
    (∑ M ∈ Finset.Ioc (-(Mmax : ℤ)) (Mmax : ℤ),
        star (unitNormalize (towerState (torusParitySublattice d L) 1 (M - 1) Φ)) ⬝ᵥ
          (staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
            (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)))
      = ∑ M ∈ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ),
        star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) Φ)) ⬝ᵥ
          (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
            (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  refine Finset.sum_nbij' (fun M => M - 1) (fun k => k + 1) ?_ ?_ ?_ ?_ ?_
  · intro M hM; simp only [Finset.mem_Ioc] at hM; simp only [Finset.mem_Ico]; omega
  · intro k hk; simp only [Finset.mem_Ico] at hk; simp only [Finset.mem_Ioc]; omega
  · intro M _; ring
  · intro k _; ring
  · intro M hM
    rw [Finset.mem_Ioc] at hM
    exact becOffDiagonal_lowering_shift_eq (torusParitySublattice d L)
      (hne M (by omega) (by omega)) (hne (M - 1) (by omega) (by omega))

/-- **Coherent window mean of the `1`-axis order operator** (Tasaki §5.3, eq. (5.3.7)): at half
filling (`Ŝ³_tot Φ = 0`), with the tower states nonzero across the window, the coherent-state
expectation of `Ô^{(1)} = ½(Ô⁺ + Ô⁻)` is `cos θ` times the raising window average,
`⟨Ξ_θ, Ô^{(1)} Ξ_θ⟩ = cos θ · (2 M_max + 1)^{-1} Σ_{M=−M_max}^{M_max−1} ⟨Γ_{M+1}, Ô⁺ Γ_M⟩`.

From the Cartesian decomposition `staggeredOrderOp1S_eq_half_smul`, the two complex moments
`becCoherent_complexMoment_raising`/`_lowering` contribute `e^{iθ}` and `e^{−iθ}` times the raising
and lowering window sums; symmetrising the lowering sum onto the raising window
(`becCoherent_loweringWindow_eq_raisingWindow`) makes the two share one real window sum, and
`½(e^{iθ} + e^{−iθ}) = cos θ` (`Complex.two_cos`). -/
theorem becCoherent_mean1 (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0)
    (hne : ∀ M : ℤ, -(Mmax : ℤ) ≤ M → M ≤ (Mmax : ℤ) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredOrderOp1S (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = (Real.cos θ : ℂ) * ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) Φ)) ⬝ᵥ
              (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  have hcos : (2 : ℂ)⁻¹ * (Complex.exp (θ * Complex.I) + Complex.exp (-θ * Complex.I))
      = (Real.cos θ : ℂ) := by
    rw [Complex.ofReal_cos, ← Complex.two_cos]; ring
  rw [staggeredOrderOp1S_eq_half_smul]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.add_mulVec,
    dotProduct_add]
  rw [becCoherent_complexMoment_raising d L θ Mmax Φ hsing,
    becCoherent_complexMoment_lowering d L θ Mmax Φ hsing,
    becCoherent_loweringWindow_eq_raisingWindow d L Mmax Φ hne]
  set S := ∑ M ∈ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ),
      star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) Φ)) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) with hS
  linear_combination (((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ * S) * hcos

/-- **Coherent window mean of the `2`-axis order operator** (Tasaki §5.3, eq. (5.3.7)): at half
filling (`Ŝ³_tot Φ = 0`), with the tower states nonzero across the window, the coherent-state
expectation of `Ô^{(2)} = (2i)^{-1}(Ô⁺ − Ô⁻)` is `sin θ` times the same raising window average,
`⟨Ξ_θ, Ô^{(2)} Ξ_θ⟩ = sin θ · (2 M_max + 1)^{-1} Σ_{M=−M_max}^{M_max−1} ⟨Γ_{M+1}, Ô⁺ Γ_M⟩`.

Mirror of `becCoherent_mean1` through the Cartesian decomposition `staggeredOrderOp2S_eq_smul`: the
raising/lowering complex moments contribute `e^{iθ}` and `e^{−iθ}` times the (symmetrised) real
window sum, and `(2i)^{-1}(e^{iθ} − e^{−iθ}) = sin θ` (`Complex.two_sin`, `Complex.I_sq`). -/
theorem becCoherent_mean2 (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0)
    (hne : ∀ M : ℤ, -(Mmax : ℤ) ≤ M → M ≤ (Mmax : ℤ) →
        towerState (torusParitySublattice d L) 1 M Φ ≠ 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredOrderOp2S (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = (Real.sin θ : ℂ) * ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) Φ)) ⬝ᵥ
              (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  have hmul : (2 * Complex.I) * (Real.sin θ : ℂ)
      = Complex.exp (θ * Complex.I) - Complex.exp (-θ * Complex.I) := by
    have h2s := Complex.two_sin (θ : ℂ)
    have hIsq := Complex.I_sq
    rw [Complex.ofReal_sin]
    linear_combination Complex.I * h2s
      + (Complex.exp (-(θ : ℂ) * Complex.I) - Complex.exp ((θ : ℂ) * Complex.I)) * hIsq
  have hsin : (2 * Complex.I)⁻¹ * (Complex.exp (θ * Complex.I) - Complex.exp (-θ * Complex.I))
      = (Real.sin θ : ℂ) := by
    rw [← hmul, inv_mul_cancel_left₀ (mul_ne_zero two_ne_zero Complex.I_ne_zero)]
  rw [staggeredOrderOp2S_eq_smul]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.sub_mulVec,
    dotProduct_sub]
  rw [becCoherent_complexMoment_raising d L θ Mmax Φ hsing,
    becCoherent_complexMoment_lowering d L θ Mmax Φ hsing,
    becCoherent_loweringWindow_eq_raisingWindow d L Mmax Φ hne]
  set S := ∑ M ∈ Finset.Ico (-(Mmax : ℤ)) (Mmax : ℤ),
      star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 1) Φ)) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) with hS
  linear_combination (((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ * S) * hsin

end LatticeSystem.Quantum
