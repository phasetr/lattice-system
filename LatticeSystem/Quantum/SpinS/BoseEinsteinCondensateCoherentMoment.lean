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

end LatticeSystem.Quantum
