import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateCoherentMoment

/-!
# Tasaki §5.3 Theorem 5.3: exact finite-`L` form of the coherent second moments (eq. (5.3.8))

The squared order operators `(Ô_L^{(α)})²` of the `U(1)` coherent state `Ξ_θ` (`becCoherentState`,
eq. (5.3.5)) enter the fluctuation part of the symmetry-breaking limits (5.3.8),
`⟨Ξ_θ, (Ô_L^{(α)})² Ξ_θ⟩ / (L^d)² → (m∗ cos θ)² / (m∗ sin θ)²`.  This file collapses the coherent
Rayleigh double sum for those squared operators into an **exact finite-`L` band representation**,
entirely axiom-free (it depends on `std3` only, carrying no concentration axiom).

Writing `Ô^{(1)} = ½(Ô⁺ + Ô⁻)` and `Ô^{(2)} = (2i)⁻¹(Ô⁺ − Ô⁻)` (`staggeredOrderOp1S_eq_half_smul`,
`staggeredOrderOp2S_eq_smul`), the square expands into the four two-step products `Ô⁺Ô⁺`, `Ô⁺Ô⁻`,
`Ô⁻Ô⁺`, `Ô⁻Ô⁻` (`staggeredOrderOp1S_sq_eq`, `staggeredOrderOp2S_sq_eq`).  At half filling
(`Ŝ³_tot Φ = 0`) each product shifts the total-`Ŝ³` sector by `+2`, `0`, `0`, `−2`, so — by the
sector orthogonality of the tower states (`becBand_ne_eq_zero_of_intEigen`, built from
`totalSpinSOp3_mulVec_staggeredRaising_eigenvec` and its lowering mirror) — the coherent double sum
collapses to a single window band carrying the phase `e^{+2iθ}`, `1`, `1`, `e^{−2iθ}` respectively:

* `becCoherent_band_collapse` / `becCoherent_diagonal_collapse`: the generic Cesàro collapse for a
  sector-shift-`k` operator (`k = ±2` off-diagonal band with phase `e^{ikθ}`, `k = 0` diagonal);
* `becCoherent_raisingRaising_collapse` / `becCoherent_loweringLowering_collapse`: the two
  off-diagonal bands `⟨Ξ_θ, Ô⁺Ô⁺ Ξ_θ⟩`, `⟨Ξ_θ, Ô⁻Ô⁻ Ξ_θ⟩` (phases `e^{±2iθ}`);
* `becCoherent_raisingLowering_collapse` / `becCoherent_loweringRaising_collapse`: the two diagonal
  bands `⟨Ξ_θ, Ô⁺Ô⁻ Ξ_θ⟩`, `⟨Ξ_θ, Ô⁻Ô⁺ Ξ_θ⟩`;
* `becCoherent_secondMoment1_eq` / `becCoherent_secondMoment2_eq`: the exact operator-square split
  `⟨Ξ_θ, (Ô^{(α)})² Ξ_θ⟩` into a `¼`-weighted combination of those four band sums.

The reduction of these band sums to `(m∗ cos θ)²` (via the norm ratios `r_M` and the window
concentration) is deferred to the assembly PR; here everything is an exact finite-`L` identity.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.3, eq. (5.3.8), pp. 141–142 (Koma–Tasaki [21]).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Two-step sector orthogonality -/

/-- **Sector orthogonality from an integer eigenvalue** (Tasaki §5.3, eq. (5.3.3)): at half filling
(`Ŝ³_tot Φ = 0`), if the operator image `P (towerState M Φ)` is a `Ŝ³_tot`-eigenvector with integer
eigenvalue `j`, then the matrix element `⟨Γ_{M'}, P Γ_M⟩` vanishes for every `M' ≠ j`.  The two
vectors are eigenvectors of the Hermitian `Ŝ³_tot` with distinct real eigenvalues `M'`, `j`.  It is
the two-step generalization of `becOffDiagonal_ne_adjacent_eq_zero`, used to collapse the coherent
second-moment double sum for the products `Ô⁺Ô⁺` (`j = M+2`), `Ô⁻Ô⁻` (`j = M−2`), `Ô⁺Ô⁻`, `Ô⁻Ô⁺`
(`j = M`). -/
private theorem becBand_ne_eq_zero_of_intEigen (A : Λ → Bool)
    (P : Matrix (Λ → Fin (N + 1)) (Λ → Fin (N + 1)) ℂ) {M M' j : ℤ}
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hP : (totalSpinSOp3 Λ N).mulVec (P.mulVec (towerState A N M Φ))
        = (j : ℂ) • P.mulVec (towerState A N M Φ))
    (hne : M' ≠ j) (hsing : (totalSpinSOp3 Λ N).mulVec Φ = 0) :
    star (unitNormalize (towerState A N M' Φ)) ⬝ᵥ
      P.mulVec (unitNormalize (towerState A N M Φ)) = 0 := by
  have hlam : (M' : ℂ) ≠ (j : ℂ) := fun h => hne (by exact_mod_cast h)
  have key : star (towerState A N M' Φ) ⬝ᵥ P.mulVec (towerState A N M Φ) = 0 := by
    have ht' : (totalSpinSOp3 Λ N).mulVec (towerState A N M' Φ)
        = (M' : ℂ) • towerState A N M' Φ := towerState_totalSpin3_eigenvector A M' hsing
    have hadj := star_mulVec_dotProduct (totalSpinSOp3 Λ N) (towerState A N M' Φ)
      (P.mulVec (towerState A N M Φ))
    rw [ht', (totalSpinSOp3_isHermitian Λ N).eq, hP, star_smul, star_intCast,
      smul_dotProduct, smul_eq_mul, dotProduct_smul, smul_eq_mul] at hadj
    have hne' : (M' : ℂ) - (j : ℂ) ≠ 0 := sub_ne_zero.mpr hlam
    have hzero : ((M' : ℂ) - (j : ℂ)) *
        (star (towerState A N M' Φ) ⬝ᵥ P.mulVec (towerState A N M Φ)) = 0 := by
      rw [sub_mul, hadj, sub_self]
    exact (mul_eq_zero.mp hzero).resolve_left hne'
  unfold unitNormalize
  rw [star_smul_dotProduct_mulVec_smul, key, mul_zero]

/-! ### Operator-square expansion -/

/-- **Two-step expansion of the squared `1`-axis order operator** (Tasaki §5.3, eq. (5.3.8)):
`(Ô^{(1)})² = ¼(Ô⁺Ô⁺ + Ô⁺Ô⁻ + Ô⁻Ô⁺ + Ô⁻Ô⁻)`, from the Cartesian half-sum
`Ô^{(1)} = ½(Ô⁺ + Ô⁻)` (`staggeredOrderOp1S_eq_half_smul`). -/
private theorem staggeredOrderOp1S_sq_eq (A : Λ → Bool) :
    (staggeredOrderOp1S A N) ^ 2
      = (4 : ℂ)⁻¹ • (staggeredRaisingOpS A N * staggeredRaisingOpS A N
          + staggeredRaisingOpS A N * staggeredLoweringOpS A N
          + staggeredLoweringOpS A N * staggeredRaisingOpS A N
          + staggeredLoweringOpS A N * staggeredLoweringOpS A N) := by
  rw [pow_two, staggeredOrderOp1S_eq_half_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show ((2 : ℂ)⁻¹ * 2⁻¹) = 4⁻¹ from by norm_num,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  congr 1
  abel

/-- **Two-step expansion of the squared `2`-axis order operator** (Tasaki §5.3, eq. (5.3.8)):
`(Ô^{(2)})² = −¼(Ô⁺Ô⁺ − Ô⁺Ô⁻ − Ô⁻Ô⁺ + Ô⁻Ô⁻)`, from the Cartesian half-difference
`Ô^{(2)} = (2i)⁻¹(Ô⁺ − Ô⁻)` (`staggeredOrderOp2S_eq_smul`; the sign is `((2i)⁻¹)² = −¼`). -/
private theorem staggeredOrderOp2S_sq_eq (A : Λ → Bool) :
    (staggeredOrderOp2S A N) ^ 2
      = (-(4 : ℂ)⁻¹) • (staggeredRaisingOpS A N * staggeredRaisingOpS A N
          - staggeredRaisingOpS A N * staggeredLoweringOpS A N
          - staggeredLoweringOpS A N * staggeredRaisingOpS A N
          + staggeredLoweringOpS A N * staggeredLoweringOpS A N) := by
  rw [pow_two, staggeredOrderOp2S_eq_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    show ((2 * Complex.I)⁻¹ * (2 * Complex.I)⁻¹) = -(4 : ℂ)⁻¹ from by
      have hI : (2 * Complex.I) * (2 * Complex.I) = -4 := by
        have h4 : (2 * Complex.I) * (2 * Complex.I) = 4 * Complex.I ^ 2 := by ring
        rw [h4, Complex.I_sq]; ring
      rw [← mul_inv, hI, show (-4 : ℂ) = -(4 : ℂ) from by norm_num, inv_neg],
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
  congr 1
  abel

/-! ### Generic Cesàro band collapse -/

/-- **Off-diagonal Cesàro band collapse** (Tasaki §5.3, eq. (5.3.8)): if the operator `P` shifts the
total-`Ŝ³` sector of the tower states by a fixed integer `k` (so `⟨Γ_{M'}, P Γ_M⟩ = 0` unless
`M' = M + k`, supplied as `horth`), then the coherent expectation of `P` collapses to the phase
`e^{ikθ}` times the window average of the single surviving band `⟨Γ_{M+k}, P Γ_M⟩`, taken over the
`M` for which both `M` and `M + k` lie in the tower window `[−M_max, M_max]`.  Generalizes
`becCoherent_complexMoment_raising` (`k = 1`) to `k = ±2` for the squared order operators. -/
theorem becCoherent_band_collapse (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ) (k : ℤ)
    (P : Matrix (HypercubicTorus d L → Fin 2) (HypercubicTorus d L → Fin 2) ℂ)
    (horth : ∀ M M' : ℤ, M' ≠ M + k →
        star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
          P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ P.mulVec (becCoherentState d L θ Mmax Φ)
      = Complex.exp ((k : ℝ) * θ * Complex.I) * ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ (Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ)).filter
              (fun M => -(Mmax : ℤ) ≤ M + k ∧ M + k ≤ (Mmax : ℤ)),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + k) Φ)) ⬝ᵥ
              P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  have hphase : ∀ M : ℤ,
      (starRingEnd ℂ) (Complex.exp (-((M + k : ℤ) : ℝ) * θ * Complex.I))
          * Complex.exp (-(M : ℝ) * θ * Complex.I) = Complex.exp ((k : ℝ) * θ * Complex.I) := by
    intro M
    rw [← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hf : ∀ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
      M ∉ (Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ)).filter
          (fun M => -(Mmax : ℤ) ≤ M + k ∧ M + k ≤ (Mmax : ℤ)) →
      (∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
            * Complex.exp (-(M : ℝ) * θ * Complex.I)
            * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
                P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)))) = 0 := by
    intro M hMicc hMnf
    have hout : (M + k) ∉ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ) := by
      intro hin
      exact hMnf (Finset.mem_filter.mpr ⟨hMicc, Finset.mem_Icc.mp hin⟩)
    refine Finset.sum_eq_zero fun M' hM' => ?_
    have hne : M' ≠ M + k := fun h => hout (h ▸ hM')
    rw [horth M M' hne, mul_zero]
  have hinner : ∀ M ∈ (Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ)).filter
          (fun M => -(Mmax : ℤ) ≤ M + k ∧ M + k ≤ (Mmax : ℤ)),
      (∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
            * Complex.exp (-(M : ℝ) * θ * Complex.I)
            * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
                P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))))
        = Complex.exp ((k : ℝ) * θ * Complex.I) *
            (star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + k) Φ)) ⬝ᵥ
              P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))) := by
    intro M hM
    rw [Finset.mem_filter, Finset.mem_Icc] at hM
    have hmem : (M + k) ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ) := Finset.mem_Icc.mpr hM.2
    rw [Finset.sum_eq_single_of_mem (M + k) hmem ?_, hphase M]
    intro M' _ hM'ne
    rw [horth M M' hM'ne, mul_zero]
  rw [becCoherentState_dotProduct_mulVec, Finset.sum_comm,
    ← Finset.sum_subset (Finset.filter_subset _ _) hf, Finset.sum_congr rfl hinner,
    ← Finset.mul_sum]
  ring

/-- **Diagonal Cesàro band collapse** (Tasaki §5.3, eq. (5.3.8)): if the operator `P` preserves the
total-`Ŝ³` sector of the tower states (so `⟨Γ_{M'}, P Γ_M⟩ = 0` unless `M' = M`, supplied as
`horth`), then the coherent-state expectation of `P` collapses to the window average of the diagonal
elements `⟨Γ_M, P Γ_M⟩` (the phase `conj(e^{−iMθ}) e^{−iMθ} = 1`).  Used for the sector-preserving
products `Ô⁺Ô⁻`, `Ô⁻Ô⁺`. -/
theorem becCoherent_diagonal_collapse (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (P : Matrix (HypercubicTorus d L → Fin 2) (HypercubicTorus d L → Fin 2) ℂ)
    (horth : ∀ M M' : ℤ, M' ≠ M →
        star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
          P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ P.mulVec (becCoherentState d L θ Mmax Φ)
      = ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) ⬝ᵥ
              P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  have hphase1 : ∀ M : ℤ,
      (starRingEnd ℂ) (Complex.exp (-(M : ℝ) * θ * Complex.I))
          * Complex.exp (-(M : ℝ) * θ * Complex.I) = 1 := by
    intro M
    rw [← Complex.exp_conj, ← Complex.exp_add,
      show (starRingEnd ℂ) (-(M : ℝ) * θ * Complex.I) + (-(M : ℝ) * θ * Complex.I) = 0 from by
        simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; ring,
      Complex.exp_zero]
  have hinner : ∀ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
      (∑ M' ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
          (starRingEnd ℂ) (Complex.exp (-(M' : ℝ) * θ * Complex.I))
            * Complex.exp (-(M : ℝ) * θ * Complex.I)
            * (star (unitNormalize (towerState (torusParitySublattice d L) 1 M' Φ)) ⬝ᵥ
                P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ))))
        = star (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) ⬝ᵥ
            P.mulVec (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
    intro M hM
    rw [Finset.sum_eq_single_of_mem M hM ?_, hphase1 M, one_mul]
    intro M' _ hM'ne
    rw [horth M M' hM'ne, mul_zero]
  rw [becCoherentState_dotProduct_mulVec, Finset.sum_comm, Finset.sum_congr rfl hinner]

/-! ### The four two-step bands of the coherent second moment -/

/-- **`Ô⁺Ô⁺` band of the coherent second moment** (Tasaki §5.3, eq. (5.3.8)): at half filling the
coherent expectation of `Ô⁺Ô⁺` collapses to the phase `e^{+2iθ}` times the window average of the
`+2`-band elements `⟨Γ_{M+2}, Ô⁺Ô⁺ Γ_M⟩` (`Ô⁺Ô⁺` raises the total magnetization by two). -/
theorem becCoherent_raisingRaising_collapse (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = Complex.exp (((2 : ℤ) : ℝ) * θ * Complex.I) * ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ (Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ)).filter
              (fun M => -(Mmax : ℤ) ≤ M + 2 ∧ M + 2 ≤ (Mmax : ℤ)),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + 2) Φ)) ⬝ᵥ
              (staggeredRaisingOpS (torusParitySublattice d L) 1
                * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  refine becCoherent_band_collapse d L θ Mmax Φ 2 _ ?_
  intro M M' hMM'
  refine becBand_ne_eq_zero_of_intEigen (torusParitySublattice d L) _ ?_ hMM' hsing
  have h0 := towerState_totalSpin3_eigenvector (torusParitySublattice d L) M hsing
  have h1 := totalSpinSOp3_mulVec_staggeredRaising_eigenvec (torusParitySublattice d L) h0
  have h2 := totalSpinSOp3_mulVec_staggeredRaising_eigenvec (torusParitySublattice d L) h1
  rw [← Matrix.mulVec_mulVec, h2,
    show ((M : ℂ) + 1 + 1) = ((M + 2 : ℤ) : ℂ) from by push_cast; ring]

/-- **`Ô⁻Ô⁻` band of the coherent second moment** (Tasaki §5.3, eq. (5.3.8)): the coherent
expectation of `Ô⁻Ô⁻` collapses to the phase `e^{−2iθ}` times the window average of the `−2`-band
elements `⟨Γ_{M−2}, Ô⁻Ô⁻ Γ_M⟩` (`Ô⁻Ô⁻` lowers the total magnetization by two). -/
theorem becCoherent_loweringLowering_collapse (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1
          * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = Complex.exp (((-2 : ℤ) : ℝ) * θ * Complex.I) * ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ (Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ)).filter
              (fun M => -(Mmax : ℤ) ≤ M + (-2) ∧ M + (-2) ≤ (Mmax : ℤ)),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 (M + (-2)) Φ)) ⬝ᵥ
              (staggeredLoweringOpS (torusParitySublattice d L) 1
                * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  refine becCoherent_band_collapse d L θ Mmax Φ (-2) _ ?_
  intro M M' hMM'
  refine becBand_ne_eq_zero_of_intEigen (torusParitySublattice d L) _ ?_ hMM' hsing
  have h0 := towerState_totalSpin3_eigenvector (torusParitySublattice d L) M hsing
  have h1 := totalSpinSOp3_mulVec_staggeredLowering_eigenvec (torusParitySublattice d L) h0
  have h2 := totalSpinSOp3_mulVec_staggeredLowering_eigenvec (torusParitySublattice d L) h1
  rw [← Matrix.mulVec_mulVec, h2,
    show ((M : ℂ) - 1 - 1) = ((M + (-2) : ℤ) : ℂ) from by push_cast; ring]

/-- **`Ô⁺Ô⁻` band of the coherent second moment** (Tasaki §5.3, eq. (5.3.8)): the coherent
expectation of `Ô⁺Ô⁻` collapses to the window average of the diagonal elements `⟨Γ_M, Ô⁺Ô⁻ Γ_M⟩`
(`Ô⁺Ô⁻` preserves the total magnetization). -/
theorem becCoherent_raisingLowering_collapse (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredRaisingOpS (torusParitySublattice d L) 1
          * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) ⬝ᵥ
              (staggeredRaisingOpS (torusParitySublattice d L) 1
                * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  refine becCoherent_diagonal_collapse d L θ Mmax Φ _ ?_
  intro M M' hMM'
  refine becBand_ne_eq_zero_of_intEigen (torusParitySublattice d L) _ ?_ hMM' hsing
  have h0 := towerState_totalSpin3_eigenvector (torusParitySublattice d L) M hsing
  have h1 := totalSpinSOp3_mulVec_staggeredLowering_eigenvec (torusParitySublattice d L) h0
  have h2 := totalSpinSOp3_mulVec_staggeredRaising_eigenvec (torusParitySublattice d L) h1
  rw [← Matrix.mulVec_mulVec, h2, show ((M : ℂ) - 1 + 1) = ((M : ℤ) : ℂ) from by ring]

/-- **`Ô⁻Ô⁺` band of the coherent second moment** (Tasaki §5.3, eq. (5.3.8)): the coherent
expectation of `Ô⁻Ô⁺` collapses to the window average of the diagonal elements `⟨Γ_M, Ô⁻Ô⁺ Γ_M⟩`
(`Ô⁻Ô⁺` preserves the total magnetization). -/
theorem becCoherent_loweringRaising_collapse (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ)
    (hsing : (totalSpinSOp3 (HypercubicTorus d L) 1).mulVec Φ = 0) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        (staggeredLoweringOpS (torusParitySublattice d L) 1
          * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
          (becCoherentState d L θ Mmax Φ)
      = ((2 * (Mmax : ℝ) + 1 : ℝ) : ℂ)⁻¹ *
          ∑ M ∈ Finset.Icc (-(Mmax : ℤ)) (Mmax : ℤ),
            star (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) ⬝ᵥ
              (staggeredLoweringOpS (torusParitySublattice d L) 1
                * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
                (unitNormalize (towerState (torusParitySublattice d L) 1 M Φ)) := by
  refine becCoherent_diagonal_collapse d L θ Mmax Φ _ ?_
  intro M M' hMM'
  refine becBand_ne_eq_zero_of_intEigen (torusParitySublattice d L) _ ?_ hMM' hsing
  have h0 := towerState_totalSpin3_eigenvector (torusParitySublattice d L) M hsing
  have h1 := totalSpinSOp3_mulVec_staggeredRaising_eigenvec (torusParitySublattice d L) h0
  have h2 := totalSpinSOp3_mulVec_staggeredLowering_eigenvec (torusParitySublattice d L) h1
  rw [← Matrix.mulVec_mulVec, h2, show ((M : ℂ) + 1 - 1) = ((M : ℤ) : ℂ) from by ring]

/-! ### Exact operator-square split of the coherent second moments -/

/-- **Exact finite-`L` representation of the `1`-axis coherent second moment** (Tasaki §5.3, eq.
(5.3.8)): the coherent Rayleigh numerator of `(Ô^{(1)})²` splits exactly into `¼` times the sum of
the four two-step band expectations `Ô⁺Ô⁺`, `Ô⁺Ô⁻`, `Ô⁻Ô⁺`, `Ô⁻Ô⁻`.  Combined with the four band
collapses (`becCoherent_raisingRaising_collapse` etc.) this is the exact finite-`L` band
representation `½ cos 2θ · S₁₁ + ½ S₂` (up to the axiom-free commutator remainder on the diagonal
band), carrying no concentration axiom. -/
theorem becCoherent_secondMoment1_eq (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        ((staggeredOrderOp1S (torusParitySublattice d L) 1) ^ 2).mulVec
          (becCoherentState d L θ Mmax Φ)
      = (4 : ℂ)⁻¹ *
        (star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)
          + star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1
              * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)
          + star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)
          + star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)) := by
  rw [staggeredOrderOp1S_sq_eq]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.add_mulVec, dotProduct_add]

/-- **Exact finite-`L` representation of the `2`-axis coherent second moment** (Tasaki §5.3, eq.
(5.3.8)): the coherent Rayleigh numerator of `(Ô^{(2)})²` splits exactly into `−¼` times the signed
sum `Ô⁺Ô⁺ − Ô⁺Ô⁻ − Ô⁻Ô⁺ + Ô⁻Ô⁻` of the four two-step band expectations.  The sign difference from
`becCoherent_secondMoment1_eq` produces the `sin²θ` companion of (5.3.8). -/
theorem becCoherent_secondMoment2_eq (d L : ℕ) [NeZero L] (θ : ℝ) (Mmax : ℕ)
    (Φ : (HypercubicTorus d L → Fin 2) → ℂ) :
    star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
        ((staggeredOrderOp2S (torusParitySublattice d L) 1) ^ 2).mulVec
          (becCoherentState d L θ Mmax Φ)
      = (-(4 : ℂ)⁻¹) *
        (star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)
          - star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredRaisingOpS (torusParitySublattice d L) 1
              * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)
          - star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredRaisingOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)
          + star (becCoherentState d L θ Mmax Φ) ⬝ᵥ
            (staggeredLoweringOpS (torusParitySublattice d L) 1
              * staggeredLoweringOpS (torusParitySublattice d L) 1).mulVec
              (becCoherentState d L θ Mmax Φ)) := by
  rw [staggeredOrderOp2S_sq_eq]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.add_mulVec,
    Matrix.sub_mulVec, dotProduct_add, dotProduct_sub]

end LatticeSystem.Quantum
