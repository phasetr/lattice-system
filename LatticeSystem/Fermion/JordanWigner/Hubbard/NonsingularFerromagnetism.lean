import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularFrustrationFree
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularFrustrationFreePos
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandHighestWeight
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandTheorem11_11
import LatticeSystem.Math.RayleighPosSemidefKernel

/-!
# Tasaki §11.4.3 Lemma 11.21: ferromagnetism assembly (Issue #4189)

Assembling the discharge of `nonsingular_lemma_11_21` from the proved pieces:
* `ĥ_p|Φ↑⟩=0` ⟹ `Ĥ|Φ↑⟩ = −C·|Φ↑⟩` (`tasakiNonsingularHamiltonian_mulVec_alphaAllUpState`),
* `Ĥ + C·1 ≥ 0` (`tasakiNonsingular_add_const_posSemidef`),
* the maximal-spin sector membership of `|Φ↑⟩` (here),

towards `exhibitsFerromagnetism` (the maximal-spin sector lies strictly below all others).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.),
§11.4.3, Lemma 11.21 (pp. 429–431).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **`(Ŝ_tot)² |Φα,all↑⟩ = S_max(S_max+1) |Φα,all↑⟩`** with `S_max = (K+1)/2` (twoS = K+1).  The
all-up flat-band state is a highest-weight state (`Ŝ⁺_tot|Φ↑⟩=0`, `Ŝ³_tot|Φ↑⟩=((K+1)/2)|Φ↑⟩`), so
its Casimir value is `m(m+1)` — positivity-free, via
`fermionTotalSpinSquared_mulVec_of_isTop_general`. -/
theorem flatBandTotalSpinSquared_mulVec_alphaAllUpState (K : ℕ) (ν : ℝ) :
    (fermionTotalSpinSquared (2 * K + 1)).mulVec (flatBandAlphaAllUpState K ν)
      = (((K + 1 : ℕ) : ℂ) / 2 * (((K + 1 : ℕ) : ℂ) / 2 + 1)) • flatBandAlphaAllUpState K ν :=
  fermionTotalSpinSquared_mulVec_of_isTop_general (2 * K + 1) (flatBandAlphaAllUpState K ν)
    (((K + 1 : ℕ) : ℂ) / 2)
    (flatBandTotalSpinPlus_mulVec_alphaAllUpState K ν)
    (flatBandTotalSpinZ_mulVec_alphaAllUpState K ν)

open scoped ComplexOrder in
/-- **Energy lower bound from frustration-free positivity.**  If every `ĥ_p ≥ 0` and `0 ≤ lam`, the
shifted energy quadratic form is nonnegative: `0 ≤ rayleighOnVec (Ĥ + C·1) φ` for every `φ`, where
`C = (K+1)(1+2ν²)s`.  Equivalently the energy is `≥ −C·‖φ‖²` everywhere — the global ground-energy
bound underlying the `sectorMinEnergy ≥ −C` half of the ferromagnetism criterion. -/
theorem nonsingular_rayleighOnVec_add_const_nonneg (K : ℕ) (ν s t U lam κ : ℝ) (hlam : 0 ≤ lam)
    (hpos : ∀ i : Fin (K + 1), (nonsingularLocalHamiltonian K ν s t U lam κ i).PosSemidef)
    (φ : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ) :
    0 ≤ rayleighOnVec (tasakiNonsingularHamiltonian K ν t s U
      + ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s)) •
        (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))) φ := by
  have hP := tasakiNonsingular_add_const_posSemidef K ν s t U lam κ hlam hpos
  unfold rayleighOnVec
  simpa using (Complex.le_def.mp (hP.dotProduct_mulVec_nonneg φ)).1

/-- The energy quadratic form of the identity equals the squared `EuclideanSpace` norm:
`rayleighOnVec 1 φ.ofLp = ‖φ‖²`. -/
theorem rayleighOnVec_one_eq_normSq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : EuclideanSpace ℂ ι) :
    rayleighOnVec (1 : Matrix ι ι ℂ) φ.ofLp = ‖φ‖ ^ 2 := by
  unfold rayleighOnVec
  rw [Matrix.one_mulVec, dotProduct_comm]
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) φ
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa using h

open scoped ComplexOrder in
/-- **Generic sector lower bound from a global energy bound.**  If `0 ≤ rayleighOnVec (H + c·1) φ`
for every vector and `0 ≤ c`, then every spin sector's minimum energy is at least `−c`:
`−c ≤ sectorMinEnergy H twoS`.  (On a unit sector vector `rayleighOnVec (H + c·1) = rayleighOnVec H
+ c`, so `rayleighOnVec H ≥ −c`; the infimum inherits the bound, and an empty sector gives the junk
value `0 ≥ −c`.) -/
theorem sectorMinEnergy_ge_of_add_const_rayleigh_nonneg {M : ℕ}
    (H : ManyBodyOp (Fin (2 * M + 2))) (c : ℝ) (hc : 0 ≤ c)
    (hpos : ∀ φ, 0 ≤ rayleighOnVec (H + (c : ℂ) • (1 : ManyBodyOp (Fin (2 * M + 2)))) φ)
    (filling twoS : ℕ) :
    -c ≤ sectorMinEnergy H filling twoS := by
  unfold sectorMinEnergy
  by_cases hne : Nonempty (spinSector (M := M) filling twoS)
  · refine le_ciInf (fun φ => ?_)
    have hu : ‖(φ : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2))‖ = 1 := φ.2.1
    have hsplit : rayleighOnVec (H + (c : ℂ) • 1) (φ : EuclideanSpace ℂ _).ofLp
        = rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp + c := by
      rw [rayleighOnVec_add_matrix, rayleighOnVec_real_smul, rayleighOnVec_one_eq_normSq, hu]
      norm_num
    have hge := hpos (φ : EuclideanSpace ℂ _).ofLp
    rw [hsplit] at hge
    linarith
  · have : IsEmpty (spinSector (M := M) filling twoS) := not_nonempty_iff.mp hne
    rw [Real.iInf_of_isEmpty]
    linarith

/-- The squared `dotProduct` self-pairing of a unit `EuclideanSpace` vector is `1`. -/
theorem star_dotProduct_self_of_norm_one {ι : Type*} [Fintype ι]
    (φ : EuclideanSpace ℂ ι) (hu : ‖φ‖ = 1) : star φ.ofLp ⬝ᵥ φ.ofLp = (1 : ℂ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) φ
  rw [EuclideanSpace.inner_eq_star_dotProduct, hu] at h
  rw [dotProduct_comm]
  simpa using h

/-- **Rayleigh value of a unit eigenvector.**  If `φ` is a unit `EuclideanSpace` vector and an
eigenvector of `H` with real eigenvalue `lam` (`H φ.ofLp = lam • φ.ofLp`), then
`rayleighOnVec H φ.ofLp = lam`. -/
theorem rayleighOnVec_of_unit_eigenvector {ι : Type*} [Fintype ι]
    (H : Matrix ι ι ℂ) (φ : EuclideanSpace ℂ ι) (hu : ‖φ‖ = 1) (lam : ℝ)
    (heig : H.mulVec φ.ofLp = (lam : ℂ) • φ.ofLp) :
    rayleighOnVec H φ.ofLp = lam := by
  unfold rayleighOnVec
  rw [heig, dotProduct_smul, star_dotProduct_self_of_norm_one φ hu, smul_eq_mul, mul_one,
    Complex.ofReal_re]

/-- **Sector upper bound from a plain-vector eigenvector.**  If `v ≠ 0` is a common eigenvector of
`H` (real eigenvalue `lam`) and of `(Ŝ_tot)²` (eigenvalue `(twoS/2)(twoS/2+1)`), then the spin
sector `twoS` has minimum energy at most `lam`: `sectorMinEnergy H twoS ≤ lam`.  The normalised
`φ₀ = ‖v‖⁻¹ • toLp v` lies in `spinSector twoS` with `rayleighOnVec H φ₀.ofLp = lam`. -/
theorem sectorMinEnergy_le_of_eigenvector {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (v : (Fin (2 * M + 2) → Fin 2) → ℂ) (hv : v ≠ 0) (lam : ℝ) (filling twoS : ℕ)
    (hHeig : H.mulVec v = (lam : ℂ) • v)
    (hNeig : (fermionTotalNumber (2 * M + 1)).mulVec v = (filling : ℂ) • v)
    (hSeig : (fermionTotalSpinSquared M).mulVec v
      = (((twoS : ℂ) / 2) * ((twoS : ℂ) / 2 + 1)) • v)
    (hbdd : BddBelow (Set.range
      (fun φ : spinSector (M := M) filling twoS =>
        rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp))) :
    sectorMinEnergy H filling twoS ≤ lam := by
  classical
  set φ : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2) := (WithLp.equiv 2 _).symm v with hφdef
  have hφne : φ ≠ 0 := by
    intro h
    refine hv ?_
    have : φ.ofLp = (0 : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2)).ofLp := by rw [h]
    simpa [hφdef] using this
  set φ₀ : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2) := (‖φ‖⁻¹ : ℂ) • φ with hφ0def
  have hofLp : φ₀.ofLp = (‖φ‖⁻¹ : ℂ) • v := rfl
  have hu : ‖φ₀‖ = 1 := by
    rw [hφ0def, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hφne)]
  -- φ₀ is a unit vector in the spin sector
  have hmem : φ₀ ∈ spinSector (M := M) filling twoS := by
    refine ⟨hu, ?_, ?_⟩
    · rw [hofLp, Matrix.mulVec_smul, hNeig, smul_comm]
    · rw [hofLp, Matrix.mulVec_smul, hSeig, smul_comm]
  -- rayleighOnVec H φ₀.ofLp = lam, since φ₀ is a unit eigenvector of H
  have hray : rayleighOnVec H φ₀.ofLp = lam := by
    refine rayleighOnVec_of_unit_eigenvector H φ₀ hu lam ?_
    rw [hofLp, Matrix.mulVec_smul, hHeig, smul_comm]
  calc sectorMinEnergy H filling twoS
      ≤ rayleighOnVec H φ₀.ofLp := ciInf_le hbdd ⟨φ₀, hmem⟩
    _ = lam := hray

open scoped ComplexOrder in
/-- **Per-unit-vector energy lower bound for the non-singular Hubbard model.**  When every `ĥ_p ≥ 0`
and `0 ≤ lam`, every unit vector has energy at least `−C` with `C = (K+1)(1+2ν²)s`. -/
theorem tasakiNonsingular_rayleighOnVec_ge (K : ℕ) (ν s t U lam κ : ℝ) (hlam : 0 ≤ lam)
    (hpos : ∀ i : Fin (K + 1), (nonsingularLocalHamiltonian K ν s t U lam κ i).PosSemidef)
    (φ : EuclideanSpace ℂ (Fin (2 * (2 * K + 1) + 2) → Fin 2)) (hu : ‖φ‖ = 1) :
    -((K + 1 : ℝ) * ((1 + 2 * ν ^ 2) * s))
      ≤ rayleighOnVec (tasakiNonsingularHamiltonian K ν t s U) φ.ofLp := by
  have h0 := nonsingular_rayleighOnVec_add_const_nonneg K ν s t U lam κ hlam hpos φ.ofLp
  rw [show ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s))
        = (((K + 1 : ℝ) * ((1 + 2 * ν ^ 2) * s) : ℝ) : ℂ) from by push_cast; ring,
    rayleighOnVec_add_matrix, rayleighOnVec_real_smul, rayleighOnVec_one_eq_normSq, hu] at h0
  simp only [one_pow, mul_one] at h0
  linarith

open scoped ComplexOrder in
/-- **Maximal-spin sector energy bound.**  When every `ĥ_p ≥ 0` (`0 ≤ lam`, `1 ≤ K`), the maximal
spin sector `twoS = K+1` has minimum energy at most `−C = −(K+1)(1+2ν²)s`, achieved by the all-up
flat-band state.  (Together with `tasakiNonsingular_rayleighOnVec_ge`, `sectorMinEnergy = −C`.) -/
theorem tasakiNonsingular_sectorMinEnergy_maxSpin_le (K : ℕ) (ν s t U lam κ : ℝ) (hK : 1 ≤ K)
    (hlam : 0 ≤ lam)
    (hpos : ∀ i : Fin (K + 1), (nonsingularLocalHamiltonian K ν s t U lam κ i).PosSemidef) :
    sectorMinEnergy (tasakiNonsingularHamiltonian K ν t s U) (K + 1) (K + 1)
      ≤ -((K + 1 : ℝ) * ((1 + 2 * ν ^ 2) * s)) := by
  have hbdd : BddBelow (Set.range (fun φ : spinSector (M := 2 * K + 1) (K + 1) (K + 1) =>
      rayleighOnVec (tasakiNonsingularHamiltonian K ν t s U)
        (φ : EuclideanSpace ℂ _).ofLp)) := by
    refine ⟨-((K + 1 : ℝ) * ((1 + 2 * ν ^ 2) * s)), ?_⟩
    rintro y ⟨⟨φv, hφmem⟩, rfl⟩
    exact tasakiNonsingular_rayleighOnVec_ge K ν s t U lam κ hlam hpos φv hφmem.1
  refine sectorMinEnergy_le_of_eigenvector (M := 2 * K + 1)
    (tasakiNonsingularHamiltonian K ν t s U) (flatBandAlphaAllUpState K ν)
    (flatBandAlphaAllUpState_ne_zero K ν) (-((K + 1 : ℝ) * ((1 + 2 * ν ^ 2) * s))) (K + 1) (K + 1)
    ?_ ?_ ?_ hbdd
  · rw [tasakiNonsingularHamiltonian_mulVec_alphaAllUpState K ν t s U hK]
    congr 1
    push_cast
    ring
  · rw [flatBandTotalNumber_mulVec_alphaAllUpState K ν]
  · rw [flatBandTotalSpinSquared_mulVec_alphaAllUpState K ν]

open scoped ComplexOrder in
/-- **A ground-energy state lies in `ker Ĥ_flat`.**  When every `ĥ_p ≥ 0` and `0 < lam`, a unit
vector `φ` whose energy equals the ground energy `−C` is annihilated by the flat-band Hamiltonian:
`Ĥ_flat φ = 0`.  Via the decomposition (11.4.46), `rayleighOnVec(Ĥ+C·1)φ = rayleighOnVec(Σĥ_p)φ +
lam·rayleighOnVec(Ĥ_flat)φ`; both PSD terms are `≥ 0` and sum to `0`, so (using `lam > 0`) the
flat-band term vanishes and the PSD-kernel lemma gives `Ĥ_flat φ = 0`.  This is the bridge from
"achieves `−C`" to Theorem 11.11 (the strict-gap step of Lemma 11.21). -/
theorem tasakiNonsingular_flatBand_mulVec_zero_of_rayleigh_eq_neg_const (K : ℕ) (ν s t U lam κ : ℝ)
    (hlam : 0 < lam)
    (hpos : ∀ i : Fin (K + 1), (nonsingularLocalHamiltonian K ν s t U lam κ i).PosSemidef)
    (φ : EuclideanSpace ℂ (Fin (2 * (2 * K + 1) + 2) → Fin 2)) (hu : ‖φ‖ = 1)
    (hE : rayleighOnVec (tasakiNonsingularHamiltonian K ν t s U) φ.ofLp
      = -((K + 1 : ℝ) * ((1 + 2 * ν ^ 2) * s))) :
    (flatBandHamiltonian K ν 1 1).mulVec φ.ofLp = 0 := by
  -- the shifted energy vanishes
  have hC : rayleighOnVec (tasakiNonsingularHamiltonian K ν t s U
      + ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s)) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))) φ.ofLp
      = 0 := by
    rw [rayleighOnVec_add_matrix,
      show ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s))
        = (((K + 1 : ℝ) * ((1 + 2 * ν ^ 2) * s) : ℝ) : ℂ) from by push_cast; ring,
      rayleighOnVec_real_smul, rayleighOnVec_one_eq_normSq, hu, hE]
    simp only [one_pow, mul_one]; ring
  -- decompose the shifted Hamiltonian into the PSD sum + lam·(flat-band remainder)
  have hdecomp : tasakiNonsingularHamiltonian K ν t s U
      + ((K + 1 : ℂ) * ((1 + 2 * ν ^ 2) * s)) • (1 : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))
      = (∑ i, nonsingularLocalHamiltonian K ν s t U lam κ i)
        + (lam : ℂ) • (flatBandHamiltonian K ν 1 1) := by
    rw [tasakiNonsingular_eq_sum_localHamiltonian K ν s t U lam κ,
      ← nonsingularRemainder_eq_flatBand]
    abel
  rw [hdecomp, rayleighOnVec_add_matrix, rayleighOnVec_sum, rayleighOnVec_real_smul] at hC
  -- each summand is ≥ 0
  have hsum_nonneg : ∀ i ∈ Finset.univ,
      0 ≤ rayleighOnVec (nonsingularLocalHamiltonian K ν s t U lam κ i) φ.ofLp := by
    intro i _
    exact (Complex.le_def.mp ((hpos i).dotProduct_mulVec_nonneg φ.ofLp)).1
  have hrem_nonneg : 0 ≤ rayleighOnVec (flatBandHamiltonian K ν 1 1) φ.ofLp :=
    (Complex.le_def.mp
      ((flatBandHamiltonian_posSemidef K ν 1 1 (by norm_num) (by norm_num)).dotProduct_mulVec_nonneg
        φ.ofLp)).1
  have hsum0 : (0 : ℝ)
      ≤ ∑ i, rayleighOnVec (nonsingularLocalHamiltonian K ν s t U lam κ i) φ.ofLp :=
    Finset.sum_nonneg hsum_nonneg
  -- the flat-band term must vanish
  have hflat0 : rayleighOnVec (flatBandHamiltonian K ν 1 1) φ.ofLp = 0 := by
    nlinarith [hC, hsum0, hrem_nonneg, hlam, mul_nonneg hlam.le hrem_nonneg]
  exact posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero
    (flatBandHamiltonian_posSemidef K ν 1 1 (by norm_num) (by norm_num)) hflat0

end LatticeSystem.Fermion
