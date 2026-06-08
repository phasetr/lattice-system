import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularFrustrationFree
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularFrustrationFreePos
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandHighestWeight
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
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
    (twoS : ℕ) :
    -c ≤ sectorMinEnergy H twoS := by
  unfold sectorMinEnergy
  by_cases hne : Nonempty (spinSector (M := M) twoS)
  · refine le_ciInf (fun φ => ?_)
    have hu : ‖(φ : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2))‖ = 1 := φ.2.1
    have hsplit : rayleighOnVec (H + (c : ℂ) • 1) (φ : EuclideanSpace ℂ _).ofLp
        = rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp + c := by
      rw [rayleighOnVec_add_matrix, rayleighOnVec_real_smul, rayleighOnVec_one_eq_normSq, hu]
      norm_num
    have hge := hpos (φ : EuclideanSpace ℂ _).ofLp
    rw [hsplit] at hge
    linarith
  · have : IsEmpty (spinSector (M := M) twoS) := not_nonempty_iff.mp hne
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

end LatticeSystem.Fermion
