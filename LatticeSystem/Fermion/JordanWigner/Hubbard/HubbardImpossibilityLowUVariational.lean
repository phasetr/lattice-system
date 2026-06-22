import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUVariationalCore

/-!
# Tasaki §11.1.1: the variational sector machinery for Theorem 11.3

This file builds the **fixed-electron-number sector compression** for the all-to-all Hubbard model
(no hard-core constraint, unlike the §11.5 t-J compression of `TJFilling*`).  The `Ne`-electron
sector `W = (N̂ = Ne)`-eigenspace is `Ĥ`-invariant (charge conservation), spanned by the
computational basis vectors `|c⟩` over the `Ne`-electron configurations.  Compressing `Ĥ` to a
matrix `Ĥ_W` in this orthonormal basis lets us run the finite-dimensional Rayleigh–Ritz argument:

* `hubbardSectorCompress` — the matrix `Tᴴ Ĥ T` of `Ĥ` in the `Ne`-electron basis;
* `rayleighOnVec_hubbardSectorCompress` — the Rayleigh bridge (operator Rayleigh of a lifted
  sector vector = matrix Rayleigh of the compression);
* `hubbardSector_minEnergy_eigenspace_ne_bot` — the compression's minimum eigenvalue lifts to a
  genuine `Ĥ`-eigenvector in `W`, so `hubbardEigenspaceAt` at that energy is nonzero;
* `hubbardSector_minEnergy_le_of_mem` — every `Ne`-electron vector's Rayleigh quotient is bounded
  below by the sector minimum (variational principle).

These are the §11.3-style sector tools specialised to the bare number sector, used by the
variational discharge of Tasaki Theorem 11.3 (the spin-flip trial state lowers the energy below the
all-up trace).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.3, eqs. (11.1.5)–(11.1.6), pp. 378–379.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped ComplexOrder

variable {N : ℕ}

/-! ## Non-vanishing of the eigenmode Slater state -/

/-- **An eigenmode Slater state is nonzero.**  `spinfulGeneralBasisState e SUp SDown ≠ 0`: it is a
nonzero scalar multiple of the occupation-basis vector for the config selecting `SUp`/`SDown`, which
is a (nonzero) basis element. -/
theorem spinfulGeneralBasisState_ne_zero {M : ℕ}
    (e : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)) (SUp SDown : Finset (Fin (M + 1))) :
    spinfulGeneralBasisState e SUp SDown ≠ 0 := by
  classical
  set g₀ : Fin (M + 1) × Fin 2 → Fin 2 :=
    fun q => if (q.2 = 0 ∧ q.1 ∈ SUp) ∨ (q.2 = 1 ∧ q.1 ∈ SDown) then 1 else 0 with hg₀
  have hg₀val : ∀ q, g₀ q = if (q.2 = 0 ∧ q.1 ∈ SUp) ∨ (q.2 = 1 ∧ q.1 ∈ SDown) then 1 else 0 :=
    fun q => rfl
  have hup : occUpSet g₀ = SUp := by
    ext j
    rw [occUpSet, Finset.mem_filter]
    constructor
    · rintro ⟨-, hj⟩
      by_contra hjn
      rw [hg₀val, if_neg (by rintro (⟨_, h⟩ | ⟨h, _⟩); exacts [hjn h, by simp at h])] at hj
      exact absurd hj (by decide)
    · intro hj
      exact ⟨Finset.mem_univ _, by rw [hg₀val (j, 0), if_pos (Or.inl ⟨rfl, hj⟩)]⟩
  have hdown : occDownSet g₀ = SDown := by
    ext j
    rw [occDownSet, Finset.mem_filter]
    constructor
    · rintro ⟨-, hj⟩
      by_contra hjn
      rw [hg₀val, if_neg (by rintro (⟨h, _⟩ | ⟨_, h⟩); exacts [by simp at h, hjn h])] at hj
      exact absurd hj (by decide)
    · intro hj
      exact ⟨Finset.mem_univ _, by rw [hg₀val (j, 1), if_pos (Or.inr ⟨rfl, hj⟩)]⟩
  obtain ⟨z, hz0, hz⟩ := generalOccMonomial_eq_smul_generalBasisState e g₀
  rw [hup, hdown] at hz
  intro hzero
  rw [hzero, smul_zero] at hz
  have hbcoe : (generalOccBasis e g₀ : (Fin (2 * M + 2) → Fin 2) → ℂ) = generalOccMonomial e g₀ :=
    congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ _ _) g₀
  have hne : generalOccMonomial e g₀ ≠ 0 := by
    rw [← hbcoe]; exact (generalOccBasis e).ne_zero g₀
  exact hne hz

/-- The self inner product is real: `⟨v, v⟩ = (Σ_i |v_i|² : ℝ)`. -/
theorem dotProduct_star_self_eq_ofReal {n : Type*} [Fintype n] (v : n → ℂ) :
    dotProduct (star v) v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def]
  push_cast
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_conj_mul_self]

/-- For a nonzero vector `v`, the squared norm `(⟨v, v⟩).re = Σ_i |v_i|²` is strictly positive. -/
theorem dotProduct_star_self_re_pos {n : Type*} [Fintype n] {v : n → ℂ} (hv : v ≠ 0) :
    0 < (dotProduct (star v) v).re := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hv
  rw [Pi.zero_apply] at hi₀
  rw [dotProduct_star_self_eq_ofReal, Complex.ofReal_re]
  refine Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _) ⟨i₀, Finset.mem_univ _, ?_⟩
  exact (Complex.normSq_pos).mpr hi₀

/-! ## The trial-state Rayleigh quotient -/

/-- **The on-site interaction scales linearly in `U`**: `Ĥ_int(U) = U • Ĥ_int(1)`. -/
theorem hubbardOnSiteInteraction_eq_smul (M : ℕ) (U : ℂ) :
    hubbardOnSiteInteraction M U = U • hubbardOnSiteInteraction M 1 := by
  rw [hubbardOnSiteInteraction, hubbardOnSiteInteraction, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, mul_one]

/-- **The energy of the eigenmode Slater state with one down electron** is bounded above by
`(kinetic energy) + U`.  For `0 ≤ U`, the spin-flipped trial state
`Ψ = spinfulGeneralBasisState e SUp SDown` with `|SDown| = 1` has Rayleigh quotient
`rayleighOnVec Ĥ Ψ ≤ (occupiedEigenEnergy).re · ‖Ψ‖² + U · ‖Ψ‖²` (kinetic exact, interaction
sandwiched by the single down electron). -/
theorem rayleighOnVec_hubbardHamiltonian_trial_le {M : ℕ}
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian)
    (SUp SDown : Finset (Fin (M + 1))) (hcard : SDown.card = 1) (U : ℝ) (hU : 0 ≤ U) :
    rayleighOnVec (hubbardHamiltonian M t (U : ℂ))
        (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown)
      ≤ (occupiedEigenEnergy hT SUp SDown).re *
          (dotProduct (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown))
            (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown)).re
        + U * (dotProduct (star (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown))
            (spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown)).re := by
  set Ψ := spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown with hΨ
  set nrm := (dotProduct (star Ψ) Ψ).re with hnrm
  -- kinetic energy is the scalar `occupiedEigenEnergy`
  have hkin : (hubbardKinetic M t).mulVec Ψ = occupiedEigenEnergy hT SUp SDown • Ψ :=
    hubbardKinetic_mulVec_spinfulGeneralBasisState hT SUp SDown
  -- down-number eigenvalue is `|SDown| = 1`
  have hdown : (fermionTotalDownNumber M).mulVec Ψ = ((SDown.card : ℕ) : ℂ) • Ψ :=
    fermionTotalDownNumber_mulVec_spinfulGeneralBasisState (eigenbasisAsBasis hT) SUp SDown
  -- split Ĥ = Ĥ_kin + Ĥ_int
  have hsplit : (hubbardHamiltonian M t (U : ℂ)).mulVec Ψ
      = (hubbardKinetic M t).mulVec Ψ + (hubbardOnSiteInteraction M (U : ℂ)).mulVec Ψ := by
    rw [hubbardHamiltonian, Matrix.add_mulVec]
  have hray : rayleighOnVec (hubbardHamiltonian M t (U : ℂ)) Ψ
      = (occupiedEigenEnergy hT SUp SDown).re * nrm
        + (dotProduct (star Ψ) ((hubbardOnSiteInteraction M (U : ℂ)).mulVec Ψ)).re := by
    unfold rayleighOnVec
    rw [hsplit, dotProduct_add, Complex.add_re, hkin, dotProduct_smul, smul_eq_mul,
      Complex.mul_re]
    have him : (dotProduct (star Ψ) Ψ).im = 0 := by
      rw [dotProduct_star_self_eq_ofReal, Complex.ofReal_im]
    rw [him, mul_zero, sub_zero, ← hnrm]
  -- interaction energy bound: `Re⟨Ψ,Ĥ_int(U)Ψ⟩ ≤ U·nrm`
  have hUscale : (hubbardOnSiteInteraction M (U : ℂ)).mulVec Ψ
      = (U : ℂ) • (hubbardOnSiteInteraction M 1).mulVec Ψ := by
    rw [hubbardOnSiteInteraction_eq_smul, Matrix.smul_mulVec]
  obtain ⟨_, hupper⟩ := hubbardOnSiteInteraction_rayleigh_bounds M Ψ
  have hdownE : (dotProduct (star Ψ) ((fermionTotalDownNumber M).mulVec Ψ)).re = nrm := by
    rw [hdown, hcard, dotProduct_smul, smul_eq_mul, Nat.cast_one, one_mul, ← hnrm]
  have hintBound : (dotProduct (star Ψ)
      ((hubbardOnSiteInteraction M (U : ℂ)).mulVec Ψ)).re ≤ U * nrm := by
    rw [hUscale, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    calc U * (dotProduct (star Ψ) ((hubbardOnSiteInteraction M 1).mulVec Ψ)).re
        ≤ U * (dotProduct (star Ψ) ((fermionTotalDownNumber M).mulVec Ψ)).re :=
          mul_le_mul_of_nonneg_left hupper hU
      _ = U * nrm := by rw [hdownE]
  rw [hray]
  linarith [hintBound]

end LatticeSystem.Fermion
