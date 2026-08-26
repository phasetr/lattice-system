import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUTrial
import LatticeSystem.Math.RayleighPosSemidefKernel
import Mathlib.Analysis.Matrix.Order

/-!
# Operator bounds on the spin-resolved kinetic operator (Tasaki §11.1.1)

Two estimates on the spin fiber `Ĥ^σ` (`HubbardKineticSpin.lean`) that the low-density
impossibility argument uses in place of an exact evaluation of the minority-spin kinetic energy.

* **Loewner bound** `Ĥ^σ ≤ ε_max·N̂_σ` whenever every single-particle level satisfies `ε_j ≤ ε_max`:
  the difference `Σ_j (ε_max − ε_j) n̂_{j,σ}` is a nonnegative combination of the
  positive-semidefinite eigenmode number operators, whose sum is the spin-`σ` particle number by
  eigenbasis completeness.
* **Fully polarized kill** `Ĥ↓Φ = 0` when `N̂_↓Φ = 0`: the down-number operator is a sum of Gram
  matrices, so a kernel vector of the total is a kernel vector of every down annihilator.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.1.1, Theorem 11.4, eqs. (11.1.8)–(11.1.10), p. 376; the underlying argument is
Tasaki, Prog. Theor. Phys. **99** (1998) 489, Theorem 3.3, Appendix F, pp. 545–547.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

open scoped BigOperators ComplexOrder

variable {M : ℕ}

open scoped MatrixOrder in
/-- **The spin-`σ` kinetic fiber is bounded by the spin-`σ` particle number**: if every
single-particle level satisfies `ε_j ≤ e`, then `Ĥ^σ ≤ e·N̂_σ` in the Loewner order.  The
difference is `Σ_j (e − ε_j) n̂_{j,σ}`, a nonnegative combination of positive-semidefinite
eigenmode number operators. -/
theorem hubbardKineticSpin_le_smul_sum_spinSiteNumber
    {t : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ} (hT : t.IsHermitian) (σ : Fin 2) {e : ℝ}
    (he : ∀ j : Fin (M + 1), hT.eigenvalues j ≤ e) :
    hubbardKineticSpin M t σ
      ≤ (e : ℂ) • ∑ i : Fin (M + 1), fermionMultiNumber (2 * M + 1) (spinfulIndex M i σ) := by
  rw [Matrix.le_iff]
  have hdiff : ((e : ℂ) • ∑ i : Fin (M + 1), fermionMultiNumber (2 * M + 1) (spinfulIndex M i σ))
        - hubbardKineticSpin M t σ
      = ∑ j : Fin (M + 1), ((e - hT.eigenvalues j : ℝ) : ℂ) • eigenNumberOp hT j σ := by
    rw [← sum_eigenNumberOp_eq_sum_spinSiteNumber hT σ,
      hubbardKineticSpin_eq_sum_eigenNumberOp hT σ, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, Complex.ofReal_sub]
  rw [hdiff]
  refine Matrix.posSemidef_sum _ fun j _ => ?_
  exact (eigenNumberOp_posSemidef hT j σ).smul
    (Complex.zero_le_real.mpr (sub_nonneg.mpr (he j)))

/-- **No spin-down electrons ⇒ every down annihilation kills the state**: `N̂_↓Φ = 0` forces
`ĉ_{x↓}Φ = 0` at every site `x`.  The down-number operator is the sum of the positive-semidefinite
Gram matrices `ĉ†_{x↓}ĉ_{x↓}`, so a vanishing total energy expectation forces each term's
expectation, hence each `ĉ_{x↓}Φ`, to vanish. -/
theorem fermionDownAnnihilation_mulVec_eq_zero_of_downNumber_zero (M : ℕ) (x : Fin (M + 1))
    {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ} (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    (fermionDownAnnihilation M x).mulVec Φ = 0 := by
  have hgram : ∀ y : Fin (M + 1),
      (fermionDownAnnihilation M y)ᴴ * fermionDownAnnihilation M y = fermionDownNumber M y := by
    intro y
    rw [fermionDownAnnihilation, fermionMultiAnnihilation_conjTranspose, fermionDownNumber,
      fermionMultiNumber]
  have hpsd : ∀ y : Fin (M + 1), (fermionDownNumber M y).PosSemidef := by
    intro y
    rw [← hgram y]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hray : rayleighOnVec (∑ y : Fin (M + 1), fermionDownNumber M y) Φ = 0 := by
    rw [← fermionTotalDownNumber, rayleighOnVec, hΦ, dotProduct_zero, Complex.zero_re]
  rw [rayleighOnVec_sum] at hray
  have hterm : rayleighOnVec (fermionDownNumber M x) Φ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y _ => (hpsd y).re_dotProduct_nonneg Φ)).mp hray x (Finset.mem_univ x)
  have hnum : (fermionDownNumber M x).mulVec Φ = 0 :=
    posSemidef_mulVec_eq_zero_of_rayleighOnVec_zero (hpsd x) hterm
  rw [← hgram x] at hnum
  exact conjTranspose_mul_self_mulVec_eq_zero hnum

/-- **The spin-down kinetic fiber annihilates the fully polarized sector**: `N̂_↓Φ = 0` implies
`Ĥ↓Φ = 0`, since every hopping term of `Ĥ↓` ends in a down annihilation. -/
theorem hubbardKineticSpin_one_mulVec_eq_zero_of_downNumber_zero (M : ℕ)
    (t : Fin (M + 1) → Fin (M + 1) → ℂ) {Φ : (Fin (2 * M + 2) → Fin 2) → ℂ}
    (hΦ : (fermionTotalDownNumber M).mulVec Φ = 0) :
    (hubbardKineticSpin M t 1).mulVec Φ = 0 := by
  rw [hubbardKineticSpin, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    show fermionMultiAnnihilation (2 * M + 1) (spinfulIndex M j 1) = fermionDownAnnihilation M j
      from rfl,
    fermionDownAnnihilation_mulVec_eq_zero_of_downNumber_zero M j hΦ, Matrix.mulVec_zero,
    smul_zero]

end LatticeSystem.Fermion
