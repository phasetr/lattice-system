import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionicTranslation
import LatticeSystem.Fermion.JordanWigner.Hubbard.NonsingularLocalStability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Tasaki §11.4.2: spin-wave excitation energy bounds (Theorem 11.19)

This file completes §11.4.2: it defines the spin-wave excitation energy `E_SW(k)`
(Tasaki, p. 423) using the fermionic translation operator `τ̂_z` (eq. (11.4.30)) and the
total `Ŝ^z`, and states **Theorem 11.19** (two-sided bounds on the spin-wave dispersion)
as a documented `axiom`.

`E_SW(k)` is the smallest energy among normalised states `Φ` with
`Ŝ^z_tot Φ = (S_max − 1) Φ` and `τ̂_z Φ = e^{-ik·z} Φ` (crystal momentum `k`).  Here `d = 1`,
the lattice has `K+1` cells, the momentum is `k ∈ Fin (K+1)` with phase
`e^{-2πik/(K+1)}`, `S_max = (K+1)/2`, and `τ̂_z` is the unit-cell translation
`translationOperator K 1`.

**Theorem 11.19** then gives constants `ν₁, η₁, ξ₁, ξ₂` and `a₁,a₂,a₃,b₁,b₂,b₃ > 0`
(depending only on `d = 1` and the range `R`) such that, under the parameter conditions
(11.4.31)/(11.4.32), the dispersion `E_SW(k) − E_min(S_max)` is sandwiched between
`F₂·2ν⁴U(1−cos k)` and `F₁·2ν⁴U(1−cos k)` (eq. (11.4.33)), with `F₁, F₂` as in
(11.4.34)/(11.4.35).  Tasaki's perturbation-theory proof is deferred; this is a documented
axiom (Theorem 11.8 / 11.13 / 11.15 / 11.18 policy).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4.2, eqs. (11.4.30)–(11.4.35), Theorem 11.19 (pp. 423–424).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The crystal-momentum phase `e^{-2πik/(K+1)}` (the eigenvalue of the unit-cell
translation `τ̂` at momentum `k ∈ Fin (K+1)`). -/
noncomputable def momentumPhase (K : ℕ) (k : Fin (K + 1)) : ℂ :=
  Complex.exp (-(2 * Real.pi * (k.val : ℝ) / (K + 1)) * Complex.I)

/-- **The spin-wave excitation energy `E_SW(k)`** (Tasaki §11.4.2, p. 423): the smallest
energy of a normalised state in the once-flipped sector `Ŝ^z_tot = S_max − 1 = (K−1)/2`
that is also a crystal-momentum-`k` eigenstate of the translation operator
(`τ̂ Φ = e^{-2πik/(K+1)} Φ`).  The infimum of the energy `rayleighOnVec Ĥ` over that joint
eigenspace (L²-unit vectors). -/
noncomputable def spinWaveEnergy (K : ℕ) (H : ManyBodyOp (Fin (2 * (2 * K + 1) + 2)))
    (k : Fin (K + 1)) : ℝ :=
  ⨅ φ : {φ : EuclideanSpace ℂ (Fin (2 * (2 * K + 1) + 2) → Fin 2) //
      ‖φ‖ = 1 ∧
      (fermionTotalSpinZ (2 * K + 1)).mulVec φ.ofLp = (((K : ℂ) - 1) / 2) • φ.ofLp ∧
      (translationOperator K 1).mulVec φ.ofLp = momentumPhase K k • φ.ofLp},
    rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp

/-- **Tasaki Theorem 11.19 (bounds on the spin-wave excitation energy), AXIOM.**
There are constants `ν₁, η₁, ξ₁, ξ₂` and `a₁,…,b₃ > 0` (depending only on `d = 1` and the
range `R`, uniform in the system size) such that, for the non-singular Hubbard model with
`0 < ν ≤ ν₁`, `|ζ| ≤ ν² η₁`, `ξ₁ t |ζ| / ν² ≤ U ≤ ξ₂ t ν` (eqs. (11.4.31)/(11.4.32)), the
spin-wave dispersion is two-sided bounded (eq. (11.4.33)):
`F₁·2ν⁴U(1−cos k) ≥ E_SW(k) − E_min(S_max) ≥ F₂·2ν⁴U(1−cos k)`,
with `F₁ = 1 + a₁ν + a₂|ζ|/ν³ + a₃t|ζ|²/(ν⁴U)` and
`F₂ = 1 − b₁ν − b₂|ζ|/ν² − b₃t|ζ|²/(ν⁴U)` (eqs. (11.4.34)/(11.4.35)).  Proved by Tasaki
via rigorous perturbation theory; recorded here as a documented axiom. -/
axiom nonsingular_theorem_11_19 (R : ℝ) (hR : 0 < R) :
    ∃ ν1 η1 ξ1 ξ2 a1 a2 a3 b1 b2 b3 : ℝ,
      0 < ν1 ∧ 0 < η1 ∧ 0 < ξ1 ∧ 0 < ξ2 ∧
        0 < a1 ∧ 0 < a2 ∧ 0 < a3 ∧ 0 < b1 ∧ 0 < b2 ∧ 0 < b3 ∧
        ∀ (K : ℕ) (ν t ζ U : ℝ) (tPert : Fin (2 * K + 2) → Fin (2 * K + 2) → ℂ)
          (k : Fin (K + 1)),
          0 < t → 0 < ν → ν ≤ ν1 → |ζ| ≤ ν ^ 2 * η1 →
          ξ1 * t * |ζ| / ν ^ 2 ≤ U → U ≤ ξ2 * t * ν →
          IsNonsingularHopping K tPert t R →
          (let H := nonsingularHubbardHamiltonian K ν t ζ tPert U
           let θ : ℝ := 2 * Real.pi * (k.val : ℝ) / (K + 1)
           let F1 : ℝ := 1 + a1 * ν + a2 * |ζ| / ν ^ 3 + a3 * t * |ζ| ^ 2 / (ν ^ 4 * U)
           let F2 : ℝ := 1 - b1 * ν - b2 * |ζ| / ν ^ 2 - b3 * t * |ζ| ^ 2 / (ν ^ 4 * U)
           F1 * (2 * ν ^ 4 * U * (1 - Real.cos θ)) ≥
               spinWaveEnergy K H k - sectorMinEnergy H (K + 1) (K + 1) ∧
             spinWaveEnergy K H k - sectorMinEnergy H (K + 1) (K + 1) ≥
               F2 * (2 * ν ^ 4 * U * (1 - Real.cos θ)))

end LatticeSystem.Fermion
