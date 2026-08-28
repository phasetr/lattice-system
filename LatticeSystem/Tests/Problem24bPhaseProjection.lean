import LatticeSystem.Quantum.SpinS.SaturatedCoherentProjection
import LatticeSystem.Quantum.SpinS.SaturatedCoherentWeight
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Test coverage for Tasaki Problem 2.4.b — `φ`-phase orientation and the capstone

Fixtures for the completion of Problem 2.4.b (Tasaki, *Physics and Mathematics
of Quantum Many-Body Systems*, statement p. 34, solution pp. 496-497, eq. (S.17)): the pointwise
`φ`-phase of the coherent state `Ξ_{θ,φ}` (the `S = 1/2` instance of (S.18), solution p. 497), the
`2π`-normalisation of the finite Fourier-weight integral, and the capstone equality
`∫₀^{2π} dφ e^{iMφ} Ξ_{θ,φ} = 2π c_M Φ_M`, solved for `Φ_M = (2π c_M)⁻¹ ∫₀^{2π} dφ e^{iMφ} Ξ_{θ,φ}`.

The fixtures pin the `φ`-phase sign, the `θ = 0` and `‖Φ_M‖ = 1` sharpness facts, the `N = 2`
binomial amplitude, the capstone's exact hypothesis set (`tasaki_problem_2_4_b_phase_projection`,
which quantifies the Fourier weight `M` via `ladderEigenvalueUp` from `SaturatedFullLadderLI.lean`),
and the `2π`-normalisation of the underlying finite Fourier-weight lemma.

The conjugation direction of `inner` inside `saturatedCoherentCoeff` (`Φ_M` first argument) is
**not pinned** here: at `φ = 0` both `Φ_M` and `Ξ_{θ,0}` have real entries, so swapping the two
`inner` arguments returns the same complex number, and `saturatedCoherentState_zero_eq_sum` already
pins `c_M` rigidly as the unique expansion coefficient. A fixture that pinned the swap would not
fail if the definition were swapped, so it would be a fail-open pin; the load-bearing, observable
orientation is instead the `φ`-phase sign pinned by the fixtures below.
-/

namespace LatticeSystem.Tests.Problem24bPhaseProjection

open LatticeSystem.Quantum

/-! ## `φ`-phase orientation, `|Λ| = 1`, `N = 1` -/

/-- **Up-configuration phase orientation.** At the single up-site configuration, the `φ`-rotated
coherent state carries the phase `e^{-iφ/2}` (not `e^{+iφ/2}`) on the `cos(θ/2)` amplitude — the
sign fixed by the repo's `magEigenvalueS` convention and matching (S.18) as printed. This is the
fixture whose sign is load-bearing: flipping it in `saturatedCoherentState_apply_phase` makes this
example fail to close. -/
example (θ φ : ℝ) :
    saturatedCoherentState (Fin 1) 1 θ φ (fun _ => 0)
      = Complex.exp (-((φ : ℂ) * Complex.I) / 2) * Complex.cos (θ / 2) := by
  rw [saturatedCoherentState_apply_phase, saturatedCoherentState_zero_apply]
  simp [magEigenvalueS, magSumS, saturatedCoherentAmp]
  ring_nf
  exact Or.inl trivial

/-- **Down-configuration phase orientation.** At the single down-site configuration, the phase is
`e^{+iφ/2}` on the `sin(θ/2)` amplitude — the opposite sign from the up configuration, as (S.18)
requires. -/
example (θ φ : ℝ) :
    saturatedCoherentState (Fin 1) 1 θ φ (fun _ => 1)
      = Complex.exp ((φ : ℂ) * Complex.I / 2) * Complex.sin (θ / 2) := by
  rw [saturatedCoherentState_apply_phase, saturatedCoherentState_zero_apply]
  simp [magEigenvalueS, magSumS, saturatedCoherentAmp]
  ring_nf
  exact Or.inl trivial

/-! ## `θ = 0` necessity of the nonvanishing hypothesis -/

/-- **Sharpness of `0 < θ`.** At `θ = 0` the coherent state collapses to the all-up state, so
every non-maximal weight-sector coefficient vanishes: the strict lower bound on `θ` in
`saturatedCoherentCoeff_ne_zero` (and hence in the capstone) is not a decorative hypothesis. -/
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {N : ℕ}
    (k : Fin (Fintype.card V * N + 1)) (hk : k ≠ 0) :
    saturatedCoherentCoeff V N 0 k = 0 := by
  classical
  have h0 : saturatedCoherentState V N 0 0 = allAlignedStateS V N 0 := by
    rw [saturatedCoherentState_zero_eq_globalRot2, saturatedGlobalRot2,
      show (0 : ℝ) • ((-Complex.I) • totalSpinSOp2 V N : ManyBodyOpS V N) = 0 from zero_smul _ _,
      NormedSpace.exp_zero, Matrix.one_mulVec]
  have htop : saturatedWeightVector V N k (allAlignedConfigS V N 0) = 0 := by
    have hmag : magEigenvalueS (allAlignedConfigS V N (0 : Fin (N + 1)))
        ≠ ladderEigenvalueUp V N k := by
      have h1 : magEigenvalueS (allAlignedConfigS V N (0 : Fin (N + 1)))
          = ladderEigenvalueUp V N 0 := by
        simp [magEigenvalueS, magSumS, allAlignedConfigS, ladderEigenvalueUp]
      rw [h1]
      exact fun h => hk (ladderEigenvalueUp_injective h).symm
    rw [saturatedWeightVector, Pi.smul_apply,
      ladderIterateUp_apply_eq_zero_of_magEigenvalueS_ne k hmag, smul_zero]
  rw [saturatedCoherentCoeff, h0, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, allAlignedStateS, basisVecS_apply, htop]

/-! ## `‖Φ_M‖ = 1` -/

/-- **Normalisation of the weight vector.** `Φ_M` (eq. (2.4.9), p. 33) is unit-normalised in the
`ℓ²` (`EuclideanSpace`) norm, not merely nonzero. This is checked as a fixture rather than exposed
as a library lemma, since nothing in the capstone's statement needs the normalisation itself. -/
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {N : ℕ}
    (k : Fin (Fintype.card V * N + 1)) :
    ‖(WithLp.toLp 2 (saturatedWeightVector V N k) : EuclideanSpace ℂ (V → Fin (N + 1)))‖ = 1 := by
  have hnn : 0 ≤ saturatedLadderNorm V N k := norm_nonneg _
  rw [saturatedWeightVector, WithLp.toLp_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hnn, ← saturatedLadderNorm]
  exact inv_mul_cancel₀ (saturatedLadderNorm_ne_zero k)

/-! ## Binomial weight at `N = 2` (`S = 1`) -/

/-- **`N = 2` coherent-state amplitude.** At `|Λ| = 1`, `N = 2`, the middle configuration's
amplitude carries the binomial factor `√(binom 2 1) = √2`, which is invisible at every existing
`N = 1` fixture (`binom 1 j = 1` there). -/
example (θ : ℝ) :
    saturatedCoherentState (Fin 1) 2 θ 0 (fun _ => 1)
      = (Real.sqrt 2 : ℂ) * Complex.cos (θ / 2) * Complex.sin (θ / 2) := by
  rw [saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-! ## Capstone signature pin and anti-vacuity -/

/-- **Capstone signature pin.** The Problem 2.4.b capstone
(`tasaki_problem_2_4_b_phase_projection`) takes exactly `[Fintype V] [DecidableEq V] [Nonempty V]`,
`0 < θ`, `θ < π`, and a weight index `k` — no expansion hypothesis, no coefficient-nonzero
hypothesis (both are re-derived internally), and no further typeclass beyond these three. Supplying
an instance the capstone does not need would let this pin accept a strengthened hypothesis set. -/
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {N : ℕ} {θ : ℝ}
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (k : Fin (Fintype.card V * N + 1)) :
    saturatedCoherentCoeff V N θ k ≠ 0 ∧
      (∫ φ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (Complex.I * ladderEigenvalueUp V N k * (φ : ℂ)) •
            (WithLp.toLp 2 (saturatedCoherentState V N θ φ) :
              EuclideanSpace ℂ (V → Fin (N + 1))))
        = ((2 * Real.pi : ℝ) : ℂ) • (saturatedCoherentCoeff V N θ k •
            (WithLp.toLp 2 (saturatedWeightVector V N k) :
              EuclideanSpace ℂ (V → Fin (N + 1)))) ∧
      (WithLp.toLp 2 (saturatedWeightVector V N k) : EuclideanSpace ℂ (V → Fin (N + 1)))
        = (((2 * Real.pi : ℝ) : ℂ) * saturatedCoherentCoeff V N θ k)⁻¹ •
            ∫ φ in (0 : ℝ)..(2 * Real.pi),
              Complex.exp (Complex.I * ladderEigenvalueUp V N k * (φ : ℂ)) •
                (WithLp.toLp 2 (saturatedCoherentState V N θ φ) :
                  EuclideanSpace ℂ (V → Fin (N + 1))) :=
  tasaki_problem_2_4_b_phase_projection hθ₀ hθπ k

/-- **Anti-vacuity.** The capstone's hypothesis set is satisfiable: at `|Λ| = 2`, `N = 1`,
`θ = π/2`, `k = 1`, it yields a concrete nonzero coefficient. Excludes a vacuous hypothesis set
mechanically. -/
example : saturatedCoherentCoeff (Fin 2) 1 (Real.pi / 2) 1 ≠ 0 :=
  (tasaki_problem_2_4_b_phase_projection (V := Fin 2) (N := 1)
    (by positivity) (by linarith [Real.pi_pos]) 1).1

/-! ## `2π` normalisation of the finite Fourier-weight lemma -/

/-- **`2π`, not `π` and not `(2π)⁻¹`.** A two-term instance of the finite Fourier-weight integral
lemma, exercising both the matching-weight branch (`j = 0`) and the distinct-weight
branch (`j = 1`) of the underlying character sum. -/
example (v : Fin 2 → ℂ) :
    (∫ φ in (0 : ℝ)..(2 * Real.pi),
        ∑ j : Fin 2, Complex.exp (((((![(0 : ℤ), 1] j) : ℤ) : ℂ)
          - ((((![(0 : ℤ), 1] (0 : Fin 2))) : ℤ) : ℂ)) * Complex.I * (φ : ℂ)) • v j)
      = ((2 * Real.pi : ℝ) : ℂ) • v 0 :=
  Math.integral_exp_int_weight_smul_sum ![(0 : ℤ), 1] v 0 (by decide)

end LatticeSystem.Tests.Problem24bPhaseProjection
