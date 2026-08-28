import LatticeSystem.Math.Analysis.FiniteExponentialWeightIntegral
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation
import LatticeSystem.Quantum.SpinS.SaturatedCoherentWeight

/-!
# Projecting the saturated-ferromagnet coherent state onto a magnetisation sector

The azimuthal angle `φ` enters the saturated-ferromagnet coherent state `Ξ_{θ,φ}` only through the
diagonal phase `e^{-iφM(σ)}` of the global rotation about axis 3, so the sector expansion of
`Ξ_{θ,φ}` is the expansion of `Ξ_{θ,0}` with each term modulated by the character of its own
magnetisation.  Integrating against the conjugate character `e^{iMφ}` over one full period
therefore keeps a single sector and returns `2π c_M Φ_M`; dividing by the (nonzero) factor
`2π c_M` expresses `Φ_M` through the coherent states alone.

The module proves the pointwise phase factorisation, the general-`φ` sector expansion, and the
resulting projection formula.  The period integral is handled by the source-independent character
orthogonality of `LatticeSystem.Math.integral_exp_int_weight_smul_sum`, applied with the integer
weights `k` labelling the sectors: only the differences of magnetisations occur in the exponent, and
those are integers even when the magnetisations themselves are half-integers.  The Bochner integral
runs in `EuclideanSpace ℂ (V → Fin (N + 1))`, while the raw function type `(V → Fin (N + 1)) → ℂ`
stays the working type for the pointwise arguments.

References: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020.
This is Problem 2.4.b (statement p. 34, solution pp. 496-497), whose solution is eq. (S.17),
p. 497.  The normalised sector state `Φ_M` is eq. (2.4.9), p. 33, its expansion coefficients come
from Theorem 2.1 / eq. (2.4.10), p. 34, the coherent state `Ξ_{θ,φ}` is eq. (2.4.6), p. 33, and the
global rotations are eq. (2.2.11), p. 22.
-/

namespace LatticeSystem.Quantum

-- `SaturatedFullLadderOrthogonality` declares a `Matrix.…` theorem inside this namespace, so the
-- unqualified name `Matrix` resolves to `LatticeSystem.Quantum.Matrix` and the scoped `*ᵥ`
-- notation fails to parse; the root namespace has to be opened explicitly.
open _root_.Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## The azimuthal phase -/

/-- The global rotation about axis 3, `Û_φ^{(3)} = exp(-iφ Ŝ_tot^{(3)})` of Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, eq. (2.2.11), p. 22, is diagonal with entries
`e^{-iφM(σ)}`, since `Ŝ_tot^{(3)}` is diagonal with entries `M(σ)`. -/
private lemma saturatedGlobalRot3_eq_diagonal (φ : ℝ) :
    saturatedGlobalRot3 V N φ
      = Matrix.diagonal (fun σ : V → Fin (N + 1) =>
          Complex.exp (-((φ : ℂ) * Complex.I) * magEigenvalueS σ)) := by
  rw [saturatedGlobalRot3, show (φ : ℝ) • ((-Complex.I) • totalSpinSOp3 V N : ManyBodyOpS V N)
      = (-((φ : ℂ) * Complex.I)) • totalSpinSOp3 V N by
    ext i j; simp [Complex.real_smul]; ring]
  simp only [Complex.exp_eq_exp_ℂ]
  exact exp_smul_totalSpinSOp3_eq_diagonal φ

/-- The coherent state at azimuthal angle `φ` is the axis-3 rotation of the coherent state at
`φ = 0`, because the two rotations of Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, eq. (2.4.6), p. 33, are applied in that order. -/
private lemma saturatedCoherentState_eq_globalRot3_mulVec (θ φ : ℝ) :
    saturatedCoherentState V N θ φ
      = saturatedGlobalRot3 V N φ *ᵥ saturatedCoherentState V N θ 0 := by
  rw [saturatedCoherentState_zero_eq_globalRot2, saturatedCoherentState, Matrix.mulVec_mulVec]

/-- **Azimuthal phase factorisation** `Ξ_{θ,φ}(σ) = e^{-iφM(σ)} Ξ_{θ,0}(σ)`: the whole `φ`
dependence of the coherent state of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
eq. (2.4.6), p. 33, is the configuration-wise magnetisation phase.  This is the general-`S` form of
the per-site phases displayed in eq. (S.18), p. 497. -/
theorem saturatedCoherentState_apply_phase (θ φ : ℝ) (σ : V → Fin (N + 1)) :
    saturatedCoherentState V N θ φ σ
      = Complex.exp (-((φ : ℂ) * Complex.I) * magEigenvalueS σ)
          * saturatedCoherentState V N θ 0 σ := by
  rw [saturatedCoherentState_eq_globalRot3_mulVec, saturatedGlobalRot3_eq_diagonal,
    Matrix.mulVec_diagonal]

/-! ## The sector expansion at a general azimuthal angle -/

/-- **Sector expansion at a general `φ`**: `Ξ_{θ,φ} = Σ_M e^{-iφM} c_M(θ) Φ_M`, the middle member
of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, eq. (S.17), p. 497.

Each sector state is supported on the configurations of its own magnetisation, so the phase
`e^{-iφM(σ)}` produced by the axis-3 rotation is constant on the support of the `M`-th term and can
be absorbed into that term's coefficient; off every support both sides vanish. -/
theorem saturatedCoherentState_eq_sum [Nonempty V] (θ φ : ℝ) :
    saturatedCoherentState V N θ φ
      = ∑ k, (Complex.exp (-((φ : ℂ) * Complex.I) * ladderEigenvalueUp V N k)
          * saturatedCoherentCoeff V N θ k) • saturatedWeightVector V N k := by
  funext σ
  rw [saturatedCoherentState_apply_phase, congrFun (saturatedCoherentState_zero_eq_sum θ) σ,
    Finset.sum_apply, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : magEigenvalueS σ = ladderEigenvalueUp V N j
  · rw [h, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
  · rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, saturatedWeightVector,
      Pi.smul_apply, smul_eq_mul,
      ladderIterateUp_apply_eq_zero_of_magEigenvalueS_ne j h, mul_zero, mul_zero, mul_zero,
      mul_zero]

/-! ## The projection formula -/

/-- **Tasaki Problem 2.4.b** (statement p. 34, solution pp. 496-497), *Physics and Mathematics of
Quantum Many-Body Systems*: for `0 < θ < π` and every magnetisation sector `M = |Λ|S - k`, the
coefficient `c_M(θ)` is nonzero, the period integral of the coherent states against the character
`e^{iMφ}` is `2π c_M(θ) Φ_M` (eq. (S.17), p. 497), and consequently the sector state `Φ_M` of
eq. (2.4.9), p. 33, is expressed through the coherent states `Ξ_{θ,φ}` of eq. (2.4.6), p. 33, alone
as `(2π c_M(θ))⁻¹ ∫₀^{2π} dφ e^{iMφ} Ξ_{θ,φ}` — the answer to the problem as posed.

The expansion of `Ξ_{θ,φ}` turns the integrand into a finite sum of sector states modulated by the
characters of the integer weight differences `k' - k`, so character orthogonality over one period
keeps exactly the `k`-th term.  Nonvanishing of `c_M(θ)` is what makes the final division legal. -/
theorem tasaki_problem_2_4_b_phase_projection [Nonempty V] {θ : ℝ}
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
                  EuclideanSpace ℂ (V → Fin (N + 1))) := by
  have hc : saturatedCoherentCoeff V N θ k ≠ 0 := saturatedCoherentCoeff_ne_zero hθ₀ hθπ k
  have hpoint : ∀ φ : ℝ,
      Complex.exp (Complex.I * ladderEigenvalueUp V N k * (φ : ℂ)) •
          (WithLp.toLp 2 (saturatedCoherentState V N θ φ) :
            EuclideanSpace ℂ (V → Fin (N + 1)))
        = ∑ j : Fin (Fintype.card V * N + 1),
            Complex.exp (((((j : ℕ) : ℤ) : ℂ) - ((((k : ℕ) : ℤ)) : ℂ)) * Complex.I * (φ : ℂ)) •
            (saturatedCoherentCoeff V N θ j •
              (WithLp.toLp 2 (saturatedWeightVector V N j) :
                EuclideanSpace ℂ (V → Fin (N + 1)))) := by
    intro φ
    rw [saturatedCoherentState_eq_sum, WithLp.toLp_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [WithLp.toLp_smul, smul_smul, smul_smul]
    congr 1
    rw [← mul_assoc, ← Complex.exp_add]
    congr 1
    unfold ladderEigenvalueUp
    push_cast
    ring_nf
  have hS17 : (∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (Complex.I * ladderEigenvalueUp V N k * (φ : ℂ)) •
        (WithLp.toLp 2 (saturatedCoherentState V N θ φ) :
          EuclideanSpace ℂ (V → Fin (N + 1))))
      = ((2 * Real.pi : ℝ) : ℂ) • (saturatedCoherentCoeff V N θ k •
          (WithLp.toLp 2 (saturatedWeightVector V N k) :
            EuclideanSpace ℂ (V → Fin (N + 1)))) := by
    refine Eq.trans (congrArg
      (fun f => intervalIntegral f 0 (2 * Real.pi) MeasureTheory.volume) (funext hpoint)) ?_
    exact Math.integral_exp_int_weight_smul_sum
      (fun j : Fin (Fintype.card V * N + 1) => ((j : ℕ) : ℤ))
      (fun j => saturatedCoherentCoeff V N θ j •
        (WithLp.toLp 2 (saturatedWeightVector V N j) :
          EuclideanSpace ℂ (V → Fin (N + 1)))) k
      (fun j h => Fin.ext (by
        have h' : ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) := h
        exact_mod_cast h'))
  refine ⟨hc, hS17, ?_⟩
  rw [hS17, smul_smul, smul_smul,
    show (((2 * Real.pi : ℝ) : ℂ) * saturatedCoherentCoeff V N θ k)⁻¹ * ((2 * Real.pi : ℝ) : ℂ)
        * saturatedCoherentCoeff V N θ k = 1 from by
      have h2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      field_simp,
    one_smul]

end LatticeSystem.Quantum
