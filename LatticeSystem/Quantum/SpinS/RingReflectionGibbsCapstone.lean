/-
Full Gibbs reflection positivity for a DLS decomposition (the Trotter capstone)
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 14).

For a reflection-positive decomposition `H = H_L + θ(H_L) − D` (`RPDecomposition`) and `β ≥ 0`, the
Gibbs weight `e^{-βH}` is a reflection-positive trace weight.  The proof is the Dyson–Lieb–Simon
Trotter assembly: write `e^{-βH} = e^{(A+B)}` with `A = -β·(H_L + θ(H_L))` and `B = β·D`, and use
the Lie product formula `e^{A+B} = lim_m (e^{A/m}·e^{B/m})^m`.  Each finite factor is consumed by an
accumulating RP trace weight: the kinetic factor `e^{A/m} = exp(Y + θ Y)` is cone-representable
(`coneRep_exp_add`, absorbed by `mul_coneRep_right`) and the interaction factor `e^{B/m}` is the
exponential of a cone-representable operator (absorbed by `mul_exp_coneRep_right`).  Induction over
the power and `RPTraceWeightS.tendsto` then give the result.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionKineticConeRep
import LatticeSystem.Quantum.SpinS.RingReflectionMulExpConeRep
import LatticeSystem.Quantum.SpinS.RingReflectionRPDecomposition
import LatticeSystem.Math.MatrixAnalysis.LieProduct

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped Matrix.Norms.Operator

variable {n N : ℕ}

/-- For a **real** scalar, scaling commutes with the `Z + θ(Z)` splitting:
`(c:ℂ)·(Z + θ Z) = (c·Z) + θ(c·Z)` (since `θ` conjugates the scalar and a real scalar is fixed). -/
theorem realSmul_add_theta (c : ℝ) (Z : ManyBodyOpS (Fin (2 * n)) N) :
    (c : ℂ) • (Z + ringReflectionThetaS n N Z)
      = (c : ℂ) • Z + ringReflectionThetaS n N ((c : ℂ) • Z) := by
  rw [smul_add, ringReflectionThetaS_smul, Complex.conj_ofReal]

/-- The interaction term of an RP decomposition is cone-representable. -/
theorem RPDecomposition.interaction_coneRep (D : RPDecomposition n N) :
    RPTraceConeRepS n N D.interaction := by
  refine ⟨D.bondιType, D.bondFintype, D.bondOp, fun _ => 1, D.bondSupported,
    fun _ => zero_le_one, ?_⟩
  letI := D.bondFintype
  rw [RPDecomposition.interaction]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Complex.ofReal_one, one_smul, (D.bondSupported b).mul_theta_comm (D.bondSupported b)]

/-- **Full Gibbs reflection positivity.**  For a reflection-positive decomposition and `β ≥ 0`, the
Gibbs weight `exp(-β · H)` is a reflection-positive trace weight. -/
theorem RPDecomposition.gibbs_rpTraceWeight (D : RPDecomposition n N) {β : ℝ} (hβ : 0 ≤ β) :
    RPTraceWeightS n N (NormedSpace.exp (-(β : ℂ) • D.toHamiltonian)) := by
  haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
    FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
  set A : ManyBodyOpS (Fin (2 * n)) N := -(β : ℂ) • (D.hLeft + ringReflectionThetaS n N D.hLeft)
    with hAdef
  set B : ManyBodyOpS (Fin (2 * n)) N := (β : ℂ) • D.interaction with hBdef
  -- the kinetic factor `e^{A/m}` is cone-representable
  have hAcone : ∀ m : ℕ, RPTraceConeRepS n N (NormedSpace.exp ((m : ℂ)⁻¹ • A)) := by
    intro m
    have hsc : (m : ℂ)⁻¹ • A
        = (((m : ℝ)⁻¹ * (-β) : ℝ) : ℂ) • (D.hLeft + ringReflectionThetaS n N D.hLeft) := by
      rw [hAdef, smul_smul]
      congr 1
      push_cast
      ring
    rw [hsc, realSmul_add_theta]
    exact coneRep_exp_add (D.hLeftSupported.smul _)
  -- the interaction factor `e^{B/m}` is the exponential of a cone-representable operator
  have hBcone : ∀ m : ℕ, RPTraceConeRepS n N ((m : ℂ)⁻¹ • B) := by
    intro m
    have hsc : (m : ℂ)⁻¹ • B = (((m : ℝ)⁻¹ * β : ℝ) : ℂ) • D.interaction := by
      rw [hBdef, smul_smul]
      congr 1
      push_cast
      ring
    rw [hsc]
    exact D.interaction_coneRep.smul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) hβ)
  -- one Trotter step preserves reflection positivity
  have hstep : ∀ (m : ℕ) (M : ManyBodyOpS (Fin (2 * n)) N), RPTraceWeightS n N M →
      RPTraceWeightS n N
        (M * (NormedSpace.exp ((m : ℂ)⁻¹ • A) * NormedSpace.exp ((m : ℂ)⁻¹ • B))) := by
    intro m M hM
    rw [← mul_assoc]
    exact (hM.mul_coneRep_right (hAcone m)).mul_exp_coneRep_right (hBcone m)
  -- the `m`-th Trotter approximant is a reflection-positive trace weight
  have hpow : ∀ m : ℕ, RPTraceWeightS n N
      ((NormedSpace.exp ((m : ℂ)⁻¹ • A) * NormedSpace.exp ((m : ℂ)⁻¹ • B)) ^ m) := by
    intro m
    suffices h : ∀ k, RPTraceWeightS n N
        ((NormedSpace.exp ((m : ℂ)⁻¹ • A) * NormedSpace.exp ((m : ℂ)⁻¹ • B)) ^ k) from h m
    intro k
    induction k with
    | zero => simpa using RPTraceWeightS.one
    | succ k ih => rw [pow_succ]; exact hstep m _ ih
  -- `A + B = -β·H`
  have hAB : A + B = -(β : ℂ) • D.toHamiltonian := by
    rw [hAdef, hBdef, RPDecomposition.toHamiltonian]
    module
  rw [← hAB]
  exact RPTraceWeightS.tendsto (fun m => hpow m) (LatticeSystem.Math.lieProductFormula A B)

end LatticeSystem.Quantum
