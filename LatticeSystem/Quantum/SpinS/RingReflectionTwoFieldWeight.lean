/-
The two-field ("doubled") Gibbs weight and its Trotter-limit representation
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: Gaussian domination PR7b-i).

Toward the reflection Cauchy–Schwarz bound driving Dyson–Lieb–Simon Gaussian domination
(Tasaki §4.1, reflection bound (4.1.51), p. 86), the doubled weight decouples the two halves of the
symmetric-field Gibbs weight: it carries an INDEPENDENT left field `a` on the left half and an
independent field `b` transported to the right half by the reflection `θ`,

    `W(a,b) := exp(−β · (Lfield(a) + θ(Lfield(b)) − D))`,

with `Lfield = ringLeftFieldHamiltonian` the field-augmented left part and
`D = (ringFieldDLSDecomposition a).interaction` the field-free crossing interaction.  The diagonal
`W(a,a)` recovers the symmetric-field weight `ringDLSFieldWeightSym` of PR7a.  Because the left part
`Lfield(a)` (left-supported) and the right part `θ(Lfield(b))` commute (disjoint supports), the
kinetic factor splits by `exp_add_of_commute`, giving the Dyson–Lieb–Simon Trotter approximant
`(E_G · θ(E_{G'}) · E_D)^m` whose limit is `W(a,b)`.

This file records the doubled weight (`ringTwoFieldWeight`), its diagonal specialisation to the
symmetric-field weight (`ringTwoFieldWeight_self`), and the Lie-product Trotter-limit representation
(`ringTwoFieldWeight_isLimit`).  The later reflection Cauchy–Schwarz PR (PR7b-iii) consumes the
Trotter representation to expand the crossing factor into its nonnegative cone form.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionFieldWeight
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsCapstone

namespace LatticeSystem.Quantum

open Matrix Filter Topology

open scoped Matrix.Norms.Operator

variable {n N : ℕ}

/-- **Two-field ("doubled") Gibbs weight.**  The weight `exp(−β · Ĥ_{a,b})` of the doubled
Hamiltonian `Ĥ_{a,b} = Lfield(a) + θ(Lfield(b)) − D`, carrying an independent left field `a` on the
left half and an independent field `b` transported to the right half by the reflection `θ`, over the
field-free crossing interaction `D = (ringFieldDLSDecomposition a).interaction`.  For `a = b` it
reduces to the symmetric-field weight `ringDLSFieldWeightSym`. -/
noncomputable def ringTwoFieldWeight (n N : ℕ) [NeZero n] (β : ℝ) (a b : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  NormedSpace.exp (-(β : ℂ) • (ringLeftFieldHamiltonian n N a
    + ringReflectionThetaS n N (ringLeftFieldHamiltonian n N b)
    - (ringFieldDLSDecomposition n N a).interaction))

/-- **Diagonal specialisation.**  With the same field `a` on both halves the doubled weight is the
symmetric-field weight of PR7a: `W(a,a) = ringDLSFieldWeightSym a`.  Indeed the doubled Hamiltonian
`Lfield(a) + θ(Lfield(a)) − D` is exactly `(ringFieldDLSDecomposition a).toHamiltonian`. -/
theorem ringTwoFieldWeight_self (n N : ℕ) [NeZero n] (β : ℝ) (a : Fin (2 * n) → ℝ) :
    ringTwoFieldWeight n N β a a = ringDLSFieldWeightSym n N β a := by
  rw [ringTwoFieldWeight, ringDLSFieldWeightSym, RPDecomposition.toHamiltonian]
  rfl

/-- **Trotter-limit representation of the doubled weight.**  The doubled weight `W(a,b)` is the
Lie-product limit of the Dyson–Lieb–Simon approximant `(E_G · θ(E_{G'}) · E_D)^m` with kinetic
factors `E_G = exp(−(β/m)·Lfield(a))`, `θ(E_{G'}) = θ(exp(−(β/m)·Lfield(b)))` and crossing factor
`E_D = exp((β/m)·D)`.  The left factor `E_G` and the right factor `θ(E_{G'})` commute (disjoint
supports), so their product is `exp(−(β/m)·(Lfield(a) + θ(Lfield(b))))`, and the two-factor Lie
product formula `lieProductFormula` applies. -/
theorem ringTwoFieldWeight_isLimit (n N : ℕ) [NeZero n] (β : ℝ) (a b : Fin (2 * n) → ℝ) :
    Tendsto (fun m : ℕ =>
        (NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringLeftFieldHamiltonian n N a))
          * ringReflectionThetaS n N
              (NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringLeftFieldHamiltonian n N b)))
          * NormedSpace.exp ((m : ℂ)⁻¹
              • ((β : ℂ) • (ringFieldDLSDecomposition n N a).interaction))) ^ m)
      atTop (𝓝 (ringTwoFieldWeight n N β a b)) := by
  set A : ManyBodyOpS (Fin (2 * n)) N := -(β : ℂ) • (ringLeftFieldHamiltonian n N a
    + ringReflectionThetaS n N (ringLeftFieldHamiltonian n N b)) with hA
  set B : ManyBodyOpS (Fin (2 * n)) N := (β : ℂ) • (ringFieldDLSDecomposition n N a).interaction
    with hB
  -- the commuting left/right kinetic factors merge into `exp((1/m)·A)`
  have hkin : ∀ m : ℕ,
      NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringLeftFieldHamiltonian n N a))
        * ringReflectionThetaS n N
            (NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringLeftFieldHamiltonian n N b)))
        = NormedSpace.exp ((m : ℂ)⁻¹ • A) := by
    intro m
    rw [ringReflectionThetaS_exp_mul_theta_exp
        (((ringLeftFieldHamiltonian_supportedOnLeft n N a).smul _).smul _)
        (((ringLeftFieldHamiltonian_supportedOnLeft n N b).smul _).smul _)]
    congr 1
    rw [ringReflectionThetaS_smul, ringReflectionThetaS_smul, hA, smul_add, smul_add]
    simp only [map_neg, Complex.conj_ofReal, map_inv₀, Complex.conj_natCast]
  -- the doubled weight is `exp(A + B)`
  have hexp : ringTwoFieldWeight n N β a b = NormedSpace.exp (A + B) := by
    rw [ringTwoFieldWeight, hA, hB]
    congr 1
    module
  rw [hexp]
  refine (LatticeSystem.Math.lieProductFormula A B).congr (fun m => ?_)
  rw [hkin m]

end LatticeSystem.Quantum
