/-
The two-field ("doubled") Gibbs weight and its Trotter-limit representation
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: Gaussian domination PR7b-i).

Toward the reflection Cauchy–Schwarz bound driving Dyson–Lieb–Simon Gaussian domination
(Tasaki §4.1, reflection bound (4.1.51), p. 86), the doubled weight decouples the two halves of the
symmetric-field Gibbs weight: it carries an INDEPENDENT left field `a` on the left half and an
independent field `b` transported to the right half by the reflection `θ`,

    `W(a,b) := exp(−β · (Lfield(a) + θ(Lfield(b)) − D))`,

with `Lfield = ringLeftFieldHamiltonian` the field-augmented left part and
`D = (ringFieldDLSDecomposition a).interaction` the field-free crossing interaction.  Because the
left part `Lfield(a)` (left-supported) and the right part `θ(Lfield(b))` commute (disjoint
supports), the kinetic factor splits by `exp_add_of_commute`, giving the Dyson–Lieb–Simon Trotter
approximant
`(E_G · θ(E_{G'}) · E_D)^m` whose limit is `W(a,b)`.

This file records the doubled weight (`ringTwoFieldWeight`).
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
field-free crossing interaction `D = (ringFieldDLSDecomposition a).interaction`. -/
noncomputable def ringTwoFieldWeight (n N : ℕ) [NeZero n] (β : ℝ) (a b : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  NormedSpace.exp (-(β : ℂ) • (ringLeftFieldHamiltonian n N a
    + ringReflectionThetaS n N (ringLeftFieldHamiltonian n N b)
    - (ringFieldDLSDecomposition n N a).interaction))

end LatticeSystem.Quantum
