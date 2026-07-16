/-
The field-augmented left Hamiltonian and its symmetric-field Gibbs weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: Gaussian domination PR1).

Toward the Dyson–Lieb–Simon Gaussian-domination bound `Z_β(h) ≤ Z_β(0)` (Tasaki §4.1, uniform-field
bound (4.1.49), reflection bound (4.1.51), p. 86), the first infrastructure piece augments the
left-half DLS part `H_L` with a diagonal single-site field
`Σ_{x < n} (a x) · Ŝ_x^{(3)}`, still left-supported.  Feeding this into the ring crossing
decomposition `ringCrossingRPDecomposition` yields, for a field configuration `a` symmetric across
the reflection plane, the field-shifted Hamiltonian
`H_{sym} = Lfield(a) + θ(Lfield(a)) − crossing`.

This file records the field-augmented left Hamiltonian (`ringLeftFieldHamiltonian`) and its left
support, and the associated DLS decomposition (`ringFieldDLSDecomposition`).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionConcreteGibbs
import LatticeSystem.Quantum.SpinS.RingReflectionThetaInvariance

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Field-augmented left Hamiltonian.**  The left-half bond Hamiltonian `H_L` plus a diagonal
single-site field `Σ_{x < n} (a x) · Ŝ_x^{(3)}` over the left half `{0,…,n−1}`.  This is the
field-shifted left part `Lfield(a)` of the Dyson–Lieb–Simon decomposition of the staggered-field
antiferromagnet (Tasaki §4.1, field coupling (4.1.9) p. 76). -/
noncomputable def ringLeftFieldHamiltonian (n N : ℕ) (a : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  ringLeftHamiltonian n N
    + ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
        (a x : ℂ) • onSiteS x (spinSOp3 N)

/-- The field-augmented left Hamiltonian is left-supported: `H_L` is left-supported and each field
term `(a x) · Ŝ_x^{(3)}` lives at a left site `x < n`. -/
theorem ringLeftFieldHamiltonian_supportedOnLeft (n N : ℕ) (a : Fin (2 * n) → ℝ) :
    SupportedOnLeftS n N (ringLeftFieldHamiltonian n N a) := by
  refine ringLeftHamiltonian_supportedOnLeft.add (SupportedOnLeftS.sum _ _ (fun x hx => ?_))
  have hxn : (x : ℕ) < n := (Finset.mem_filter.mp hx).2
  exact (onSiteS_supportedOnLeft hxn _).smul _

/-- **Field-augmented DLS decomposition.**  The ring crossing reflection-positive decomposition with
the field-augmented left part `ringLeftFieldHamiltonian`; its reconstructed Hamiltonian is the
symmetric-field ring Hamiltonian `Lfield(a) + θ(Lfield(a)) − crossing`. -/
noncomputable def ringFieldDLSDecomposition (n N : ℕ) [NeZero n] (a : Fin (2 * n) → ℝ) :
    RPDecomposition n N :=
  ringCrossingRPDecomposition (ringLeftFieldHamiltonian n N a)
    (ringLeftFieldHamiltonian_supportedOnLeft n N a)

end LatticeSystem.Quantum
