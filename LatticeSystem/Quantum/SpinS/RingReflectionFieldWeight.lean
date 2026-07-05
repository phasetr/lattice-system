/-
The field-augmented left Hamiltonian and its symmetric-field Gibbs weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: Gaussian domination PR1).

Toward the Dyson–Lieb–Simon Gaussian-domination bound `Z_β(h) ≤ Z_β(0)` (Tasaki §4.1, uniform-field
bound (4.1.49), reflection bound (4.1.51), p. 86), the first infrastructure piece augments the
left-half DLS part `H_L` with a diagonal single-site field
`Σ_{x < n} (a x) · Ŝ_x^{(3)}`, still left-supported.  Feeding this into the ring crossing
decomposition `ringCrossingRPDecomposition` yields, for a field configuration `a` symmetric across
the reflection plane, the field-shifted Hamiltonian
`H_{sym} = Lfield(a) + θ(Lfield(a)) − crossing`; its Gibbs weight `exp(−β·H_{sym})` is again a
reflection-positive trace weight and is reflection invariant.  This symmetric-field weight is the
Fourier-insertion target consumed by the later Gaussian-domination PRs.

This file records the field-augmented left Hamiltonian (`ringLeftFieldHamiltonian`) and its left
support, the associated DLS decomposition (`ringFieldDLSDecomposition`), the symmetric-field Gibbs
weight (`ringDLSFieldWeightSym`) with its reflection-positive trace-weight property and its
reflection invariance.
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

/-- **The field-augmented DLS Hamiltonian is reflection invariant**: `θ(toHamiltonian) =
toHamiltonian`.  The `Lfield + θ(Lfield)` part is swapped to itself by the involution `θ` and each
crossing-bond interaction is `θ`-fixed. -/
theorem ringReflectionThetaS_ringFieldDLSDecomposition_toHamiltonian (n N : ℕ) [NeZero n]
    (a : Fin (2 * n) → ℝ) :
    ringReflectionThetaS n N (ringFieldDLSDecomposition n N a).toHamiltonian
      = (ringFieldDLSDecomposition n N a).toHamiltonian := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [ringFieldDLSDecomposition, ringCrossingRPDecomposition_toHamiltonian,
    ringReflectionThetaS_sub, ringReflectionThetaS_add, ringReflectionThetaS_involutive n N,
    ringReflectionThetaS_add,
    ringReflectionThetaS_crossBondInteractionS (by rw [ringCrossingSite_zero_val]; exact hn),
    ringReflectionThetaS_crossBondInteractionS (by rw [ringCrossingSite_one_val]; omega),
    add_comm (ringReflectionThetaS n N (ringLeftFieldHamiltonian n N a))
      (ringLeftFieldHamiltonian n N a)]

/-- **Symmetric-field Gibbs weight** `exp(−β · H_{sym})` with `H_{sym} =
(ringFieldDLSDecomposition a).toHamiltonian` the symmetric-field ring Hamiltonian.  This is the
finite-β field-shifted weight whose reflection positivity drives Gaussian domination. -/
noncomputable def ringDLSFieldWeightSym (n N : ℕ) [NeZero n] (β : ℝ) (a : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  NormedSpace.exp (-(β : ℂ) • (ringFieldDLSDecomposition n N a).toHamiltonian)

/-- **The symmetric-field weight is a reflection-positive trace weight** (for `β ≥ 0`), directly by
the Gibbs capstone `RPDecomposition.gibbs_rpTraceWeight` applied to the field-augmented
decomposition. -/
theorem ringDLSFieldWeightSym_rpTraceWeight (n N : ℕ) [NeZero n] {β : ℝ} (hβ : 0 ≤ β)
    (a : Fin (2 * n) → ℝ) : RPTraceWeightS n N (ringDLSFieldWeightSym n N β a) :=
  (ringFieldDLSDecomposition n N a).gibbs_rpTraceWeight hβ

/-- **The symmetric-field weight is reflection invariant**: `θ(exp(−β·H_{sym})) = exp(−β·H_{sym})`.
Supplies the `θ M = M` hypothesis for the chessboard/real-diagonal reflection lemmas. -/
theorem ringReflectionThetaS_ringDLSFieldWeightSym (n N : ℕ) [NeZero n] (β : ℝ)
    (a : Fin (2 * n) → ℝ) :
    ringReflectionThetaS n N (ringDLSFieldWeightSym n N β a) = ringDLSFieldWeightSym n N β a := by
  rw [ringDLSFieldWeightSym, ringReflectionThetaS_exp, ringReflectionThetaS_smul, map_neg,
    Complex.conj_ofReal, ringReflectionThetaS_ringFieldDLSDecomposition_toHamiltonian]

end LatticeSystem.Quantum
