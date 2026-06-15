import LatticeSystem.Quantum.SpinS.AnisotropicEdgeStates
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg

/-!
# Tasaki §8.2.1: the λ-D model and Néel ≤ string order (Theorem 8.3)

The phase diagram of the Haldane phase is best seen in the two-parameter **λ-D model** (eq.
(8.2.1)),
an `S = 1` open chain with both Ising (`λ`) and crystal-field (`D`) anisotropy:
`Ĥ_{λ,D} = Σ_x [Ŝ_x^{(1)}Ŝ_{x+1}^{(1)} + Ŝ_x^{(2)}Ŝ_{x+1}^{(2)} + λ Ŝ_x^{(3)}Ŝ_{x+1}^{(3)}]
            + D Σ_x (Ŝ_x^{(3)})²`.
At `λ = 1` it is the open-boundary version of the anisotropic model (8.1.1) (which (8.1.1) takes
with periodic boundary, agreeing in the bulk); at `λ = 1, D = 0` the Heisenberg chain.  For `λ > 0`
the ground-state phase diagram has three phases: the **large-`D`** phase, the **Haldane** phase
(with
hidden antiferromagnetic order), and — for large `λ` — the **Ising AF** phase with genuine Néel
order in the 3-direction.

Two order parameters distinguish them (eqs. (8.2.2)–(8.2.3)): the **Néel order parameter**
`O_Néel^{(α)} = lim_{y−x↑∞} lim_{L↑∞} (−1)^{y−x} ⟨Ŝ_x^{(α)} Ŝ_y^{(α)}⟩` and the den Nijs–Rommelse
**string order parameter** `O_string^{(α)}`.  Néel order need not imply hidden order in general, but
on the `λ-D` line the converse comparison holds:

**Theorem 8.3** (Kennedy–Tasaki): for `λ ≥ 0` and any `D`, `O_Néel^{(α)} ≤ O_string^{(α)}` for
`α = 1, 2, 3` — nonzero Néel order forces nonzero hidden antiferromagnetic order.  Moreover the
transverse Néel parameters coincide and are nonnegative, `O_Néel^{(1)} = O_Néel^{(2)} ≥ 0`.

The λ-D Hamiltonian is *defined concretely*.  The two order parameters are thermodynamic
double-limit quantities of the model's ground state (not formalized), recorded as uninterpreted
real-valued functions of the model parameters; Theorem 8.3, whose proof uses the path-integral
representation (§6.3), is a documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §8.2.1, Theorem 8.3, eqs. (8.2.1)–(8.2.4), pp. 239–241; T. Kennedy, H. Tasaki, Phys. Rev. B
**45**, 304 (1992).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **λ-D model Hamiltonian** (eq. (8.2.1)): the `S = 1` open chain with Ising anisotropy `λ`
(the XXZ coupling `Ŝ_x^{(1)}Ŝ_y^{(1)} + Ŝ_x^{(2)}Ŝ_y^{(2)} + λ Ŝ_x^{(3)}Ŝ_y^{(3)}` summed over the
open nearest-neighbour bonds) and crystal-field anisotropy `D` (the single-ion `D (Ŝ^{(3)})²` term).
At `λ = 1` it is the **open-boundary** version of the anisotropic model (8.1.1) (which (8.1.1) takes
with periodic boundary); the two agree in the bulk / thermodynamic limit. -/
noncomputable def lambdaDChainHamiltonianS (L : ℕ) (lam D : ℝ) : ManyBodyOpS (Fin L) 2 :=
  (∑ x : Fin L, ∑ y : Fin L,
      openAnisotropicChainCoupling L x y • spinSDotXXZ x y (lam : ℂ) 2) +
    (D : ℂ) • ∑ x : Fin L, spinSSiteOp3 x 2 * spinSSiteOp3 x 2

/-- The **Néel order parameter** `O_Néel^{(α)}(λ, D)` of the λ-D model (eq. (8.2.2)): the
thermodynamic double limit `lim_{y−x↑∞} lim_{L↑∞} (−1)^{y−x} ⟨Φ_GS| Ŝ_x^{(α)} Ŝ_y^{(α)} |Φ_GS⟩` of
the staggered two-point function in the ground state, for `α : Fin 3` (`0, 1, 2 ↔ α = 1, 2, 3`). 
The
double limit is not formalized, so this is an uninterpreted real-valued function of `(λ, D, α)`. -/
axiom neelOrderParameterS : ℝ → ℝ → Fin 3 → ℝ

/-- The **string order parameter** `O_string^{(α)}(λ, D)` of the λ-D model (eq. (8.2.3)): the den
Nijs–Rommelse string order `−lim_{y−x↑∞} lim_{L↑∞} ⟨Φ_GS| Ŝ_x^{(α)} exp(iπ Σ Ŝ^{(α)}) Ŝ_y^{(α)}
|Φ_GS⟩` of the ground state, for `α : Fin 3`.  An uninterpreted real-valued function of `(λ, D, α)`
(the double limit is not formalized). -/
axiom stringOrderParameterS : ℝ → ℝ → Fin 3 → ℝ

/-- **Tasaki Theorem 8.3 (Néel order ≤ string order), AXIOM (eq. (8.2.4)).**  For the λ-D model with
`λ ≥ 0` and any crystal field `D`, the Néel order parameter is bounded by the string order parameter
in every direction: `O_Néel^{(α)}(λ, D) ≤ O_string^{(α)}(λ, D)` for `α = 1, 2, 3`.  Thus nonzero
Néel
order (the Ising AF phase) forces nonzero hidden antiferromagnetic order — the latter is the more
robust order parameter.  Proved via the path-integral representation (§6.3); recorded as a
documented
axiom. -/
axiom tasaki_theorem_8_3 (lam D : ℝ) (hlam : 0 ≤ lam) (α : Fin 3) :
    neelOrderParameterS lam D α ≤ stringOrderParameterS lam D α

/-- **Tasaki §8.2 footnote (transverse Néel parameters), AXIOM.**  For the λ-D model with `λ ≥ 0`
the Néel order parameters in the two transverse directions `α = 1, 2` coincide and are nonnegative:
`O_Néel^{(1)}(λ, D) = O_Néel^{(2)}(λ, D) ≥ 0`.  The `λ ≥ 0` hypothesis matches the parameter range
of Theorem 8.3, of which this is a companion. -/
axiom tasaki_neel_transverse_eq_nonneg (lam D : ℝ) (hlam : 0 ≤ lam) :
    neelOrderParameterS lam D 0 = neelOrderParameterS lam D 1 ∧ 0 ≤ neelOrderParameterS lam D 0

end LatticeSystem.Quantum
