/-
The DLS Hamiltonian and its Gibbs weight are reflection-invariant
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer 35).

The gauged DLS Hamiltonian `ringDLSDecomposition.toHamiltonian = H_L + θ(H_L) − Σ_b C_b` is
reflection-invariant under `θ`: the `H_L + θ(H_L)` part is swapped to itself by the involution, and
each crossing-bond interaction `C_b = Σ_α Ŝ_x^α · θ(Ŝ_x^α)` is fixed because `Ŝ_x^α` (a left-site
operator) commutes with its right-half reflection `θ(Ŝ_x^α)`.  Consequently the gauged ring Gibbs
weight `exp(−β · toHamiltonian)` is reflection-invariant, supplying the hypothesis `θ M = M` needed
to apply the reflection-positivity chessboard and real-diagonal lemmas to the concrete weight.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionChessboard
import LatticeSystem.Quantum.SpinS.RingReflectionConcreteGibbs
import LatticeSystem.Quantum.SpinS.RingReflectionExpSupport

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- The crossing-bond interaction at a left site is reflection-invariant: `θ(C_x) = C_x`, because
`Ŝ_x^α` commutes with its right-half reflection `θ(Ŝ_x^α)`. -/
theorem ringReflectionThetaS_crossBondInteractionS {x : Fin (2 * n)} (hx : (x : ℕ) < n) :
    ringReflectionThetaS n N (crossBondInteractionS x N) = crossBondInteractionS x N := by
  have h1 := onSiteS_supportedOnLeft hx (spinSOp1 N)
  have h2 := onSiteS_supportedOnLeft hx (spinSOp2 N)
  have h3 := onSiteS_supportedOnLeft hx (spinSOp3 N)
  simp only [crossBondInteractionS]
  rw [ringReflectionThetaS_add, ringReflectionThetaS_add, ringReflectionThetaS_mul,
    ringReflectionThetaS_mul, ringReflectionThetaS_mul, ringReflectionThetaS_involutive n N,
    ringReflectionThetaS_involutive n N, ringReflectionThetaS_involutive n N,
    h1.mul_theta_comm h1, h2.mul_theta_comm h2, h3.mul_theta_comm h3]

/-- **The gauged DLS Hamiltonian is reflection-invariant**: `θ(toHamiltonian) = toHamiltonian`. -/
theorem ringReflectionThetaS_toHamiltonian (n N : ℕ) [NeZero n] :
    ringReflectionThetaS n N (ringDLSDecomposition n N).toHamiltonian
      = (ringDLSDecomposition n N).toHamiltonian := by
  have hn := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [ringDLSDecomposition_toHamiltonian, ringReflectionThetaS_sub, ringReflectionThetaS_add,
    ringReflectionThetaS_involutive n N, ringReflectionThetaS_add,
    ringReflectionThetaS_crossBondInteractionS
      (by rw [ringCrossingSite_zero_val]; exact hn),
    ringReflectionThetaS_crossBondInteractionS
      (by rw [ringCrossingSite_one_val]; omega),
    add_comm (ringReflectionThetaS n N (ringLeftHamiltonian n N)) (ringLeftHamiltonian n N)]

/-- **The gauged ring Gibbs weight is reflection-invariant**: `θ(exp(−β·toHamiltonian)) =
exp(−β·toHamiltonian)`.  This supplies the `θ M = M` hypothesis for the chessboard/real-diagonal
lemmas. -/
theorem ringReflectionThetaS_ringDLSGibbs (n N : ℕ) [NeZero n] (β : ℝ) :
    ringReflectionThetaS n N
        (NormedSpace.exp (-(β : ℂ) • (ringDLSDecomposition n N).toHamiltonian))
      = NormedSpace.exp (-(β : ℂ) • (ringDLSDecomposition n N).toHamiltonian) := by
  rw [ringReflectionThetaS_exp, ringReflectionThetaS_smul, map_neg, Complex.conj_ofReal,
    ringReflectionThetaS_toHamiltonian]

end LatticeSystem.Quantum
