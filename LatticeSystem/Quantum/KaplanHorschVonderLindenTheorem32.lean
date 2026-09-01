import LatticeSystem.Quantum.KaplanHorschVonderLinden
import LatticeSystem.Quantum.HorschVonderLindenLowLyingState
import LatticeSystem.Quantum.SpinS.ExpectationNormBound

/-!
# Tasaki §3.4 Theorem 3.2 (Kaplan–Horsch–von der Linden): eqs. (3.4.21)-(3.4.22)

Theorem 3.2 is the finite-volume variational lower bound eq. (3.4.21) together with the double
limit eq. (3.4.22), `lim_{h↓0} liminf_{L↑∞} ⟨Φ_GS,h|Ô_L/L^d|Φ_GS,h⟩ ≥ √q₀`, stated with
`Filter.liminf` in both limits per footnote 24. It is not yet implemented: this module currently
carries only its import list.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, Theorem 3.2, eqs. (3.4.21)-(3.4.22), pp. 69-70.
-/

namespace LatticeSystem.Quantum

/-- TDD Red anchor for the module's `private` error-term helper: since `private` restricts
visibility to this file, its presence can only be pinned here, not from `LatticeSystem/Tests/`. -/
private theorem redPin_errorTerm_tendsto_zero : True := by
  have _ := @kaplanHorschVonderLinden_errorTerm_tendsto_zero
  trivial

/-- TDD Red anchor for the module's `private` liminf-kernel helper, for the same reason as
`redPin_errorTerm_tendsto_zero` above. -/
private theorem redPin_liminf_bounds : True := by
  have _ := @kaplanHorschVonderLinden_liminf_bounds
  trivial

end LatticeSystem.Quantum
