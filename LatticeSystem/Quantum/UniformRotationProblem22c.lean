import LatticeSystem.Quantum.SU2Integral
import LatticeSystem.Quantum.TotalSpin.Rotation
import LatticeSystem.Quantum.SpinHalfRotation.Conjugation

/-!
# Tasaki Problem 2.2.c: the rotated `|↑⟩₁|↓⟩₂` is determined by `n` alone (pp. 23-24)

Tasaki *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer, 2020), §2.2,
Problem 2.2.c, pp. 23-24 (footnote 16, p. 23; footnote 17, p. 24; solution p. 496, eq. (S.16)).

Fix a unit vector `n ∈ ℝ³` and let `Û` be *any* uniform rotation of the two-spin system in the
class of footnote 16 — an arbitrary finite product of the global rotations
`Û_θ^{(α)} = exp(−iθ Ŝ_tot^{(α)})` (eq. (2.2.11), p. 22) over axes `α = 1, 2, 3` and angles `θ` —
such that `Û Ŝ_x^{(3)} Û† = Ŝ_x · n` at both sites `x = 1, 2`. Problem 2.2.c asks to show that
`Û |↑⟩₁|↓⟩₂` is determined solely by `n`, i.e. does not depend on the particular choice of `Û`
within that class. This module states that conclusion pairwise: any two admissible rotations `U`,
`V` with the same `n` send `|↑⟩₁|↓⟩₂` to the same vector. The printed hypothesis `‖n‖ = 1` is not
used by the proof; only the doc comment records that it is unused, the theorem statement does not
drop it as a stated conclusion.
-/
