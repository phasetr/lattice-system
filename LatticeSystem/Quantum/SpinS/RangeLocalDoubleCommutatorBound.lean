/-
General range-`r` locality bound for the order-operator double commutator.

Tasaki Problem 3.4.a, eq. (3.4.13), generalises the bond-local double-commutator estimate
eq. (3.4.11) from a Hamiltonian and order operator built from bonds to ones built from *every*
site, each local term acting only within coordinate sup-norm distance `r` of its own site:

`⟨Φ_GS|[Ô_L,[Ĥ,Ô_L]]|Φ_GS⟩ ≤ 4 (2r+1)^d (4r+1)^d h₀ o₀² L^d`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, Problem 3.4.a, statement pp. 67-68, printed solution p. 501; operator-norm properties
(A.2.5)/(A.2.6), p. 463.

STATUS: header-only stub (TDD Red for PR-4 of the §3.4 arc, issue #5395). The capstone
`tasaki_problem_3_4_a_doubleCommutator_expectation_le` is introduced by a later commit of the same
PR.
-/
import LatticeSystem.Quantum.SpinS.LocalDoubleCommutatorBound
import LatticeSystem.Math.Combinatorics.CoordinateBall

namespace LatticeSystem.Quantum

end LatticeSystem.Quantum
