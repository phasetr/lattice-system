import LatticeSystem.Quantum.SpinS.ManyBodyPiRotation
import LatticeSystem.Quantum.SpinS.ManyBodyTensorConj
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis2
import LatticeSystem.Quantum.SpinS.TotalSpin
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# The many-body lift of the `π` rotations: Tasaki eq. (2.2.11), p. 22

Tasaki *defines* the global rotation operator by

  `Û_θ^{(α)} := exp[−iθ Ŝ_tot^{(α)}] = ∏_{x ∈ Λ} exp[−iθ Ŝ_x^{(α)}]`  (eq. (2.2.11), p. 22),

the second equality being asserted in the same display.  This module proves that equality at
`θ = π` and combines it with the single-site closed forms of eq. (2.1.34), p. 20
(`spinSPiRotationAxis_eq_exp` of `Quantum/SpinS/SpinSPiRotationExpAxis2.lean`), so that the
closed-form global rotation `manyBodySPiRotation` of `Quantum/SpinS/ManyBodyPiRotation.lean` is
identified with the operator exponential `exp(−iπ Ŝ_tot^{(α)})` the book writes.  Tasaki
Problem 2.2.a, p. 23 (`[solution → p. 496]`) — commutation, anticommutation and eigenvector
orthogonality for distinct axes — is then restated on the exponential objects.

The route is axis-independent and uses no property of `Ŝ^{(α)}`: the site embedding `onSiteS x`
is a continuous unital ring homomorphism, hence commutes with the matrix exponential
(`onSiteS_exp`); a many-body tensor is the noncommutative product of the site embeddings of its
factors (`manyBodyTensorS_eq_noncommProd`); and the exponential of a sum of site embeddings,
which commute pairwise across distinct sites, is that product (`manyBodyTensorS_const_exp`).
The products are `Finset.noncommProd` because the many-body operators do not commute in general
and `Λ` carries no order.

The capstone `manyBodySPiRotation_eq_exp` is uniform in the axis `α : Fin 3`, its right-hand
side being written with the inline vector `![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N,
totalSpinSOp3 Λ N] α`, which is by definition `totalSpinSOpVec Λ N α` of
`Quantum/SpinS/CartesianAxis.lean`.

Only `[Fintype Λ]` and `[DecidableEq Λ]` are assumed; `Λ` may be empty, in which case both sides
of the capstone are the identity and the odd-parity statements are vacuous.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2, eq. (2.2.11), p. 22, and Problem 2.2.a, p. 23, `[solution → p. 496]`; §2.1,
eq. (2.1.34), p. 20.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ## The site embedding and the matrix exponential -/

set_option backward.isDefEq.respectTransparency false in
/-- The site embedding commutes with the matrix exponential, `ι_x(exp A) = exp(ι_x A)`: `onSiteS i`
is a unital ring homomorphism, and it is continuous because it is linear between
finite-dimensional spaces, so the exponential series is mapped term by term.

Matrices carry no canonical norm, so the norm needed to run the series is supplied for the length
of the proof term by the scoped operator-norm instances; the `set_option` is an
elaboration-transparency option (not a lint suppression) required for the resulting defeq check
between the canonical Pi-product topology on matrices and the metric topology of those
instances, and mathlib carries it on every lemma of this shape. -/
theorem onSiteS_exp (i : Λ) (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    onSiteS i (NormedSpace.exp A) = NormedSpace.exp (onSiteS i A) :=
  open scoped Matrix.Norms.Operator in
    NormedSpace.map_exp (onSiteSRingHom i)
      (LinearMap.continuous_of_finiteDimensional (onSiteSLinearMap i)) A

end LatticeSystem.Quantum
