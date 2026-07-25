import LatticeSystem.Quantum.SpinS.SublatticeSpinLadderDefCore

/-!
# Sublattice axis operators squared as conjTranspose products
(build-speed companion)

Build-speed companion to `SublatticeSpin.lean`. Hosts the identities
`(Ŝ_A^(α))² = (Ŝ_A^(α))ᴴ * Ŝ_A^(α)` for `α ∈ {1, 2, 3}`, which follow
from Hermiticity of the sublattice axis operators and supply the
positive-semidefiniteness input consumed by
`Theorem23SublatticeCasimirNonneg.lean`.

The sublattice ladder *definitions* and the Cartan relations between
sublattice generators live in the imported foundational layer
`SublatticeSpinLadderDefCore.lean`. This is **separate** from the
companion `SublatticeSpinLadder.lean` (from refactor #28), which holds
ladder *applications* (realness / annihilation / adjoint /
magnetization-shift / Cartan identities / cross-sublattice commute).

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-! ## Sublattice axis squared as conjTranspose product -/

/-- `(Ŝ_A^(1))² = (Ŝ_A^(1))ᴴ * Ŝ_A^(1)`. Direct from Hermiticity. -/
theorem sublatticeSpinSOp1_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinSOp1 N A * sublatticeSpinSOp1 N A =
      (sublatticeSpinSOp1 N A).conjTranspose * sublatticeSpinSOp1 N A := by
  rw [(sublatticeSpinSOp1_isHermitian N A).eq]

/-- `(Ŝ_A^(2))² = (Ŝ_A^(2))ᴴ * Ŝ_A^(2)`. Direct from Hermiticity. -/
theorem sublatticeSpinSOp2_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinSOp2 N A * sublatticeSpinSOp2 N A =
      (sublatticeSpinSOp2 N A).conjTranspose * sublatticeSpinSOp2 N A := by
  rw [(sublatticeSpinSOp2_isHermitian N A).eq]

/-- `(Ŝ_A^(3))² = (Ŝ_A^(3))ᴴ * Ŝ_A^(3)`. Direct from Hermiticity. -/
theorem sublatticeSpinSOp3_sq_eq_conjTranspose_mul (A : Λ → Bool) :
    sublatticeSpinSOp3 N A * sublatticeSpinSOp3 N A =
      (sublatticeSpinSOp3 N A).conjTranspose * sublatticeSpinSOp3 N A := by
  rw [(sublatticeSpinSOp3_isHermitian N A).eq]

end LatticeSystem.Quantum
