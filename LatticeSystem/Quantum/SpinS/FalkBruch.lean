/-
The abstract ground-state Falk–Bruch inequality
(Tasaki §4.1 Corollary 4.3, toward the absence of long-range order in one dimension).

For a positive-semidefinite `K` (here `K = H − E₀`, the Hamiltonian shifted to the ground energy)
and a vector `w` in the range of `K` (with potential `y`, `K y = w`), the squared norm of `w` is
bounded by the product of the "energy" `⟨w, K w⟩` and the "susceptibility" `⟨y, w⟩ = ⟨y, K y⟩`:
`(⟨w, w⟩)² ≤ ⟨w, K w⟩ · ⟨y, w⟩`.  This is the ground-state Falk–Bruch / infrared bound; it is an
immediate instance of the positive-semidefinite Cauchy–Schwarz inequality with the second argument
`y` chosen so that `K y = w`.  For the staggered order parameter (`w = Ô Φ`) the energy is half the
f-sum-rule double commutator and the susceptibility is controlled by reflection positivity, giving
`⟨Φ, Ô² Φ⟩ ≤ C·L` in one dimension.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerEnergyBound

namespace LatticeSystem.Quantum

open Matrix
open scoped ComplexOrder

/-- **Abstract ground-state Falk–Bruch inequality.**  For a positive-semidefinite `K` and a vector
`w` in the range of `K` (`K y = w`), `(Re⟨w, w⟩)² ≤ Re⟨w, K w⟩ · Re⟨y, w⟩` — an immediate instance of
PSD Cauchy–Schwarz. -/
theorem falkBruch_of_mulVec_eq {n : Type*} [Fintype n] {K : Matrix n n ℂ} (hK : K.PosSemidef)
    {w y : n → ℂ} (hy : K.mulVec y = w) :
    (star w ⬝ᵥ w).re ^ 2
      ≤ (star w ⬝ᵥ K.mulVec w).re * (star y ⬝ᵥ w).re := by
  have hcs := posSemidef_re_dotProduct_mulVec_sq_le hK w y
  rwa [hy] at hcs

end LatticeSystem.Quantum
