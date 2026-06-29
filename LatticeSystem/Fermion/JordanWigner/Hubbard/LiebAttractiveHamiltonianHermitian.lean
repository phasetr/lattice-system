import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinfulNumberHermitian
import LatticeSystem.Math.MatrixAnalysis.HermitianSum

/-!
# The attractive Hubbard Hamiltonian is Hermitian (Tasaki §10.2.4)

Layer PR38b toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The
Perron–Frobenius/variational arguments in the PSD ground-representative step (PR38c)
require `Ĥ = attractiveHubbardHamiltonian` to be Hermitian. The kinetic part is
Hermitian for symmetric real hopping (`hubbardKinetic_isHermitian`); the attractive
interaction `−Σ_x U_x n̂_{x,↑} n̂_{x,↓}` is a real combination of Hermitian
double-occupancy operators, hence Hermitian.

## Main results

* `attractiveHubbardInteraction_isHermitian` — the interaction is Hermitian.
* `attractiveHubbardHamiltonian_isHermitian` — `Ĥ` is Hermitian (for symmetric `T`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1, pp. 348–349; §10.2.4, pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-- The attractive on-site interaction `−Σ_x U_x n̂_{x,↑} n̂_{x,↓}` is Hermitian. -/
theorem attractiveHubbardInteraction_isHermitian (U : Fin (N + 1) → ℝ) :
    (attractiveHubbardInteraction N U).IsHermitian := by
  rw [attractiveHubbardInteraction, hubbardOnSiteInteractionSite]
  refine Matrix.isHermitian_sum _ (fun x _ => ?_)
  change ((-(U x : ℂ)) • (fermionUpNumber N x * fermionDownNumber N x))ᴴ = _
  rw [Matrix.conjTranspose_smul, (fermionUpNumber_mul_fermionDownNumber_isHermitian N x).eq,
    star_neg, ← starRingEnd_apply, Complex.conj_ofReal]

/-- **The attractive Hubbard Hamiltonian is Hermitian** for symmetric real hopping `T`. -/
theorem attractiveHubbardHamiltonian_isHermitian
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) :
    (attractiveHubbardHamiltonian N T U).IsHermitian := by
  rw [attractiveHubbardHamiltonian]
  refine Matrix.IsHermitian.add (hubbardKinetic_isHermitian N (fun i j => ?_)) ?_
  · rw [← starRingEnd_apply, Complex.conj_ofReal]; exact_mod_cast hT i j
  · exact attractiveHubbardInteraction_isHermitian U

end LatticeSystem.Fermion
