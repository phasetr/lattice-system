import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Quantum.SpinS.RayleighInfMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Tasaki §11.4: total-spin sector minimum energy and the ferromagnetism criterion

This file formalises Tasaki's precise definition of *exhibiting (saturated)
ferromagnetism* (Tasaki §11.4, eq. (11.4.26)), the foundation for the non-singular
Hubbard theorems 11.18–11.20.

For a many-body Hamiltonian `Ĥ` on the spinful Jordan–Wigner backbone, the **minimum
energy in the total-spin-`S` sector** is
`E_min(S) := min { ⟨Φ|Ĥ|Φ⟩ : (Ŝ_tot)² Φ = S(S+1) Φ, ‖Φ‖ = 1 }`  (eq. (11.4.26)),
and the ground-state energy is `E_GS = min_S E_min(S)`.  The model **exhibits
ferromagnetism** iff `E_min(S_max) < E_min(S)` for every `S ≠ S_max`.

Sectors are indexed by `twoS = 2S ∈ ℕ` (so `S = twoS/2`, allowing half-integer total
spin), with `(Ŝ_tot)²`-eigenvalue `(twoS/2)(twoS/2 + 1)` — matching the `D/2` convention
of `mielke_theorem_11_13`.  The unit-norm constraint uses the `EuclideanSpace` (L²) norm,
matching the project's min-eigenvalue convention (`HermitianMinEigenvalueViaRayleigh`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.4, eq. (11.4.26) (p. 422).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))

/-- The set of normalised states in the total-spin sector `S = twoS/2`: unit vectors
`Φ` of `EuclideanSpace ℂ` over the computational-basis configurations with
`(Ŝ_tot)² Φ = (twoS/2)(twoS/2 + 1) Φ`. -/
def spinSector (twoS : ℕ) :
    Set (EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2)) :=
  {φ | ‖φ‖ = 1 ∧
    (fermionTotalSpinSquared M).mulVec φ.ofLp
      = (((twoS : ℂ) / 2) * ((twoS : ℂ) / 2 + 1)) • φ.ofLp}

/-- **`E_min(S)` — the minimum energy in the total-spin-`S` sector** (Tasaki eq. (11.4.26),
`S = twoS/2`): the infimum of the (unnormalised) energy `rayleighOnVec Ĥ` over the unit
vectors of the `(Ŝ_tot)²`-eigensector.  (For an empty/unachievable sector the infimum is
the junk value `Real.sInf ∅ = 0`; the ferromagnetism criterion only compares achievable
sectors, where the infimum is the genuine sector ground energy.) -/
noncomputable def sectorMinEnergy (twoS : ℕ) : ℝ :=
  ⨅ φ : spinSector (M := M) twoS, rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp

/-- **The (saturated) ferromagnetism criterion** (Tasaki §11.4): the model with maximal
total spin `S_max = twoSmax/2` exhibits ferromagnetism iff the maximal-spin sector lies
strictly below every other sector, `E_min(S_max) < E_min(S)` for all `S ≠ S_max`. -/
def exhibitsFerromagnetism (twoSmax : ℕ) : Prop :=
  ∀ twoS : ℕ, twoS < twoSmax → sectorMinEnergy H twoSmax < sectorMinEnergy H twoS

end LatticeSystem.Fermion
