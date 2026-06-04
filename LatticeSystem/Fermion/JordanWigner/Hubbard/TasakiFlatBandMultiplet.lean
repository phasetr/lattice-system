import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandNonvanishing
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral

/-!
# Tasaki §11.3.1: the ferromagnetic spin multiplet of the all-up `α` state

The spin-content half of the existence direction of Theorem 11.11.  The all-up
`α` state `|Φα,all↑⟩` is a nonzero highest-weight state with
`Ŝ^z_tot = (K+1)/2 = |E|/2` (the half-filled-band weight), so the general
highest-weight tower `highestWeight_spinMultiplet_general` produces a
`(K+2) = (2 S_max + 1)`-dimensional maximal-spin multiplet:

* `flatBand_ferromagnetic_multiplet`: the `K + 2` lowered states
  `(Ŝ^-_tot)^k |Φα,all↑⟩` (`k = 0, …, K+1`) are linearly independent and all carry
  total spin `(Ŝ_tot)² = S_max(S_max + 1)` with `S_max = (K+1)/2`.

This packages the three prerequisites proven earlier — the general tower
(`SpinLoweringTowerGeneral.lean`), the highest-weight data
(`TasakiFlatBandHighestWeight.lean`), and nonvanishing
(`TasakiFlatBandNonvanishing.lean`) — into Tasaki's ferromagnetic multiplet.
That every member is moreover a zero-energy *ground* state requires the energy
tower `Ĥ (Ŝ^-_tot)^k |Φα⟩ = 0` (flat-band SU(2) lowering symmetry) and the
positive-semidefiniteness `Ĥ ≥ 0`, handled in subsequent steps.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11 (existence half, spin content),
`S_max = N_e/2 = (K+1)/2`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **Tasaki §11.3.1 ferromagnetic spin multiplet (Theorem 11.11, spin content).**
The `K + 2 = 2 S_max + 1` lowered states `(Ŝ^-_tot)^k |Φα,all↑⟩`
(`k = 0, …, K+1`) of the flat-band model are linearly independent and all lie in
the maximal-spin sector `S_tot = S_max = (K+1)/2 = N_e/2`: each is an eigenstate
of `(Ŝ_tot)²` with eigenvalue `S_max(S_max + 1)`.

Obtained by feeding the highest-weight data of `|Φα,all↑⟩` (`Ŝ^+_tot |Φα⟩ = 0`,
`Ŝ^z_tot |Φα⟩ = ((K+1)/2) |Φα⟩`, `|Φα⟩ ≠ 0`) into the general highest-weight
tower `highestWeight_spinMultiplet_general` at `L = K + 1 = |E|`. -/
theorem flatBand_ferromagnetic_multiplet (K : ℕ) (ν : ℝ) :
    LinearIndependent ℂ (fun k : Fin (K + 2) =>
        ((fermionTotalSpinMinus (2 * K + 1)) ^ (k : ℕ)).mulVec
          (flatBandAlphaAllUpState K ν)) ∧
      (∀ k : Fin (K + 2), (fermionTotalSpinSquared (2 * K + 1)).mulVec
          (((fermionTotalSpinMinus (2 * K + 1)) ^ (k : ℕ)).mulVec
            (flatBandAlphaAllUpState K ν)) =
        (((K + 1 : ℕ) : ℂ) / 2 * (((K + 1 : ℕ) : ℂ) / 2 + 1)) •
          (((fermionTotalSpinMinus (2 * K + 1)) ^ (k : ℕ)).mulVec
            (flatBandAlphaAllUpState K ν))) :=
  highestWeight_spinMultiplet_general (2 * K + 1) (K + 1) (flatBandAlphaAllUpState K ν)
    (flatBandAlphaAllUpState_ne_zero K ν)
    (flatBandTotalSpinPlus_mulVec_alphaAllUpState K ν)
    (flatBandTotalSpinZ_mulVec_alphaAllUpState K ν)

end LatticeSystem.Fermion
