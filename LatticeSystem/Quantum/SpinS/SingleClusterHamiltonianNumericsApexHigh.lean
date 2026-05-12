/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Apex-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 199`
(spin `S = N/2 ≥ 199/2`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`,
the `N = 116..131` in `SingleClusterHamiltonianNumericsInfiniteHigh.lean`,
the `N = 132..148` in `SingleClusterHamiltonianNumericsTransfiniteHigh.lean`,
the `N = 149..165` in `SingleClusterHamiltonianNumericsAbsoluteHigh.lean`,
and the `N = 166..198` in `SingleClusterHamiltonianNumericsOmegaHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all twelve numerics files can elaborate
in parallel after the main file. The split from `OmegaHigh` to
`ApexHigh` was introduced as the 50-PR build-performance cadence
refactor #21 when `OmegaHigh` reached 3211 lines / ~9.3 s user CPU
after the N=166..198 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

/-- **Spin-199/2 2-vertex (dimer) ground-state energy** (γ-5 step 1488):
`singleClusterGSEnergyS 1 199 = -39999/4 = -S(S+1)` for `S = 199/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredninetynine :
    singleClusterGSEnergyS 1 199 = (-39999 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1488):
`singleClusterMaxEnergyS 1 199 = 39601/4 = S²` for `S = 199/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredninetynine :
    singleClusterMaxEnergyS 1 199 = (39601 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 3-vertex (trimer) ground-state energy** (γ-5 step 1489):
`singleClusterGSEnergyS 2 199 = -19900 = -S(1+zS)` for `S = 199/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredninetynine :
    singleClusterGSEnergyS 2 199 = (-19900 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1489):
`singleClusterMaxEnergyS 2 199 = 39601/2 = zS²` for `S = 199/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredninetynine :
    singleClusterMaxEnergyS 2 199 = (39601 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 4-vertex (quartet) ground-state energy** (γ-5 step 1490):
`singleClusterGSEnergyS 3 199 = -119201/4 = -S(1+zS)` for `S = 199/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredninetynine :
    singleClusterGSEnergyS 3 199 = (-119201 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1490):
`singleClusterMaxEnergyS 3 199 = 118803/4 = zS²` for `S = 199/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredninetynine :
    singleClusterMaxEnergyS 3 199 = (118803 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1491):
`singleClusterGSEnergyS 4 199 = -79401/2 = -S(1+zS)` for `S = 199/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredninetynine :
    singleClusterGSEnergyS 4 199 = (-79401 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1491):
`singleClusterMaxEnergyS 4 199 = 39601 = zS²` for `S = 199/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredninetynine :
    singleClusterMaxEnergyS 4 199 = (39601 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1492):
`singleClusterGSEnergyS 5 199 = -198403/4 = -S(1+zS)` for `S = 199/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredninetynine :
    singleClusterGSEnergyS 5 199 = (-198403 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1492):
`singleClusterMaxEnergyS 5 199 = 198005/4 = zS²` for `S = 199/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredninetynine :
    singleClusterMaxEnergyS 5 199 = (198005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
