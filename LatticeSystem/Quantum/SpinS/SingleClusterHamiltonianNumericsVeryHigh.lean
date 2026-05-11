/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Very-high-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for
`39 ≤ N ≤ 47` (spin `39/2 ≤ S ≤ 47/2`). The `N = 1..28`
specialisations live in `SingleClusterHamiltonianNumerics.lean`,
the `N = 29..38` in `SingleClusterHamiltonianNumericsHigh.lean`,
the `N = 48..59` in `SingleClusterHamiltonianNumericsUltraHigh.lean`,
the `N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`,
the `N = 116..131` in `SingleClusterHamiltonianNumericsInfiniteHigh.lean`,
the `N = 132..148` in `SingleClusterHamiltonianNumericsTransfiniteHigh.lean`,
and the `N ≥ 149` in `SingleClusterHamiltonianNumericsAbsoluteHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all ten numerics files can elaborate
in parallel after the main file. Splitting was introduced as part of
the 50-PR build-performance cadence (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

/-- **Spin-39/2 dimer ground-state energy** (γ-5 step 528):
`singleClusterGSEnergyS 1 39 = -1599/4 = -S(S+1)` for `S = 39/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtynine :
    singleClusterGSEnergyS 1 39 = (-1599 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39/2 dimer maximum-Casimir-sector energy** (γ-5 step 528):
`singleClusterMaxEnergyS 1 39 = 1521/4 = S²` for `S = 39/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtynine :
    singleClusterMaxEnergyS 1 39 = (1521 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39/2 3-vertex-star ground-state energy** (γ-5 step 529):
`singleClusterGSEnergyS 2 39 = -780 = -S(1+zS)` for `S = 39/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtynine :
    singleClusterGSEnergyS 2 39 = (-780 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 529):
`singleClusterMaxEnergyS 2 39 = 1521/2 = zS²` for `S = 39/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtynine :
    singleClusterMaxEnergyS 2 39 = (1521 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39/2 4-vertex-star ground-state energy** (γ-5 step 530):
`singleClusterGSEnergyS 3 39 = -4641/4 = -S(1+zS)` for `S = 39/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtynine :
    singleClusterGSEnergyS 3 39 = (-4641 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 530):
`singleClusterMaxEnergyS 3 39 = 4563/4 = zS²` for `S = 39/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtynine :
    singleClusterMaxEnergyS 3 39 = (4563 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39/2 5-vertex-star ground-state energy** (γ-5 step 531):
`singleClusterGSEnergyS 4 39 = -3081/2 = -S(1+zS)` for `S = 39/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtynine :
    singleClusterGSEnergyS 4 39 = (-3081 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 531):
`singleClusterMaxEnergyS 4 39 = 1521 = zS²` for `S = 39/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtynine :
    singleClusterMaxEnergyS 4 39 = (1521 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39/2 6-vertex-star ground-state energy** (γ-5 step 532):
`singleClusterGSEnergyS 5 39 = -7683/4 = -S(1+zS)` for `S = 39/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtynine :
    singleClusterGSEnergyS 5 39 = (-7683 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 532):
`singleClusterMaxEnergyS 5 39 = 7605/4 = zS²` for `S = 39/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtynine :
    singleClusterMaxEnergyS 5 39 = (7605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39/2 7-vertex-star ground-state energy** (γ-5 step 533):
`singleClusterGSEnergyS 6 39 = -2301 = -S(1+zS)` for `S = 39/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtynine :
    singleClusterGSEnergyS 6 39 = (-2301 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 533):
`singleClusterMaxEnergyS 6 39 = 4563/2 = zS²` for `S = 39/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtynine :
    singleClusterMaxEnergyS 6 39 = (4563 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-20 dimer ground-state energy** (γ-5 step 534):
`singleClusterGSEnergyS 1 40 = -420 = -S(S+1)` for `S = 20`. -/
@[simp] theorem singleClusterGSEnergyS_one_forty :
    singleClusterGSEnergyS 1 40 = (-420 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-20 dimer maximum-Casimir-sector energy** (γ-5 step 534):
`singleClusterMaxEnergyS 1 40 = 400 = S²` for `S = 20`. -/
@[simp] theorem singleClusterMaxEnergyS_one_forty :
    singleClusterMaxEnergyS 1 40 = (400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-20 3-vertex-star ground-state energy** (γ-5 step 535):
`singleClusterGSEnergyS 2 40 = -820 = -S(1+zS)` for `S = 20, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_forty :
    singleClusterGSEnergyS 2 40 = (-820 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-20 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 535):
`singleClusterMaxEnergyS 2 40 = 800 = zS²` for `S = 20, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_forty :
    singleClusterMaxEnergyS 2 40 = (800 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-20 4-vertex-star ground-state energy** (γ-5 step 536):
`singleClusterGSEnergyS 3 40 = -1220 = -S(1+zS)` for `S = 20, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_forty :
    singleClusterGSEnergyS 3 40 = (-1220 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-20 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 536):
`singleClusterMaxEnergyS 3 40 = 1200 = zS²` for `S = 20, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_forty :
    singleClusterMaxEnergyS 3 40 = (1200 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-20 5-vertex-star ground-state energy** (γ-5 step 537):
`singleClusterGSEnergyS 4 40 = -1620 = -S(1+zS)` for `S = 20, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_forty :
    singleClusterGSEnergyS 4 40 = (-1620 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-20 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 537):
`singleClusterMaxEnergyS 4 40 = 1600 = zS²` for `S = 20, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_forty :
    singleClusterMaxEnergyS 4 40 = (1600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-20 6-vertex-star ground-state energy** (γ-5 step 538):
`singleClusterGSEnergyS 5 40 = -2020 = -S(1+zS)` for `S = 20, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_forty :
    singleClusterGSEnergyS 5 40 = (-2020 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-20 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 538):
`singleClusterMaxEnergyS 5 40 = 2000 = zS²` for `S = 20, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_forty :
    singleClusterMaxEnergyS 5 40 = (2000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-20 7-vertex-star ground-state energy** (γ-5 step 539):
`singleClusterGSEnergyS 6 40 = -2420 = -S(1+zS)` for `S = 20, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_forty :
    singleClusterGSEnergyS 6 40 = (-2420 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-20 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 539):
`singleClusterMaxEnergyS 6 40 = 2400 = zS²` for `S = 20, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_forty :
    singleClusterMaxEnergyS 6 40 = (2400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41/2 dimer ground-state energy** (γ-5 step 540):
`singleClusterGSEnergyS 1 41 = -1763/4 = -S(S+1)` for `S = 41/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortyone :
    singleClusterGSEnergyS 1 41 = (-1763 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41/2 dimer maximum-Casimir-sector energy** (γ-5 step 540):
`singleClusterMaxEnergyS 1 41 = 1681/4 = S²` for `S = 41/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortyone :
    singleClusterMaxEnergyS 1 41 = (1681 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41/2 3-vertex-star ground-state energy** (γ-5 step 541):
`singleClusterGSEnergyS 2 41 = -861 = -S(1+zS)` for `S = 41/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortyone :
    singleClusterGSEnergyS 2 41 = (-861 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 541):
`singleClusterMaxEnergyS 2 41 = 1681/2 = zS²` for `S = 41/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortyone :
    singleClusterMaxEnergyS 2 41 = (1681 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41/2 4-vertex-star ground-state energy** (γ-5 step 542):
`singleClusterGSEnergyS 3 41 = -5125/4 = -S(1+zS)` for `S = 41/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortyone :
    singleClusterGSEnergyS 3 41 = (-5125 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 542):
`singleClusterMaxEnergyS 3 41 = 5043/4 = zS²` for `S = 41/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortyone :
    singleClusterMaxEnergyS 3 41 = (5043 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41/2 5-vertex-star ground-state energy** (γ-5 step 543):
`singleClusterGSEnergyS 4 41 = -3403/2 = -S(1+zS)` for `S = 41/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortyone :
    singleClusterGSEnergyS 4 41 = (-3403 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 543):
`singleClusterMaxEnergyS 4 41 = 1681 = zS²` for `S = 41/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortyone :
    singleClusterMaxEnergyS 4 41 = (1681 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41/2 6-vertex-star ground-state energy** (γ-5 step 544):
`singleClusterGSEnergyS 5 41 = -8487/4 = -S(1+zS)` for `S = 41/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortyone :
    singleClusterGSEnergyS 5 41 = (-8487 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 544):
`singleClusterMaxEnergyS 5 41 = 8405/4 = zS²` for `S = 41/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortyone :
    singleClusterMaxEnergyS 5 41 = (8405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41/2 7-vertex-star ground-state energy** (γ-5 step 545):
`singleClusterGSEnergyS 6 41 = -2542 = -S(1+zS)` for `S = 41/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortyone :
    singleClusterGSEnergyS 6 41 = (-2542 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 545):
`singleClusterMaxEnergyS 6 41 = 5043/2 = zS²` for `S = 41/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortyone :
    singleClusterMaxEnergyS 6 41 = (5043 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21 2-vertex (dimer) ground-state energy** (γ-5 step 546):
`singleClusterGSEnergyS 1 42 = -462 = -S(S+1)` for `S = 21`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortytwo :
    singleClusterGSEnergyS 1 42 = (-462 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 546):
`singleClusterMaxEnergyS 1 42 = 441 = S²` for `S = 21`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortytwo :
    singleClusterMaxEnergyS 1 42 = (441 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21 3-vertex (trimer) ground-state energy** (γ-5 step 547):
`singleClusterGSEnergyS 2 42 = -903 = -S(1+zS)` for `S = 21, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortytwo :
    singleClusterGSEnergyS 2 42 = (-903 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 547):
`singleClusterMaxEnergyS 2 42 = 882 = zS²` for `S = 21, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortytwo :
    singleClusterMaxEnergyS 2 42 = (882 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21 4-vertex (quartet) ground-state energy** (γ-5 step 548):
`singleClusterGSEnergyS 3 42 = -1344 = -S(1+zS)` for `S = 21, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortytwo :
    singleClusterGSEnergyS 3 42 = (-1344 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 548):
`singleClusterMaxEnergyS 3 42 = 1323 = zS²` for `S = 21, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortytwo :
    singleClusterMaxEnergyS 3 42 = (1323 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21 5-vertex (pentamer) ground-state energy** (γ-5 step 549):
`singleClusterGSEnergyS 4 42 = -1785 = -S(1+zS)` for `S = 21, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortytwo :
    singleClusterGSEnergyS 4 42 = (-1785 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 549):
`singleClusterMaxEnergyS 4 42 = 1764 = zS²` for `S = 21, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortytwo :
    singleClusterMaxEnergyS 4 42 = (1764 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21 6-vertex (hexamer) ground-state energy** (γ-5 step 550):
`singleClusterGSEnergyS 5 42 = -2226 = -S(1+zS)` for `S = 21, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortytwo :
    singleClusterGSEnergyS 5 42 = (-2226 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 550):
`singleClusterMaxEnergyS 5 42 = 2205 = zS²` for `S = 21, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortytwo :
    singleClusterMaxEnergyS 5 42 = (2205 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21 7-vertex (heptamer) ground-state energy** (γ-5 step 551):
`singleClusterGSEnergyS 6 42 = -2667 = -S(1+zS)` for `S = 21, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortytwo :
    singleClusterGSEnergyS 6 42 = (-2667 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 551):
`singleClusterMaxEnergyS 6 42 = 2646 = zS²` for `S = 21, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortytwo :
    singleClusterMaxEnergyS 6 42 = (2646 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43/2 2-vertex (dimer) ground-state energy** (γ-5 step 552):
`singleClusterGSEnergyS 1 43 = -1935/4 = -S(S+1)` for `S = 43/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortythree :
    singleClusterGSEnergyS 1 43 = (-1935 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 552):
`singleClusterMaxEnergyS 1 43 = 1849/4 = S²` for `S = 43/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortythree :
    singleClusterMaxEnergyS 1 43 = (1849 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43/2 3-vertex (trimer) ground-state energy** (γ-5 step 553):
`singleClusterGSEnergyS 2 43 = -946 = -S(1+zS)` for `S = 43/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortythree :
    singleClusterGSEnergyS 2 43 = (-946 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 553):
`singleClusterMaxEnergyS 2 43 = 1849/2 = zS²` for `S = 43/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortythree :
    singleClusterMaxEnergyS 2 43 = (1849 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43/2 4-vertex (quartet) ground-state energy** (γ-5 step 554):
`singleClusterGSEnergyS 3 43 = -5633/4 = -S(1+zS)` for `S = 43/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortythree :
    singleClusterGSEnergyS 3 43 = (-5633 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 554):
`singleClusterMaxEnergyS 3 43 = 5547/4 = zS²` for `S = 43/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortythree :
    singleClusterMaxEnergyS 3 43 = (5547 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43/2 5-vertex (pentamer) ground-state energy** (γ-5 step 555):
`singleClusterGSEnergyS 4 43 = -3741/2 = -S(1+zS)` for `S = 43/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortythree :
    singleClusterGSEnergyS 4 43 = (-3741 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 555):
`singleClusterMaxEnergyS 4 43 = 1849 = zS²` for `S = 43/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortythree :
    singleClusterMaxEnergyS 4 43 = (1849 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43/2 6-vertex (hexamer) ground-state energy** (γ-5 step 556):
`singleClusterGSEnergyS 5 43 = -9331/4 = -S(1+zS)` for `S = 43/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortythree :
    singleClusterGSEnergyS 5 43 = (-9331 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 556):
`singleClusterMaxEnergyS 5 43 = 9245/4 = zS²` for `S = 43/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortythree :
    singleClusterMaxEnergyS 5 43 = (9245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43/2 7-vertex (heptamer) ground-state energy** (γ-5 step 557):
`singleClusterGSEnergyS 6 43 = -2795 = -S(1+zS)` for `S = 43/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortythree :
    singleClusterGSEnergyS 6 43 = (-2795 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 557):
`singleClusterMaxEnergyS 6 43 = 5547/2 = zS²` for `S = 43/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortythree :
    singleClusterMaxEnergyS 6 43 = (5547 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-22 2-vertex (dimer) ground-state energy** (γ-5 step 558):
`singleClusterGSEnergyS 1 44 = -506 = -S(S+1)` for `S = 22`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortyfour :
    singleClusterGSEnergyS 1 44 = (-506 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-22 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 558):
`singleClusterMaxEnergyS 1 44 = 484 = S²` for `S = 22`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortyfour :
    singleClusterMaxEnergyS 1 44 = (484 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-22 3-vertex (trimer) ground-state energy** (γ-5 step 559):
`singleClusterGSEnergyS 2 44 = -990 = -S(1+zS)` for `S = 22, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortyfour :
    singleClusterGSEnergyS 2 44 = (-990 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-22 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 559):
`singleClusterMaxEnergyS 2 44 = 968 = zS²` for `S = 22, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortyfour :
    singleClusterMaxEnergyS 2 44 = (968 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-22 4-vertex (quartet) ground-state energy** (γ-5 step 560):
`singleClusterGSEnergyS 3 44 = -1474 = -S(1+zS)` for `S = 22, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortyfour :
    singleClusterGSEnergyS 3 44 = (-1474 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-22 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 560):
`singleClusterMaxEnergyS 3 44 = 1452 = zS²` for `S = 22, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortyfour :
    singleClusterMaxEnergyS 3 44 = (1452 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-22 5-vertex (pentamer) ground-state energy** (γ-5 step 561):
`singleClusterGSEnergyS 4 44 = -1958 = -S(1+zS)` for `S = 22, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortyfour :
    singleClusterGSEnergyS 4 44 = (-1958 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-22 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 561):
`singleClusterMaxEnergyS 4 44 = 1936 = zS²` for `S = 22, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortyfour :
    singleClusterMaxEnergyS 4 44 = (1936 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-22 6-vertex (hexamer) ground-state energy** (γ-5 step 562):
`singleClusterGSEnergyS 5 44 = -2442 = -S(1+zS)` for `S = 22, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortyfour :
    singleClusterGSEnergyS 5 44 = (-2442 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-22 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 562):
`singleClusterMaxEnergyS 5 44 = 2420 = zS²` for `S = 22, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortyfour :
    singleClusterMaxEnergyS 5 44 = (2420 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-22 7-vertex (heptamer) ground-state energy** (γ-5 step 563):
`singleClusterGSEnergyS 6 44 = -2926 = -S(1+zS)` for `S = 22, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortyfour :
    singleClusterGSEnergyS 6 44 = (-2926 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-22 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 563):
`singleClusterMaxEnergyS 6 44 = 2904 = zS²` for `S = 22, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortyfour :
    singleClusterMaxEnergyS 6 44 = (2904 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45/2 2-vertex (dimer) ground-state energy** (γ-5 step 564):
`singleClusterGSEnergyS 1 45 = -2115/4 = -S(S+1)` for `S = 45/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortyfive :
    singleClusterGSEnergyS 1 45 = (-2115 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 564):
`singleClusterMaxEnergyS 1 45 = 2025/4 = S²` for `S = 45/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortyfive :
    singleClusterMaxEnergyS 1 45 = (2025 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45/2 3-vertex (trimer) ground-state energy** (γ-5 step 565):
`singleClusterGSEnergyS 2 45 = -1035 = -S(1+zS)` for `S = 45/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortyfive :
    singleClusterGSEnergyS 2 45 = (-1035 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 565):
`singleClusterMaxEnergyS 2 45 = 2025/2 = zS²` for `S = 45/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortyfive :
    singleClusterMaxEnergyS 2 45 = (2025 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45/2 4-vertex (quartet) ground-state energy** (γ-5 step 566):
`singleClusterGSEnergyS 3 45 = -6165/4 = -S(1+zS)` for `S = 45/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortyfive :
    singleClusterGSEnergyS 3 45 = (-6165 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 566):
`singleClusterMaxEnergyS 3 45 = 6075/4 = zS²` for `S = 45/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortyfive :
    singleClusterMaxEnergyS 3 45 = (6075 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45/2 5-vertex (pentamer) ground-state energy** (γ-5 step 567):
`singleClusterGSEnergyS 4 45 = -4095/2 = -S(1+zS)` for `S = 45/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortyfive :
    singleClusterGSEnergyS 4 45 = (-4095 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 567):
`singleClusterMaxEnergyS 4 45 = 2025 = zS²` for `S = 45/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortyfive :
    singleClusterMaxEnergyS 4 45 = (2025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45/2 6-vertex (hexamer) ground-state energy** (γ-5 step 568):
`singleClusterGSEnergyS 5 45 = -10215/4 = -S(1+zS)` for `S = 45/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortyfive :
    singleClusterGSEnergyS 5 45 = (-10215 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 568):
`singleClusterMaxEnergyS 5 45 = 10125/4 = zS²` for `S = 45/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortyfive :
    singleClusterMaxEnergyS 5 45 = (10125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45/2 7-vertex (heptamer) ground-state energy** (γ-5 step 569):
`singleClusterGSEnergyS 6 45 = -3060 = -S(1+zS)` for `S = 45/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortyfive :
    singleClusterGSEnergyS 6 45 = (-3060 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 569):
`singleClusterMaxEnergyS 6 45 = 6075/2 = zS²` for `S = 45/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortyfive :
    singleClusterMaxEnergyS 6 45 = (6075 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23 2-vertex (dimer) ground-state energy** (γ-5 step 570):
`singleClusterGSEnergyS 1 46 = -552 = -S(S+1)` for `S = 23`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortysix :
    singleClusterGSEnergyS 1 46 = (-552 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 570):
`singleClusterMaxEnergyS 1 46 = 529 = S²` for `S = 23`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortysix :
    singleClusterMaxEnergyS 1 46 = (529 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23 3-vertex (trimer) ground-state energy** (γ-5 step 571):
`singleClusterGSEnergyS 2 46 = -1081 = -S(1+zS)` for `S = 23, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortysix :
    singleClusterGSEnergyS 2 46 = (-1081 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 571):
`singleClusterMaxEnergyS 2 46 = 1058 = zS²` for `S = 23, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortysix :
    singleClusterMaxEnergyS 2 46 = (1058 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23 4-vertex (quartet) ground-state energy** (γ-5 step 572):
`singleClusterGSEnergyS 3 46 = -1610 = -S(1+zS)` for `S = 23, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortysix :
    singleClusterGSEnergyS 3 46 = (-1610 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 572):
`singleClusterMaxEnergyS 3 46 = 1587 = zS²` for `S = 23, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortysix :
    singleClusterMaxEnergyS 3 46 = (1587 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23 5-vertex (pentamer) ground-state energy** (γ-5 step 573):
`singleClusterGSEnergyS 4 46 = -2139 = -S(1+zS)` for `S = 23, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortysix :
    singleClusterGSEnergyS 4 46 = (-2139 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 573):
`singleClusterMaxEnergyS 4 46 = 2116 = zS²` for `S = 23, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortysix :
    singleClusterMaxEnergyS 4 46 = (2116 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23 6-vertex (hexamer) ground-state energy** (γ-5 step 574):
`singleClusterGSEnergyS 5 46 = -2668 = -S(1+zS)` for `S = 23, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortysix :
    singleClusterGSEnergyS 5 46 = (-2668 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 574):
`singleClusterMaxEnergyS 5 46 = 2645 = zS²` for `S = 23, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortysix :
    singleClusterMaxEnergyS 5 46 = (2645 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23 7-vertex (heptamer) ground-state energy** (γ-5 step 575):
`singleClusterGSEnergyS 6 46 = -3197 = -S(1+zS)` for `S = 23, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortysix :
    singleClusterGSEnergyS 6 46 = (-3197 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 575):
`singleClusterMaxEnergyS 6 46 = 3174 = zS²` for `S = 23, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortysix :
    singleClusterMaxEnergyS 6 46 = (3174 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47/2 2-vertex (dimer) ground-state energy** (γ-5 step 576):
`singleClusterGSEnergyS 1 47 = -2303/4 = -S(S+1)` for `S = 47/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortyseven :
    singleClusterGSEnergyS 1 47 = (-2303 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 576):
`singleClusterMaxEnergyS 1 47 = 2209/4 = S²` for `S = 47/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortyseven :
    singleClusterMaxEnergyS 1 47 = (2209 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47/2 3-vertex (trimer) ground-state energy** (γ-5 step 577):
`singleClusterGSEnergyS 2 47 = -1128 = -S(1+zS)` for `S = 47/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortyseven :
    singleClusterGSEnergyS 2 47 = (-1128 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 577):
`singleClusterMaxEnergyS 2 47 = 2209/2 = zS²` for `S = 47/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortyseven :
    singleClusterMaxEnergyS 2 47 = (2209 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47/2 4-vertex (quartet) ground-state energy** (γ-5 step 578):
`singleClusterGSEnergyS 3 47 = -6721/4 = -S(1+zS)` for `S = 47/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortyseven :
    singleClusterGSEnergyS 3 47 = (-6721 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 578):
`singleClusterMaxEnergyS 3 47 = 6627/4 = zS²` for `S = 47/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortyseven :
    singleClusterMaxEnergyS 3 47 = (6627 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47/2 5-vertex (pentamer) ground-state energy** (γ-5 step 579):
`singleClusterGSEnergyS 4 47 = -4465/2 = -S(1+zS)` for `S = 47/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortyseven :
    singleClusterGSEnergyS 4 47 = (-4465 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 579):
`singleClusterMaxEnergyS 4 47 = 2209 = zS²` for `S = 47/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortyseven :
    singleClusterMaxEnergyS 4 47 = (2209 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47/2 6-vertex (hexamer) ground-state energy** (γ-5 step 580):
`singleClusterGSEnergyS 5 47 = -11139/4 = -S(1+zS)` for `S = 47/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortyseven :
    singleClusterGSEnergyS 5 47 = (-11139 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 580):
`singleClusterMaxEnergyS 5 47 = 11045/4 = zS²` for `S = 47/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortyseven :
    singleClusterMaxEnergyS 5 47 = (11045 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47/2 7-vertex (heptamer) ground-state energy** (γ-5 step 581):
`singleClusterGSEnergyS 6 47 = -3337 = -S(1+zS)` for `S = 47/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortyseven :
    singleClusterGSEnergyS 6 47 = (-3337 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 581):
`singleClusterMaxEnergyS 6 47 = 6627/2 = zS²` for `S = 47/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortyseven :
    singleClusterMaxEnergyS 6 47 = (6627 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
