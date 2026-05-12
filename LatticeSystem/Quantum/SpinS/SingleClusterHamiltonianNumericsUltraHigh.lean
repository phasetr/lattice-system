/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Ultra-high-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for
`48 ≤ N ≤ 59` (spin `24 ≤ S = N/2 ≤ 59/2`). The `N = 1..28`
specialisations live in `SingleClusterHamiltonianNumerics.lean`,
the `N = 29..38` in `SingleClusterHamiltonianNumericsHigh.lean`,
the `N = 39..47` in `SingleClusterHamiltonianNumericsVeryHigh.lean`,
the `N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`,
the `N = 116..131` in `SingleClusterHamiltonianNumericsInfiniteHigh.lean`,
the `N = 132..148` in `SingleClusterHamiltonianNumericsTransfiniteHigh.lean`,
the `N = 149..165` in `SingleClusterHamiltonianNumericsAbsoluteHigh.lean`,
and the `N ≥ 166` in `SingleClusterHamiltonianNumericsOmegaHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all eleven numerics files can elaborate
in parallel after the main file. Splitting was introduced as part of
the 50-PR build-performance cadence (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

/-- **Spin-24 2-vertex (dimer) ground-state energy** (γ-5 step 582):
`singleClusterGSEnergyS 1 48 = -600 = -S(S+1)` for `S = 24`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortyeight :
    singleClusterGSEnergyS 1 48 = (-600 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-24 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 582):
`singleClusterMaxEnergyS 1 48 = 576 = S²` for `S = 24`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortyeight :
    singleClusterMaxEnergyS 1 48 = (576 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-24 3-vertex (trimer) ground-state energy** (γ-5 step 583):
`singleClusterGSEnergyS 2 48 = -1176 = -S(1+zS)` for `S = 24, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortyeight :
    singleClusterGSEnergyS 2 48 = (-1176 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-24 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 583):
`singleClusterMaxEnergyS 2 48 = 1152 = zS²` for `S = 24, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortyeight :
    singleClusterMaxEnergyS 2 48 = (1152 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-24 4-vertex (quartet) ground-state energy** (γ-5 step 584):
`singleClusterGSEnergyS 3 48 = -1752 = -S(1+zS)` for `S = 24, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortyeight :
    singleClusterGSEnergyS 3 48 = (-1752 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-24 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 584):
`singleClusterMaxEnergyS 3 48 = 1728 = zS²` for `S = 24, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortyeight :
    singleClusterMaxEnergyS 3 48 = (1728 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-24 5-vertex (pentamer) ground-state energy** (γ-5 step 585):
`singleClusterGSEnergyS 4 48 = -2328 = -S(1+zS)` for `S = 24, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortyeight :
    singleClusterGSEnergyS 4 48 = (-2328 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-24 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 585):
`singleClusterMaxEnergyS 4 48 = 2304 = zS²` for `S = 24, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortyeight :
    singleClusterMaxEnergyS 4 48 = (2304 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-24 6-vertex (hexamer) ground-state energy** (γ-5 step 586):
`singleClusterGSEnergyS 5 48 = -2904 = -S(1+zS)` for `S = 24, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortyeight :
    singleClusterGSEnergyS 5 48 = (-2904 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-24 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 586):
`singleClusterMaxEnergyS 5 48 = 2880 = zS²` for `S = 24, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortyeight :
    singleClusterMaxEnergyS 5 48 = (2880 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-24 7-vertex (heptamer) ground-state energy** (γ-5 step 587):
`singleClusterGSEnergyS 6 48 = -3480 = -S(1+zS)` for `S = 24, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortyeight :
    singleClusterGSEnergyS 6 48 = (-3480 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-24 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 587):
`singleClusterMaxEnergyS 6 48 = 3456 = zS²` for `S = 24, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortyeight :
    singleClusterMaxEnergyS 6 48 = (3456 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49/2 2-vertex (dimer) ground-state energy** (γ-5 step 588):
`singleClusterGSEnergyS 1 49 = -2499/4 = -S(S+1)` for `S = 49/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fortynine :
    singleClusterGSEnergyS 1 49 = (-2499 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 588):
`singleClusterMaxEnergyS 1 49 = 2401/4 = S²` for `S = 49/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fortynine :
    singleClusterMaxEnergyS 1 49 = (2401 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49/2 3-vertex (trimer) ground-state energy** (γ-5 step 589):
`singleClusterGSEnergyS 2 49 = -1225 = -S(1+zS)` for `S = 49/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fortynine :
    singleClusterGSEnergyS 2 49 = (-1225 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 589):
`singleClusterMaxEnergyS 2 49 = 2401/2 = zS²` for `S = 49/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fortynine :
    singleClusterMaxEnergyS 2 49 = (2401 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49/2 4-vertex (quartet) ground-state energy** (γ-5 step 590):
`singleClusterGSEnergyS 3 49 = -7301/4 = -S(1+zS)` for `S = 49/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fortynine :
    singleClusterGSEnergyS 3 49 = (-7301 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 590):
`singleClusterMaxEnergyS 3 49 = 7203/4 = zS²` for `S = 49/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fortynine :
    singleClusterMaxEnergyS 3 49 = (7203 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49/2 5-vertex (pentamer) ground-state energy** (γ-5 step 591):
`singleClusterGSEnergyS 4 49 = -4851/2 = -S(1+zS)` for `S = 49/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fortynine :
    singleClusterGSEnergyS 4 49 = (-4851 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 591):
`singleClusterMaxEnergyS 4 49 = 2401 = zS²` for `S = 49/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fortynine :
    singleClusterMaxEnergyS 4 49 = (2401 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49/2 6-vertex (hexamer) ground-state energy** (γ-5 step 592):
`singleClusterGSEnergyS 5 49 = -12103/4 = -S(1+zS)` for `S = 49/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fortynine :
    singleClusterGSEnergyS 5 49 = (-12103 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 592):
`singleClusterMaxEnergyS 5 49 = 12005/4 = zS²` for `S = 49/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fortynine :
    singleClusterMaxEnergyS 5 49 = (12005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49/2 7-vertex (heptamer) ground-state energy** (γ-5 step 593):
`singleClusterGSEnergyS 6 49 = -3626 = -S(1+zS)` for `S = 49/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fortynine :
    singleClusterGSEnergyS 6 49 = (-3626 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 593):
`singleClusterMaxEnergyS 6 49 = 7203/2 = zS²` for `S = 49/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fortynine :
    singleClusterMaxEnergyS 6 49 = (7203 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25 2-vertex (dimer) ground-state energy** (γ-5 step 594):
`singleClusterGSEnergyS 1 50 = -650 = -S(S+1)` for `S = 25`. -/
@[simp] theorem singleClusterGSEnergyS_one_fifty :
    singleClusterGSEnergyS 1 50 = (-650 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 594):
`singleClusterMaxEnergyS 1 50 = 625 = S²` for `S = 25`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fifty :
    singleClusterMaxEnergyS 1 50 = (625 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25 3-vertex (trimer) ground-state energy** (γ-5 step 595):
`singleClusterGSEnergyS 2 50 = -1275 = -S(1+zS)` for `S = 25, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fifty :
    singleClusterGSEnergyS 2 50 = (-1275 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 595):
`singleClusterMaxEnergyS 2 50 = 1250 = zS²` for `S = 25, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fifty :
    singleClusterMaxEnergyS 2 50 = (1250 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25 4-vertex (quartet) ground-state energy** (γ-5 step 596):
`singleClusterGSEnergyS 3 50 = -1900 = -S(1+zS)` for `S = 25, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fifty :
    singleClusterGSEnergyS 3 50 = (-1900 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 596):
`singleClusterMaxEnergyS 3 50 = 1875 = zS²` for `S = 25, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fifty :
    singleClusterMaxEnergyS 3 50 = (1875 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25 5-vertex (pentamer) ground-state energy** (γ-5 step 597):
`singleClusterGSEnergyS 4 50 = -2525 = -S(1+zS)` for `S = 25, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fifty :
    singleClusterGSEnergyS 4 50 = (-2525 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 597):
`singleClusterMaxEnergyS 4 50 = 2500 = zS²` for `S = 25, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fifty :
    singleClusterMaxEnergyS 4 50 = (2500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25 6-vertex (hexamer) ground-state energy** (γ-5 step 598):
`singleClusterGSEnergyS 5 50 = -3150 = -S(1+zS)` for `S = 25, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fifty :
    singleClusterGSEnergyS 5 50 = (-3150 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 598):
`singleClusterMaxEnergyS 5 50 = 3125 = zS²` for `S = 25, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fifty :
    singleClusterMaxEnergyS 5 50 = (3125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25 7-vertex (heptamer) ground-state energy** (γ-5 step 599):
`singleClusterGSEnergyS 6 50 = -3775 = -S(1+zS)` for `S = 25, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fifty :
    singleClusterGSEnergyS 6 50 = (-3775 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 599):
`singleClusterMaxEnergyS 6 50 = 3750 = zS²` for `S = 25, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fifty :
    singleClusterMaxEnergyS 6 50 = (3750 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51/2 2-vertex (dimer) ground-state energy** (γ-5 step 600):
`singleClusterGSEnergyS 1 51 = -2703/4 = -S(S+1)` for `S = 51/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftyone :
    singleClusterGSEnergyS 1 51 = (-2703 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 600):
`singleClusterMaxEnergyS 1 51 = 2601/4 = S²` for `S = 51/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftyone :
    singleClusterMaxEnergyS 1 51 = (2601 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51/2 3-vertex (trimer) ground-state energy** (γ-5 step 601):
`singleClusterGSEnergyS 2 51 = -1326 = -S(1+zS)` for `S = 51/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftyone :
    singleClusterGSEnergyS 2 51 = (-1326 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 601):
`singleClusterMaxEnergyS 2 51 = 2601/2 = zS²` for `S = 51/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftyone :
    singleClusterMaxEnergyS 2 51 = (2601 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51/2 4-vertex (quartet) ground-state energy** (γ-5 step 602):
`singleClusterGSEnergyS 3 51 = -7905/4 = -S(1+zS)` for `S = 51/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftyone :
    singleClusterGSEnergyS 3 51 = (-7905 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 602):
`singleClusterMaxEnergyS 3 51 = 7803/4 = zS²` for `S = 51/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftyone :
    singleClusterMaxEnergyS 3 51 = (7803 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51/2 5-vertex (pentamer) ground-state energy** (γ-5 step 603):
`singleClusterGSEnergyS 4 51 = -5253/2 = -S(1+zS)` for `S = 51/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftyone :
    singleClusterGSEnergyS 4 51 = (-5253 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 603):
`singleClusterMaxEnergyS 4 51 = 2601 = zS²` for `S = 51/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftyone :
    singleClusterMaxEnergyS 4 51 = (2601 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51/2 6-vertex (hexamer) ground-state energy** (γ-5 step 604):
`singleClusterGSEnergyS 5 51 = -13107/4 = -S(1+zS)` for `S = 51/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftyone :
    singleClusterGSEnergyS 5 51 = (-13107 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 604):
`singleClusterMaxEnergyS 5 51 = 13005/4 = zS²` for `S = 51/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftyone :
    singleClusterMaxEnergyS 5 51 = (13005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51/2 7-vertex (heptamer) ground-state energy** (γ-5 step 605):
`singleClusterGSEnergyS 6 51 = -3927 = -S(1+zS)` for `S = 51/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftyone :
    singleClusterGSEnergyS 6 51 = (-3927 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 605):
`singleClusterMaxEnergyS 6 51 = 7803/2 = zS²` for `S = 51/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftyone :
    singleClusterMaxEnergyS 6 51 = (7803 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-26 2-vertex (dimer) ground-state energy** (γ-5 step 606):
`singleClusterGSEnergyS 1 52 = -702 = -S(S+1)` for `S = 26`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftytwo :
    singleClusterGSEnergyS 1 52 = (-702 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-26 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 606):
`singleClusterMaxEnergyS 1 52 = 676 = S²` for `S = 26`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftytwo :
    singleClusterMaxEnergyS 1 52 = (676 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-26 3-vertex (trimer) ground-state energy** (γ-5 step 607):
`singleClusterGSEnergyS 2 52 = -1378 = -S(1+zS)` for `S = 26, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftytwo :
    singleClusterGSEnergyS 2 52 = (-1378 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-26 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 607):
`singleClusterMaxEnergyS 2 52 = 1352 = zS²` for `S = 26, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftytwo :
    singleClusterMaxEnergyS 2 52 = (1352 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-26 4-vertex (quartet) ground-state energy** (γ-5 step 608):
`singleClusterGSEnergyS 3 52 = -2054 = -S(1+zS)` for `S = 26, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftytwo :
    singleClusterGSEnergyS 3 52 = (-2054 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-26 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 608):
`singleClusterMaxEnergyS 3 52 = 2028 = zS²` for `S = 26, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftytwo :
    singleClusterMaxEnergyS 3 52 = (2028 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-26 5-vertex (pentamer) ground-state energy** (γ-5 step 609):
`singleClusterGSEnergyS 4 52 = -2730 = -S(1+zS)` for `S = 26, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftytwo :
    singleClusterGSEnergyS 4 52 = (-2730 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-26 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 609):
`singleClusterMaxEnergyS 4 52 = 2704 = zS²` for `S = 26, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftytwo :
    singleClusterMaxEnergyS 4 52 = (2704 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-26 6-vertex (hexamer) ground-state energy** (γ-5 step 610):
`singleClusterGSEnergyS 5 52 = -3406 = -S(1+zS)` for `S = 26, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftytwo :
    singleClusterGSEnergyS 5 52 = (-3406 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-26 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 610):
`singleClusterMaxEnergyS 5 52 = 3380 = zS²` for `S = 26, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftytwo :
    singleClusterMaxEnergyS 5 52 = (3380 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-26 7-vertex (heptamer) ground-state energy** (γ-5 step 611):
`singleClusterGSEnergyS 6 52 = -4082 = -S(1+zS)` for `S = 26, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftytwo :
    singleClusterGSEnergyS 6 52 = (-4082 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-26 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 611):
`singleClusterMaxEnergyS 6 52 = 4056 = zS²` for `S = 26, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftytwo :
    singleClusterMaxEnergyS 6 52 = (4056 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53/2 2-vertex (dimer) ground-state energy** (γ-5 step 612):
`singleClusterGSEnergyS 1 53 = -2915/4 = -S(S+1)` for `S = 53/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftythree :
    singleClusterGSEnergyS 1 53 = (-2915 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 612):
`singleClusterMaxEnergyS 1 53 = 2809/4 = S²` for `S = 53/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftythree :
    singleClusterMaxEnergyS 1 53 = (2809 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53/2 3-vertex (trimer) ground-state energy** (γ-5 step 613):
`singleClusterGSEnergyS 2 53 = -1431 = -S(1+zS)` for `S = 53/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftythree :
    singleClusterGSEnergyS 2 53 = (-1431 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 613):
`singleClusterMaxEnergyS 2 53 = 2809/2 = zS²` for `S = 53/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftythree :
    singleClusterMaxEnergyS 2 53 = (2809 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53/2 4-vertex (quartet) ground-state energy** (γ-5 step 614):
`singleClusterGSEnergyS 3 53 = -8533/4 = -S(1+zS)` for `S = 53/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftythree :
    singleClusterGSEnergyS 3 53 = (-8533 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 614):
`singleClusterMaxEnergyS 3 53 = 8427/4 = zS²` for `S = 53/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftythree :
    singleClusterMaxEnergyS 3 53 = (8427 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53/2 5-vertex (pentamer) ground-state energy** (γ-5 step 615):
`singleClusterGSEnergyS 4 53 = -5671/2 = -S(1+zS)` for `S = 53/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftythree :
    singleClusterGSEnergyS 4 53 = (-5671 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 615):
`singleClusterMaxEnergyS 4 53 = 2809 = zS²` for `S = 53/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftythree :
    singleClusterMaxEnergyS 4 53 = (2809 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53/2 6-vertex (hexamer) ground-state energy** (γ-5 step 616):
`singleClusterGSEnergyS 5 53 = -14151/4 = -S(1+zS)` for `S = 53/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftythree :
    singleClusterGSEnergyS 5 53 = (-14151 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 616):
`singleClusterMaxEnergyS 5 53 = 14045/4 = zS²` for `S = 53/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftythree :
    singleClusterMaxEnergyS 5 53 = (14045 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53/2 7-vertex (heptamer) ground-state energy** (γ-5 step 617):
`singleClusterGSEnergyS 6 53 = -4240 = -S(1+zS)` for `S = 53/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftythree :
    singleClusterGSEnergyS 6 53 = (-4240 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 617):
`singleClusterMaxEnergyS 6 53 = 8427/2 = zS²` for `S = 53/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftythree :
    singleClusterMaxEnergyS 6 53 = (8427 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27 2-vertex (dimer) ground-state energy** (γ-5 step 618):
`singleClusterGSEnergyS 1 54 = -756 = -S(S+1)` for `S = 27`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftyfour :
    singleClusterGSEnergyS 1 54 = (-756 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 618):
`singleClusterMaxEnergyS 1 54 = 729 = S²` for `S = 27`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftyfour :
    singleClusterMaxEnergyS 1 54 = (729 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27 3-vertex (trimer) ground-state energy** (γ-5 step 619):
`singleClusterGSEnergyS 2 54 = -1485 = -S(1+zS)` for `S = 27, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftyfour :
    singleClusterGSEnergyS 2 54 = (-1485 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 619):
`singleClusterMaxEnergyS 2 54 = 1458 = zS²` for `S = 27, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftyfour :
    singleClusterMaxEnergyS 2 54 = (1458 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27 4-vertex (quartet) ground-state energy** (γ-5 step 620):
`singleClusterGSEnergyS 3 54 = -2214 = -S(1+zS)` for `S = 27, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftyfour :
    singleClusterGSEnergyS 3 54 = (-2214 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 620):
`singleClusterMaxEnergyS 3 54 = 2187 = zS²` for `S = 27, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftyfour :
    singleClusterMaxEnergyS 3 54 = (2187 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27 5-vertex (pentamer) ground-state energy** (γ-5 step 621):
`singleClusterGSEnergyS 4 54 = -2943 = -S(1+zS)` for `S = 27, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftyfour :
    singleClusterGSEnergyS 4 54 = (-2943 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 621):
`singleClusterMaxEnergyS 4 54 = 2916 = zS²` for `S = 27, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftyfour :
    singleClusterMaxEnergyS 4 54 = (2916 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27 6-vertex (hexamer) ground-state energy** (γ-5 step 622):
`singleClusterGSEnergyS 5 54 = -3672 = -S(1+zS)` for `S = 27, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftyfour :
    singleClusterGSEnergyS 5 54 = (-3672 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 622):
`singleClusterMaxEnergyS 5 54 = 3645 = zS²` for `S = 27, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftyfour :
    singleClusterMaxEnergyS 5 54 = (3645 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27 7-vertex (heptamer) ground-state energy** (γ-5 step 623):
`singleClusterGSEnergyS 6 54 = -4401 = -S(1+zS)` for `S = 27, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftyfour :
    singleClusterGSEnergyS 6 54 = (-4401 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 623):
`singleClusterMaxEnergyS 6 54 = 4374 = zS²` for `S = 27, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftyfour :
    singleClusterMaxEnergyS 6 54 = (4374 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55/2 2-vertex (dimer) ground-state energy** (γ-5 step 624):
`singleClusterGSEnergyS 1 55 = -3135/4 = -S(S+1)` for `S = 55/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftyfive :
    singleClusterGSEnergyS 1 55 = (-3135 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 624):
`singleClusterMaxEnergyS 1 55 = 3025/4 = S²` for `S = 55/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftyfive :
    singleClusterMaxEnergyS 1 55 = (3025 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55/2 3-vertex (trimer) ground-state energy** (γ-5 step 625):
`singleClusterGSEnergyS 2 55 = -1540 = -S(1+zS)` for `S = 55/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftyfive :
    singleClusterGSEnergyS 2 55 = (-1540 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 625):
`singleClusterMaxEnergyS 2 55 = 3025/2 = zS²` for `S = 55/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftyfive :
    singleClusterMaxEnergyS 2 55 = (3025 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55/2 4-vertex (quartet) ground-state energy** (γ-5 step 626):
`singleClusterGSEnergyS 3 55 = -9185/4 = -S(1+zS)` for `S = 55/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftyfive :
    singleClusterGSEnergyS 3 55 = (-9185 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 626):
`singleClusterMaxEnergyS 3 55 = 9075/4 = zS²` for `S = 55/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftyfive :
    singleClusterMaxEnergyS 3 55 = (9075 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55/2 5-vertex (pentamer) ground-state energy** (γ-5 step 627):
`singleClusterGSEnergyS 4 55 = -6105/2 = -S(1+zS)` for `S = 55/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftyfive :
    singleClusterGSEnergyS 4 55 = (-6105 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 627):
`singleClusterMaxEnergyS 4 55 = 3025 = zS²` for `S = 55/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftyfive :
    singleClusterMaxEnergyS 4 55 = (3025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55/2 6-vertex (hexamer) ground-state energy** (γ-5 step 628):
`singleClusterGSEnergyS 5 55 = -15235/4 = -S(1+zS)` for `S = 55/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftyfive :
    singleClusterGSEnergyS 5 55 = (-15235 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 628):
`singleClusterMaxEnergyS 5 55 = 15125/4 = zS²` for `S = 55/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftyfive :
    singleClusterMaxEnergyS 5 55 = (15125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55/2 7-vertex (heptamer) ground-state energy** (γ-5 step 629):
`singleClusterGSEnergyS 6 55 = -4565 = -S(1+zS)` for `S = 55/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftyfive :
    singleClusterGSEnergyS 6 55 = (-4565 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 629):
`singleClusterMaxEnergyS 6 55 = 9075/2 = zS²` for `S = 55/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftyfive :
    singleClusterMaxEnergyS 6 55 = (9075 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-28 2-vertex (dimer) ground-state energy** (γ-5 step 630):
`singleClusterGSEnergyS 1 56 = -812 = -S(S+1)` for `S = 28`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftysix :
    singleClusterGSEnergyS 1 56 = (-812 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-28 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 630):
`singleClusterMaxEnergyS 1 56 = 784 = S²` for `S = 28`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftysix :
    singleClusterMaxEnergyS 1 56 = (784 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-28 3-vertex (trimer) ground-state energy** (γ-5 step 631):
`singleClusterGSEnergyS 2 56 = -1596 = -S(1+zS)` for `S = 28, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftysix :
    singleClusterGSEnergyS 2 56 = (-1596 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-28 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 631):
`singleClusterMaxEnergyS 2 56 = 1568 = zS²` for `S = 28, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftysix :
    singleClusterMaxEnergyS 2 56 = (1568 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-28 4-vertex (quartet) ground-state energy** (γ-5 step 632):
`singleClusterGSEnergyS 3 56 = -2380 = -S(1+zS)` for `S = 28, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftysix :
    singleClusterGSEnergyS 3 56 = (-2380 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-28 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 632):
`singleClusterMaxEnergyS 3 56 = 2352 = zS²` for `S = 28, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftysix :
    singleClusterMaxEnergyS 3 56 = (2352 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-28 5-vertex (pentamer) ground-state energy** (γ-5 step 633):
`singleClusterGSEnergyS 4 56 = -3164 = -S(1+zS)` for `S = 28, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftysix :
    singleClusterGSEnergyS 4 56 = (-3164 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-28 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 633):
`singleClusterMaxEnergyS 4 56 = 3136 = zS²` for `S = 28, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftysix :
    singleClusterMaxEnergyS 4 56 = (3136 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-28 6-vertex (hexamer) ground-state energy** (γ-5 step 634):
`singleClusterGSEnergyS 5 56 = -3948 = -S(1+zS)` for `S = 28, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftysix :
    singleClusterGSEnergyS 5 56 = (-3948 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-28 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 634):
`singleClusterMaxEnergyS 5 56 = 3920 = zS²` for `S = 28, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftysix :
    singleClusterMaxEnergyS 5 56 = (3920 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-28 7-vertex (heptamer) ground-state energy** (γ-5 step 635):
`singleClusterGSEnergyS 6 56 = -4732 = -S(1+zS)` for `S = 28, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftysix :
    singleClusterGSEnergyS 6 56 = (-4732 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-28 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 635):
`singleClusterMaxEnergyS 6 56 = 4704 = zS²` for `S = 28, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftysix :
    singleClusterMaxEnergyS 6 56 = (4704 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57/2 2-vertex (dimer) ground-state energy** (γ-5 step 636):
`singleClusterGSEnergyS 1 57 = -3363/4 = -S(S+1)` for `S = 57/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftyseven :
    singleClusterGSEnergyS 1 57 = (-3363 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 636):
`singleClusterMaxEnergyS 1 57 = 3249/4 = S²` for `S = 57/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftyseven :
    singleClusterMaxEnergyS 1 57 = (3249 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57/2 3-vertex (trimer) ground-state energy** (γ-5 step 637):
`singleClusterGSEnergyS 2 57 = -1653 = -S(1+zS)` for `S = 57/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftyseven :
    singleClusterGSEnergyS 2 57 = (-1653 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 637):
`singleClusterMaxEnergyS 2 57 = 3249/2 = zS²` for `S = 57/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftyseven :
    singleClusterMaxEnergyS 2 57 = (3249 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57/2 4-vertex (quartet) ground-state energy** (γ-5 step 638):
`singleClusterGSEnergyS 3 57 = -9861/4 = -S(1+zS)` for `S = 57/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftyseven :
    singleClusterGSEnergyS 3 57 = (-9861 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 638):
`singleClusterMaxEnergyS 3 57 = 9747/4 = zS²` for `S = 57/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftyseven :
    singleClusterMaxEnergyS 3 57 = (9747 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57/2 5-vertex (pentamer) ground-state energy** (γ-5 step 639):
`singleClusterGSEnergyS 4 57 = -6555/2 = -S(1+zS)` for `S = 57/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftyseven :
    singleClusterGSEnergyS 4 57 = (-6555 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 639):
`singleClusterMaxEnergyS 4 57 = 3249 = zS²` for `S = 57/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftyseven :
    singleClusterMaxEnergyS 4 57 = (3249 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57/2 6-vertex (hexamer) ground-state energy** (γ-5 step 640):
`singleClusterGSEnergyS 5 57 = -16359/4 = -S(1+zS)` for `S = 57/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftyseven :
    singleClusterGSEnergyS 5 57 = (-16359 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 640):
`singleClusterMaxEnergyS 5 57 = 16245/4 = zS²` for `S = 57/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftyseven :
    singleClusterMaxEnergyS 5 57 = (16245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57/2 7-vertex (heptamer) ground-state energy** (γ-5 step 641):
`singleClusterGSEnergyS 6 57 = -4902 = -S(1+zS)` for `S = 57/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftyseven :
    singleClusterGSEnergyS 6 57 = (-4902 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 641):
`singleClusterMaxEnergyS 6 57 = 9747/2 = zS²` for `S = 57/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftyseven :
    singleClusterMaxEnergyS 6 57 = (9747 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29 2-vertex (dimer) ground-state energy** (γ-5 step 642):
`singleClusterGSEnergyS 1 58 = -870 = -S(S+1)` for `S = 29`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftyeight :
    singleClusterGSEnergyS 1 58 = (-870 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 642):
`singleClusterMaxEnergyS 1 58 = 841 = S²` for `S = 29`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftyeight :
    singleClusterMaxEnergyS 1 58 = (841 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29 3-vertex (trimer) ground-state energy** (γ-5 step 643):
`singleClusterGSEnergyS 2 58 = -1711 = -S(1+zS)` for `S = 29, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftyeight :
    singleClusterGSEnergyS 2 58 = (-1711 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 643):
`singleClusterMaxEnergyS 2 58 = 1682 = zS²` for `S = 29, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftyeight :
    singleClusterMaxEnergyS 2 58 = (1682 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29 4-vertex (quartet) ground-state energy** (γ-5 step 644):
`singleClusterGSEnergyS 3 58 = -2552 = -S(1+zS)` for `S = 29, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftyeight :
    singleClusterGSEnergyS 3 58 = (-2552 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 644):
`singleClusterMaxEnergyS 3 58 = 2523 = zS²` for `S = 29, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftyeight :
    singleClusterMaxEnergyS 3 58 = (2523 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29 5-vertex (pentamer) ground-state energy** (γ-5 step 645):
`singleClusterGSEnergyS 4 58 = -3393 = -S(1+zS)` for `S = 29, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftyeight :
    singleClusterGSEnergyS 4 58 = (-3393 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 645):
`singleClusterMaxEnergyS 4 58 = 3364 = zS²` for `S = 29, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftyeight :
    singleClusterMaxEnergyS 4 58 = (3364 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29 6-vertex (hexamer) ground-state energy** (γ-5 step 646):
`singleClusterGSEnergyS 5 58 = -4234 = -S(1+zS)` for `S = 29, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftyeight :
    singleClusterGSEnergyS 5 58 = (-4234 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 646):
`singleClusterMaxEnergyS 5 58 = 4205 = zS²` for `S = 29, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftyeight :
    singleClusterMaxEnergyS 5 58 = (4205 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29 7-vertex (heptamer) ground-state energy** (γ-5 step 647):
`singleClusterGSEnergyS 6 58 = -5075 = -S(1+zS)` for `S = 29, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftyeight :
    singleClusterGSEnergyS 6 58 = (-5075 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 647):
`singleClusterMaxEnergyS 6 58 = 5046 = zS²` for `S = 29, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftyeight :
    singleClusterMaxEnergyS 6 58 = (5046 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59/2 2-vertex (dimer) ground-state energy** (γ-5 step 648):
`singleClusterGSEnergyS 1 59 = -3599/4 = -S(S+1)` for `S = 59/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fiftynine :
    singleClusterGSEnergyS 1 59 = (-3599 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 648):
`singleClusterMaxEnergyS 1 59 = 3481/4 = S²` for `S = 59/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fiftynine :
    singleClusterMaxEnergyS 1 59 = (3481 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59/2 3-vertex (trimer) ground-state energy** (γ-5 step 649):
`singleClusterGSEnergyS 2 59 = -1770 = -S(1+zS)` for `S = 59/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fiftynine :
    singleClusterGSEnergyS 2 59 = (-1770 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 649):
`singleClusterMaxEnergyS 2 59 = 3481/2 = zS²` for `S = 59/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fiftynine :
    singleClusterMaxEnergyS 2 59 = (3481 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59/2 4-vertex (quartet) ground-state energy** (γ-5 step 650):
`singleClusterGSEnergyS 3 59 = -10561/4 = -S(1+zS)` for `S = 59/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fiftynine :
    singleClusterGSEnergyS 3 59 = (-10561 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 650):
`singleClusterMaxEnergyS 3 59 = 10443/4 = zS²` for `S = 59/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fiftynine :
    singleClusterMaxEnergyS 3 59 = (10443 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59/2 5-vertex (pentamer) ground-state energy** (γ-5 step 651):
`singleClusterGSEnergyS 4 59 = -7021/2 = -S(1+zS)` for `S = 59/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fiftynine :
    singleClusterGSEnergyS 4 59 = (-7021 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 651):
`singleClusterMaxEnergyS 4 59 = 3481 = zS²` for `S = 59/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fiftynine :
    singleClusterMaxEnergyS 4 59 = (3481 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59/2 6-vertex (hexamer) ground-state energy** (γ-5 step 652):
`singleClusterGSEnergyS 5 59 = -17523/4 = -S(1+zS)` for `S = 59/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fiftynine :
    singleClusterGSEnergyS 5 59 = (-17523 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 652):
`singleClusterMaxEnergyS 5 59 = 17405/4 = zS²` for `S = 59/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fiftynine :
    singleClusterMaxEnergyS 5 59 = (17405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59/2 7-vertex (heptamer) ground-state energy** (γ-5 step 653):
`singleClusterGSEnergyS 6 59 = -5251 = -S(1+zS)` for `S = 59/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fiftynine :
    singleClusterGSEnergyS 6 59 = (-5251 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 653):
`singleClusterMaxEnergyS 6 59 = 10443/2 = zS²` for `S = 59/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fiftynine :
    singleClusterMaxEnergyS 6 59 = (10443 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
