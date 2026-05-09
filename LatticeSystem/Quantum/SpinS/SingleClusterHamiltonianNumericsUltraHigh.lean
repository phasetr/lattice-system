/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Ultra-high-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 48`
(spin `S = N/2 ≥ 24`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, and the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all four numerics files can elaborate
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

/-- **Spin-30 2-vertex (dimer) ground-state energy** (γ-5 step 654):
`singleClusterGSEnergyS 1 60 = -930 = -S(S+1)` for `S = 30`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixty :
    singleClusterGSEnergyS 1 60 = (-930 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-30 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 654):
`singleClusterMaxEnergyS 1 60 = 900 = S²` for `S = 30`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixty :
    singleClusterMaxEnergyS 1 60 = (900 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-30 3-vertex (trimer) ground-state energy** (γ-5 step 655):
`singleClusterGSEnergyS 2 60 = -1830 = -S(1+zS)` for `S = 30, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixty :
    singleClusterGSEnergyS 2 60 = (-1830 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-30 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 655):
`singleClusterMaxEnergyS 2 60 = 1800 = zS²` for `S = 30, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixty :
    singleClusterMaxEnergyS 2 60 = (1800 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-30 4-vertex (quartet) ground-state energy** (γ-5 step 656):
`singleClusterGSEnergyS 3 60 = -2730 = -S(1+zS)` for `S = 30, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixty :
    singleClusterGSEnergyS 3 60 = (-2730 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-30 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 656):
`singleClusterMaxEnergyS 3 60 = 2700 = zS²` for `S = 30, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixty :
    singleClusterMaxEnergyS 3 60 = (2700 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-30 5-vertex (pentamer) ground-state energy** (γ-5 step 657):
`singleClusterGSEnergyS 4 60 = -3630 = -S(1+zS)` for `S = 30, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixty :
    singleClusterGSEnergyS 4 60 = (-3630 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-30 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 657):
`singleClusterMaxEnergyS 4 60 = 3600 = zS²` for `S = 30, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixty :
    singleClusterMaxEnergyS 4 60 = (3600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-30 6-vertex (hexamer) ground-state energy** (γ-5 step 658):
`singleClusterGSEnergyS 5 60 = -4530 = -S(1+zS)` for `S = 30, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixty :
    singleClusterGSEnergyS 5 60 = (-4530 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-30 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 658):
`singleClusterMaxEnergyS 5 60 = 4500 = zS²` for `S = 30, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixty :
    singleClusterMaxEnergyS 5 60 = (4500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-30 7-vertex (heptamer) ground-state energy** (γ-5 step 659):
`singleClusterGSEnergyS 6 60 = -5430 = -S(1+zS)` for `S = 30, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixty :
    singleClusterGSEnergyS 6 60 = (-5430 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-30 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 659):
`singleClusterMaxEnergyS 6 60 = 5400 = zS²` for `S = 30, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixty :
    singleClusterMaxEnergyS 6 60 = (5400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61/2 2-vertex (dimer) ground-state energy** (γ-5 step 660):
`singleClusterGSEnergyS 1 61 = -3843/4 = -S(S+1)` for `S = 61/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtyone :
    singleClusterGSEnergyS 1 61 = (-3843 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 660):
`singleClusterMaxEnergyS 1 61 = 3721/4 = S²` for `S = 61/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtyone :
    singleClusterMaxEnergyS 1 61 = (3721 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61/2 3-vertex (trimer) ground-state energy** (γ-5 step 661):
`singleClusterGSEnergyS 2 61 = -1891 = -S(1+zS)` for `S = 61/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtyone :
    singleClusterGSEnergyS 2 61 = (-1891 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 661):
`singleClusterMaxEnergyS 2 61 = 3721/2 = zS²` for `S = 61/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtyone :
    singleClusterMaxEnergyS 2 61 = (3721 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61/2 4-vertex (quartet) ground-state energy** (γ-5 step 662):
`singleClusterGSEnergyS 3 61 = -11285/4 = -S(1+zS)` for `S = 61/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtyone :
    singleClusterGSEnergyS 3 61 = (-11285 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 662):
`singleClusterMaxEnergyS 3 61 = 11163/4 = zS²` for `S = 61/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtyone :
    singleClusterMaxEnergyS 3 61 = (11163 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61/2 5-vertex (pentamer) ground-state energy** (γ-5 step 663):
`singleClusterGSEnergyS 4 61 = -7503/2 = -S(1+zS)` for `S = 61/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtyone :
    singleClusterGSEnergyS 4 61 = (-7503 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 663):
`singleClusterMaxEnergyS 4 61 = 3721 = zS²` for `S = 61/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtyone :
    singleClusterMaxEnergyS 4 61 = (3721 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61/2 6-vertex (hexamer) ground-state energy** (γ-5 step 664):
`singleClusterGSEnergyS 5 61 = -18727/4 = -S(1+zS)` for `S = 61/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtyone :
    singleClusterGSEnergyS 5 61 = (-18727 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 664):
`singleClusterMaxEnergyS 5 61 = 18605/4 = zS²` for `S = 61/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtyone :
    singleClusterMaxEnergyS 5 61 = (18605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61/2 7-vertex (heptamer) ground-state energy** (γ-5 step 665):
`singleClusterGSEnergyS 6 61 = -5612 = -S(1+zS)` for `S = 61/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtyone :
    singleClusterGSEnergyS 6 61 = (-5612 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 665):
`singleClusterMaxEnergyS 6 61 = 11163/2 = zS²` for `S = 61/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtyone :
    singleClusterMaxEnergyS 6 61 = (11163 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31 2-vertex (dimer) ground-state energy** (γ-5 step 666):
`singleClusterGSEnergyS 1 62 = -992 = -S(S+1)` for `S = 31`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtytwo :
    singleClusterGSEnergyS 1 62 = (-992 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 666):
`singleClusterMaxEnergyS 1 62 = 961 = S²` for `S = 31`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtytwo :
    singleClusterMaxEnergyS 1 62 = (961 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31 3-vertex (trimer) ground-state energy** (γ-5 step 667):
`singleClusterGSEnergyS 2 62 = -1953 = -S(1+zS)` for `S = 31, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtytwo :
    singleClusterGSEnergyS 2 62 = (-1953 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 667):
`singleClusterMaxEnergyS 2 62 = 1922 = zS²` for `S = 31, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtytwo :
    singleClusterMaxEnergyS 2 62 = (1922 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31 4-vertex (quartet) ground-state energy** (γ-5 step 668):
`singleClusterGSEnergyS 3 62 = -2914 = -S(1+zS)` for `S = 31, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtytwo :
    singleClusterGSEnergyS 3 62 = (-2914 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 668):
`singleClusterMaxEnergyS 3 62 = 2883 = zS²` for `S = 31, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtytwo :
    singleClusterMaxEnergyS 3 62 = (2883 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31 5-vertex (pentamer) ground-state energy** (γ-5 step 669):
`singleClusterGSEnergyS 4 62 = -3875 = -S(1+zS)` for `S = 31, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtytwo :
    singleClusterGSEnergyS 4 62 = (-3875 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 669):
`singleClusterMaxEnergyS 4 62 = 3844 = zS²` for `S = 31, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtytwo :
    singleClusterMaxEnergyS 4 62 = (3844 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31 6-vertex (hexamer) ground-state energy** (γ-5 step 670):
`singleClusterGSEnergyS 5 62 = -4836 = -S(1+zS)` for `S = 31, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtytwo :
    singleClusterGSEnergyS 5 62 = (-4836 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 670):
`singleClusterMaxEnergyS 5 62 = 4805 = zS²` for `S = 31, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtytwo :
    singleClusterMaxEnergyS 5 62 = (4805 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31 7-vertex (heptamer) ground-state energy** (γ-5 step 671):
`singleClusterGSEnergyS 6 62 = -5797 = -S(1+zS)` for `S = 31, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtytwo :
    singleClusterGSEnergyS 6 62 = (-5797 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 671):
`singleClusterMaxEnergyS 6 62 = 5766 = zS²` for `S = 31, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtytwo :
    singleClusterMaxEnergyS 6 62 = (5766 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63/2 2-vertex (dimer) ground-state energy** (γ-5 step 672):
`singleClusterGSEnergyS 1 63 = -4095/4 = -S(S+1)` for `S = 63/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtythree :
    singleClusterGSEnergyS 1 63 = (-4095 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 672):
`singleClusterMaxEnergyS 1 63 = 3969/4 = S²` for `S = 63/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtythree :
    singleClusterMaxEnergyS 1 63 = (3969 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63/2 3-vertex (trimer) ground-state energy** (γ-5 step 673):
`singleClusterGSEnergyS 2 63 = -2016 = -S(1+zS)` for `S = 63/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtythree :
    singleClusterGSEnergyS 2 63 = (-2016 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 673):
`singleClusterMaxEnergyS 2 63 = 3969/2 = zS²` for `S = 63/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtythree :
    singleClusterMaxEnergyS 2 63 = (3969 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63/2 4-vertex (quartet) ground-state energy** (γ-5 step 674):
`singleClusterGSEnergyS 3 63 = -12033/4 = -S(1+zS)` for `S = 63/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtythree :
    singleClusterGSEnergyS 3 63 = (-12033 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 674):
`singleClusterMaxEnergyS 3 63 = 11907/4 = zS²` for `S = 63/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtythree :
    singleClusterMaxEnergyS 3 63 = (11907 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63/2 5-vertex (pentamer) ground-state energy** (γ-5 step 675):
`singleClusterGSEnergyS 4 63 = -8001/2 = -S(1+zS)` for `S = 63/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtythree :
    singleClusterGSEnergyS 4 63 = (-8001 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 675):
`singleClusterMaxEnergyS 4 63 = 3969 = zS²` for `S = 63/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtythree :
    singleClusterMaxEnergyS 4 63 = (3969 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63/2 6-vertex (hexamer) ground-state energy** (γ-5 step 676):
`singleClusterGSEnergyS 5 63 = -19971/4 = -S(1+zS)` for `S = 63/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtythree :
    singleClusterGSEnergyS 5 63 = (-19971 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 676):
`singleClusterMaxEnergyS 5 63 = 19845/4 = zS²` for `S = 63/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtythree :
    singleClusterMaxEnergyS 5 63 = (19845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63/2 7-vertex (heptamer) ground-state energy** (γ-5 step 677):
`singleClusterGSEnergyS 6 63 = -5985 = -S(1+zS)` for `S = 63/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtythree :
    singleClusterGSEnergyS 6 63 = (-5985 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 677):
`singleClusterMaxEnergyS 6 63 = 11907/2 = zS²` for `S = 63/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtythree :
    singleClusterMaxEnergyS 6 63 = (11907 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-32 2-vertex (dimer) ground-state energy** (γ-5 step 678):
`singleClusterGSEnergyS 1 64 = -1056 = -S(S+1)` for `S = 32`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtyfour :
    singleClusterGSEnergyS 1 64 = (-1056 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-32 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 678):
`singleClusterMaxEnergyS 1 64 = 1024 = S²` for `S = 32`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtyfour :
    singleClusterMaxEnergyS 1 64 = (1024 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-32 3-vertex (trimer) ground-state energy** (γ-5 step 679):
`singleClusterGSEnergyS 2 64 = -2080 = -S(1+zS)` for `S = 32, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtyfour :
    singleClusterGSEnergyS 2 64 = (-2080 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-32 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 679):
`singleClusterMaxEnergyS 2 64 = 2048 = zS²` for `S = 32, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtyfour :
    singleClusterMaxEnergyS 2 64 = (2048 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-32 4-vertex (quartet) ground-state energy** (γ-5 step 680):
`singleClusterGSEnergyS 3 64 = -3104 = -S(1+zS)` for `S = 32, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtyfour :
    singleClusterGSEnergyS 3 64 = (-3104 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-32 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 680):
`singleClusterMaxEnergyS 3 64 = 3072 = zS²` for `S = 32, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtyfour :
    singleClusterMaxEnergyS 3 64 = (3072 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-32 5-vertex (pentamer) ground-state energy** (γ-5 step 681):
`singleClusterGSEnergyS 4 64 = -4128 = -S(1+zS)` for `S = 32, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtyfour :
    singleClusterGSEnergyS 4 64 = (-4128 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-32 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 681):
`singleClusterMaxEnergyS 4 64 = 4096 = zS²` for `S = 32, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtyfour :
    singleClusterMaxEnergyS 4 64 = (4096 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-32 6-vertex (hexamer) ground-state energy** (γ-5 step 682):
`singleClusterGSEnergyS 5 64 = -5152 = -S(1+zS)` for `S = 32, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtyfour :
    singleClusterGSEnergyS 5 64 = (-5152 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-32 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 682):
`singleClusterMaxEnergyS 5 64 = 5120 = zS²` for `S = 32, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtyfour :
    singleClusterMaxEnergyS 5 64 = (5120 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-32 7-vertex (heptamer) ground-state energy** (γ-5 step 683):
`singleClusterGSEnergyS 6 64 = -6176 = -S(1+zS)` for `S = 32, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtyfour :
    singleClusterGSEnergyS 6 64 = (-6176 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-32 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 683):
`singleClusterMaxEnergyS 6 64 = 6144 = zS²` for `S = 32, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtyfour :
    singleClusterMaxEnergyS 6 64 = (6144 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65/2 2-vertex (dimer) ground-state energy** (γ-5 step 684):
`singleClusterGSEnergyS 1 65 = -4355/4 = -S(S+1)` for `S = 65/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtyfive :
    singleClusterGSEnergyS 1 65 = (-4355 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 684):
`singleClusterMaxEnergyS 1 65 = 4225/4 = S²` for `S = 65/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtyfive :
    singleClusterMaxEnergyS 1 65 = (4225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65/2 3-vertex (trimer) ground-state energy** (γ-5 step 685):
`singleClusterGSEnergyS 2 65 = -2145 = -S(1+zS)` for `S = 65/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtyfive :
    singleClusterGSEnergyS 2 65 = (-2145 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 685):
`singleClusterMaxEnergyS 2 65 = 4225/2 = zS²` for `S = 65/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtyfive :
    singleClusterMaxEnergyS 2 65 = (4225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65/2 4-vertex (quartet) ground-state energy** (γ-5 step 686):
`singleClusterGSEnergyS 3 65 = -12805/4 = -S(1+zS)` for `S = 65/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtyfive :
    singleClusterGSEnergyS 3 65 = (-12805 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 686):
`singleClusterMaxEnergyS 3 65 = 12675/4 = zS²` for `S = 65/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtyfive :
    singleClusterMaxEnergyS 3 65 = (12675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65/2 5-vertex (pentamer) ground-state energy** (γ-5 step 687):
`singleClusterGSEnergyS 4 65 = -8515/2 = -S(1+zS)` for `S = 65/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtyfive :
    singleClusterGSEnergyS 4 65 = (-8515 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 687):
`singleClusterMaxEnergyS 4 65 = 4225 = zS²` for `S = 65/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtyfive :
    singleClusterMaxEnergyS 4 65 = (4225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65/2 6-vertex (hexamer) ground-state energy** (γ-5 step 688):
`singleClusterGSEnergyS 5 65 = -21255/4 = -S(1+zS)` for `S = 65/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtyfive :
    singleClusterGSEnergyS 5 65 = (-21255 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 688):
`singleClusterMaxEnergyS 5 65 = 21125/4 = zS²` for `S = 65/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtyfive :
    singleClusterMaxEnergyS 5 65 = (21125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65/2 7-vertex (heptamer) ground-state energy** (γ-5 step 689):
`singleClusterGSEnergyS 6 65 = -6370 = -S(1+zS)` for `S = 65/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtyfive :
    singleClusterGSEnergyS 6 65 = (-6370 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 689):
`singleClusterMaxEnergyS 6 65 = 12675/2 = zS²` for `S = 65/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtyfive :
    singleClusterMaxEnergyS 6 65 = (12675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33 2-vertex (dimer) ground-state energy** (γ-5 step 690):
`singleClusterGSEnergyS 1 66 = -1122 = -S(S+1)` for `S = 33`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtysix :
    singleClusterGSEnergyS 1 66 = (-1122 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 690):
`singleClusterMaxEnergyS 1 66 = 1089 = S²` for `S = 33`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtysix :
    singleClusterMaxEnergyS 1 66 = (1089 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33 3-vertex (trimer) ground-state energy** (γ-5 step 691):
`singleClusterGSEnergyS 2 66 = -2211 = -S(1+zS)` for `S = 33, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtysix :
    singleClusterGSEnergyS 2 66 = (-2211 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 691):
`singleClusterMaxEnergyS 2 66 = 2178 = zS²` for `S = 33, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtysix :
    singleClusterMaxEnergyS 2 66 = (2178 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33 4-vertex (quartet) ground-state energy** (γ-5 step 692):
`singleClusterGSEnergyS 3 66 = -3300 = -S(1+zS)` for `S = 33, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtysix :
    singleClusterGSEnergyS 3 66 = (-3300 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 692):
`singleClusterMaxEnergyS 3 66 = 3267 = zS²` for `S = 33, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtysix :
    singleClusterMaxEnergyS 3 66 = (3267 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33 5-vertex (pentamer) ground-state energy** (γ-5 step 693):
`singleClusterGSEnergyS 4 66 = -4389 = -S(1+zS)` for `S = 33, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtysix :
    singleClusterGSEnergyS 4 66 = (-4389 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 693):
`singleClusterMaxEnergyS 4 66 = 4356 = zS²` for `S = 33, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtysix :
    singleClusterMaxEnergyS 4 66 = (4356 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33 6-vertex (hexamer) ground-state energy** (γ-5 step 694):
`singleClusterGSEnergyS 5 66 = -5478 = -S(1+zS)` for `S = 33, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtysix :
    singleClusterGSEnergyS 5 66 = (-5478 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 694):
`singleClusterMaxEnergyS 5 66 = 5445 = zS²` for `S = 33, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtysix :
    singleClusterMaxEnergyS 5 66 = (5445 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33 7-vertex (heptamer) ground-state energy** (γ-5 step 695):
`singleClusterGSEnergyS 6 66 = -6567 = -S(1+zS)` for `S = 33, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtysix :
    singleClusterGSEnergyS 6 66 = (-6567 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 695):
`singleClusterMaxEnergyS 6 66 = 6534 = zS²` for `S = 33, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtysix :
    singleClusterMaxEnergyS 6 66 = (6534 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67/2 2-vertex (dimer) ground-state energy** (γ-5 step 696):
`singleClusterGSEnergyS 1 67 = -4623/4 = -S(S+1)` for `S = 67/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtyseven :
    singleClusterGSEnergyS 1 67 = (-4623 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 696):
`singleClusterMaxEnergyS 1 67 = 4489/4 = S²` for `S = 67/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtyseven :
    singleClusterMaxEnergyS 1 67 = (4489 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67/2 3-vertex (trimer) ground-state energy** (γ-5 step 697):
`singleClusterGSEnergyS 2 67 = -2278 = -S(1+zS)` for `S = 67/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtyseven :
    singleClusterGSEnergyS 2 67 = (-2278 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 697):
`singleClusterMaxEnergyS 2 67 = 4489/2 = zS²` for `S = 67/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtyseven :
    singleClusterMaxEnergyS 2 67 = (4489 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67/2 4-vertex (quartet) ground-state energy** (γ-5 step 698):
`singleClusterGSEnergyS 3 67 = -13601/4 = -S(1+zS)` for `S = 67/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtyseven :
    singleClusterGSEnergyS 3 67 = (-13601 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 698):
`singleClusterMaxEnergyS 3 67 = 13467/4 = zS²` for `S = 67/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtyseven :
    singleClusterMaxEnergyS 3 67 = (13467 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67/2 5-vertex (pentamer) ground-state energy** (γ-5 step 699):
`singleClusterGSEnergyS 4 67 = -9045/2 = -S(1+zS)` for `S = 67/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtyseven :
    singleClusterGSEnergyS 4 67 = (-9045 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 699):
`singleClusterMaxEnergyS 4 67 = 4489 = zS²` for `S = 67/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtyseven :
    singleClusterMaxEnergyS 4 67 = (4489 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67/2 6-vertex (hexamer) ground-state energy** (γ-5 step 700):
`singleClusterGSEnergyS 5 67 = -22579/4 = -S(1+zS)` for `S = 67/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtyseven :
    singleClusterGSEnergyS 5 67 = (-22579 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 700):
`singleClusterMaxEnergyS 5 67 = 22445/4 = zS²` for `S = 67/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtyseven :
    singleClusterMaxEnergyS 5 67 = (22445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67/2 7-vertex (heptamer) ground-state energy** (γ-5 step 701):
`singleClusterGSEnergyS 6 67 = -6767 = -S(1+zS)` for `S = 67/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtyseven :
    singleClusterGSEnergyS 6 67 = (-6767 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 701):
`singleClusterMaxEnergyS 6 67 = 13467/2 = zS²` for `S = 67/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtyseven :
    singleClusterMaxEnergyS 6 67 = (13467 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-34 2-vertex (dimer) ground-state energy** (γ-5 step 702):
`singleClusterGSEnergyS 1 68 = -1190 = -S(S+1)` for `S = 34`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtyeight :
    singleClusterGSEnergyS 1 68 = (-1190 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-34 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 702):
`singleClusterMaxEnergyS 1 68 = 1156 = S²` for `S = 34`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtyeight :
    singleClusterMaxEnergyS 1 68 = (1156 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-34 3-vertex (trimer) ground-state energy** (γ-5 step 703):
`singleClusterGSEnergyS 2 68 = -2346 = -S(1+zS)` for `S = 34, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtyeight :
    singleClusterGSEnergyS 2 68 = (-2346 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-34 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 703):
`singleClusterMaxEnergyS 2 68 = 2312 = zS²` for `S = 34, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtyeight :
    singleClusterMaxEnergyS 2 68 = (2312 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-34 4-vertex (quartet) ground-state energy** (γ-5 step 704):
`singleClusterGSEnergyS 3 68 = -3502 = -S(1+zS)` for `S = 34, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtyeight :
    singleClusterGSEnergyS 3 68 = (-3502 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-34 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 704):
`singleClusterMaxEnergyS 3 68 = 3468 = zS²` for `S = 34, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtyeight :
    singleClusterMaxEnergyS 3 68 = (3468 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-34 5-vertex (pentamer) ground-state energy** (γ-5 step 705):
`singleClusterGSEnergyS 4 68 = -4658 = -S(1+zS)` for `S = 34, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtyeight :
    singleClusterGSEnergyS 4 68 = (-4658 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-34 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 705):
`singleClusterMaxEnergyS 4 68 = 4624 = zS²` for `S = 34, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtyeight :
    singleClusterMaxEnergyS 4 68 = (4624 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-34 6-vertex (hexamer) ground-state energy** (γ-5 step 706):
`singleClusterGSEnergyS 5 68 = -5814 = -S(1+zS)` for `S = 34, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtyeight :
    singleClusterGSEnergyS 5 68 = (-5814 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-34 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 706):
`singleClusterMaxEnergyS 5 68 = 5780 = zS²` for `S = 34, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtyeight :
    singleClusterMaxEnergyS 5 68 = (5780 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-34 7-vertex (heptamer) ground-state energy** (γ-5 step 707):
`singleClusterGSEnergyS 6 68 = -6970 = -S(1+zS)` for `S = 34, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtyeight :
    singleClusterGSEnergyS 6 68 = (-6970 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-34 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 707):
`singleClusterMaxEnergyS 6 68 = 6936 = zS²` for `S = 34, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtyeight :
    singleClusterMaxEnergyS 6 68 = (6936 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69/2 2-vertex (dimer) ground-state energy** (γ-5 step 708):
`singleClusterGSEnergyS 1 69 = -4899/4 = -S(S+1)` for `S = 69/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixtynine :
    singleClusterGSEnergyS 1 69 = (-4899 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 708):
`singleClusterMaxEnergyS 1 69 = 4761/4 = S²` for `S = 69/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixtynine :
    singleClusterMaxEnergyS 1 69 = (4761 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69/2 3-vertex (trimer) ground-state energy** (γ-5 step 709):
`singleClusterGSEnergyS 2 69 = -2415 = -S(1+zS)` for `S = 69/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixtynine :
    singleClusterGSEnergyS 2 69 = (-2415 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 709):
`singleClusterMaxEnergyS 2 69 = 4761/2 = zS²` for `S = 69/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixtynine :
    singleClusterMaxEnergyS 2 69 = (4761 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69/2 4-vertex (quartet) ground-state energy** (γ-5 step 710):
`singleClusterGSEnergyS 3 69 = -14421/4 = -S(1+zS)` for `S = 69/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixtynine :
    singleClusterGSEnergyS 3 69 = (-14421 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 710):
`singleClusterMaxEnergyS 3 69 = 14283/4 = zS²` for `S = 69/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixtynine :
    singleClusterMaxEnergyS 3 69 = (14283 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69/2 5-vertex (pentamer) ground-state energy** (γ-5 step 711):
`singleClusterGSEnergyS 4 69 = -9591/2 = -S(1+zS)` for `S = 69/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixtynine :
    singleClusterGSEnergyS 4 69 = (-9591 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 711):
`singleClusterMaxEnergyS 4 69 = 4761 = zS²` for `S = 69/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixtynine :
    singleClusterMaxEnergyS 4 69 = (4761 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69/2 6-vertex (hexamer) ground-state energy** (γ-5 step 712):
`singleClusterGSEnergyS 5 69 = -23943/4 = -S(1+zS)` for `S = 69/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixtynine :
    singleClusterGSEnergyS 5 69 = (-23943 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 712):
`singleClusterMaxEnergyS 5 69 = 23805/4 = zS²` for `S = 69/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixtynine :
    singleClusterMaxEnergyS 5 69 = (23805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69/2 7-vertex (heptamer) ground-state energy** (γ-5 step 713):
`singleClusterGSEnergyS 6 69 = -7176 = -S(1+zS)` for `S = 69/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixtynine :
    singleClusterGSEnergyS 6 69 = (-7176 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 713):
`singleClusterMaxEnergyS 6 69 = 14283/2 = zS²` for `S = 69/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixtynine :
    singleClusterMaxEnergyS 6 69 = (14283 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35 2-vertex (dimer) ground-state energy** (γ-5 step 714):
`singleClusterGSEnergyS 1 70 = -1260 = -S(S+1)` for `S = 35`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventy :
    singleClusterGSEnergyS 1 70 = (-1260 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 714):
`singleClusterMaxEnergyS 1 70 = 1225 = S²` for `S = 35`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventy :
    singleClusterMaxEnergyS 1 70 = (1225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35 3-vertex (trimer) ground-state energy** (γ-5 step 715):
`singleClusterGSEnergyS 2 70 = -2485 = -S(1+zS)` for `S = 35, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventy :
    singleClusterGSEnergyS 2 70 = (-2485 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 715):
`singleClusterMaxEnergyS 2 70 = 2450 = zS²` for `S = 35, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventy :
    singleClusterMaxEnergyS 2 70 = (2450 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35 4-vertex (quartet) ground-state energy** (γ-5 step 716):
`singleClusterGSEnergyS 3 70 = -3710 = -S(1+zS)` for `S = 35, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventy :
    singleClusterGSEnergyS 3 70 = (-3710 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 716):
`singleClusterMaxEnergyS 3 70 = 3675 = zS²` for `S = 35, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventy :
    singleClusterMaxEnergyS 3 70 = (3675 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35 5-vertex (pentamer) ground-state energy** (γ-5 step 717):
`singleClusterGSEnergyS 4 70 = -4935 = -S(1+zS)` for `S = 35, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventy :
    singleClusterGSEnergyS 4 70 = (-4935 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 717):
`singleClusterMaxEnergyS 4 70 = 4900 = zS²` for `S = 35, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventy :
    singleClusterMaxEnergyS 4 70 = (4900 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35 6-vertex (hexamer) ground-state energy** (γ-5 step 718):
`singleClusterGSEnergyS 5 70 = -6160 = -S(1+zS)` for `S = 35, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventy :
    singleClusterGSEnergyS 5 70 = (-6160 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 718):
`singleClusterMaxEnergyS 5 70 = 6125 = zS²` for `S = 35, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventy :
    singleClusterMaxEnergyS 5 70 = (6125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35 7-vertex (heptamer) ground-state energy** (γ-5 step 719):
`singleClusterGSEnergyS 6 70 = -7385 = -S(1+zS)` for `S = 35, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventy :
    singleClusterGSEnergyS 6 70 = (-7385 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 719):
`singleClusterMaxEnergyS 6 70 = 7350 = zS²` for `S = 35, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventy :
    singleClusterMaxEnergyS 6 70 = (7350 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71/2 2-vertex (dimer) ground-state energy** (γ-5 step 720):
`singleClusterGSEnergyS 1 71 = -5183/4 = -S(S+1)` for `S = 71/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventyone :
    singleClusterGSEnergyS 1 71 = (-5183 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 720):
`singleClusterMaxEnergyS 1 71 = 5041/4 = S²` for `S = 71/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventyone :
    singleClusterMaxEnergyS 1 71 = (5041 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71/2 3-vertex (trimer) ground-state energy** (γ-5 step 721):
`singleClusterGSEnergyS 2 71 = -2556 = -S(1+zS)` for `S = 71/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventyone :
    singleClusterGSEnergyS 2 71 = (-2556 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 721):
`singleClusterMaxEnergyS 2 71 = 5041/2 = zS²` for `S = 71/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventyone :
    singleClusterMaxEnergyS 2 71 = (5041 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71/2 4-vertex (quartet) ground-state energy** (γ-5 step 722):
`singleClusterGSEnergyS 3 71 = -15265/4 = -S(1+zS)` for `S = 71/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventyone :
    singleClusterGSEnergyS 3 71 = (-15265 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 722):
`singleClusterMaxEnergyS 3 71 = 15123/4 = zS²` for `S = 71/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventyone :
    singleClusterMaxEnergyS 3 71 = (15123 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71/2 5-vertex (pentamer) ground-state energy** (γ-5 step 723):
`singleClusterGSEnergyS 4 71 = -10153/2 = -S(1+zS)` for `S = 71/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventyone :
    singleClusterGSEnergyS 4 71 = (-10153 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 723):
`singleClusterMaxEnergyS 4 71 = 5041 = zS²` for `S = 71/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventyone :
    singleClusterMaxEnergyS 4 71 = (5041 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71/2 6-vertex (hexamer) ground-state energy** (γ-5 step 724):
`singleClusterGSEnergyS 5 71 = -25347/4 = -S(1+zS)` for `S = 71/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventyone :
    singleClusterGSEnergyS 5 71 = (-25347 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 724):
`singleClusterMaxEnergyS 5 71 = 25205/4 = zS²` for `S = 71/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventyone :
    singleClusterMaxEnergyS 5 71 = (25205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71/2 7-vertex (heptamer) ground-state energy** (γ-5 step 725):
`singleClusterGSEnergyS 6 71 = -7597 = -S(1+zS)` for `S = 71/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventyone :
    singleClusterGSEnergyS 6 71 = (-7597 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 725):
`singleClusterMaxEnergyS 6 71 = 15123/2 = zS²` for `S = 71/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventyone :
    singleClusterMaxEnergyS 6 71 = (15123 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-36 2-vertex (dimer) ground-state energy** (γ-5 step 726):
`singleClusterGSEnergyS 1 72 = -1332 = -S(S+1)` for `S = 36`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventytwo :
    singleClusterGSEnergyS 1 72 = (-1332 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-36 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 726):
`singleClusterMaxEnergyS 1 72 = 1296 = S²` for `S = 36`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventytwo :
    singleClusterMaxEnergyS 1 72 = (1296 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-36 3-vertex (trimer) ground-state energy** (γ-5 step 727):
`singleClusterGSEnergyS 2 72 = -2628 = -S(1+zS)` for `S = 36, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventytwo :
    singleClusterGSEnergyS 2 72 = (-2628 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-36 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 727):
`singleClusterMaxEnergyS 2 72 = 2592 = zS²` for `S = 36, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventytwo :
    singleClusterMaxEnergyS 2 72 = (2592 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-36 4-vertex (quartet) ground-state energy** (γ-5 step 728):
`singleClusterGSEnergyS 3 72 = -3924 = -S(1+zS)` for `S = 36, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventytwo :
    singleClusterGSEnergyS 3 72 = (-3924 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-36 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 728):
`singleClusterMaxEnergyS 3 72 = 3888 = zS²` for `S = 36, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventytwo :
    singleClusterMaxEnergyS 3 72 = (3888 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-36 5-vertex (pentamer) ground-state energy** (γ-5 step 729):
`singleClusterGSEnergyS 4 72 = -5220 = -S(1+zS)` for `S = 36, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventytwo :
    singleClusterGSEnergyS 4 72 = (-5220 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-36 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 729):
`singleClusterMaxEnergyS 4 72 = 5184 = zS²` for `S = 36, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventytwo :
    singleClusterMaxEnergyS 4 72 = (5184 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-36 6-vertex (hexamer) ground-state energy** (γ-5 step 730):
`singleClusterGSEnergyS 5 72 = -6516 = -S(1+zS)` for `S = 36, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventytwo :
    singleClusterGSEnergyS 5 72 = (-6516 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-36 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 730):
`singleClusterMaxEnergyS 5 72 = 6480 = zS²` for `S = 36, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventytwo :
    singleClusterMaxEnergyS 5 72 = (6480 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-36 7-vertex (heptamer) ground-state energy** (γ-5 step 731):
`singleClusterGSEnergyS 6 72 = -7812 = -S(1+zS)` for `S = 36, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventytwo :
    singleClusterGSEnergyS 6 72 = (-7812 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-36 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 731):
`singleClusterMaxEnergyS 6 72 = 7776 = zS²` for `S = 36, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventytwo :
    singleClusterMaxEnergyS 6 72 = (7776 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73/2 2-vertex (dimer) ground-state energy** (γ-5 step 732):
`singleClusterGSEnergyS 1 73 = -5475/4 = -S(S+1)` for `S = 73/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventythree :
    singleClusterGSEnergyS 1 73 = (-5475 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 732):
`singleClusterMaxEnergyS 1 73 = 5329/4 = S²` for `S = 73/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventythree :
    singleClusterMaxEnergyS 1 73 = (5329 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73/2 3-vertex (trimer) ground-state energy** (γ-5 step 733):
`singleClusterGSEnergyS 2 73 = -2701 = -S(1+zS)` for `S = 73/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventythree :
    singleClusterGSEnergyS 2 73 = (-2701 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 733):
`singleClusterMaxEnergyS 2 73 = 5329/2 = zS²` for `S = 73/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventythree :
    singleClusterMaxEnergyS 2 73 = (5329 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73/2 4-vertex (quartet) ground-state energy** (γ-5 step 734):
`singleClusterGSEnergyS 3 73 = -16133/4 = -S(1+zS)` for `S = 73/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventythree :
    singleClusterGSEnergyS 3 73 = (-16133 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 734):
`singleClusterMaxEnergyS 3 73 = 15987/4 = zS²` for `S = 73/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventythree :
    singleClusterMaxEnergyS 3 73 = (15987 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73/2 5-vertex (pentamer) ground-state energy** (γ-5 step 735):
`singleClusterGSEnergyS 4 73 = -10731/2 = -S(1+zS)` for `S = 73/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventythree :
    singleClusterGSEnergyS 4 73 = (-10731 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 735):
`singleClusterMaxEnergyS 4 73 = 5329 = zS²` for `S = 73/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventythree :
    singleClusterMaxEnergyS 4 73 = (5329 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73/2 6-vertex (hexamer) ground-state energy** (γ-5 step 736):
`singleClusterGSEnergyS 5 73 = -26791/4 = -S(1+zS)` for `S = 73/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventythree :
    singleClusterGSEnergyS 5 73 = (-26791 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 736):
`singleClusterMaxEnergyS 5 73 = 26645/4 = zS²` for `S = 73/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventythree :
    singleClusterMaxEnergyS 5 73 = (26645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73/2 7-vertex (heptamer) ground-state energy** (γ-5 step 737):
`singleClusterGSEnergyS 6 73 = -8030 = -S(1+zS)` for `S = 73/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventythree :
    singleClusterGSEnergyS 6 73 = (-8030 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 737):
`singleClusterMaxEnergyS 6 73 = 15987/2 = zS²` for `S = 73/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventythree :
    singleClusterMaxEnergyS 6 73 = (15987 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37 2-vertex (dimer) ground-state energy** (γ-5 step 738):
`singleClusterGSEnergyS 1 74 = -1406 = -S(S+1)` for `S = 37`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventyfour :
    singleClusterGSEnergyS 1 74 = (-1406 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 738):
`singleClusterMaxEnergyS 1 74 = 1369 = S²` for `S = 37`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventyfour :
    singleClusterMaxEnergyS 1 74 = (1369 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37 3-vertex (trimer) ground-state energy** (γ-5 step 739):
`singleClusterGSEnergyS 2 74 = -2775 = -S(1+zS)` for `S = 37, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventyfour :
    singleClusterGSEnergyS 2 74 = (-2775 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 739):
`singleClusterMaxEnergyS 2 74 = 2738 = zS²` for `S = 37, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventyfour :
    singleClusterMaxEnergyS 2 74 = (2738 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37 4-vertex (quartet) ground-state energy** (γ-5 step 740):
`singleClusterGSEnergyS 3 74 = -4144 = -S(1+zS)` for `S = 37, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventyfour :
    singleClusterGSEnergyS 3 74 = (-4144 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 740):
`singleClusterMaxEnergyS 3 74 = 4107 = zS²` for `S = 37, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventyfour :
    singleClusterMaxEnergyS 3 74 = (4107 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37 5-vertex (pentamer) ground-state energy** (γ-5 step 741):
`singleClusterGSEnergyS 4 74 = -5513 = -S(1+zS)` for `S = 37, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventyfour :
    singleClusterGSEnergyS 4 74 = (-5513 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 741):
`singleClusterMaxEnergyS 4 74 = 5476 = zS²` for `S = 37, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventyfour :
    singleClusterMaxEnergyS 4 74 = (5476 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37 6-vertex (hexamer) ground-state energy** (γ-5 step 742):
`singleClusterGSEnergyS 5 74 = -6882 = -S(1+zS)` for `S = 37, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventyfour :
    singleClusterGSEnergyS 5 74 = (-6882 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 742):
`singleClusterMaxEnergyS 5 74 = 6845 = zS²` for `S = 37, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventyfour :
    singleClusterMaxEnergyS 5 74 = (6845 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37 7-vertex (heptamer) ground-state energy** (γ-5 step 743):
`singleClusterGSEnergyS 6 74 = -8251 = -S(1+zS)` for `S = 37, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventyfour :
    singleClusterGSEnergyS 6 74 = (-8251 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 743):
`singleClusterMaxEnergyS 6 74 = 8214 = zS²` for `S = 37, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventyfour :
    singleClusterMaxEnergyS 6 74 = (8214 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75/2 2-vertex (dimer) ground-state energy** (γ-5 step 744):
`singleClusterGSEnergyS 1 75 = -5775/4 = -S(S+1)` for `S = 75/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventyfive :
    singleClusterGSEnergyS 1 75 = (-5775 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 744):
`singleClusterMaxEnergyS 1 75 = 5625/4 = S²` for `S = 75/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventyfive :
    singleClusterMaxEnergyS 1 75 = (5625 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75/2 3-vertex (trimer) ground-state energy** (γ-5 step 745):
`singleClusterGSEnergyS 2 75 = -2850 = -S(1+zS)` for `S = 75/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventyfive :
    singleClusterGSEnergyS 2 75 = (-2850 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 745):
`singleClusterMaxEnergyS 2 75 = 5625/2 = zS²` for `S = 75/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventyfive :
    singleClusterMaxEnergyS 2 75 = (5625 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75/2 4-vertex (quartet) ground-state energy** (γ-5 step 746):
`singleClusterGSEnergyS 3 75 = -17025/4 = -S(1+zS)` for `S = 75/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventyfive :
    singleClusterGSEnergyS 3 75 = (-17025 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 746):
`singleClusterMaxEnergyS 3 75 = 16875/4 = zS²` for `S = 75/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventyfive :
    singleClusterMaxEnergyS 3 75 = (16875 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75/2 5-vertex (pentamer) ground-state energy** (γ-5 step 747):
`singleClusterGSEnergyS 4 75 = -11325/2 = -S(1+zS)` for `S = 75/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventyfive :
    singleClusterGSEnergyS 4 75 = (-11325 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 747):
`singleClusterMaxEnergyS 4 75 = 5625 = zS²` for `S = 75/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventyfive :
    singleClusterMaxEnergyS 4 75 = (5625 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75/2 6-vertex (hexamer) ground-state energy** (γ-5 step 748):
`singleClusterGSEnergyS 5 75 = -28275/4 = -S(1+zS)` for `S = 75/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventyfive :
    singleClusterGSEnergyS 5 75 = (-28275 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 748):
`singleClusterMaxEnergyS 5 75 = 28125/4 = zS²` for `S = 75/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventyfive :
    singleClusterMaxEnergyS 5 75 = (28125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75/2 7-vertex (heptamer) ground-state energy** (γ-5 step 749):
`singleClusterGSEnergyS 6 75 = -8475 = -S(1+zS)` for `S = 75/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventyfive :
    singleClusterGSEnergyS 6 75 = (-8475 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 749):
`singleClusterMaxEnergyS 6 75 = 16875/2 = zS²` for `S = 75/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventyfive :
    singleClusterMaxEnergyS 6 75 = (16875 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-38 2-vertex (dimer) ground-state energy** (γ-5 step 750):
`singleClusterGSEnergyS 1 76 = -1482 = -S(S+1)` for `S = 38`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventysix :
    singleClusterGSEnergyS 1 76 = (-1482 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-38 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 750):
`singleClusterMaxEnergyS 1 76 = 1444 = S²` for `S = 38`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventysix :
    singleClusterMaxEnergyS 1 76 = (1444 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-38 3-vertex (trimer) ground-state energy** (γ-5 step 751):
`singleClusterGSEnergyS 2 76 = -2926 = -S(1+zS)` for `S = 38, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventysix :
    singleClusterGSEnergyS 2 76 = (-2926 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-38 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 751):
`singleClusterMaxEnergyS 2 76 = 2888 = zS²` for `S = 38, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventysix :
    singleClusterMaxEnergyS 2 76 = (2888 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-38 4-vertex (quartet) ground-state energy** (γ-5 step 752):
`singleClusterGSEnergyS 3 76 = -4370 = -S(1+zS)` for `S = 38, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventysix :
    singleClusterGSEnergyS 3 76 = (-4370 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-38 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 752):
`singleClusterMaxEnergyS 3 76 = 4332 = zS²` for `S = 38, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventysix :
    singleClusterMaxEnergyS 3 76 = (4332 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-38 5-vertex (pentamer) ground-state energy** (γ-5 step 753):
`singleClusterGSEnergyS 4 76 = -5814 = -S(1+zS)` for `S = 38, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventysix :
    singleClusterGSEnergyS 4 76 = (-5814 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-38 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 753):
`singleClusterMaxEnergyS 4 76 = 5776 = zS²` for `S = 38, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventysix :
    singleClusterMaxEnergyS 4 76 = (5776 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-38 6-vertex (hexamer) ground-state energy** (γ-5 step 754):
`singleClusterGSEnergyS 5 76 = -7258 = -S(1+zS)` for `S = 38, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventysix :
    singleClusterGSEnergyS 5 76 = (-7258 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-38 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 754):
`singleClusterMaxEnergyS 5 76 = 7220 = zS²` for `S = 38, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventysix :
    singleClusterMaxEnergyS 5 76 = (7220 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-38 7-vertex (heptamer) ground-state energy** (γ-5 step 755):
`singleClusterGSEnergyS 6 76 = -8702 = -S(1+zS)` for `S = 38, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventysix :
    singleClusterGSEnergyS 6 76 = (-8702 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-38 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 755):
`singleClusterMaxEnergyS 6 76 = 8664 = zS²` for `S = 38, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventysix :
    singleClusterMaxEnergyS 6 76 = (8664 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77/2 2-vertex (dimer) ground-state energy** (γ-5 step 756):
`singleClusterGSEnergyS 1 77 = -6083/4 = -S(S+1)` for `S = 77/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventyseven :
    singleClusterGSEnergyS 1 77 = (-6083 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 756):
`singleClusterMaxEnergyS 1 77 = 5929/4 = S²` for `S = 77/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventyseven :
    singleClusterMaxEnergyS 1 77 = (5929 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77/2 3-vertex (trimer) ground-state energy** (γ-5 step 757):
`singleClusterGSEnergyS 2 77 = -3003 = -S(1+zS)` for `S = 77/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventyseven :
    singleClusterGSEnergyS 2 77 = (-3003 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 757):
`singleClusterMaxEnergyS 2 77 = 5929/2 = zS²` for `S = 77/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventyseven :
    singleClusterMaxEnergyS 2 77 = (5929 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77/2 4-vertex (quartet) ground-state energy** (γ-5 step 758):
`singleClusterGSEnergyS 3 77 = -17941/4 = -S(1+zS)` for `S = 77/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventyseven :
    singleClusterGSEnergyS 3 77 = (-17941 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 758):
`singleClusterMaxEnergyS 3 77 = 17787/4 = zS²` for `S = 77/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventyseven :
    singleClusterMaxEnergyS 3 77 = (17787 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77/2 5-vertex (pentamer) ground-state energy** (γ-5 step 759):
`singleClusterGSEnergyS 4 77 = -11935/2 = -S(1+zS)` for `S = 77/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventyseven :
    singleClusterGSEnergyS 4 77 = (-11935 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 759):
`singleClusterMaxEnergyS 4 77 = 5929 = zS²` for `S = 77/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventyseven :
    singleClusterMaxEnergyS 4 77 = (5929 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77/2 6-vertex (hexamer) ground-state energy** (γ-5 step 760):
`singleClusterGSEnergyS 5 77 = -29799/4 = -S(1+zS)` for `S = 77/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventyseven :
    singleClusterGSEnergyS 5 77 = (-29799 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 760):
`singleClusterMaxEnergyS 5 77 = 29645/4 = zS²` for `S = 77/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventyseven :
    singleClusterMaxEnergyS 5 77 = (29645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77/2 7-vertex (heptamer) ground-state energy** (γ-5 step 761):
`singleClusterGSEnergyS 6 77 = -8932 = -S(1+zS)` for `S = 77/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventyseven :
    singleClusterGSEnergyS 6 77 = (-8932 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 761):
`singleClusterMaxEnergyS 6 77 = 17787/2 = zS²` for `S = 77/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventyseven :
    singleClusterMaxEnergyS 6 77 = (17787 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39 2-vertex (dimer) ground-state energy** (γ-5 step 762):
`singleClusterGSEnergyS 1 78 = -1560 = -S(S+1)` for `S = 39`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventyeight :
    singleClusterGSEnergyS 1 78 = (-1560 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 762):
`singleClusterMaxEnergyS 1 78 = 1521 = S²` for `S = 39`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventyeight :
    singleClusterMaxEnergyS 1 78 = (1521 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39 3-vertex (trimer) ground-state energy** (γ-5 step 763):
`singleClusterGSEnergyS 2 78 = -3081 = -S(1+zS)` for `S = 39, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventyeight :
    singleClusterGSEnergyS 2 78 = (-3081 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 763):
`singleClusterMaxEnergyS 2 78 = 3042 = zS²` for `S = 39, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventyeight :
    singleClusterMaxEnergyS 2 78 = (3042 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39 4-vertex (quartet) ground-state energy** (γ-5 step 764):
`singleClusterGSEnergyS 3 78 = -4602 = -S(1+zS)` for `S = 39, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventyeight :
    singleClusterGSEnergyS 3 78 = (-4602 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 764):
`singleClusterMaxEnergyS 3 78 = 4563 = zS²` for `S = 39, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventyeight :
    singleClusterMaxEnergyS 3 78 = (4563 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39 5-vertex (pentamer) ground-state energy** (γ-5 step 765):
`singleClusterGSEnergyS 4 78 = -6123 = -S(1+zS)` for `S = 39, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventyeight :
    singleClusterGSEnergyS 4 78 = (-6123 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 765):
`singleClusterMaxEnergyS 4 78 = 6084 = zS²` for `S = 39, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventyeight :
    singleClusterMaxEnergyS 4 78 = (6084 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39 6-vertex (hexamer) ground-state energy** (γ-5 step 766):
`singleClusterGSEnergyS 5 78 = -7644 = -S(1+zS)` for `S = 39, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventyeight :
    singleClusterGSEnergyS 5 78 = (-7644 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 766):
`singleClusterMaxEnergyS 5 78 = 7605 = zS²` for `S = 39, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventyeight :
    singleClusterMaxEnergyS 5 78 = (7605 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-39 7-vertex (heptamer) ground-state energy** (γ-5 step 767):
`singleClusterGSEnergyS 6 78 = -9165 = -S(1+zS)` for `S = 39, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventyeight :
    singleClusterGSEnergyS 6 78 = (-9165 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-39 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 767):
`singleClusterMaxEnergyS 6 78 = 9126 = zS²` for `S = 39, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventyeight :
    singleClusterMaxEnergyS 6 78 = (9126 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79/2 2-vertex (dimer) ground-state energy** (γ-5 step 768):
`singleClusterGSEnergyS 1 79 = -6399/4 = -S(S+1)` for `S = 79/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventynine :
    singleClusterGSEnergyS 1 79 = (-6399 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 768):
`singleClusterMaxEnergyS 1 79 = 6241/4 = S²` for `S = 79/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventynine :
    singleClusterMaxEnergyS 1 79 = (6241 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79/2 3-vertex (trimer) ground-state energy** (γ-5 step 769):
`singleClusterGSEnergyS 2 79 = -3160 = -S(1+zS)` for `S = 79/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventynine :
    singleClusterGSEnergyS 2 79 = (-3160 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 769):
`singleClusterMaxEnergyS 2 79 = 6241/2 = zS²` for `S = 79/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventynine :
    singleClusterMaxEnergyS 2 79 = (6241 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79/2 4-vertex (quartet) ground-state energy** (γ-5 step 770):
`singleClusterGSEnergyS 3 79 = -18881/4 = -S(1+zS)` for `S = 79/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventynine :
    singleClusterGSEnergyS 3 79 = (-18881 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 770):
`singleClusterMaxEnergyS 3 79 = 18723/4 = zS²` for `S = 79/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventynine :
    singleClusterMaxEnergyS 3 79 = (18723 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79/2 5-vertex (pentamer) ground-state energy** (γ-5 step 771):
`singleClusterGSEnergyS 4 79 = -12561/2 = -S(1+zS)` for `S = 79/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventynine :
    singleClusterGSEnergyS 4 79 = (-12561 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 771):
`singleClusterMaxEnergyS 4 79 = 6241 = zS²` for `S = 79/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventynine :
    singleClusterMaxEnergyS 4 79 = (6241 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79/2 6-vertex (hexamer) ground-state energy** (γ-5 step 772):
`singleClusterGSEnergyS 5 79 = -31363/4 = -S(1+zS)` for `S = 79/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventynine :
    singleClusterGSEnergyS 5 79 = (-31363 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 772):
`singleClusterMaxEnergyS 5 79 = 31205/4 = zS²` for `S = 79/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventynine :
    singleClusterMaxEnergyS 5 79 = (31205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79/2 7-vertex (heptamer) ground-state energy** (γ-5 step 773):
`singleClusterGSEnergyS 6 79 = -9401 = -S(1+zS)` for `S = 79/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventynine :
    singleClusterGSEnergyS 6 79 = (-9401 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 773):
`singleClusterMaxEnergyS 6 79 = 18723/2 = zS²` for `S = 79/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventynine :
    singleClusterMaxEnergyS 6 79 = (18723 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-40 2-vertex (dimer) ground-state energy** (γ-5 step 774):
`singleClusterGSEnergyS 1 80 = -1640 = -S(S+1)` for `S = 40`. -/
@[simp] theorem singleClusterGSEnergyS_one_eighty :
    singleClusterGSEnergyS 1 80 = (-1640 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-40 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 774):
`singleClusterMaxEnergyS 1 80 = 1600 = S²` for `S = 40`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eighty :
    singleClusterMaxEnergyS 1 80 = (1600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-40 3-vertex (trimer) ground-state energy** (γ-5 step 775):
`singleClusterGSEnergyS 2 80 = -3240 = -S(1+zS)` for `S = 40, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eighty :
    singleClusterGSEnergyS 2 80 = (-3240 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-40 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 775):
`singleClusterMaxEnergyS 2 80 = 3200 = zS²` for `S = 40, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eighty :
    singleClusterMaxEnergyS 2 80 = (3200 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-40 4-vertex (quartet) ground-state energy** (γ-5 step 776):
`singleClusterGSEnergyS 3 80 = -4840 = -S(1+zS)` for `S = 40, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eighty :
    singleClusterGSEnergyS 3 80 = (-4840 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-40 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 776):
`singleClusterMaxEnergyS 3 80 = 4800 = zS²` for `S = 40, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eighty :
    singleClusterMaxEnergyS 3 80 = (4800 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-40 5-vertex (pentamer) ground-state energy** (γ-5 step 777):
`singleClusterGSEnergyS 4 80 = -6440 = -S(1+zS)` for `S = 40, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eighty :
    singleClusterGSEnergyS 4 80 = (-6440 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-40 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 777):
`singleClusterMaxEnergyS 4 80 = 6400 = zS²` for `S = 40, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eighty :
    singleClusterMaxEnergyS 4 80 = (6400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
