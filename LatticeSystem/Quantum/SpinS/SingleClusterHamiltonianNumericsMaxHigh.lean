/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Max-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 78`
(spin `S = N/2 ≥ 39`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, and the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all six numerics files can elaborate
in parallel after the main file. The split from `ExtremeHigh` to
`MaxHigh` was introduced as the 50-PR build-performance cadence
refactor #9 when `ExtremeHigh` reached ~10.5 s user CPU after the
N=78..98 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

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

/-- **Spin-40 6-vertex (hexamer) ground-state energy** (γ-5 step 778):
`singleClusterGSEnergyS 5 80 = -8040 = -S(1+zS)` for `S = 40, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eighty :
    singleClusterGSEnergyS 5 80 = (-8040 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-40 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 778):
`singleClusterMaxEnergyS 5 80 = 8000 = zS²` for `S = 40, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eighty :
    singleClusterMaxEnergyS 5 80 = (8000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-40 7-vertex (heptamer) ground-state energy** (γ-5 step 779):
`singleClusterGSEnergyS 6 80 = -9640 = -S(1+zS)` for `S = 40, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eighty :
    singleClusterGSEnergyS 6 80 = (-9640 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-40 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 779):
`singleClusterMaxEnergyS 6 80 = 9600 = zS²` for `S = 40, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eighty :
    singleClusterMaxEnergyS 6 80 = (9600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81/2 2-vertex (dimer) ground-state energy** (γ-5 step 780):
`singleClusterGSEnergyS 1 81 = -6723/4 = -S(S+1)` for `S = 81/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightyone :
    singleClusterGSEnergyS 1 81 = (-6723 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 780):
`singleClusterMaxEnergyS 1 81 = 6561/4 = S²` for `S = 81/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightyone :
    singleClusterMaxEnergyS 1 81 = (6561 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81/2 3-vertex (trimer) ground-state energy** (γ-5 step 781):
`singleClusterGSEnergyS 2 81 = -3321 = -S(1+zS)` for `S = 81/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightyone :
    singleClusterGSEnergyS 2 81 = (-3321 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 781):
`singleClusterMaxEnergyS 2 81 = 6561/2 = zS²` for `S = 81/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightyone :
    singleClusterMaxEnergyS 2 81 = (6561 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81/2 4-vertex (quartet) ground-state energy** (γ-5 step 782):
`singleClusterGSEnergyS 3 81 = -19845/4 = -S(1+zS)` for `S = 81/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightyone :
    singleClusterGSEnergyS 3 81 = (-19845 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 782):
`singleClusterMaxEnergyS 3 81 = 19683/4 = zS²` for `S = 81/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightyone :
    singleClusterMaxEnergyS 3 81 = (19683 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81/2 5-vertex (pentamer) ground-state energy** (γ-5 step 783):
`singleClusterGSEnergyS 4 81 = -13203/2 = -S(1+zS)` for `S = 81/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightyone :
    singleClusterGSEnergyS 4 81 = (-13203 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 783):
`singleClusterMaxEnergyS 4 81 = 6561 = zS²` for `S = 81/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightyone :
    singleClusterMaxEnergyS 4 81 = (6561 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81/2 6-vertex (hexamer) ground-state energy** (γ-5 step 784):
`singleClusterGSEnergyS 5 81 = -32967/4 = -S(1+zS)` for `S = 81/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightyone :
    singleClusterGSEnergyS 5 81 = (-32967 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 784):
`singleClusterMaxEnergyS 5 81 = 32805/4 = zS²` for `S = 81/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightyone :
    singleClusterMaxEnergyS 5 81 = (32805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81/2 7-vertex (heptamer) ground-state energy** (γ-5 step 785):
`singleClusterGSEnergyS 6 81 = -9882 = -S(1+zS)` for `S = 81/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightyone :
    singleClusterGSEnergyS 6 81 = (-9882 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 785):
`singleClusterMaxEnergyS 6 81 = 19683/2 = zS²` for `S = 81/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightyone :
    singleClusterMaxEnergyS 6 81 = (19683 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41 2-vertex (dimer) ground-state energy** (γ-5 step 786):
`singleClusterGSEnergyS 1 82 = -1722 = -S(S+1)` for `S = 41`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightytwo :
    singleClusterGSEnergyS 1 82 = (-1722 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 786):
`singleClusterMaxEnergyS 1 82 = 1681 = S²` for `S = 41`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightytwo :
    singleClusterMaxEnergyS 1 82 = (1681 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41 3-vertex (trimer) ground-state energy** (γ-5 step 787):
`singleClusterGSEnergyS 2 82 = -3403 = -S(1+zS)` for `S = 41, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightytwo :
    singleClusterGSEnergyS 2 82 = (-3403 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 787):
`singleClusterMaxEnergyS 2 82 = 3362 = zS²` for `S = 41, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightytwo :
    singleClusterMaxEnergyS 2 82 = (3362 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41 4-vertex (quartet) ground-state energy** (γ-5 step 788):
`singleClusterGSEnergyS 3 82 = -5084 = -S(1+zS)` for `S = 41, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightytwo :
    singleClusterGSEnergyS 3 82 = (-5084 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 788):
`singleClusterMaxEnergyS 3 82 = 5043 = zS²` for `S = 41, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightytwo :
    singleClusterMaxEnergyS 3 82 = (5043 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41 5-vertex (pentamer) ground-state energy** (γ-5 step 789):
`singleClusterGSEnergyS 4 82 = -6765 = -S(1+zS)` for `S = 41, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightytwo :
    singleClusterGSEnergyS 4 82 = (-6765 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 789):
`singleClusterMaxEnergyS 4 82 = 6724 = zS²` for `S = 41, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightytwo :
    singleClusterMaxEnergyS 4 82 = (6724 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41 6-vertex (hexamer) ground-state energy** (γ-5 step 790):
`singleClusterGSEnergyS 5 82 = -8446 = -S(1+zS)` for `S = 41, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightytwo :
    singleClusterGSEnergyS 5 82 = (-8446 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 790):
`singleClusterMaxEnergyS 5 82 = 8405 = zS²` for `S = 41, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightytwo :
    singleClusterMaxEnergyS 5 82 = (8405 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-41 7-vertex (heptamer) ground-state energy** (γ-5 step 791):
`singleClusterGSEnergyS 6 82 = -10127 = -S(1+zS)` for `S = 41, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightytwo :
    singleClusterGSEnergyS 6 82 = (-10127 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-41 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 791):
`singleClusterMaxEnergyS 6 82 = 10086 = zS²` for `S = 41, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightytwo :
    singleClusterMaxEnergyS 6 82 = (10086 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83/2 2-vertex (dimer) ground-state energy** (γ-5 step 792):
`singleClusterGSEnergyS 1 83 = -7055/4 = -S(S+1)` for `S = 83/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightythree :
    singleClusterGSEnergyS 1 83 = (-7055 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 792):
`singleClusterMaxEnergyS 1 83 = 6889/4 = S²` for `S = 83/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightythree :
    singleClusterMaxEnergyS 1 83 = (6889 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83/2 3-vertex (trimer) ground-state energy** (γ-5 step 793):
`singleClusterGSEnergyS 2 83 = -3486 = -S(1+zS)` for `S = 83/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightythree :
    singleClusterGSEnergyS 2 83 = (-3486 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 793):
`singleClusterMaxEnergyS 2 83 = 6889/2 = zS²` for `S = 83/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightythree :
    singleClusterMaxEnergyS 2 83 = (6889 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83/2 4-vertex (quartet) ground-state energy** (γ-5 step 794):
`singleClusterGSEnergyS 3 83 = -20833/4 = -S(1+zS)` for `S = 83/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightythree :
    singleClusterGSEnergyS 3 83 = (-20833 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 794):
`singleClusterMaxEnergyS 3 83 = 20667/4 = zS²` for `S = 83/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightythree :
    singleClusterMaxEnergyS 3 83 = (20667 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83/2 5-vertex (pentamer) ground-state energy** (γ-5 step 795):
`singleClusterGSEnergyS 4 83 = -13861/2 = -S(1+zS)` for `S = 83/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightythree :
    singleClusterGSEnergyS 4 83 = (-13861 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 795):
`singleClusterMaxEnergyS 4 83 = 6889 = zS²` for `S = 83/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightythree :
    singleClusterMaxEnergyS 4 83 = (6889 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83/2 6-vertex (hexamer) ground-state energy** (γ-5 step 796):
`singleClusterGSEnergyS 5 83 = -34611/4 = -S(1+zS)` for `S = 83/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightythree :
    singleClusterGSEnergyS 5 83 = (-34611 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 796):
`singleClusterMaxEnergyS 5 83 = 34445/4 = zS²` for `S = 83/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightythree :
    singleClusterMaxEnergyS 5 83 = (34445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83/2 7-vertex (heptamer) ground-state energy** (γ-5 step 797):
`singleClusterGSEnergyS 6 83 = -10375 = -S(1+zS)` for `S = 83/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightythree :
    singleClusterGSEnergyS 6 83 = (-10375 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 797):
`singleClusterMaxEnergyS 6 83 = 20667/2 = zS²` for `S = 83/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightythree :
    singleClusterMaxEnergyS 6 83 = (20667 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-42 2-vertex (dimer) ground-state energy** (γ-5 step 798):
`singleClusterGSEnergyS 1 84 = -1806 = -S(S+1)` for `S = 42`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightyfour :
    singleClusterGSEnergyS 1 84 = (-1806 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-42 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 798):
`singleClusterMaxEnergyS 1 84 = 1764 = S²` for `S = 42`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightyfour :
    singleClusterMaxEnergyS 1 84 = (1764 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-42 3-vertex (trimer) ground-state energy** (γ-5 step 799):
`singleClusterGSEnergyS 2 84 = -3570 = -S(1+zS)` for `S = 42, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightyfour :
    singleClusterGSEnergyS 2 84 = (-3570 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-42 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 799):
`singleClusterMaxEnergyS 2 84 = 3528 = zS²` for `S = 42, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightyfour :
    singleClusterMaxEnergyS 2 84 = (3528 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-42 4-vertex (quartet) ground-state energy** (γ-5 step 800):
`singleClusterGSEnergyS 3 84 = -5334 = -S(1+zS)` for `S = 42, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightyfour :
    singleClusterGSEnergyS 3 84 = (-5334 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-42 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 800):
`singleClusterMaxEnergyS 3 84 = 5292 = zS²` for `S = 42, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightyfour :
    singleClusterMaxEnergyS 3 84 = (5292 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-42 5-vertex (pentamer) ground-state energy** (γ-5 step 801):
`singleClusterGSEnergyS 4 84 = -7098 = -S(1+zS)` for `S = 42, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightyfour :
    singleClusterGSEnergyS 4 84 = (-7098 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-42 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 801):
`singleClusterMaxEnergyS 4 84 = 7056 = zS²` for `S = 42, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightyfour :
    singleClusterMaxEnergyS 4 84 = (7056 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-42 6-vertex (hexamer) ground-state energy** (γ-5 step 802):
`singleClusterGSEnergyS 5 84 = -8862 = -S(1+zS)` for `S = 42, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightyfour :
    singleClusterGSEnergyS 5 84 = (-8862 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-42 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 802):
`singleClusterMaxEnergyS 5 84 = 8820 = zS²` for `S = 42, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightyfour :
    singleClusterMaxEnergyS 5 84 = (8820 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-42 7-vertex (heptamer) ground-state energy** (γ-5 step 803):
`singleClusterGSEnergyS 6 84 = -10626 = -S(1+zS)` for `S = 42, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightyfour :
    singleClusterGSEnergyS 6 84 = (-10626 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-42 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 803):
`singleClusterMaxEnergyS 6 84 = 10584 = zS²` for `S = 42, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightyfour :
    singleClusterMaxEnergyS 6 84 = (10584 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85/2 2-vertex (dimer) ground-state energy** (γ-5 step 804):
`singleClusterGSEnergyS 1 85 = -7395/4 = -S(S+1)` for `S = 85/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightyfive :
    singleClusterGSEnergyS 1 85 = (-7395 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 804):
`singleClusterMaxEnergyS 1 85 = 7225/4 = S²` for `S = 85/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightyfive :
    singleClusterMaxEnergyS 1 85 = (7225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85/2 3-vertex (trimer) ground-state energy** (γ-5 step 805):
`singleClusterGSEnergyS 2 85 = -3655 = -S(1+zS)` for `S = 85/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightyfive :
    singleClusterGSEnergyS 2 85 = (-3655 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 805):
`singleClusterMaxEnergyS 2 85 = 7225/2 = zS²` for `S = 85/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightyfive :
    singleClusterMaxEnergyS 2 85 = (7225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85/2 4-vertex (quartet) ground-state energy** (γ-5 step 806):
`singleClusterGSEnergyS 3 85 = -21845/4 = -S(1+zS)` for `S = 85/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightyfive :
    singleClusterGSEnergyS 3 85 = (-21845 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 806):
`singleClusterMaxEnergyS 3 85 = 21675/4 = zS²` for `S = 85/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightyfive :
    singleClusterMaxEnergyS 3 85 = (21675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85/2 5-vertex (pentamer) ground-state energy** (γ-5 step 807):
`singleClusterGSEnergyS 4 85 = -14535/2 = -S(1+zS)` for `S = 85/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightyfive :
    singleClusterGSEnergyS 4 85 = (-14535 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 807):
`singleClusterMaxEnergyS 4 85 = 7225 = zS²` for `S = 85/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightyfive :
    singleClusterMaxEnergyS 4 85 = (7225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85/2 6-vertex (hexamer) ground-state energy** (γ-5 step 808):
`singleClusterGSEnergyS 5 85 = -36295/4 = -S(1+zS)` for `S = 85/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightyfive :
    singleClusterGSEnergyS 5 85 = (-36295 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 808):
`singleClusterMaxEnergyS 5 85 = 36125/4 = zS²` for `S = 85/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightyfive :
    singleClusterMaxEnergyS 5 85 = (36125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85/2 7-vertex (heptamer) ground-state energy** (γ-5 step 809):
`singleClusterGSEnergyS 6 85 = -10880 = -S(1+zS)` for `S = 85/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightyfive :
    singleClusterGSEnergyS 6 85 = (-10880 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 809):
`singleClusterMaxEnergyS 6 85 = 21675/2 = zS²` for `S = 85/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightyfive :
    singleClusterMaxEnergyS 6 85 = (21675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43 2-vertex (dimer) ground-state energy** (γ-5 step 810):
`singleClusterGSEnergyS 1 86 = -1892 = -S(S+1)` for `S = 43`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightysix :
    singleClusterGSEnergyS 1 86 = (-1892 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 810):
`singleClusterMaxEnergyS 1 86 = 1849 = S²` for `S = 43`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightysix :
    singleClusterMaxEnergyS 1 86 = (1849 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43 3-vertex (trimer) ground-state energy** (γ-5 step 811):
`singleClusterGSEnergyS 2 86 = -3741 = -S(1+zS)` for `S = 43, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightysix :
    singleClusterGSEnergyS 2 86 = (-3741 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 811):
`singleClusterMaxEnergyS 2 86 = 3698 = zS²` for `S = 43, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightysix :
    singleClusterMaxEnergyS 2 86 = (3698 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43 4-vertex (quartet) ground-state energy** (γ-5 step 812):
`singleClusterGSEnergyS 3 86 = -5590 = -S(1+zS)` for `S = 43, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightysix :
    singleClusterGSEnergyS 3 86 = (-5590 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 812):
`singleClusterMaxEnergyS 3 86 = 5547 = zS²` for `S = 43, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightysix :
    singleClusterMaxEnergyS 3 86 = (5547 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43 5-vertex (pentamer) ground-state energy** (γ-5 step 813):
`singleClusterGSEnergyS 4 86 = -7439 = -S(1+zS)` for `S = 43, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightysix :
    singleClusterGSEnergyS 4 86 = (-7439 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 813):
`singleClusterMaxEnergyS 4 86 = 7396 = zS²` for `S = 43, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightysix :
    singleClusterMaxEnergyS 4 86 = (7396 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43 6-vertex (hexamer) ground-state energy** (γ-5 step 814):
`singleClusterGSEnergyS 5 86 = -9288 = -S(1+zS)` for `S = 43, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightysix :
    singleClusterGSEnergyS 5 86 = (-9288 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 814):
`singleClusterMaxEnergyS 5 86 = 9245 = zS²` for `S = 43, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightysix :
    singleClusterMaxEnergyS 5 86 = (9245 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-43 7-vertex (heptamer) ground-state energy** (γ-5 step 815):
`singleClusterGSEnergyS 6 86 = -11137 = -S(1+zS)` for `S = 43, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightysix :
    singleClusterGSEnergyS 6 86 = (-11137 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-43 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 815):
`singleClusterMaxEnergyS 6 86 = 11094 = zS²` for `S = 43, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightysix :
    singleClusterMaxEnergyS 6 86 = (11094 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87/2 2-vertex (dimer) ground-state energy** (γ-5 step 816):
`singleClusterGSEnergyS 1 87 = -7743/4 = -S(S+1)` for `S = 87/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightyseven :
    singleClusterGSEnergyS 1 87 = (-7743 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 816):
`singleClusterMaxEnergyS 1 87 = 7569/4 = S²` for `S = 87/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightyseven :
    singleClusterMaxEnergyS 1 87 = (7569 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87/2 3-vertex (trimer) ground-state energy** (γ-5 step 817):
`singleClusterGSEnergyS 2 87 = -3828 = -S(1+zS)` for `S = 87/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightyseven :
    singleClusterGSEnergyS 2 87 = (-3828 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 817):
`singleClusterMaxEnergyS 2 87 = 7569/2 = zS²` for `S = 87/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightyseven :
    singleClusterMaxEnergyS 2 87 = (7569 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87/2 4-vertex (quartet) ground-state energy** (γ-5 step 818):
`singleClusterGSEnergyS 3 87 = -22881/4 = -S(1+zS)` for `S = 87/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightyseven :
    singleClusterGSEnergyS 3 87 = (-22881 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 818):
`singleClusterMaxEnergyS 3 87 = 22707/4 = zS²` for `S = 87/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightyseven :
    singleClusterMaxEnergyS 3 87 = (22707 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87/2 5-vertex (pentamer) ground-state energy** (γ-5 step 819):
`singleClusterGSEnergyS 4 87 = -15225/2 = -S(1+zS)` for `S = 87/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightyseven :
    singleClusterGSEnergyS 4 87 = (-15225 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 819):
`singleClusterMaxEnergyS 4 87 = 7569 = zS²` for `S = 87/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightyseven :
    singleClusterMaxEnergyS 4 87 = (7569 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87/2 6-vertex (hexamer) ground-state energy** (γ-5 step 820):
`singleClusterGSEnergyS 5 87 = -38019/4 = -S(1+zS)` for `S = 87/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightyseven :
    singleClusterGSEnergyS 5 87 = (-38019 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 820):
`singleClusterMaxEnergyS 5 87 = 37845/4 = zS²` for `S = 87/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightyseven :
    singleClusterMaxEnergyS 5 87 = (37845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87/2 7-vertex (heptamer) ground-state energy** (γ-5 step 821):
`singleClusterGSEnergyS 6 87 = -11397 = -S(1+zS)` for `S = 87/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightyseven :
    singleClusterGSEnergyS 6 87 = (-11397 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 821):
`singleClusterMaxEnergyS 6 87 = 22707/2 = zS²` for `S = 87/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightyseven :
    singleClusterMaxEnergyS 6 87 = (22707 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-44 2-vertex (dimer) ground-state energy** (γ-5 step 822):
`singleClusterGSEnergyS 1 88 = -1980 = -S(S+1)` for `S = 44`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightyeight :
    singleClusterGSEnergyS 1 88 = (-1980 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-44 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 822):
`singleClusterMaxEnergyS 1 88 = 1936 = S²` for `S = 44`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightyeight :
    singleClusterMaxEnergyS 1 88 = (1936 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-44 3-vertex (trimer) ground-state energy** (γ-5 step 823):
`singleClusterGSEnergyS 2 88 = -3916 = -S(1+zS)` for `S = 44, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightyeight :
    singleClusterGSEnergyS 2 88 = (-3916 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-44 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 823):
`singleClusterMaxEnergyS 2 88 = 3872 = zS²` for `S = 44, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightyeight :
    singleClusterMaxEnergyS 2 88 = (3872 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-44 4-vertex (quartet) ground-state energy** (γ-5 step 824):
`singleClusterGSEnergyS 3 88 = -5852 = -S(1+zS)` for `S = 44, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightyeight :
    singleClusterGSEnergyS 3 88 = (-5852 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-44 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 824):
`singleClusterMaxEnergyS 3 88 = 5808 = zS²` for `S = 44, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightyeight :
    singleClusterMaxEnergyS 3 88 = (5808 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-44 5-vertex (pentamer) ground-state energy** (γ-5 step 825):
`singleClusterGSEnergyS 4 88 = -7788 = -S(1+zS)` for `S = 44, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightyeight :
    singleClusterGSEnergyS 4 88 = (-7788 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-44 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 825):
`singleClusterMaxEnergyS 4 88 = 7744 = zS²` for `S = 44, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightyeight :
    singleClusterMaxEnergyS 4 88 = (7744 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-44 6-vertex (hexamer) ground-state energy** (γ-5 step 826):
`singleClusterGSEnergyS 5 88 = -9724 = -S(1+zS)` for `S = 44, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightyeight :
    singleClusterGSEnergyS 5 88 = (-9724 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-44 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 826):
`singleClusterMaxEnergyS 5 88 = 9680 = zS²` for `S = 44, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightyeight :
    singleClusterMaxEnergyS 5 88 = (9680 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-44 7-vertex (heptamer) ground-state energy** (γ-5 step 827):
`singleClusterGSEnergyS 6 88 = -11660 = -S(1+zS)` for `S = 44, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightyeight :
    singleClusterGSEnergyS 6 88 = (-11660 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-44 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 827):
`singleClusterMaxEnergyS 6 88 = 11616 = zS²` for `S = 44, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightyeight :
    singleClusterMaxEnergyS 6 88 = (11616 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89/2 2-vertex (dimer) ground-state energy** (γ-5 step 828):
`singleClusterGSEnergyS 1 89 = -8099/4 = -S(S+1)` for `S = 89/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_eightynine :
    singleClusterGSEnergyS 1 89 = (-8099 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 828):
`singleClusterMaxEnergyS 1 89 = 7921/4 = S²` for `S = 89/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eightynine :
    singleClusterMaxEnergyS 1 89 = (7921 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89/2 3-vertex (trimer) ground-state energy** (γ-5 step 829):
`singleClusterGSEnergyS 2 89 = -4005 = -S(1+zS)` for `S = 89/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eightynine :
    singleClusterGSEnergyS 2 89 = (-4005 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 829):
`singleClusterMaxEnergyS 2 89 = 7921/2 = zS²` for `S = 89/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eightynine :
    singleClusterMaxEnergyS 2 89 = (7921 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89/2 4-vertex (quartet) ground-state energy** (γ-5 step 830):
`singleClusterGSEnergyS 3 89 = -23941/4 = -S(1+zS)` for `S = 89/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eightynine :
    singleClusterGSEnergyS 3 89 = (-23941 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 830):
`singleClusterMaxEnergyS 3 89 = 23763/4 = zS²` for `S = 89/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eightynine :
    singleClusterMaxEnergyS 3 89 = (23763 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89/2 5-vertex (pentamer) ground-state energy** (γ-5 step 831):
`singleClusterGSEnergyS 4 89 = -15931/2 = -S(1+zS)` for `S = 89/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eightynine :
    singleClusterGSEnergyS 4 89 = (-15931 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 831):
`singleClusterMaxEnergyS 4 89 = 7921 = zS²` for `S = 89/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eightynine :
    singleClusterMaxEnergyS 4 89 = (7921 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89/2 6-vertex (hexamer) ground-state energy** (γ-5 step 832):
`singleClusterGSEnergyS 5 89 = -39783/4 = -S(1+zS)` for `S = 89/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eightynine :
    singleClusterGSEnergyS 5 89 = (-39783 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 832):
`singleClusterMaxEnergyS 5 89 = 39605/4 = zS²` for `S = 89/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eightynine :
    singleClusterMaxEnergyS 5 89 = (39605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89/2 7-vertex (heptamer) ground-state energy** (γ-5 step 833):
`singleClusterGSEnergyS 6 89 = -11926 = -S(1+zS)` for `S = 89/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eightynine :
    singleClusterGSEnergyS 6 89 = (-11926 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 833):
`singleClusterMaxEnergyS 6 89 = 23763/2 = zS²` for `S = 89/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eightynine :
    singleClusterMaxEnergyS 6 89 = (23763 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45 2-vertex (dimer) ground-state energy** (γ-5 step 834):
`singleClusterGSEnergyS 1 90 = -2070 = -S(S+1)` for `S = 45`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninety :
    singleClusterGSEnergyS 1 90 = (-2070 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 834):
`singleClusterMaxEnergyS 1 90 = 2025 = S²` for `S = 45`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninety :
    singleClusterMaxEnergyS 1 90 = (2025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45 3-vertex (trimer) ground-state energy** (γ-5 step 835):
`singleClusterGSEnergyS 2 90 = -4095 = -S(1+zS)` for `S = 45, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninety :
    singleClusterGSEnergyS 2 90 = (-4095 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 835):
`singleClusterMaxEnergyS 2 90 = 4050 = zS²` for `S = 45, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninety :
    singleClusterMaxEnergyS 2 90 = (4050 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45 4-vertex (quartet) ground-state energy** (γ-5 step 836):
`singleClusterGSEnergyS 3 90 = -6120 = -S(1+zS)` for `S = 45, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninety :
    singleClusterGSEnergyS 3 90 = (-6120 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 836):
`singleClusterMaxEnergyS 3 90 = 6075 = zS²` for `S = 45, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninety :
    singleClusterMaxEnergyS 3 90 = (6075 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45 5-vertex (pentamer) ground-state energy** (γ-5 step 837):
`singleClusterGSEnergyS 4 90 = -8145 = -S(1+zS)` for `S = 45, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninety :
    singleClusterGSEnergyS 4 90 = (-8145 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 837):
`singleClusterMaxEnergyS 4 90 = 8100 = zS²` for `S = 45, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninety :
    singleClusterMaxEnergyS 4 90 = (8100 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45 6-vertex (hexamer) ground-state energy** (γ-5 step 838):
`singleClusterGSEnergyS 5 90 = -10170 = -S(1+zS)` for `S = 45, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninety :
    singleClusterGSEnergyS 5 90 = (-10170 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 838):
`singleClusterMaxEnergyS 5 90 = 10125 = zS²` for `S = 45, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninety :
    singleClusterMaxEnergyS 5 90 = (10125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-45 7-vertex (heptamer) ground-state energy** (γ-5 step 839):
`singleClusterGSEnergyS 6 90 = -12195 = -S(1+zS)` for `S = 45, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninety :
    singleClusterGSEnergyS 6 90 = (-12195 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-45 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 839):
`singleClusterMaxEnergyS 6 90 = 12150 = zS²` for `S = 45, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninety :
    singleClusterMaxEnergyS 6 90 = (12150 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91/2 2-vertex (dimer) ground-state energy** (γ-5 step 840):
`singleClusterGSEnergyS 1 91 = -8463/4 = -S(S+1)` for `S = 91/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetyone :
    singleClusterGSEnergyS 1 91 = (-8463 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 840):
`singleClusterMaxEnergyS 1 91 = 8281/4 = S²` for `S = 91/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetyone :
    singleClusterMaxEnergyS 1 91 = (8281 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91/2 3-vertex (trimer) ground-state energy** (γ-5 step 841):
`singleClusterGSEnergyS 2 91 = -4186 = -S(1+zS)` for `S = 91/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetyone :
    singleClusterGSEnergyS 2 91 = (-4186 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 841):
`singleClusterMaxEnergyS 2 91 = 8281/2 = zS²` for `S = 91/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetyone :
    singleClusterMaxEnergyS 2 91 = (8281 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91/2 4-vertex (quartet) ground-state energy** (γ-5 step 842):
`singleClusterGSEnergyS 3 91 = -25025/4 = -S(1+zS)` for `S = 91/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetyone :
    singleClusterGSEnergyS 3 91 = (-25025 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 842):
`singleClusterMaxEnergyS 3 91 = 24843/4 = zS²` for `S = 91/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetyone :
    singleClusterMaxEnergyS 3 91 = (24843 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91/2 5-vertex (pentamer) ground-state energy** (γ-5 step 843):
`singleClusterGSEnergyS 4 91 = -16653/2 = -S(1+zS)` for `S = 91/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetyone :
    singleClusterGSEnergyS 4 91 = (-16653 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 843):
`singleClusterMaxEnergyS 4 91 = 8281 = zS²` for `S = 91/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetyone :
    singleClusterMaxEnergyS 4 91 = (8281 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91/2 6-vertex (hexamer) ground-state energy** (γ-5 step 844):
`singleClusterGSEnergyS 5 91 = -41587/4 = -S(1+zS)` for `S = 91/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetyone :
    singleClusterGSEnergyS 5 91 = (-41587 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 844):
`singleClusterMaxEnergyS 5 91 = 41405/4 = zS²` for `S = 91/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetyone :
    singleClusterMaxEnergyS 5 91 = (41405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91/2 7-vertex (heptamer) ground-state energy** (γ-5 step 845):
`singleClusterGSEnergyS 6 91 = -12467 = -S(1+zS)` for `S = 91/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetyone :
    singleClusterGSEnergyS 6 91 = (-12467 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 845):
`singleClusterMaxEnergyS 6 91 = 24843/2 = zS²` for `S = 91/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetyone :
    singleClusterMaxEnergyS 6 91 = (24843 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-46 2-vertex (dimer) ground-state energy** (γ-5 step 846):
`singleClusterGSEnergyS 1 92 = -2162 = -S(S+1)` for `S = 46`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetytwo :
    singleClusterGSEnergyS 1 92 = (-2162 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-46 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 846):
`singleClusterMaxEnergyS 1 92 = 2116 = S²` for `S = 46`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetytwo :
    singleClusterMaxEnergyS 1 92 = (2116 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-46 3-vertex (trimer) ground-state energy** (γ-5 step 847):
`singleClusterGSEnergyS 2 92 = -4278 = -S(1+zS)` for `S = 46, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetytwo :
    singleClusterGSEnergyS 2 92 = (-4278 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-46 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 847):
`singleClusterMaxEnergyS 2 92 = 4232 = zS²` for `S = 46, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetytwo :
    singleClusterMaxEnergyS 2 92 = (4232 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-46 4-vertex (quartet) ground-state energy** (γ-5 step 848):
`singleClusterGSEnergyS 3 92 = -6394 = -S(1+zS)` for `S = 46, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetytwo :
    singleClusterGSEnergyS 3 92 = (-6394 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-46 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 848):
`singleClusterMaxEnergyS 3 92 = 6348 = zS²` for `S = 46, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetytwo :
    singleClusterMaxEnergyS 3 92 = (6348 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-46 5-vertex (pentamer) ground-state energy** (γ-5 step 849):
`singleClusterGSEnergyS 4 92 = -8510 = -S(1+zS)` for `S = 46, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetytwo :
    singleClusterGSEnergyS 4 92 = (-8510 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-46 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 849):
`singleClusterMaxEnergyS 4 92 = 8464 = zS²` for `S = 46, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetytwo :
    singleClusterMaxEnergyS 4 92 = (8464 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-46 6-vertex (hexamer) ground-state energy** (γ-5 step 850):
`singleClusterGSEnergyS 5 92 = -10626 = -S(1+zS)` for `S = 46, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetytwo :
    singleClusterGSEnergyS 5 92 = (-10626 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-46 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 850):
`singleClusterMaxEnergyS 5 92 = 10580 = zS²` for `S = 46, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetytwo :
    singleClusterMaxEnergyS 5 92 = (10580 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-46 7-vertex (heptamer) ground-state energy** (γ-5 step 851):
`singleClusterGSEnergyS 6 92 = -12742 = -S(1+zS)` for `S = 46, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetytwo :
    singleClusterGSEnergyS 6 92 = (-12742 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-46 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 851):
`singleClusterMaxEnergyS 6 92 = 12696 = zS²` for `S = 46, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetytwo :
    singleClusterMaxEnergyS 6 92 = (12696 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-93/2 2-vertex (dimer) ground-state energy** (γ-5 step 852):
`singleClusterGSEnergyS 1 93 = -8835/4 = -S(S+1)` for `S = 93/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetythree :
    singleClusterGSEnergyS 1 93 = (-8835 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-93/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 852):
`singleClusterMaxEnergyS 1 93 = 8649/4 = S²` for `S = 93/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetythree :
    singleClusterMaxEnergyS 1 93 = (8649 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-93/2 3-vertex (trimer) ground-state energy** (γ-5 step 853):
`singleClusterGSEnergyS 2 93 = -4371 = -S(1+zS)` for `S = 93/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetythree :
    singleClusterGSEnergyS 2 93 = (-4371 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-93/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 853):
`singleClusterMaxEnergyS 2 93 = 8649/2 = zS²` for `S = 93/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetythree :
    singleClusterMaxEnergyS 2 93 = (8649 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-93/2 4-vertex (quartet) ground-state energy** (γ-5 step 854):
`singleClusterGSEnergyS 3 93 = -26133/4 = -S(1+zS)` for `S = 93/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetythree :
    singleClusterGSEnergyS 3 93 = (-26133 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-93/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 854):
`singleClusterMaxEnergyS 3 93 = 25947/4 = zS²` for `S = 93/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetythree :
    singleClusterMaxEnergyS 3 93 = (25947 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-93/2 5-vertex (pentamer) ground-state energy** (γ-5 step 855):
`singleClusterGSEnergyS 4 93 = -17391/2 = -S(1+zS)` for `S = 93/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetythree :
    singleClusterGSEnergyS 4 93 = (-17391 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-93/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 855):
`singleClusterMaxEnergyS 4 93 = 8649 = zS²` for `S = 93/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetythree :
    singleClusterMaxEnergyS 4 93 = (8649 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-93/2 6-vertex (hexamer) ground-state energy** (γ-5 step 856):
`singleClusterGSEnergyS 5 93 = -43431/4 = -S(1+zS)` for `S = 93/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetythree :
    singleClusterGSEnergyS 5 93 = (-43431 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-93/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 856):
`singleClusterMaxEnergyS 5 93 = 43245/4 = zS²` for `S = 93/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetythree :
    singleClusterMaxEnergyS 5 93 = (43245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-93/2 7-vertex (heptamer) ground-state energy** (γ-5 step 857):
`singleClusterGSEnergyS 6 93 = -13020 = -S(1+zS)` for `S = 93/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetythree :
    singleClusterGSEnergyS 6 93 = (-13020 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-93/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 857):
`singleClusterMaxEnergyS 6 93 = 25947/2 = zS²` for `S = 93/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetythree :
    singleClusterMaxEnergyS 6 93 = (25947 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47 2-vertex (dimer) ground-state energy** (γ-5 step 858):
`singleClusterGSEnergyS 1 94 = -2256 = -S(S+1)` for `S = 47`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetyfour :
    singleClusterGSEnergyS 1 94 = (-2256 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 858):
`singleClusterMaxEnergyS 1 94 = 2209 = S²` for `S = 47`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetyfour :
    singleClusterMaxEnergyS 1 94 = (2209 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47 3-vertex (trimer) ground-state energy** (γ-5 step 859):
`singleClusterGSEnergyS 2 94 = -4465 = -S(1+zS)` for `S = 47, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetyfour :
    singleClusterGSEnergyS 2 94 = (-4465 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 859):
`singleClusterMaxEnergyS 2 94 = 4418 = zS²` for `S = 47, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetyfour :
    singleClusterMaxEnergyS 2 94 = (4418 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47 4-vertex (quartet) ground-state energy** (γ-5 step 860):
`singleClusterGSEnergyS 3 94 = -6674 = -S(1+zS)` for `S = 47, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetyfour :
    singleClusterGSEnergyS 3 94 = (-6674 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 860):
`singleClusterMaxEnergyS 3 94 = 6627 = zS²` for `S = 47, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetyfour :
    singleClusterMaxEnergyS 3 94 = (6627 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47 5-vertex (pentamer) ground-state energy** (γ-5 step 861):
`singleClusterGSEnergyS 4 94 = -8883 = -S(1+zS)` for `S = 47, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetyfour :
    singleClusterGSEnergyS 4 94 = (-8883 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 861):
`singleClusterMaxEnergyS 4 94 = 8836 = zS²` for `S = 47, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetyfour :
    singleClusterMaxEnergyS 4 94 = (8836 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47 6-vertex (hexamer) ground-state energy** (γ-5 step 862):
`singleClusterGSEnergyS 5 94 = -11092 = -S(1+zS)` for `S = 47, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetyfour :
    singleClusterGSEnergyS 5 94 = (-11092 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 862):
`singleClusterMaxEnergyS 5 94 = 11045 = zS²` for `S = 47, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetyfour :
    singleClusterMaxEnergyS 5 94 = (11045 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-47 7-vertex (heptamer) ground-state energy** (γ-5 step 863):
`singleClusterGSEnergyS 6 94 = -13301 = -S(1+zS)` for `S = 47, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetyfour :
    singleClusterGSEnergyS 6 94 = (-13301 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-47 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 863):
`singleClusterMaxEnergyS 6 94 = 13254 = zS²` for `S = 47, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetyfour :
    singleClusterMaxEnergyS 6 94 = (13254 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-95/2 2-vertex (dimer) ground-state energy** (γ-5 step 864):
`singleClusterGSEnergyS 1 95 = -9215/4 = -S(S+1)` for `S = 95/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetyfive :
    singleClusterGSEnergyS 1 95 = (-9215 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-95/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 864):
`singleClusterMaxEnergyS 1 95 = 9025/4 = S²` for `S = 95/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetyfive :
    singleClusterMaxEnergyS 1 95 = (9025 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-95/2 3-vertex (trimer) ground-state energy** (γ-5 step 865):
`singleClusterGSEnergyS 2 95 = -4560 = -S(1+zS)` for `S = 95/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetyfive :
    singleClusterGSEnergyS 2 95 = (-4560 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-95/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 865):
`singleClusterMaxEnergyS 2 95 = 9025/2 = zS²` for `S = 95/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetyfive :
    singleClusterMaxEnergyS 2 95 = (9025 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-95/2 4-vertex (quartet) ground-state energy** (γ-5 step 866):
`singleClusterGSEnergyS 3 95 = -27265/4 = -S(1+zS)` for `S = 95/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetyfive :
    singleClusterGSEnergyS 3 95 = (-27265 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-95/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 866):
`singleClusterMaxEnergyS 3 95 = 27075/4 = zS²` for `S = 95/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetyfive :
    singleClusterMaxEnergyS 3 95 = (27075 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-95/2 5-vertex (pentamer) ground-state energy** (γ-5 step 867):
`singleClusterGSEnergyS 4 95 = -18145/2 = -S(1+zS)` for `S = 95/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetyfive :
    singleClusterGSEnergyS 4 95 = (-18145 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-95/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 867):
`singleClusterMaxEnergyS 4 95 = 9025 = zS²` for `S = 95/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetyfive :
    singleClusterMaxEnergyS 4 95 = (9025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-95/2 6-vertex (hexamer) ground-state energy** (γ-5 step 868):
`singleClusterGSEnergyS 5 95 = -45315/4 = -S(1+zS)` for `S = 95/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetyfive :
    singleClusterGSEnergyS 5 95 = (-45315 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-95/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 868):
`singleClusterMaxEnergyS 5 95 = 45125/4 = zS²` for `S = 95/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetyfive :
    singleClusterMaxEnergyS 5 95 = (45125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-95/2 7-vertex (heptamer) ground-state energy** (γ-5 step 869):
`singleClusterGSEnergyS 6 95 = -13585 = -S(1+zS)` for `S = 95/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetyfive :
    singleClusterGSEnergyS 6 95 = (-13585 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-95/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 869):
`singleClusterMaxEnergyS 6 95 = 27075/2 = zS²` for `S = 95/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetyfive :
    singleClusterMaxEnergyS 6 95 = (27075 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-48 2-vertex (dimer) ground-state energy** (γ-5 step 870):
`singleClusterGSEnergyS 1 96 = -2352 = -S(S+1)` for `S = 48`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetysix :
    singleClusterGSEnergyS 1 96 = (-2352 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-48 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 870):
`singleClusterMaxEnergyS 1 96 = 2304 = S²` for `S = 48`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetysix :
    singleClusterMaxEnergyS 1 96 = (2304 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-48 3-vertex (trimer) ground-state energy** (γ-5 step 871):
`singleClusterGSEnergyS 2 96 = -4656 = -S(1+zS)` for `S = 48, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetysix :
    singleClusterGSEnergyS 2 96 = (-4656 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-48 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 871):
`singleClusterMaxEnergyS 2 96 = 4608 = zS²` for `S = 48, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetysix :
    singleClusterMaxEnergyS 2 96 = (4608 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-48 4-vertex (quartet) ground-state energy** (γ-5 step 872):
`singleClusterGSEnergyS 3 96 = -6960 = -S(1+zS)` for `S = 48, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetysix :
    singleClusterGSEnergyS 3 96 = (-6960 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-48 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 872):
`singleClusterMaxEnergyS 3 96 = 6912 = zS²` for `S = 48, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetysix :
    singleClusterMaxEnergyS 3 96 = (6912 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-48 5-vertex (pentamer) ground-state energy** (γ-5 step 873):
`singleClusterGSEnergyS 4 96 = -9264 = -S(1+zS)` for `S = 48, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetysix :
    singleClusterGSEnergyS 4 96 = (-9264 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-48 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 873):
`singleClusterMaxEnergyS 4 96 = 9216 = zS²` for `S = 48, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetysix :
    singleClusterMaxEnergyS 4 96 = (9216 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-48 6-vertex (hexamer) ground-state energy** (γ-5 step 874):
`singleClusterGSEnergyS 5 96 = -11568 = -S(1+zS)` for `S = 48, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetysix :
    singleClusterGSEnergyS 5 96 = (-11568 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-48 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 874):
`singleClusterMaxEnergyS 5 96 = 11520 = zS²` for `S = 48, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetysix :
    singleClusterMaxEnergyS 5 96 = (11520 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-48 7-vertex (heptamer) ground-state energy** (γ-5 step 875):
`singleClusterGSEnergyS 6 96 = -13872 = -S(1+zS)` for `S = 48, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetysix :
    singleClusterGSEnergyS 6 96 = (-13872 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-48 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 875):
`singleClusterMaxEnergyS 6 96 = 13824 = zS²` for `S = 48, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetysix :
    singleClusterMaxEnergyS 6 96 = (13824 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-97/2 2-vertex (dimer) ground-state energy** (γ-5 step 876):
`singleClusterGSEnergyS 1 97 = -9603/4 = -S(S+1)` for `S = 97/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetyseven :
    singleClusterGSEnergyS 1 97 = (-9603 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-97/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 876):
`singleClusterMaxEnergyS 1 97 = 9409/4 = S²` for `S = 97/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetyseven :
    singleClusterMaxEnergyS 1 97 = (9409 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-97/2 3-vertex (trimer) ground-state energy** (γ-5 step 877):
`singleClusterGSEnergyS 2 97 = -4753 = -S(1+zS)` for `S = 97/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetyseven :
    singleClusterGSEnergyS 2 97 = (-4753 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-97/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 877):
`singleClusterMaxEnergyS 2 97 = 9409/2 = zS²` for `S = 97/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetyseven :
    singleClusterMaxEnergyS 2 97 = (9409 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-97/2 4-vertex (quartet) ground-state energy** (γ-5 step 878):
`singleClusterGSEnergyS 3 97 = -28421/4 = -S(1+zS)` for `S = 97/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetyseven :
    singleClusterGSEnergyS 3 97 = (-28421 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-97/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 878):
`singleClusterMaxEnergyS 3 97 = 28227/4 = zS²` for `S = 97/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetyseven :
    singleClusterMaxEnergyS 3 97 = (28227 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-97/2 5-vertex (pentamer) ground-state energy** (γ-5 step 879):
`singleClusterGSEnergyS 4 97 = -18915/2 = -S(1+zS)` for `S = 97/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetyseven :
    singleClusterGSEnergyS 4 97 = (-18915 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-97/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 879):
`singleClusterMaxEnergyS 4 97 = 9409 = zS²` for `S = 97/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetyseven :
    singleClusterMaxEnergyS 4 97 = (9409 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-97/2 6-vertex (hexamer) ground-state energy** (γ-5 step 880):
`singleClusterGSEnergyS 5 97 = -47239/4 = -S(1+zS)` for `S = 97/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetyseven :
    singleClusterGSEnergyS 5 97 = (-47239 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-97/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 880):
`singleClusterMaxEnergyS 5 97 = 47045/4 = zS²` for `S = 97/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetyseven :
    singleClusterMaxEnergyS 5 97 = (47045 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-97/2 7-vertex (heptamer) ground-state energy** (γ-5 step 881):
`singleClusterGSEnergyS 6 97 = -14162 = -S(1+zS)` for `S = 97/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetyseven :
    singleClusterGSEnergyS 6 97 = (-14162 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-97/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 881):
`singleClusterMaxEnergyS 6 97 = 28227/2 = zS²` for `S = 97/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetyseven :
    singleClusterMaxEnergyS 6 97 = (28227 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49 2-vertex (dimer) ground-state energy** (γ-5 step 882):
`singleClusterGSEnergyS 1 98 = -2450 = -S(S+1)` for `S = 49`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetyeight :
    singleClusterGSEnergyS 1 98 = (-2450 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 882):
`singleClusterMaxEnergyS 1 98 = 2401 = S²` for `S = 49`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetyeight :
    singleClusterMaxEnergyS 1 98 = (2401 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49 3-vertex (trimer) ground-state energy** (γ-5 step 883):
`singleClusterGSEnergyS 2 98 = -4851 = -S(1+zS)` for `S = 49, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetyeight :
    singleClusterGSEnergyS 2 98 = (-4851 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 883):
`singleClusterMaxEnergyS 2 98 = 4802 = zS²` for `S = 49, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetyeight :
    singleClusterMaxEnergyS 2 98 = (4802 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49 4-vertex (quartet) ground-state energy** (γ-5 step 884):
`singleClusterGSEnergyS 3 98 = -7252 = -S(1+zS)` for `S = 49, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetyeight :
    singleClusterGSEnergyS 3 98 = (-7252 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 884):
`singleClusterMaxEnergyS 3 98 = 7203 = zS²` for `S = 49, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetyeight :
    singleClusterMaxEnergyS 3 98 = (7203 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49 5-vertex (pentamer) ground-state energy** (γ-5 step 885):
`singleClusterGSEnergyS 4 98 = -9653 = -S(1+zS)` for `S = 49, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetyeight :
    singleClusterGSEnergyS 4 98 = (-9653 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 885):
`singleClusterMaxEnergyS 4 98 = 9604 = zS²` for `S = 49, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetyeight :
    singleClusterMaxEnergyS 4 98 = (9604 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49 6-vertex (hexamer) ground-state energy** (γ-5 step 886):
`singleClusterGSEnergyS 5 98 = -12054 = -S(1+zS)` for `S = 49, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetyeight :
    singleClusterGSEnergyS 5 98 = (-12054 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 886):
`singleClusterMaxEnergyS 5 98 = 12005 = zS²` for `S = 49, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetyeight :
    singleClusterMaxEnergyS 5 98 = (12005 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-49 7-vertex (heptamer) ground-state energy** (γ-5 step 887):
`singleClusterGSEnergyS 6 98 = -14455 = -S(1+zS)` for `S = 49, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetyeight :
    singleClusterGSEnergyS 6 98 = (-14455 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-49 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 887):
`singleClusterMaxEnergyS 6 98 = 14406 = zS²` for `S = 49, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetyeight :
    singleClusterMaxEnergyS 6 98 = (14406 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-99/2 2-vertex (dimer) ground-state energy** (γ-5 step 888):
`singleClusterGSEnergyS 1 99 = -9999/4 = -S(S+1)` for `S = 99/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_ninetynine :
    singleClusterGSEnergyS 1 99 = (-9999 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-99/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 888):
`singleClusterMaxEnergyS 1 99 = 9801/4 = S²` for `S = 99/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ninetynine :
    singleClusterMaxEnergyS 1 99 = (9801 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-99/2 3-vertex (trimer) ground-state energy** (γ-5 step 889):
`singleClusterGSEnergyS 2 99 = -4950 = -S(1+zS)` for `S = 99/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ninetynine :
    singleClusterGSEnergyS 2 99 = (-4950 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-99/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 889):
`singleClusterMaxEnergyS 2 99 = 9801/2 = zS²` for `S = 99/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ninetynine :
    singleClusterMaxEnergyS 2 99 = (9801 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-99/2 4-vertex (quartet) ground-state energy** (γ-5 step 890):
`singleClusterGSEnergyS 3 99 = -29601/4 = -S(1+zS)` for `S = 99/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ninetynine :
    singleClusterGSEnergyS 3 99 = (-29601 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-99/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 890):
`singleClusterMaxEnergyS 3 99 = 29403/4 = zS²` for `S = 99/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ninetynine :
    singleClusterMaxEnergyS 3 99 = (29403 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-99/2 5-vertex (pentamer) ground-state energy** (γ-5 step 891):
`singleClusterGSEnergyS 4 99 = -19701/2 = -S(1+zS)` for `S = 99/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ninetynine :
    singleClusterGSEnergyS 4 99 = (-19701 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-99/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 891):
`singleClusterMaxEnergyS 4 99 = 9801 = zS²` for `S = 99/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ninetynine :
    singleClusterMaxEnergyS 4 99 = (9801 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-99/2 6-vertex (hexamer) ground-state energy** (γ-5 step 892):
`singleClusterGSEnergyS 5 99 = -49203/4 = -S(1+zS)` for `S = 99/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ninetynine :
    singleClusterGSEnergyS 5 99 = (-49203 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-99/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 892):
`singleClusterMaxEnergyS 5 99 = 49005/4 = zS²` for `S = 99/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ninetynine :
    singleClusterMaxEnergyS 5 99 = (49005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-99/2 7-vertex (heptamer) ground-state energy** (γ-5 step 893):
`singleClusterGSEnergyS 6 99 = -14751 = -S(1+zS)` for `S = 99/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ninetynine :
    singleClusterGSEnergyS 6 99 = (-14751 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-99/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 893):
`singleClusterMaxEnergyS 6 99 = 29403/2 = zS²` for `S = 99/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ninetynine :
    singleClusterMaxEnergyS 6 99 = (29403 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-50 2-vertex (dimer) ground-state energy** (γ-5 step 894):
`singleClusterGSEnergyS 1 100 = -2550 = -S(S+1)` for `S = 50`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundred :
    singleClusterGSEnergyS 1 100 = (-2550 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-50 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 894):
`singleClusterMaxEnergyS 1 100 = 2500 = S²` for `S = 50`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundred :
    singleClusterMaxEnergyS 1 100 = (2500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-50 3-vertex (trimer) ground-state energy** (γ-5 step 895):
`singleClusterGSEnergyS 2 100 = -5050 = -S(1+zS)` for `S = 50, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundred :
    singleClusterGSEnergyS 2 100 = (-5050 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-50 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 895):
`singleClusterMaxEnergyS 2 100 = 5000 = zS²` for `S = 50, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundred :
    singleClusterMaxEnergyS 2 100 = (5000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-50 4-vertex (quartet) ground-state energy** (γ-5 step 896):
`singleClusterGSEnergyS 3 100 = -7550 = -S(1+zS)` for `S = 50, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundred :
    singleClusterGSEnergyS 3 100 = (-7550 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-50 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 896):
`singleClusterMaxEnergyS 3 100 = 7500 = zS²` for `S = 50, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundred :
    singleClusterMaxEnergyS 3 100 = (7500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-50 5-vertex (pentamer) ground-state energy** (γ-5 step 897):
`singleClusterGSEnergyS 4 100 = -10050 = -S(1+zS)` for `S = 50, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundred :
    singleClusterGSEnergyS 4 100 = (-10050 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-50 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 897):
`singleClusterMaxEnergyS 4 100 = 10000 = zS²` for `S = 50, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundred :
    singleClusterMaxEnergyS 4 100 = (10000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-50 6-vertex (hexamer) ground-state energy** (γ-5 step 898):
`singleClusterGSEnergyS 5 100 = -12550 = -S(1+zS)` for `S = 50, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundred :
    singleClusterGSEnergyS 5 100 = (-12550 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-50 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 898):
`singleClusterMaxEnergyS 5 100 = 12500 = zS²` for `S = 50, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundred :
    singleClusterMaxEnergyS 5 100 = (12500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-50 7-vertex (heptamer) ground-state energy** (γ-5 step 899):
`singleClusterGSEnergyS 6 100 = -15050 = -S(1+zS)` for `S = 50, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundred :
    singleClusterGSEnergyS 6 100 = (-15050 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-50 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 899):
`singleClusterMaxEnergyS 6 100 = 15000 = zS²` for `S = 50, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundred :
    singleClusterMaxEnergyS 6 100 = (15000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101/2 2-vertex (dimer) ground-state energy** (γ-5 step 900):
`singleClusterGSEnergyS 1 101 = -10403/4 = -S(S+1)` for `S = 101/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredone :
    singleClusterGSEnergyS 1 101 = (-10403 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 900):
`singleClusterMaxEnergyS 1 101 = 10201/4 = S²` for `S = 101/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredone :
    singleClusterMaxEnergyS 1 101 = (10201 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101/2 3-vertex (trimer) ground-state energy** (γ-5 step 901):
`singleClusterGSEnergyS 2 101 = -5151 = -S(1+zS)` for `S = 101/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredone :
    singleClusterGSEnergyS 2 101 = (-5151 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 901):
`singleClusterMaxEnergyS 2 101 = 10201/2 = zS²` for `S = 101/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredone :
    singleClusterMaxEnergyS 2 101 = (10201 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101/2 4-vertex (quartet) ground-state energy** (γ-5 step 902):
`singleClusterGSEnergyS 3 101 = -30805/4 = -S(1+zS)` for `S = 101/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredone :
    singleClusterGSEnergyS 3 101 = (-30805 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 902):
`singleClusterMaxEnergyS 3 101 = 30603/4 = zS²` for `S = 101/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredone :
    singleClusterMaxEnergyS 3 101 = (30603 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101/2 5-vertex (pentamer) ground-state energy** (γ-5 step 903):
`singleClusterGSEnergyS 4 101 = -20503/2 = -S(1+zS)` for `S = 101/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredone :
    singleClusterGSEnergyS 4 101 = (-20503 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 903):
`singleClusterMaxEnergyS 4 101 = 10201 = zS²` for `S = 101/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredone :
    singleClusterMaxEnergyS 4 101 = (10201 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101/2 6-vertex (hexamer) ground-state energy** (γ-5 step 904):
`singleClusterGSEnergyS 5 101 = -51207/4 = -S(1+zS)` for `S = 101/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredone :
    singleClusterGSEnergyS 5 101 = (-51207 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 904):
`singleClusterMaxEnergyS 5 101 = 51005/4 = zS²` for `S = 101/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredone :
    singleClusterMaxEnergyS 5 101 = (51005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101/2 7-vertex (heptamer) ground-state energy** (γ-5 step 905):
`singleClusterGSEnergyS 6 101 = -15352 = -S(1+zS)` for `S = 101/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredone :
    singleClusterGSEnergyS 6 101 = (-15352 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 905):
`singleClusterMaxEnergyS 6 101 = 30603/2 = zS²` for `S = 101/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredone :
    singleClusterMaxEnergyS 6 101 = (30603 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51 2-vertex (dimer) ground-state energy** (γ-5 step 906):
`singleClusterGSEnergyS 1 102 = -2652 = -S(S+1)` for `S = 51`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwo :
    singleClusterGSEnergyS 1 102 = (-2652 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 906):
`singleClusterMaxEnergyS 1 102 = 2601 = S²` for `S = 51`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwo :
    singleClusterMaxEnergyS 1 102 = (2601 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51 3-vertex (trimer) ground-state energy** (γ-5 step 907):
`singleClusterGSEnergyS 2 102 = -5253 = -S(1+zS)` for `S = 51, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwo :
    singleClusterGSEnergyS 2 102 = (-5253 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 907):
`singleClusterMaxEnergyS 2 102 = 5202 = zS²` for `S = 51, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwo :
    singleClusterMaxEnergyS 2 102 = (5202 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51 4-vertex (quartet) ground-state energy** (γ-5 step 908):
`singleClusterGSEnergyS 3 102 = -7854 = -S(1+zS)` for `S = 51, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwo :
    singleClusterGSEnergyS 3 102 = (-7854 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 908):
`singleClusterMaxEnergyS 3 102 = 7803 = zS²` for `S = 51, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwo :
    singleClusterMaxEnergyS 3 102 = (7803 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51 5-vertex (pentamer) ground-state energy** (γ-5 step 909):
`singleClusterGSEnergyS 4 102 = -10455 = -S(1+zS)` for `S = 51, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwo :
    singleClusterGSEnergyS 4 102 = (-10455 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 909):
`singleClusterMaxEnergyS 4 102 = 10404 = zS²` for `S = 51, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwo :
    singleClusterMaxEnergyS 4 102 = (10404 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51 6-vertex (hexamer) ground-state energy** (γ-5 step 910):
`singleClusterGSEnergyS 5 102 = -13056 = -S(1+zS)` for `S = 51, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwo :
    singleClusterGSEnergyS 5 102 = (-13056 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 910):
`singleClusterMaxEnergyS 5 102 = 13005 = zS²` for `S = 51, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwo :
    singleClusterMaxEnergyS 5 102 = (13005 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-51 7-vertex (heptamer) ground-state energy** (γ-5 step 911):
`singleClusterGSEnergyS 6 102 = -15657 = -S(1+zS)` for `S = 51, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwo :
    singleClusterGSEnergyS 6 102 = (-15657 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-51 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 911):
`singleClusterMaxEnergyS 6 102 = 15606 = zS²` for `S = 51, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwo :
    singleClusterMaxEnergyS 6 102 = (15606 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103/2 2-vertex (dimer) ground-state energy** (γ-5 step 912):
`singleClusterGSEnergyS 1 103 = -10815/4 = -S(S+1)` for `S = 103/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthree :
    singleClusterGSEnergyS 1 103 = (-10815 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 912):
`singleClusterMaxEnergyS 1 103 = 10609/4 = S²` for `S = 103/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthree :
    singleClusterMaxEnergyS 1 103 = (10609 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103/2 3-vertex (trimer) ground-state energy** (γ-5 step 913):
`singleClusterGSEnergyS 2 103 = -5356 = -S(1+zS)` for `S = 103/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthree :
    singleClusterGSEnergyS 2 103 = (-5356 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 913):
`singleClusterMaxEnergyS 2 103 = 10609/2 = zS²` for `S = 103/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthree :
    singleClusterMaxEnergyS 2 103 = (10609 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103/2 4-vertex (quartet) ground-state energy** (γ-5 step 914):
`singleClusterGSEnergyS 3 103 = -32033/4 = -S(1+zS)` for `S = 103/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthree :
    singleClusterGSEnergyS 3 103 = (-32033 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 914):
`singleClusterMaxEnergyS 3 103 = 31827/4 = zS²` for `S = 103/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthree :
    singleClusterMaxEnergyS 3 103 = (31827 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103/2 5-vertex (pentamer) ground-state energy** (γ-5 step 915):
`singleClusterGSEnergyS 4 103 = -21321/2 = -S(1+zS)` for `S = 103/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthree :
    singleClusterGSEnergyS 4 103 = (-21321 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 915):
`singleClusterMaxEnergyS 4 103 = 10609 = zS²` for `S = 103/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthree :
    singleClusterMaxEnergyS 4 103 = (10609 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103/2 6-vertex (hexamer) ground-state energy** (γ-5 step 916):
`singleClusterGSEnergyS 5 103 = -53251/4 = -S(1+zS)` for `S = 103/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthree :
    singleClusterGSEnergyS 5 103 = (-53251 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 916):
`singleClusterMaxEnergyS 5 103 = 53045/4 = zS²` for `S = 103/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthree :
    singleClusterMaxEnergyS 5 103 = (53045 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103/2 7-vertex (heptamer) ground-state energy** (γ-5 step 917):
`singleClusterGSEnergyS 6 103 = -15965 = -S(1+zS)` for `S = 103/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthree :
    singleClusterGSEnergyS 6 103 = (-15965 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 917):
`singleClusterMaxEnergyS 6 103 = 31827/2 = zS²` for `S = 103/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthree :
    singleClusterMaxEnergyS 6 103 = (31827 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-52 2-vertex (dimer) ground-state energy** (γ-5 step 918):
`singleClusterGSEnergyS 1 104 = -2756 = -S(S+1)` for `S = 52`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfour :
    singleClusterGSEnergyS 1 104 = (-2756 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-52 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 918):
`singleClusterMaxEnergyS 1 104 = 2704 = S²` for `S = 52`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfour :
    singleClusterMaxEnergyS 1 104 = (2704 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-52 3-vertex (trimer) ground-state energy** (γ-5 step 919):
`singleClusterGSEnergyS 2 104 = -5460 = -S(1+zS)` for `S = 52, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfour :
    singleClusterGSEnergyS 2 104 = (-5460 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-52 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 919):
`singleClusterMaxEnergyS 2 104 = 5408 = zS²` for `S = 52, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfour :
    singleClusterMaxEnergyS 2 104 = (5408 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-52 4-vertex (quartet) ground-state energy** (γ-5 step 920):
`singleClusterGSEnergyS 3 104 = -8164 = -S(1+zS)` for `S = 52, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfour :
    singleClusterGSEnergyS 3 104 = (-8164 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-52 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 920):
`singleClusterMaxEnergyS 3 104 = 8112 = zS²` for `S = 52, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfour :
    singleClusterMaxEnergyS 3 104 = (8112 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-52 5-vertex (pentamer) ground-state energy** (γ-5 step 921):
`singleClusterGSEnergyS 4 104 = -10868 = -S(1+zS)` for `S = 52, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfour :
    singleClusterGSEnergyS 4 104 = (-10868 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-52 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 921):
`singleClusterMaxEnergyS 4 104 = 10816 = zS²` for `S = 52, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfour :
    singleClusterMaxEnergyS 4 104 = (10816 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-52 6-vertex (hexamer) ground-state energy** (γ-5 step 922):
`singleClusterGSEnergyS 5 104 = -13572 = -S(1+zS)` for `S = 52, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfour :
    singleClusterGSEnergyS 5 104 = (-13572 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-52 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 922):
`singleClusterMaxEnergyS 5 104 = 13520 = zS²` for `S = 52, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfour :
    singleClusterMaxEnergyS 5 104 = (13520 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-52 7-vertex (heptamer) ground-state energy** (γ-5 step 923):
`singleClusterGSEnergyS 6 104 = -16276 = -S(1+zS)` for `S = 52, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfour :
    singleClusterGSEnergyS 6 104 = (-16276 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-52 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 923):
`singleClusterMaxEnergyS 6 104 = 16224 = zS²` for `S = 52, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfour :
    singleClusterMaxEnergyS 6 104 = (16224 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
