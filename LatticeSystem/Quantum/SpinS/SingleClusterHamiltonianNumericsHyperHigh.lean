/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Hyper-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 99`
(spin `S = N/2 ≥ 99/2`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
and the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all seven numerics files can elaborate
in parallel after the main file. The split from `MaxHigh` to
`HyperHigh` was introduced as the 50-PR build-performance cadence
refactor #11 when `MaxHigh` reached ~9.8 s user CPU after the
N=99..115 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

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

/-- **Spin-105/2 2-vertex (dimer) ground-state energy** (γ-5 step 924):
`singleClusterGSEnergyS 1 105 = -11235/4 = -S(S+1)` for `S = 105/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfive :
    singleClusterGSEnergyS 1 105 = (-11235 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 924):
`singleClusterMaxEnergyS 1 105 = 11025/4 = S²` for `S = 105/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfive :
    singleClusterMaxEnergyS 1 105 = (11025 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105/2 3-vertex (trimer) ground-state energy** (γ-5 step 925):
`singleClusterGSEnergyS 2 105 = -5565 = -S(1+zS)` for `S = 105/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfive :
    singleClusterGSEnergyS 2 105 = (-5565 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 925):
`singleClusterMaxEnergyS 2 105 = 11025/2 = zS²` for `S = 105/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfive :
    singleClusterMaxEnergyS 2 105 = (11025 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105/2 4-vertex (quartet) ground-state energy** (γ-5 step 926):
`singleClusterGSEnergyS 3 105 = -33285/4 = -S(1+zS)` for `S = 105/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfive :
    singleClusterGSEnergyS 3 105 = (-33285 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 926):
`singleClusterMaxEnergyS 3 105 = 33075/4 = zS²` for `S = 105/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfive :
    singleClusterMaxEnergyS 3 105 = (33075 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105/2 5-vertex (pentamer) ground-state energy** (γ-5 step 927):
`singleClusterGSEnergyS 4 105 = -22155/2 = -S(1+zS)` for `S = 105/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfive :
    singleClusterGSEnergyS 4 105 = (-22155 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 927):
`singleClusterMaxEnergyS 4 105 = 11025 = zS²` for `S = 105/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfive :
    singleClusterMaxEnergyS 4 105 = (11025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105/2 6-vertex (hexamer) ground-state energy** (γ-5 step 928):
`singleClusterGSEnergyS 5 105 = -55335/4 = -S(1+zS)` for `S = 105/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfive :
    singleClusterGSEnergyS 5 105 = (-55335 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 928):
`singleClusterMaxEnergyS 5 105 = 55125/4 = zS²` for `S = 105/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfive :
    singleClusterMaxEnergyS 5 105 = (55125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105/2 7-vertex (heptamer) ground-state energy** (γ-5 step 929):
`singleClusterGSEnergyS 6 105 = -16590 = -S(1+zS)` for `S = 105/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfive :
    singleClusterGSEnergyS 6 105 = (-16590 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 929):
`singleClusterMaxEnergyS 6 105 = 33075/2 = zS²` for `S = 105/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfive :
    singleClusterMaxEnergyS 6 105 = (33075 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53 2-vertex (dimer) ground-state energy** (γ-5 step 930):
`singleClusterGSEnergyS 1 106 = -2862 = -S(S+1)` for `S = 53`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsix :
    singleClusterGSEnergyS 1 106 = (-2862 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 930):
`singleClusterMaxEnergyS 1 106 = 2809 = S²` for `S = 53`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsix :
    singleClusterMaxEnergyS 1 106 = (2809 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53 3-vertex (trimer) ground-state energy** (γ-5 step 931):
`singleClusterGSEnergyS 2 106 = -5671 = -S(1+zS)` for `S = 53, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsix :
    singleClusterGSEnergyS 2 106 = (-5671 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 931):
`singleClusterMaxEnergyS 2 106 = 5618 = zS²` for `S = 53, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsix :
    singleClusterMaxEnergyS 2 106 = (5618 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53 4-vertex (quartet) ground-state energy** (γ-5 step 932):
`singleClusterGSEnergyS 3 106 = -8480 = -S(1+zS)` for `S = 53, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsix :
    singleClusterGSEnergyS 3 106 = (-8480 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 932):
`singleClusterMaxEnergyS 3 106 = 8427 = zS²` for `S = 53, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsix :
    singleClusterMaxEnergyS 3 106 = (8427 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53 5-vertex (pentamer) ground-state energy** (γ-5 step 933):
`singleClusterGSEnergyS 4 106 = -11289 = -S(1+zS)` for `S = 53, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsix :
    singleClusterGSEnergyS 4 106 = (-11289 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 933):
`singleClusterMaxEnergyS 4 106 = 11236 = zS²` for `S = 53, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsix :
    singleClusterMaxEnergyS 4 106 = (11236 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53 6-vertex (hexamer) ground-state energy** (γ-5 step 934):
`singleClusterGSEnergyS 5 106 = -14098 = -S(1+zS)` for `S = 53, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsix :
    singleClusterGSEnergyS 5 106 = (-14098 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 934):
`singleClusterMaxEnergyS 5 106 = 14045 = zS²` for `S = 53, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsix :
    singleClusterMaxEnergyS 5 106 = (14045 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-53 7-vertex (heptamer) ground-state energy** (γ-5 step 935):
`singleClusterGSEnergyS 6 106 = -16907 = -S(1+zS)` for `S = 53, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsix :
    singleClusterGSEnergyS 6 106 = (-16907 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-53 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 935):
`singleClusterMaxEnergyS 6 106 = 16854 = zS²` for `S = 53, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsix :
    singleClusterMaxEnergyS 6 106 = (16854 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107/2 2-vertex (dimer) ground-state energy** (γ-5 step 936):
`singleClusterGSEnergyS 1 107 = -11663/4 = -S(S+1)` for `S = 107/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseven :
    singleClusterGSEnergyS 1 107 = (-11663 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 936):
`singleClusterMaxEnergyS 1 107 = 11449/4 = S²` for `S = 107/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseven :
    singleClusterMaxEnergyS 1 107 = (11449 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107/2 3-vertex (trimer) ground-state energy** (γ-5 step 937):
`singleClusterGSEnergyS 2 107 = -5778 = -S(1+zS)` for `S = 107/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseven :
    singleClusterGSEnergyS 2 107 = (-5778 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 937):
`singleClusterMaxEnergyS 2 107 = 11449/2 = zS²` for `S = 107/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseven :
    singleClusterMaxEnergyS 2 107 = (11449 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107/2 4-vertex (quartet) ground-state energy** (γ-5 step 938):
`singleClusterGSEnergyS 3 107 = -34561/4 = -S(1+zS)` for `S = 107/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseven :
    singleClusterGSEnergyS 3 107 = (-34561 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 938):
`singleClusterMaxEnergyS 3 107 = 34347/4 = zS²` for `S = 107/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseven :
    singleClusterMaxEnergyS 3 107 = (34347 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107/2 5-vertex (pentamer) ground-state energy** (γ-5 step 939):
`singleClusterGSEnergyS 4 107 = -23005/2 = -S(1+zS)` for `S = 107/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseven :
    singleClusterGSEnergyS 4 107 = (-23005 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 939):
`singleClusterMaxEnergyS 4 107 = 11449 = zS²` for `S = 107/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseven :
    singleClusterMaxEnergyS 4 107 = (11449 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107/2 6-vertex (hexamer) ground-state energy** (γ-5 step 940):
`singleClusterGSEnergyS 5 107 = -57459/4 = -S(1+zS)` for `S = 107/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseven :
    singleClusterGSEnergyS 5 107 = (-57459 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 940):
`singleClusterMaxEnergyS 5 107 = 57245/4 = zS²` for `S = 107/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseven :
    singleClusterMaxEnergyS 5 107 = (57245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107/2 7-vertex (heptamer) ground-state energy** (γ-5 step 941):
`singleClusterGSEnergyS 6 107 = -17227 = -S(1+zS)` for `S = 107/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseven :
    singleClusterGSEnergyS 6 107 = (-17227 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 941):
`singleClusterMaxEnergyS 6 107 = 34347/2 = zS²` for `S = 107/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseven :
    singleClusterMaxEnergyS 6 107 = (34347 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-54 2-vertex (dimer) ground-state energy** (γ-5 step 942):
`singleClusterGSEnergyS 1 108 = -2970 = -S(S+1)` for `S = 54`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeight :
    singleClusterGSEnergyS 1 108 = (-2970 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-54 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 942):
`singleClusterMaxEnergyS 1 108 = 2916 = S²` for `S = 54`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeight :
    singleClusterMaxEnergyS 1 108 = (2916 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-54 3-vertex (trimer) ground-state energy** (γ-5 step 943):
`singleClusterGSEnergyS 2 108 = -5886 = -S(1+zS)` for `S = 54, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeight :
    singleClusterGSEnergyS 2 108 = (-5886 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-54 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 943):
`singleClusterMaxEnergyS 2 108 = 5832 = zS²` for `S = 54, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeight :
    singleClusterMaxEnergyS 2 108 = (5832 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-54 4-vertex (quartet) ground-state energy** (γ-5 step 944):
`singleClusterGSEnergyS 3 108 = -8802 = -S(1+zS)` for `S = 54, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeight :
    singleClusterGSEnergyS 3 108 = (-8802 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-54 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 944):
`singleClusterMaxEnergyS 3 108 = 8748 = zS²` for `S = 54, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeight :
    singleClusterMaxEnergyS 3 108 = (8748 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-54 5-vertex (pentamer) ground-state energy** (γ-5 step 945):
`singleClusterGSEnergyS 4 108 = -11718 = -S(1+zS)` for `S = 54, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeight :
    singleClusterGSEnergyS 4 108 = (-11718 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-54 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 945):
`singleClusterMaxEnergyS 4 108 = 11664 = zS²` for `S = 54, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeight :
    singleClusterMaxEnergyS 4 108 = (11664 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-54 6-vertex (hexamer) ground-state energy** (γ-5 step 946):
`singleClusterGSEnergyS 5 108 = -14634 = -S(1+zS)` for `S = 54, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeight :
    singleClusterGSEnergyS 5 108 = (-14634 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-54 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 946):
`singleClusterMaxEnergyS 5 108 = 14580 = zS²` for `S = 54, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeight :
    singleClusterMaxEnergyS 5 108 = (14580 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-54 7-vertex (heptamer) ground-state energy** (γ-5 step 947):
`singleClusterGSEnergyS 6 108 = -17550 = -S(1+zS)` for `S = 54, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeight :
    singleClusterGSEnergyS 6 108 = (-17550 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-54 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 947):
`singleClusterMaxEnergyS 6 108 = 17496 = zS²` for `S = 54, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeight :
    singleClusterMaxEnergyS 6 108 = (17496 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109/2 2-vertex (dimer) ground-state energy** (γ-5 step 948):
`singleClusterGSEnergyS 1 109 = -12099/4 = -S(S+1)` for `S = 109/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundrednine :
    singleClusterGSEnergyS 1 109 = (-12099 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 948):
`singleClusterMaxEnergyS 1 109 = 11881/4 = S²` for `S = 109/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundrednine :
    singleClusterMaxEnergyS 1 109 = (11881 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109/2 3-vertex (trimer) ground-state energy** (γ-5 step 949):
`singleClusterGSEnergyS 2 109 = -5995 = -S(1+zS)` for `S = 109/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundrednine :
    singleClusterGSEnergyS 2 109 = (-5995 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 949):
`singleClusterMaxEnergyS 2 109 = 11881/2 = zS²` for `S = 109/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundrednine :
    singleClusterMaxEnergyS 2 109 = (11881 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109/2 4-vertex (quartet) ground-state energy** (γ-5 step 950):
`singleClusterGSEnergyS 3 109 = -35861/4 = -S(1+zS)` for `S = 109/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundrednine :
    singleClusterGSEnergyS 3 109 = (-35861 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 950):
`singleClusterMaxEnergyS 3 109 = 35643/4 = zS²` for `S = 109/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundrednine :
    singleClusterMaxEnergyS 3 109 = (35643 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109/2 5-vertex (pentamer) ground-state energy** (γ-5 step 951):
`singleClusterGSEnergyS 4 109 = -23871/2 = -S(1+zS)` for `S = 109/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundrednine :
    singleClusterGSEnergyS 4 109 = (-23871 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 951):
`singleClusterMaxEnergyS 4 109 = 11881 = zS²` for `S = 109/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundrednine :
    singleClusterMaxEnergyS 4 109 = (11881 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109/2 6-vertex (hexamer) ground-state energy** (γ-5 step 952):
`singleClusterGSEnergyS 5 109 = -59623/4 = -S(1+zS)` for `S = 109/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundrednine :
    singleClusterGSEnergyS 5 109 = (-59623 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 952):
`singleClusterMaxEnergyS 5 109 = 59405/4 = zS²` for `S = 109/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundrednine :
    singleClusterMaxEnergyS 5 109 = (59405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109/2 7-vertex (heptamer) ground-state energy** (γ-5 step 953):
`singleClusterGSEnergyS 6 109 = -17876 = -S(1+zS)` for `S = 109/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundrednine :
    singleClusterGSEnergyS 6 109 = (-17876 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 953):
`singleClusterMaxEnergyS 6 109 = 35643/2 = zS²` for `S = 109/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundrednine :
    singleClusterMaxEnergyS 6 109 = (35643 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55 2-vertex (dimer) ground-state energy** (γ-5 step 954):
`singleClusterGSEnergyS 1 110 = -3080 = -S(S+1)` for `S = 55`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredten :
    singleClusterGSEnergyS 1 110 = (-3080 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 954):
`singleClusterMaxEnergyS 1 110 = 3025 = S²` for `S = 55`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredten :
    singleClusterMaxEnergyS 1 110 = (3025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55 3-vertex (trimer) ground-state energy** (γ-5 step 955):
`singleClusterGSEnergyS 2 110 = -6105 = -S(1+zS)` for `S = 55, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredten :
    singleClusterGSEnergyS 2 110 = (-6105 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 955):
`singleClusterMaxEnergyS 2 110 = 6050 = zS²` for `S = 55, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredten :
    singleClusterMaxEnergyS 2 110 = (6050 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55 4-vertex (quartet) ground-state energy** (γ-5 step 956):
`singleClusterGSEnergyS 3 110 = -9130 = -S(1+zS)` for `S = 55, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredten :
    singleClusterGSEnergyS 3 110 = (-9130 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 956):
`singleClusterMaxEnergyS 3 110 = 9075 = zS²` for `S = 55, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredten :
    singleClusterMaxEnergyS 3 110 = (9075 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55 5-vertex (pentamer) ground-state energy** (γ-5 step 957):
`singleClusterGSEnergyS 4 110 = -12155 = -S(1+zS)` for `S = 55, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredten :
    singleClusterGSEnergyS 4 110 = (-12155 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 957):
`singleClusterMaxEnergyS 4 110 = 12100 = zS²` for `S = 55, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredten :
    singleClusterMaxEnergyS 4 110 = (12100 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55 6-vertex (hexamer) ground-state energy** (γ-5 step 958):
`singleClusterGSEnergyS 5 110 = -15180 = -S(1+zS)` for `S = 55, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredten :
    singleClusterGSEnergyS 5 110 = (-15180 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 958):
`singleClusterMaxEnergyS 5 110 = 15125 = zS²` for `S = 55, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredten :
    singleClusterMaxEnergyS 5 110 = (15125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-55 7-vertex (heptamer) ground-state energy** (γ-5 step 959):
`singleClusterGSEnergyS 6 110 = -18205 = -S(1+zS)` for `S = 55, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredten :
    singleClusterGSEnergyS 6 110 = (-18205 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-55 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 959):
`singleClusterMaxEnergyS 6 110 = 18150 = zS²` for `S = 55, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredten :
    singleClusterMaxEnergyS 6 110 = (18150 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111/2 2-vertex (dimer) ground-state energy** (γ-5 step 960):
`singleClusterGSEnergyS 1 111 = -12543/4 = -S(S+1)` for `S = 111/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeleven :
    singleClusterGSEnergyS 1 111 = (-12543 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 960):
`singleClusterMaxEnergyS 1 111 = 12321/4 = S²` for `S = 111/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeleven :
    singleClusterMaxEnergyS 1 111 = (12321 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111/2 3-vertex (trimer) ground-state energy** (γ-5 step 961):
`singleClusterGSEnergyS 2 111 = -6216 = -S(1+zS)` for `S = 111/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeleven :
    singleClusterGSEnergyS 2 111 = (-6216 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 961):
`singleClusterMaxEnergyS 2 111 = 12321/2 = zS²` for `S = 111/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeleven :
    singleClusterMaxEnergyS 2 111 = (12321 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111/2 4-vertex (quartet) ground-state energy** (γ-5 step 962):
`singleClusterGSEnergyS 3 111 = -37185/4 = -S(1+zS)` for `S = 111/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeleven :
    singleClusterGSEnergyS 3 111 = (-37185 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 962):
`singleClusterMaxEnergyS 3 111 = 36963/4 = zS²` for `S = 111/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeleven :
    singleClusterMaxEnergyS 3 111 = (36963 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111/2 5-vertex (pentamer) ground-state energy** (γ-5 step 963):
`singleClusterGSEnergyS 4 111 = -24753/2 = -S(1+zS)` for `S = 111/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeleven :
    singleClusterGSEnergyS 4 111 = (-24753 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 963):
`singleClusterMaxEnergyS 4 111 = 12321 = zS²` for `S = 111/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeleven :
    singleClusterMaxEnergyS 4 111 = (12321 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111/2 6-vertex (hexamer) ground-state energy** (γ-5 step 964):
`singleClusterGSEnergyS 5 111 = -61827/4 = -S(1+zS)` for `S = 111/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeleven :
    singleClusterGSEnergyS 5 111 = (-61827 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 964):
`singleClusterMaxEnergyS 5 111 = 61605/4 = zS²` for `S = 111/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeleven :
    singleClusterMaxEnergyS 5 111 = (61605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111/2 7-vertex (heptamer) ground-state energy** (γ-5 step 965):
`singleClusterGSEnergyS 6 111 = -18537 = -S(1+zS)` for `S = 111/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeleven :
    singleClusterGSEnergyS 6 111 = (-18537 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 965):
`singleClusterMaxEnergyS 6 111 = 36963/2 = zS²` for `S = 111/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeleven :
    singleClusterMaxEnergyS 6 111 = (36963 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-56 2-vertex (dimer) ground-state energy** (γ-5 step 966):
`singleClusterGSEnergyS 1 112 = -3192 = -S(S+1)` for `S = 56`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwelve :
    singleClusterGSEnergyS 1 112 = (-3192 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-56 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 966):
`singleClusterMaxEnergyS 1 112 = 3136 = S²` for `S = 56`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwelve :
    singleClusterMaxEnergyS 1 112 = (3136 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-56 3-vertex (trimer) ground-state energy** (γ-5 step 967):
`singleClusterGSEnergyS 2 112 = -6328 = -S(1+zS)` for `S = 56, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwelve :
    singleClusterGSEnergyS 2 112 = (-6328 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-56 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 967):
`singleClusterMaxEnergyS 2 112 = 6272 = zS²` for `S = 56, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwelve :
    singleClusterMaxEnergyS 2 112 = (6272 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-56 4-vertex (quartet) ground-state energy** (γ-5 step 968):
`singleClusterGSEnergyS 3 112 = -9464 = -S(1+zS)` for `S = 56, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwelve :
    singleClusterGSEnergyS 3 112 = (-9464 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-56 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 968):
`singleClusterMaxEnergyS 3 112 = 9408 = zS²` for `S = 56, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwelve :
    singleClusterMaxEnergyS 3 112 = (9408 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-56 5-vertex (pentamer) ground-state energy** (γ-5 step 969):
`singleClusterGSEnergyS 4 112 = -12600 = -S(1+zS)` for `S = 56, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwelve :
    singleClusterGSEnergyS 4 112 = (-12600 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-56 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 969):
`singleClusterMaxEnergyS 4 112 = 12544 = zS²` for `S = 56, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwelve :
    singleClusterMaxEnergyS 4 112 = (12544 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-56 6-vertex (hexamer) ground-state energy** (γ-5 step 970):
`singleClusterGSEnergyS 5 112 = -15736 = -S(1+zS)` for `S = 56, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwelve :
    singleClusterGSEnergyS 5 112 = (-15736 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-56 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 970):
`singleClusterMaxEnergyS 5 112 = 15680 = zS²` for `S = 56, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwelve :
    singleClusterMaxEnergyS 5 112 = (15680 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-56 7-vertex (heptamer) ground-state energy** (γ-5 step 971):
`singleClusterGSEnergyS 6 112 = -18872 = -S(1+zS)` for `S = 56, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwelve :
    singleClusterGSEnergyS 6 112 = (-18872 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-56 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 971):
`singleClusterMaxEnergyS 6 112 = 18816 = zS²` for `S = 56, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwelve :
    singleClusterMaxEnergyS 6 112 = (18816 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113/2 2-vertex (dimer) ground-state energy** (γ-5 step 972):
`singleClusterGSEnergyS 1 113 = -12995/4 = -S(S+1)` for `S = 113/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirteen :
    singleClusterGSEnergyS 1 113 = (-12995 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 972):
`singleClusterMaxEnergyS 1 113 = 12769/4 = S²` for `S = 113/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirteen :
    singleClusterMaxEnergyS 1 113 = (12769 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113/2 3-vertex (trimer) ground-state energy** (γ-5 step 973):
`singleClusterGSEnergyS 2 113 = -6441 = -S(1+zS)` for `S = 113/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirteen :
    singleClusterGSEnergyS 2 113 = (-6441 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 973):
`singleClusterMaxEnergyS 2 113 = 12769/2 = zS²` for `S = 113/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirteen :
    singleClusterMaxEnergyS 2 113 = (12769 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113/2 4-vertex (quartet) ground-state energy** (γ-5 step 974):
`singleClusterGSEnergyS 3 113 = -38533/4 = -S(1+zS)` for `S = 113/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirteen :
    singleClusterGSEnergyS 3 113 = (-38533 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 974):
`singleClusterMaxEnergyS 3 113 = 38307/4 = zS²` for `S = 113/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirteen :
    singleClusterMaxEnergyS 3 113 = (38307 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113/2 5-vertex (pentamer) ground-state energy** (γ-5 step 975):
`singleClusterGSEnergyS 4 113 = -25651/2 = -S(1+zS)` for `S = 113/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirteen :
    singleClusterGSEnergyS 4 113 = (-25651 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 975):
`singleClusterMaxEnergyS 4 113 = 12769 = zS²` for `S = 113/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirteen :
    singleClusterMaxEnergyS 4 113 = (12769 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113/2 6-vertex (hexamer) ground-state energy** (γ-5 step 976):
`singleClusterGSEnergyS 5 113 = -64071/4 = -S(1+zS)` for `S = 113/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirteen :
    singleClusterGSEnergyS 5 113 = (-64071 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 976):
`singleClusterMaxEnergyS 5 113 = 63845/4 = zS²` for `S = 113/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirteen :
    singleClusterMaxEnergyS 5 113 = (63845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113/2 7-vertex (heptamer) ground-state energy** (γ-5 step 977):
`singleClusterGSEnergyS 6 113 = -19210 = -S(1+zS)` for `S = 113/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirteen :
    singleClusterGSEnergyS 6 113 = (-19210 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 977):
`singleClusterMaxEnergyS 6 113 = 38307/2 = zS²` for `S = 113/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirteen :
    singleClusterMaxEnergyS 6 113 = (38307 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57 2-vertex (dimer) ground-state energy** (γ-5 step 978):
`singleClusterGSEnergyS 1 114 = -3306 = -S(S+1)` for `S = 57`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfourteen :
    singleClusterGSEnergyS 1 114 = (-3306 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 978):
`singleClusterMaxEnergyS 1 114 = 3249 = S²` for `S = 57`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfourteen :
    singleClusterMaxEnergyS 1 114 = (3249 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57 3-vertex (trimer) ground-state energy** (γ-5 step 979):
`singleClusterGSEnergyS 2 114 = -6555 = -S(1+zS)` for `S = 57, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfourteen :
    singleClusterGSEnergyS 2 114 = (-6555 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 979):
`singleClusterMaxEnergyS 2 114 = 6498 = zS²` for `S = 57, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfourteen :
    singleClusterMaxEnergyS 2 114 = (6498 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57 4-vertex (quartet) ground-state energy** (γ-5 step 980):
`singleClusterGSEnergyS 3 114 = -9804 = -S(1+zS)` for `S = 57, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfourteen :
    singleClusterGSEnergyS 3 114 = (-9804 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 980):
`singleClusterMaxEnergyS 3 114 = 9747 = zS²` for `S = 57, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfourteen :
    singleClusterMaxEnergyS 3 114 = (9747 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57 5-vertex (pentamer) ground-state energy** (γ-5 step 981):
`singleClusterGSEnergyS 4 114 = -13053 = -S(1+zS)` for `S = 57, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfourteen :
    singleClusterGSEnergyS 4 114 = (-13053 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 981):
`singleClusterMaxEnergyS 4 114 = 12996 = zS²` for `S = 57, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfourteen :
    singleClusterMaxEnergyS 4 114 = (12996 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57 6-vertex (hexamer) ground-state energy** (γ-5 step 982):
`singleClusterGSEnergyS 5 114 = -16302 = -S(1+zS)` for `S = 57, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfourteen :
    singleClusterGSEnergyS 5 114 = (-16302 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 982):
`singleClusterMaxEnergyS 5 114 = 16245 = zS²` for `S = 57, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfourteen :
    singleClusterMaxEnergyS 5 114 = (16245 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-57 7-vertex (heptamer) ground-state energy** (γ-5 step 983):
`singleClusterGSEnergyS 6 114 = -19551 = -S(1+zS)` for `S = 57, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfourteen :
    singleClusterGSEnergyS 6 114 = (-19551 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-57 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 983):
`singleClusterMaxEnergyS 6 114 = 19494 = zS²` for `S = 57, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfourteen :
    singleClusterMaxEnergyS 6 114 = (19494 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115/2 2-vertex (dimer) ground-state energy** (γ-5 step 984):
`singleClusterGSEnergyS 1 115 = -13455/4 = -S(S+1)` for `S = 115/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfifteen :
    singleClusterGSEnergyS 1 115 = (-13455 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 984):
`singleClusterMaxEnergyS 1 115 = 13225/4 = S²` for `S = 115/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfifteen :
    singleClusterMaxEnergyS 1 115 = (13225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115/2 3-vertex (trimer) ground-state energy** (γ-5 step 985):
`singleClusterGSEnergyS 2 115 = -6670 = -S(1+zS)` for `S = 115/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfifteen :
    singleClusterGSEnergyS 2 115 = (-6670 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 985):
`singleClusterMaxEnergyS 2 115 = 13225/2 = zS²` for `S = 115/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfifteen :
    singleClusterMaxEnergyS 2 115 = (13225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115/2 4-vertex (quartet) ground-state energy** (γ-5 step 986):
`singleClusterGSEnergyS 3 115 = -39905/4 = -S(1+zS)` for `S = 115/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfifteen :
    singleClusterGSEnergyS 3 115 = (-39905 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 986):
`singleClusterMaxEnergyS 3 115 = 39675/4 = zS²` for `S = 115/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfifteen :
    singleClusterMaxEnergyS 3 115 = (39675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115/2 5-vertex (pentamer) ground-state energy** (γ-5 step 987):
`singleClusterGSEnergyS 4 115 = -26565/2 = -S(1+zS)` for `S = 115/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfifteen :
    singleClusterGSEnergyS 4 115 = (-26565 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 987):
`singleClusterMaxEnergyS 4 115 = 13225 = zS²` for `S = 115/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfifteen :
    singleClusterMaxEnergyS 4 115 = (13225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115/2 6-vertex (hexamer) ground-state energy** (γ-5 step 988):
`singleClusterGSEnergyS 5 115 = -66355/4 = -S(1+zS)` for `S = 115/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfifteen :
    singleClusterGSEnergyS 5 115 = (-66355 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 988):
`singleClusterMaxEnergyS 5 115 = 66125/4 = zS²` for `S = 115/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfifteen :
    singleClusterMaxEnergyS 5 115 = (66125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115/2 7-vertex (heptamer) ground-state energy** (γ-5 step 989):
`singleClusterGSEnergyS 6 115 = -19895 = -S(1+zS)` for `S = 115/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfifteen :
    singleClusterGSEnergyS 6 115 = (-19895 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 989):
`singleClusterMaxEnergyS 6 115 = 39675/2 = zS²` for `S = 115/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfifteen :
    singleClusterMaxEnergyS 6 115 = (39675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-58 2-vertex (dimer) ground-state energy** (γ-5 step 990):
`singleClusterGSEnergyS 1 116 = -3422 = -S(S+1)` for `S = 58`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixteen :
    singleClusterGSEnergyS 1 116 = (-3422 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-58 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 990):
`singleClusterMaxEnergyS 1 116 = 3364 = S²` for `S = 58`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixteen :
    singleClusterMaxEnergyS 1 116 = (3364 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-58 3-vertex (trimer) ground-state energy** (γ-5 step 991):
`singleClusterGSEnergyS 2 116 = -6786 = -S(1+zS)` for `S = 58, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixteen :
    singleClusterGSEnergyS 2 116 = (-6786 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-58 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 991):
`singleClusterMaxEnergyS 2 116 = 6728 = zS²` for `S = 58, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixteen :
    singleClusterMaxEnergyS 2 116 = (6728 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-58 4-vertex (quartet) ground-state energy** (γ-5 step 992):
`singleClusterGSEnergyS 3 116 = -10150 = -S(1+zS)` for `S = 58, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixteen :
    singleClusterGSEnergyS 3 116 = (-10150 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-58 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 992):
`singleClusterMaxEnergyS 3 116 = 10092 = zS²` for `S = 58, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixteen :
    singleClusterMaxEnergyS 3 116 = (10092 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-58 5-vertex (pentamer) ground-state energy** (γ-5 step 993):
`singleClusterGSEnergyS 4 116 = -13514 = -S(1+zS)` for `S = 58, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixteen :
    singleClusterGSEnergyS 4 116 = (-13514 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-58 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 993):
`singleClusterMaxEnergyS 4 116 = 13456 = zS²` for `S = 58, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixteen :
    singleClusterMaxEnergyS 4 116 = (13456 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-58 6-vertex (hexamer) ground-state energy** (γ-5 step 994):
`singleClusterGSEnergyS 5 116 = -16878 = -S(1+zS)` for `S = 58, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixteen :
    singleClusterGSEnergyS 5 116 = (-16878 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-58 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 994):
`singleClusterMaxEnergyS 5 116 = 16820 = zS²` for `S = 58, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixteen :
    singleClusterMaxEnergyS 5 116 = (16820 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-58 7-vertex (heptamer) ground-state energy** (γ-5 step 995):
`singleClusterGSEnergyS 6 116 = -20242 = -S(1+zS)` for `S = 58, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixteen :
    singleClusterGSEnergyS 6 116 = (-20242 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-58 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 995):
`singleClusterMaxEnergyS 6 116 = 20184 = zS²` for `S = 58, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixteen :
    singleClusterMaxEnergyS 6 116 = (20184 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-117/2 2-vertex (dimer) ground-state energy** (γ-5 step 996):
`singleClusterGSEnergyS 1 117 = -13923/4 = -S(S+1)` for `S = 117/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventeen :
    singleClusterGSEnergyS 1 117 = (-13923 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-117/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 996):
`singleClusterMaxEnergyS 1 117 = 13689/4 = S²` for `S = 117/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventeen :
    singleClusterMaxEnergyS 1 117 = (13689 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-117/2 3-vertex (trimer) ground-state energy** (γ-5 step 997):
`singleClusterGSEnergyS 2 117 = -6903 = -S(1+zS)` for `S = 117/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventeen :
    singleClusterGSEnergyS 2 117 = (-6903 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-117/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 997):
`singleClusterMaxEnergyS 2 117 = 13689/2 = zS²` for `S = 117/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventeen :
    singleClusterMaxEnergyS 2 117 = (13689 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
