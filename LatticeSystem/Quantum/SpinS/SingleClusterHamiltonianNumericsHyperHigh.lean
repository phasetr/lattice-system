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

The next 50-PR cadence checkpoint (refactor #12, after spin-123/2
row close at γ-5 step 1037) was an evaluate-only iteration:
`HyperHigh` measured ~7.0 s user CPU at 2432 lines (N=99..123),
still well under the historical ~10 s split trigger, so no further
file split was required at that point. The next split (to a new
`InfiniteHigh.lean` or similar) is anticipated when `HyperHigh`
crosses ~9 s, expected around N≈140.
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

/-- **Spin-117/2 4-vertex (quartet) ground-state energy** (γ-5 step 998):
`singleClusterGSEnergyS 3 117 = -41301/4 = -S(1+zS)` for `S = 117/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventeen :
    singleClusterGSEnergyS 3 117 = (-41301 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-117/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 998):
`singleClusterMaxEnergyS 3 117 = 41067/4 = zS²` for `S = 117/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventeen :
    singleClusterMaxEnergyS 3 117 = (41067 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-117/2 5-vertex (pentamer) ground-state energy** (γ-5 step 999):
`singleClusterGSEnergyS 4 117 = -27495/2 = -S(1+zS)` for `S = 117/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventeen :
    singleClusterGSEnergyS 4 117 = (-27495 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-117/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 999):
`singleClusterMaxEnergyS 4 117 = 13689 = zS²` for `S = 117/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventeen :
    singleClusterMaxEnergyS 4 117 = (13689 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-117/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1000, milestone):
`singleClusterGSEnergyS 5 117 = -68679/4 = -S(1+zS)` for `S = 117/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventeen :
    singleClusterGSEnergyS 5 117 = (-68679 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-117/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1000, milestone):
`singleClusterMaxEnergyS 5 117 = 68445/4 = zS²` for `S = 117/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventeen :
    singleClusterMaxEnergyS 5 117 = (68445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-117/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1001):
`singleClusterGSEnergyS 6 117 = -20592 = -S(1+zS)` for `S = 117/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventeen :
    singleClusterGSEnergyS 6 117 = (-20592 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-117/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1001):
`singleClusterMaxEnergyS 6 117 = 41067/2 = zS²` for `S = 117/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventeen :
    singleClusterMaxEnergyS 6 117 = (41067 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59 2-vertex (dimer) ground-state energy** (γ-5 step 1002):
`singleClusterGSEnergyS 1 118 = -3540 = -S(S+1)` for `S = 59`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeighteen :
    singleClusterGSEnergyS 1 118 = (-3540 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1002):
`singleClusterMaxEnergyS 1 118 = 3481 = S²` for `S = 59`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeighteen :
    singleClusterMaxEnergyS 1 118 = (3481 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59 3-vertex (trimer) ground-state energy** (γ-5 step 1003):
`singleClusterGSEnergyS 2 118 = -7021 = -S(1+zS)` for `S = 59, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeighteen :
    singleClusterGSEnergyS 2 118 = (-7021 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1003):
`singleClusterMaxEnergyS 2 118 = 6962 = zS²` for `S = 59, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeighteen :
    singleClusterMaxEnergyS 2 118 = (6962 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59 4-vertex (quartet) ground-state energy** (γ-5 step 1004):
`singleClusterGSEnergyS 3 118 = -10502 = -S(1+zS)` for `S = 59, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeighteen :
    singleClusterGSEnergyS 3 118 = (-10502 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1004):
`singleClusterMaxEnergyS 3 118 = 10443 = zS²` for `S = 59, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeighteen :
    singleClusterMaxEnergyS 3 118 = (10443 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59 5-vertex (pentamer) ground-state energy** (γ-5 step 1005):
`singleClusterGSEnergyS 4 118 = -13983 = -S(1+zS)` for `S = 59, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeighteen :
    singleClusterGSEnergyS 4 118 = (-13983 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1005):
`singleClusterMaxEnergyS 4 118 = 13924 = zS²` for `S = 59, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeighteen :
    singleClusterMaxEnergyS 4 118 = (13924 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59 6-vertex (hexamer) ground-state energy** (γ-5 step 1006):
`singleClusterGSEnergyS 5 118 = -17464 = -S(1+zS)` for `S = 59, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeighteen :
    singleClusterGSEnergyS 5 118 = (-17464 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1006):
`singleClusterMaxEnergyS 5 118 = 17405 = zS²` for `S = 59, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeighteen :
    singleClusterMaxEnergyS 5 118 = (17405 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-59 7-vertex (heptamer) ground-state energy** (γ-5 step 1007):
`singleClusterGSEnergyS 6 118 = -20945 = -S(1+zS)` for `S = 59, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeighteen :
    singleClusterGSEnergyS 6 118 = (-20945 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-59 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1007):
`singleClusterMaxEnergyS 6 118 = 20886 = zS²` for `S = 59, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeighteen :
    singleClusterMaxEnergyS 6 118 = (20886 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-119/2 2-vertex (dimer) ground-state energy** (γ-5 step 1008):
`singleClusterGSEnergyS 1 119 = -14399/4 = -S(S+1)` for `S = 119/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundrednineteen :
    singleClusterGSEnergyS 1 119 = (-14399 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-119/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1008):
`singleClusterMaxEnergyS 1 119 = 14161/4 = S²` for `S = 119/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundrednineteen :
    singleClusterMaxEnergyS 1 119 = (14161 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-119/2 3-vertex (trimer) ground-state energy** (γ-5 step 1009):
`singleClusterGSEnergyS 2 119 = -7140 = -S(1+zS)` for `S = 119/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundrednineteen :
    singleClusterGSEnergyS 2 119 = (-7140 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-119/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1009):
`singleClusterMaxEnergyS 2 119 = 14161/2 = zS²` for `S = 119/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundrednineteen :
    singleClusterMaxEnergyS 2 119 = (14161 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-119/2 4-vertex (quartet) ground-state energy** (γ-5 step 1010):
`singleClusterGSEnergyS 3 119 = -42721/4 = -S(1+zS)` for `S = 119/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundrednineteen :
    singleClusterGSEnergyS 3 119 = (-42721 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-119/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1010):
`singleClusterMaxEnergyS 3 119 = 42483/4 = zS²` for `S = 119/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundrednineteen :
    singleClusterMaxEnergyS 3 119 = (42483 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-119/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1011):
`singleClusterGSEnergyS 4 119 = -28441/2 = -S(1+zS)` for `S = 119/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundrednineteen :
    singleClusterGSEnergyS 4 119 = (-28441 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-119/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1011):
`singleClusterMaxEnergyS 4 119 = 14161 = zS²` for `S = 119/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundrednineteen :
    singleClusterMaxEnergyS 4 119 = (14161 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-119/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1012):
`singleClusterGSEnergyS 5 119 = -71043/4 = -S(1+zS)` for `S = 119/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundrednineteen :
    singleClusterGSEnergyS 5 119 = (-71043 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-119/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1012):
`singleClusterMaxEnergyS 5 119 = 70805/4 = zS²` for `S = 119/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundrednineteen :
    singleClusterMaxEnergyS 5 119 = (70805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-119/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1013):
`singleClusterGSEnergyS 6 119 = -21301 = -S(1+zS)` for `S = 119/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundrednineteen :
    singleClusterGSEnergyS 6 119 = (-21301 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-119/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1013):
`singleClusterMaxEnergyS 6 119 = 42483/2 = zS²` for `S = 119/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundrednineteen :
    singleClusterMaxEnergyS 6 119 = (42483 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-60 2-vertex (dimer) ground-state energy** (γ-5 step 1014):
`singleClusterGSEnergyS 1 120 = -3660 = -S(S+1)` for `S = 60`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwenty :
    singleClusterGSEnergyS 1 120 = (-3660 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-60 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1014):
`singleClusterMaxEnergyS 1 120 = 3600 = S²` for `S = 60`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwenty :
    singleClusterMaxEnergyS 1 120 = (3600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-60 3-vertex (trimer) ground-state energy** (γ-5 step 1015):
`singleClusterGSEnergyS 2 120 = -7260 = -S(1+zS)` for `S = 60, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwenty :
    singleClusterGSEnergyS 2 120 = (-7260 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-60 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1015):
`singleClusterMaxEnergyS 2 120 = 7200 = zS²` for `S = 60, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwenty :
    singleClusterMaxEnergyS 2 120 = (7200 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-60 4-vertex (quartet) ground-state energy** (γ-5 step 1016):
`singleClusterGSEnergyS 3 120 = -10860 = -S(1+zS)` for `S = 60, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwenty :
    singleClusterGSEnergyS 3 120 = (-10860 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-60 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1016):
`singleClusterMaxEnergyS 3 120 = 10800 = zS²` for `S = 60, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwenty :
    singleClusterMaxEnergyS 3 120 = (10800 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-60 5-vertex (pentamer) ground-state energy** (γ-5 step 1017):
`singleClusterGSEnergyS 4 120 = -14460 = -S(1+zS)` for `S = 60, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwenty :
    singleClusterGSEnergyS 4 120 = (-14460 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-60 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1017):
`singleClusterMaxEnergyS 4 120 = 14400 = zS²` for `S = 60, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwenty :
    singleClusterMaxEnergyS 4 120 = (14400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-60 6-vertex (hexamer) ground-state energy** (γ-5 step 1018):
`singleClusterGSEnergyS 5 120 = -18060 = -S(1+zS)` for `S = 60, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwenty :
    singleClusterGSEnergyS 5 120 = (-18060 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-60 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1018):
`singleClusterMaxEnergyS 5 120 = 18000 = zS²` for `S = 60, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwenty :
    singleClusterMaxEnergyS 5 120 = (18000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-60 7-vertex (heptamer) ground-state energy** (γ-5 step 1019):
`singleClusterGSEnergyS 6 120 = -21660 = -S(1+zS)` for `S = 60, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwenty :
    singleClusterGSEnergyS 6 120 = (-21660 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-60 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1019):
`singleClusterMaxEnergyS 6 120 = 21600 = zS²` for `S = 60, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwenty :
    singleClusterMaxEnergyS 6 120 = (21600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-121/2 2-vertex (dimer) ground-state energy** (γ-5 step 1020):
`singleClusterGSEnergyS 1 121 = -14883/4 = -S(S+1)` for `S = 121/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentyone :
    singleClusterGSEnergyS 1 121 = (-14883 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-121/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1020):
`singleClusterMaxEnergyS 1 121 = 14641/4 = S²` for `S = 121/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentyone :
    singleClusterMaxEnergyS 1 121 = (14641 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-121/2 3-vertex (trimer) ground-state energy** (γ-5 step 1021):
`singleClusterGSEnergyS 2 121 = -7381 = -S(1+zS)` for `S = 121/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentyone :
    singleClusterGSEnergyS 2 121 = (-7381 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-121/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1021):
`singleClusterMaxEnergyS 2 121 = 14641/2 = zS²` for `S = 121/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentyone :
    singleClusterMaxEnergyS 2 121 = (14641 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-121/2 4-vertex (quartet) ground-state energy** (γ-5 step 1022):
`singleClusterGSEnergyS 3 121 = -44165/4 = -S(1+zS)` for `S = 121/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentyone :
    singleClusterGSEnergyS 3 121 = (-44165 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-121/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1022):
`singleClusterMaxEnergyS 3 121 = 43923/4 = zS²` for `S = 121/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentyone :
    singleClusterMaxEnergyS 3 121 = (43923 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-121/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1023):
`singleClusterGSEnergyS 4 121 = -29403/2 = -S(1+zS)` for `S = 121/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentyone :
    singleClusterGSEnergyS 4 121 = (-29403 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-121/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1023):
`singleClusterMaxEnergyS 4 121 = 14641 = zS²` for `S = 121/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentyone :
    singleClusterMaxEnergyS 4 121 = (14641 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-121/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1024):
`singleClusterGSEnergyS 5 121 = -73447/4 = -S(1+zS)` for `S = 121/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentyone :
    singleClusterGSEnergyS 5 121 = (-73447 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-121/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1024):
`singleClusterMaxEnergyS 5 121 = 73205/4 = zS²` for `S = 121/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentyone :
    singleClusterMaxEnergyS 5 121 = (73205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-121/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1025):
`singleClusterGSEnergyS 6 121 = -22022 = -S(1+zS)` for `S = 121/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentyone :
    singleClusterGSEnergyS 6 121 = (-22022 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-121/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1025):
`singleClusterMaxEnergyS 6 121 = 43923/2 = zS²` for `S = 121/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentyone :
    singleClusterMaxEnergyS 6 121 = (43923 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61 2-vertex (dimer) ground-state energy** (γ-5 step 1026):
`singleClusterGSEnergyS 1 122 = -3782 = -S(S+1)` for `S = 61`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentytwo :
    singleClusterGSEnergyS 1 122 = (-3782 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1026):
`singleClusterMaxEnergyS 1 122 = 3721 = S²` for `S = 61`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentytwo :
    singleClusterMaxEnergyS 1 122 = (3721 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61 3-vertex (trimer) ground-state energy** (γ-5 step 1027):
`singleClusterGSEnergyS 2 122 = -7503 = -S(1+zS)` for `S = 61, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentytwo :
    singleClusterGSEnergyS 2 122 = (-7503 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1027):
`singleClusterMaxEnergyS 2 122 = 7442 = zS²` for `S = 61, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentytwo :
    singleClusterMaxEnergyS 2 122 = (7442 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61 4-vertex (quartet) ground-state energy** (γ-5 step 1028):
`singleClusterGSEnergyS 3 122 = -11224 = -S(1+zS)` for `S = 61, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentytwo :
    singleClusterGSEnergyS 3 122 = (-11224 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1028):
`singleClusterMaxEnergyS 3 122 = 11163 = zS²` for `S = 61, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentytwo :
    singleClusterMaxEnergyS 3 122 = (11163 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61 5-vertex (pentamer) ground-state energy** (γ-5 step 1029):
`singleClusterGSEnergyS 4 122 = -14945 = -S(1+zS)` for `S = 61, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentytwo :
    singleClusterGSEnergyS 4 122 = (-14945 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1029):
`singleClusterMaxEnergyS 4 122 = 14884 = zS²` for `S = 61, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentytwo :
    singleClusterMaxEnergyS 4 122 = (14884 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61 6-vertex (hexamer) ground-state energy** (γ-5 step 1030):
`singleClusterGSEnergyS 5 122 = -18666 = -S(1+zS)` for `S = 61, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentytwo :
    singleClusterGSEnergyS 5 122 = (-18666 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1030):
`singleClusterMaxEnergyS 5 122 = 18605 = zS²` for `S = 61, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentytwo :
    singleClusterMaxEnergyS 5 122 = (18605 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-61 7-vertex (heptamer) ground-state energy** (γ-5 step 1031):
`singleClusterGSEnergyS 6 122 = -22387 = -S(1+zS)` for `S = 61, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentytwo :
    singleClusterGSEnergyS 6 122 = (-22387 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-61 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1031):
`singleClusterMaxEnergyS 6 122 = 22326 = zS²` for `S = 61, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentytwo :
    singleClusterMaxEnergyS 6 122 = (22326 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-123/2 2-vertex (dimer) ground-state energy** (γ-5 step 1032):
`singleClusterGSEnergyS 1 123 = -15375/4 = -S(S+1)` for `S = 123/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentythree :
    singleClusterGSEnergyS 1 123 = (-15375 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-123/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1032):
`singleClusterMaxEnergyS 1 123 = 15129/4 = S²` for `S = 123/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentythree :
    singleClusterMaxEnergyS 1 123 = (15129 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-123/2 3-vertex (trimer) ground-state energy** (γ-5 step 1033):
`singleClusterGSEnergyS 2 123 = -7626 = -S(1+zS)` for `S = 123/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentythree :
    singleClusterGSEnergyS 2 123 = (-7626 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-123/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1033):
`singleClusterMaxEnergyS 2 123 = 15129/2 = zS²` for `S = 123/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentythree :
    singleClusterMaxEnergyS 2 123 = (15129 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-123/2 4-vertex (quartet) ground-state energy** (γ-5 step 1034):
`singleClusterGSEnergyS 3 123 = -45633/4 = -S(1+zS)` for `S = 123/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentythree :
    singleClusterGSEnergyS 3 123 = (-45633 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-123/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1034):
`singleClusterMaxEnergyS 3 123 = 45387/4 = zS²` for `S = 123/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentythree :
    singleClusterMaxEnergyS 3 123 = (45387 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-123/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1035):
`singleClusterGSEnergyS 4 123 = -30381/2 = -S(1+zS)` for `S = 123/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentythree :
    singleClusterGSEnergyS 4 123 = (-30381 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-123/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1035):
`singleClusterMaxEnergyS 4 123 = 15129 = zS²` for `S = 123/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentythree :
    singleClusterMaxEnergyS 4 123 = (15129 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-123/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1036):
`singleClusterGSEnergyS 5 123 = -75891/4 = -S(1+zS)` for `S = 123/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentythree :
    singleClusterGSEnergyS 5 123 = (-75891 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-123/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1036):
`singleClusterMaxEnergyS 5 123 = 75645/4 = zS²` for `S = 123/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentythree :
    singleClusterMaxEnergyS 5 123 = (75645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-123/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1037):
`singleClusterGSEnergyS 6 123 = -22755 = -S(1+zS)` for `S = 123/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentythree :
    singleClusterGSEnergyS 6 123 = (-22755 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-123/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1037):
`singleClusterMaxEnergyS 6 123 = 45387/2 = zS²` for `S = 123/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentythree :
    singleClusterMaxEnergyS 6 123 = (45387 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-62 2-vertex (dimer) ground-state energy** (γ-5 step 1038):
`singleClusterGSEnergyS 1 124 = -3906 = -S(S+1)` for `S = 62`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentyfour :
    singleClusterGSEnergyS 1 124 = (-3906 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-62 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1038):
`singleClusterMaxEnergyS 1 124 = 3844 = S²` for `S = 62`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentyfour :
    singleClusterMaxEnergyS 1 124 = (3844 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-62 3-vertex (trimer) ground-state energy** (γ-5 step 1039):
`singleClusterGSEnergyS 2 124 = -7750 = -S(1+zS)` for `S = 62, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentyfour :
    singleClusterGSEnergyS 2 124 = (-7750 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-62 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1039):
`singleClusterMaxEnergyS 2 124 = 7688 = zS²` for `S = 62, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentyfour :
    singleClusterMaxEnergyS 2 124 = (7688 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-62 4-vertex (quartet) ground-state energy** (γ-5 step 1040):
`singleClusterGSEnergyS 3 124 = -11594 = -S(1+zS)` for `S = 62, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentyfour :
    singleClusterGSEnergyS 3 124 = (-11594 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-62 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1040):
`singleClusterMaxEnergyS 3 124 = 11532 = zS²` for `S = 62, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentyfour :
    singleClusterMaxEnergyS 3 124 = (11532 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-62 5-vertex (pentamer) ground-state energy** (γ-5 step 1041):
`singleClusterGSEnergyS 4 124 = -15438 = -S(1+zS)` for `S = 62, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentyfour :
    singleClusterGSEnergyS 4 124 = (-15438 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-62 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1041):
`singleClusterMaxEnergyS 4 124 = 15376 = zS²` for `S = 62, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentyfour :
    singleClusterMaxEnergyS 4 124 = (15376 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-62 6-vertex (hexamer) ground-state energy** (γ-5 step 1042):
`singleClusterGSEnergyS 5 124 = -19282 = -S(1+zS)` for `S = 62, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentyfour :
    singleClusterGSEnergyS 5 124 = (-19282 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-62 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1042):
`singleClusterMaxEnergyS 5 124 = 19220 = zS²` for `S = 62, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentyfour :
    singleClusterMaxEnergyS 5 124 = (19220 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-62 7-vertex (heptamer) ground-state energy** (γ-5 step 1043):
`singleClusterGSEnergyS 6 124 = -23126 = -S(1+zS)` for `S = 62, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentyfour :
    singleClusterGSEnergyS 6 124 = (-23126 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-62 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1043):
`singleClusterMaxEnergyS 6 124 = 23064 = zS²` for `S = 62, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentyfour :
    singleClusterMaxEnergyS 6 124 = (23064 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-125/2 2-vertex (dimer) ground-state energy** (γ-5 step 1044):
`singleClusterGSEnergyS 1 125 = -15875/4 = -S(S+1)` for `S = 125/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentyfive :
    singleClusterGSEnergyS 1 125 = (-15875 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-125/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1044):
`singleClusterMaxEnergyS 1 125 = 15625/4 = S²` for `S = 125/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentyfive :
    singleClusterMaxEnergyS 1 125 = (15625 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-125/2 3-vertex (trimer) ground-state energy** (γ-5 step 1045):
`singleClusterGSEnergyS 2 125 = -7875 = -S(1+zS)` for `S = 125/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentyfive :
    singleClusterGSEnergyS 2 125 = (-7875 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-125/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1045):
`singleClusterMaxEnergyS 2 125 = 15625/2 = zS²` for `S = 125/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentyfive :
    singleClusterMaxEnergyS 2 125 = (15625 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-125/2 4-vertex (quartet) ground-state energy** (γ-5 step 1046):
`singleClusterGSEnergyS 3 125 = -47125/4 = -S(1+zS)` for `S = 125/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentyfive :
    singleClusterGSEnergyS 3 125 = (-47125 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-125/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1046):
`singleClusterMaxEnergyS 3 125 = 46875/4 = zS²` for `S = 125/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentyfive :
    singleClusterMaxEnergyS 3 125 = (46875 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-125/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1047):
`singleClusterGSEnergyS 4 125 = -31375/2 = -S(1+zS)` for `S = 125/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentyfive :
    singleClusterGSEnergyS 4 125 = (-31375 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-125/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1047):
`singleClusterMaxEnergyS 4 125 = 15625 = zS²` for `S = 125/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentyfive :
    singleClusterMaxEnergyS 4 125 = (15625 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-125/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1048):
`singleClusterGSEnergyS 5 125 = -78375/4 = -S(1+zS)` for `S = 125/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentyfive :
    singleClusterGSEnergyS 5 125 = (-78375 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-125/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1048):
`singleClusterMaxEnergyS 5 125 = 78125/4 = zS²` for `S = 125/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentyfive :
    singleClusterMaxEnergyS 5 125 = (78125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-125/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1049):
`singleClusterGSEnergyS 6 125 = -23500 = -S(1+zS)` for `S = 125/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentyfive :
    singleClusterGSEnergyS 6 125 = (-23500 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-125/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1049):
`singleClusterMaxEnergyS 6 125 = 46875/2 = zS²` for `S = 125/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentyfive :
    singleClusterMaxEnergyS 6 125 = (46875 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63 2-vertex (dimer) ground-state energy** (γ-5 step 1050):
`singleClusterGSEnergyS 1 126 = -4032 = -S(S+1)` for `S = 63`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentysix :
    singleClusterGSEnergyS 1 126 = (-4032 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1050):
`singleClusterMaxEnergyS 1 126 = 3969 = S²` for `S = 63`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentysix :
    singleClusterMaxEnergyS 1 126 = (3969 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63 3-vertex (trimer) ground-state energy** (γ-5 step 1051):
`singleClusterGSEnergyS 2 126 = -8001 = -S(1+zS)` for `S = 63, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentysix :
    singleClusterGSEnergyS 2 126 = (-8001 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1051):
`singleClusterMaxEnergyS 2 126 = 7938 = zS²` for `S = 63, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentysix :
    singleClusterMaxEnergyS 2 126 = (7938 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63 4-vertex (quartet) ground-state energy** (γ-5 step 1052):
`singleClusterGSEnergyS 3 126 = -11970 = -S(1+zS)` for `S = 63, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentysix :
    singleClusterGSEnergyS 3 126 = (-11970 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1052):
`singleClusterMaxEnergyS 3 126 = 11907 = zS²` for `S = 63, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentysix :
    singleClusterMaxEnergyS 3 126 = (11907 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63 5-vertex (pentamer) ground-state energy** (γ-5 step 1053):
`singleClusterGSEnergyS 4 126 = -15939 = -S(1+zS)` for `S = 63, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentysix :
    singleClusterGSEnergyS 4 126 = (-15939 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1053):
`singleClusterMaxEnergyS 4 126 = 15876 = zS²` for `S = 63, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentysix :
    singleClusterMaxEnergyS 4 126 = (15876 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63 6-vertex (hexamer) ground-state energy** (γ-5 step 1054):
`singleClusterGSEnergyS 5 126 = -19908 = -S(1+zS)` for `S = 63, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentysix :
    singleClusterGSEnergyS 5 126 = (-19908 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1054):
`singleClusterMaxEnergyS 5 126 = 19845 = zS²` for `S = 63, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentysix :
    singleClusterMaxEnergyS 5 126 = (19845 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-63 7-vertex (heptamer) ground-state energy** (γ-5 step 1055):
`singleClusterGSEnergyS 6 126 = -23877 = -S(1+zS)` for `S = 63, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentysix :
    singleClusterGSEnergyS 6 126 = (-23877 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-63 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1055):
`singleClusterMaxEnergyS 6 126 = 23814 = zS²` for `S = 63, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentysix :
    singleClusterMaxEnergyS 6 126 = (23814 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-127/2 2-vertex (dimer) ground-state energy** (γ-5 step 1056):
`singleClusterGSEnergyS 1 127 = -16383/4 = -S(S+1)` for `S = 127/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentyseven :
    singleClusterGSEnergyS 1 127 = (-16383 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-127/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1056):
`singleClusterMaxEnergyS 1 127 = 16129/4 = S²` for `S = 127/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentyseven :
    singleClusterMaxEnergyS 1 127 = (16129 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-127/2 3-vertex (trimer) ground-state energy** (γ-5 step 1057):
`singleClusterGSEnergyS 2 127 = -8128 = -S(1+zS)` for `S = 127/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentyseven :
    singleClusterGSEnergyS 2 127 = (-8128 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-127/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1057):
`singleClusterMaxEnergyS 2 127 = 16129/2 = zS²` for `S = 127/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentyseven :
    singleClusterMaxEnergyS 2 127 = (16129 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-127/2 4-vertex (quartet) ground-state energy** (γ-5 step 1058):
`singleClusterGSEnergyS 3 127 = -48641/4 = -S(1+zS)` for `S = 127/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentyseven :
    singleClusterGSEnergyS 3 127 = (-48641 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-127/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1058):
`singleClusterMaxEnergyS 3 127 = 48387/4 = zS²` for `S = 127/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentyseven :
    singleClusterMaxEnergyS 3 127 = (48387 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-127/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1059):
`singleClusterGSEnergyS 4 127 = -32385/2 = -S(1+zS)` for `S = 127/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentyseven :
    singleClusterGSEnergyS 4 127 = (-32385 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-127/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1059):
`singleClusterMaxEnergyS 4 127 = 16129 = zS²` for `S = 127/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentyseven :
    singleClusterMaxEnergyS 4 127 = (16129 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-127/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1060):
`singleClusterGSEnergyS 5 127 = -80899/4 = -S(1+zS)` for `S = 127/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentyseven :
    singleClusterGSEnergyS 5 127 = (-80899 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-127/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1060):
`singleClusterMaxEnergyS 5 127 = 80645/4 = zS²` for `S = 127/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentyseven :
    singleClusterMaxEnergyS 5 127 = (80645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-127/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1061):
`singleClusterGSEnergyS 6 127 = -24257 = -S(1+zS)` for `S = 127/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentyseven :
    singleClusterGSEnergyS 6 127 = (-24257 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-127/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1061):
`singleClusterMaxEnergyS 6 127 = 48387/2 = zS²` for `S = 127/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentyseven :
    singleClusterMaxEnergyS 6 127 = (48387 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-64 2-vertex (dimer) ground-state energy** (γ-5 step 1062):
`singleClusterGSEnergyS 1 128 = -4160 = -S(S+1)` for `S = 64`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentyeight :
    singleClusterGSEnergyS 1 128 = (-4160 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-64 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1062):
`singleClusterMaxEnergyS 1 128 = 4096 = S²` for `S = 64`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentyeight :
    singleClusterMaxEnergyS 1 128 = (4096 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
