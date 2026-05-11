/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Absolute-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 149`
(spin `S = N/2 ≥ 149/2`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`,
the `N = 116..131` in `SingleClusterHamiltonianNumericsInfiniteHigh.lean`,
and the `N = 132..148` in `SingleClusterHamiltonianNumericsTransfiniteHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all ten numerics files can elaborate
in parallel after the main file. The split from `TransfiniteHigh` to
`AbsoluteHigh` was introduced as the 50-PR build-performance cadence
refactor #17 when `TransfiniteHigh` reached ~8.7 s user CPU after the
N=132..165 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

/-- **Spin-149/2 2-vertex (dimer) ground-state energy** (γ-5 step 1188):
`singleClusterGSEnergyS 1 149 = -22499/4 = -S(S+1)` for `S = 149/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortynine :
    singleClusterGSEnergyS 1 149 = (-22499 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-149/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1188):
`singleClusterMaxEnergyS 1 149 = 22201/4 = S²` for `S = 149/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortynine :
    singleClusterMaxEnergyS 1 149 = (22201 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-149/2 3-vertex (trimer) ground-state energy** (γ-5 step 1189):
`singleClusterGSEnergyS 2 149 = -11175 = -S(1+zS)` for `S = 149/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortynine :
    singleClusterGSEnergyS 2 149 = (-11175 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-149/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1189):
`singleClusterMaxEnergyS 2 149 = 22201/2 = zS²` for `S = 149/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortynine :
    singleClusterMaxEnergyS 2 149 = (22201 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-149/2 4-vertex (quartet) ground-state energy** (γ-5 step 1190):
`singleClusterGSEnergyS 3 149 = -66901/4 = -S(1+zS)` for `S = 149/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortynine :
    singleClusterGSEnergyS 3 149 = (-66901 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-149/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1190):
`singleClusterMaxEnergyS 3 149 = 66603/4 = zS²` for `S = 149/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortynine :
    singleClusterMaxEnergyS 3 149 = (66603 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-149/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1191):
`singleClusterGSEnergyS 4 149 = -44551/2 = -S(1+zS)` for `S = 149/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortynine :
    singleClusterGSEnergyS 4 149 = (-44551 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-149/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1191):
`singleClusterMaxEnergyS 4 149 = 22201 = zS²` for `S = 149/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortynine :
    singleClusterMaxEnergyS 4 149 = (22201 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-149/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1192):
`singleClusterGSEnergyS 5 149 = -111303/4 = -S(1+zS)` for `S = 149/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortynine :
    singleClusterGSEnergyS 5 149 = (-111303 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-149/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1192):
`singleClusterMaxEnergyS 5 149 = 111005/4 = zS²` for `S = 149/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortynine :
    singleClusterMaxEnergyS 5 149 = (111005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-149/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1193):
`singleClusterGSEnergyS 6 149 = -33376 = -S(1+zS)` for `S = 149/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortynine :
    singleClusterGSEnergyS 6 149 = (-33376 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-149/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1193):
`singleClusterMaxEnergyS 6 149 = 66603/2 = zS²` for `S = 149/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortynine :
    singleClusterMaxEnergyS 6 149 = (66603 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75 2-vertex (dimer) ground-state energy** (γ-5 step 1194):
`singleClusterGSEnergyS 1 150 = -5700 = -S(S+1)` for `S = 75`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfifty :
    singleClusterGSEnergyS 1 150 = (-5700 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1194):
`singleClusterMaxEnergyS 1 150 = 5625 = S²` for `S = 75`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfifty :
    singleClusterMaxEnergyS 1 150 = (5625 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75 3-vertex (trimer) ground-state energy** (γ-5 step 1195):
`singleClusterGSEnergyS 2 150 = -11325 = -S(1+zS)` for `S = 75, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfifty :
    singleClusterGSEnergyS 2 150 = (-11325 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1195):
`singleClusterMaxEnergyS 2 150 = 11250 = zS²` for `S = 75, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfifty :
    singleClusterMaxEnergyS 2 150 = (11250 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75 4-vertex (quartet) ground-state energy** (γ-5 step 1196):
`singleClusterGSEnergyS 3 150 = -16950 = -S(1+zS)` for `S = 75, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfifty :
    singleClusterGSEnergyS 3 150 = (-16950 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1196):
`singleClusterMaxEnergyS 3 150 = 16875 = zS²` for `S = 75, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfifty :
    singleClusterMaxEnergyS 3 150 = (16875 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75 5-vertex (pentamer) ground-state energy** (γ-5 step 1197):
`singleClusterGSEnergyS 4 150 = -22575 = -S(1+zS)` for `S = 75, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfifty :
    singleClusterGSEnergyS 4 150 = (-22575 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1197):
`singleClusterMaxEnergyS 4 150 = 22500 = zS²` for `S = 75, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfifty :
    singleClusterMaxEnergyS 4 150 = (22500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75 6-vertex (hexamer) ground-state energy** (γ-5 step 1198):
`singleClusterGSEnergyS 5 150 = -28200 = -S(1+zS)` for `S = 75, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfifty :
    singleClusterGSEnergyS 5 150 = (-28200 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1198):
`singleClusterMaxEnergyS 5 150 = 28125 = zS²` for `S = 75, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfifty :
    singleClusterMaxEnergyS 5 150 = (28125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-75 7-vertex (heptamer) ground-state energy** (γ-5 step 1199):
`singleClusterGSEnergyS 6 150 = -33825 = -S(1+zS)` for `S = 75, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfifty :
    singleClusterGSEnergyS 6 150 = (-33825 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-75 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1199):
`singleClusterMaxEnergyS 6 150 = 33750 = zS²` for `S = 75, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfifty :
    singleClusterMaxEnergyS 6 150 = (33750 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-151/2 2-vertex (dimer) ground-state energy** (γ-5 step 1200):
`singleClusterGSEnergyS 1 151 = -23103/4 = -S(S+1)` for `S = 151/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftyone :
    singleClusterGSEnergyS 1 151 = (-23103 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-151/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1200):
`singleClusterMaxEnergyS 1 151 = 22801/4 = S²` for `S = 151/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftyone :
    singleClusterMaxEnergyS 1 151 = (22801 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-151/2 3-vertex (trimer) ground-state energy** (γ-5 step 1201):
`singleClusterGSEnergyS 2 151 = -11476 = -S(1+zS)` for `S = 151/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftyone :
    singleClusterGSEnergyS 2 151 = (-11476 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-151/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1201):
`singleClusterMaxEnergyS 2 151 = 22801/2 = zS²` for `S = 151/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftyone :
    singleClusterMaxEnergyS 2 151 = (22801 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-151/2 4-vertex (quartet) ground-state energy** (γ-5 step 1202):
`singleClusterGSEnergyS 3 151 = -68705/4 = -S(1+zS)` for `S = 151/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftyone :
    singleClusterGSEnergyS 3 151 = (-68705 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-151/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1202):
`singleClusterMaxEnergyS 3 151 = 68403/4 = zS²` for `S = 151/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftyone :
    singleClusterMaxEnergyS 3 151 = (68403 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-151/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1203):
`singleClusterGSEnergyS 4 151 = -45753/2 = -S(1+zS)` for `S = 151/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftyone :
    singleClusterGSEnergyS 4 151 = (-45753 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-151/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1203):
`singleClusterMaxEnergyS 4 151 = 22801 = zS²` for `S = 151/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftyone :
    singleClusterMaxEnergyS 4 151 = (22801 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-151/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1204):
`singleClusterGSEnergyS 5 151 = -114307/4 = -S(1+zS)` for `S = 151/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftyone :
    singleClusterGSEnergyS 5 151 = (-114307 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-151/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1204):
`singleClusterMaxEnergyS 5 151 = 114005/4 = zS²` for `S = 151/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftyone :
    singleClusterMaxEnergyS 5 151 = (114005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-151/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1205):
`singleClusterGSEnergyS 6 151 = -34277 = -S(1+zS)` for `S = 151/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftyone :
    singleClusterGSEnergyS 6 151 = (-34277 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-151/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1205):
`singleClusterMaxEnergyS 6 151 = 68403/2 = zS²` for `S = 151/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftyone :
    singleClusterMaxEnergyS 6 151 = (68403 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-76 2-vertex (dimer) ground-state energy** (γ-5 step 1206):
`singleClusterGSEnergyS 1 152 = -5852 = -S(S+1)` for `S = 76`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftytwo :
    singleClusterGSEnergyS 1 152 = (-5852 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-76 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1206):
`singleClusterMaxEnergyS 1 152 = 5776 = S²` for `S = 76`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftytwo :
    singleClusterMaxEnergyS 1 152 = (5776 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-76 3-vertex (trimer) ground-state energy** (γ-5 step 1207):
`singleClusterGSEnergyS 2 152 = -11628 = -S(1+zS)` for `S = 76, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftytwo :
    singleClusterGSEnergyS 2 152 = (-11628 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-76 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1207):
`singleClusterMaxEnergyS 2 152 = 11552 = zS²` for `S = 76, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftytwo :
    singleClusterMaxEnergyS 2 152 = (11552 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-76 4-vertex (quartet) ground-state energy** (γ-5 step 1208):
`singleClusterGSEnergyS 3 152 = -17404 = -S(1+zS)` for `S = 76, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftytwo :
    singleClusterGSEnergyS 3 152 = (-17404 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-76 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1208):
`singleClusterMaxEnergyS 3 152 = 17328 = zS²` for `S = 76, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftytwo :
    singleClusterMaxEnergyS 3 152 = (17328 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-76 5-vertex (pentamer) ground-state energy** (γ-5 step 1209):
`singleClusterGSEnergyS 4 152 = -23180 = -S(1+zS)` for `S = 76, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftytwo :
    singleClusterGSEnergyS 4 152 = (-23180 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-76 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1209):
`singleClusterMaxEnergyS 4 152 = 23104 = zS²` for `S = 76, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftytwo :
    singleClusterMaxEnergyS 4 152 = (23104 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-76 6-vertex (hexamer) ground-state energy** (γ-5 step 1210):
`singleClusterGSEnergyS 5 152 = -28956 = -S(1+zS)` for `S = 76, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftytwo :
    singleClusterGSEnergyS 5 152 = (-28956 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-76 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1210):
`singleClusterMaxEnergyS 5 152 = 28880 = zS²` for `S = 76, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftytwo :
    singleClusterMaxEnergyS 5 152 = (28880 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-76 7-vertex (heptamer) ground-state energy** (γ-5 step 1211):
`singleClusterGSEnergyS 6 152 = -34732 = -S(1+zS)` for `S = 76, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftytwo :
    singleClusterGSEnergyS 6 152 = (-34732 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-76 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1211):
`singleClusterMaxEnergyS 6 152 = 34656 = zS²` for `S = 76, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftytwo :
    singleClusterMaxEnergyS 6 152 = (34656 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-153/2 2-vertex (dimer) ground-state energy** (γ-5 step 1212):
`singleClusterGSEnergyS 1 153 = -23715/4 = -S(S+1)` for `S = 153/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftythree :
    singleClusterGSEnergyS 1 153 = (-23715 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-153/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1212):
`singleClusterMaxEnergyS 1 153 = 23409/4 = S²` for `S = 153/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftythree :
    singleClusterMaxEnergyS 1 153 = (23409 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-153/2 3-vertex (trimer) ground-state energy** (γ-5 step 1213):
`singleClusterGSEnergyS 2 153 = -11781 = -S(1+zS)` for `S = 153/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftythree :
    singleClusterGSEnergyS 2 153 = (-11781 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-153/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1213):
`singleClusterMaxEnergyS 2 153 = 23409/2 = zS²` for `S = 153/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftythree :
    singleClusterMaxEnergyS 2 153 = (23409 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-153/2 4-vertex (quartet) ground-state energy** (γ-5 step 1214):
`singleClusterGSEnergyS 3 153 = -70533/4 = -S(1+zS)` for `S = 153/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftythree :
    singleClusterGSEnergyS 3 153 = (-70533 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-153/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1214):
`singleClusterMaxEnergyS 3 153 = 70227/4 = zS²` for `S = 153/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftythree :
    singleClusterMaxEnergyS 3 153 = (70227 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-153/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1215):
`singleClusterGSEnergyS 4 153 = -46971/2 = -S(1+zS)` for `S = 153/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftythree :
    singleClusterGSEnergyS 4 153 = (-46971 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-153/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1215):
`singleClusterMaxEnergyS 4 153 = 23409 = zS²` for `S = 153/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftythree :
    singleClusterMaxEnergyS 4 153 = (23409 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-153/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1216):
`singleClusterGSEnergyS 5 153 = -117351/4 = -S(1+zS)` for `S = 153/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftythree :
    singleClusterGSEnergyS 5 153 = (-117351 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-153/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1216):
`singleClusterMaxEnergyS 5 153 = 117045/4 = zS²` for `S = 153/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftythree :
    singleClusterMaxEnergyS 5 153 = (117045 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-153/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1217):
`singleClusterGSEnergyS 6 153 = -35190 = -S(1+zS)` for `S = 153/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftythree :
    singleClusterGSEnergyS 6 153 = (-35190 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-153/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1217):
`singleClusterMaxEnergyS 6 153 = 70227/2 = zS²` for `S = 153/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftythree :
    singleClusterMaxEnergyS 6 153 = (70227 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77 2-vertex (dimer) ground-state energy** (γ-5 step 1218):
`singleClusterGSEnergyS 1 154 = -6006 = -S(S+1)` for `S = 77`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftyfour :
    singleClusterGSEnergyS 1 154 = (-6006 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1218):
`singleClusterMaxEnergyS 1 154 = 5929 = S²` for `S = 77`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftyfour :
    singleClusterMaxEnergyS 1 154 = (5929 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77 3-vertex (trimer) ground-state energy** (γ-5 step 1219):
`singleClusterGSEnergyS 2 154 = -11935 = -S(1+zS)` for `S = 77, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftyfour :
    singleClusterGSEnergyS 2 154 = (-11935 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1219):
`singleClusterMaxEnergyS 2 154 = 11858 = zS²` for `S = 77, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftyfour :
    singleClusterMaxEnergyS 2 154 = (11858 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77 4-vertex (quartet) ground-state energy** (γ-5 step 1220):
`singleClusterGSEnergyS 3 154 = -17864 = -S(1+zS)` for `S = 77, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftyfour :
    singleClusterGSEnergyS 3 154 = (-17864 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1220):
`singleClusterMaxEnergyS 3 154 = 17787 = zS²` for `S = 77, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftyfour :
    singleClusterMaxEnergyS 3 154 = (17787 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77 5-vertex (pentamer) ground-state energy** (γ-5 step 1221):
`singleClusterGSEnergyS 4 154 = -23793 = -S(1+zS)` for `S = 77, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftyfour :
    singleClusterGSEnergyS 4 154 = (-23793 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1221):
`singleClusterMaxEnergyS 4 154 = 23716 = zS²` for `S = 77, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftyfour :
    singleClusterMaxEnergyS 4 154 = (23716 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77 6-vertex (hexamer) ground-state energy** (γ-5 step 1222):
`singleClusterGSEnergyS 5 154 = -29722 = -S(1+zS)` for `S = 77, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftyfour :
    singleClusterGSEnergyS 5 154 = (-29722 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1222):
`singleClusterMaxEnergyS 5 154 = 29645 = zS²` for `S = 77, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftyfour :
    singleClusterMaxEnergyS 5 154 = (29645 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-77 7-vertex (heptamer) ground-state energy** (γ-5 step 1223):
`singleClusterGSEnergyS 6 154 = -35651 = -S(1+zS)` for `S = 77, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftyfour :
    singleClusterGSEnergyS 6 154 = (-35651 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-77 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1223):
`singleClusterMaxEnergyS 6 154 = 35574 = zS²` for `S = 77, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftyfour :
    singleClusterMaxEnergyS 6 154 = (35574 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-155/2 2-vertex (dimer) ground-state energy** (γ-5 step 1224):
`singleClusterGSEnergyS 1 155 = -24335/4 = -S(S+1)` for `S = 155/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftyfive :
    singleClusterGSEnergyS 1 155 = (-24335 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-155/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1224):
`singleClusterMaxEnergyS 1 155 = 24025/4 = S²` for `S = 155/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftyfive :
    singleClusterMaxEnergyS 1 155 = (24025 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-155/2 3-vertex (trimer) ground-state energy** (γ-5 step 1225):
`singleClusterGSEnergyS 2 155 = -12090 = -S(1+zS)` for `S = 155/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftyfive :
    singleClusterGSEnergyS 2 155 = (-12090 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-155/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1225):
`singleClusterMaxEnergyS 2 155 = 24025/2 = zS²` for `S = 155/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftyfive :
    singleClusterMaxEnergyS 2 155 = (24025 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-155/2 4-vertex (quartet) ground-state energy** (γ-5 step 1226):
`singleClusterGSEnergyS 3 155 = -72385/4 = -S(1+zS)` for `S = 155/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftyfive :
    singleClusterGSEnergyS 3 155 = (-72385 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-155/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1226):
`singleClusterMaxEnergyS 3 155 = 72075/4 = zS²` for `S = 155/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftyfive :
    singleClusterMaxEnergyS 3 155 = (72075 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-155/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1227):
`singleClusterGSEnergyS 4 155 = -48205/2 = -S(1+zS)` for `S = 155/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftyfive :
    singleClusterGSEnergyS 4 155 = (-48205 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-155/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1227):
`singleClusterMaxEnergyS 4 155 = 24025 = zS²` for `S = 155/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftyfive :
    singleClusterMaxEnergyS 4 155 = (24025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-155/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1228):
`singleClusterGSEnergyS 5 155 = -120435/4 = -S(1+zS)` for `S = 155/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftyfive :
    singleClusterGSEnergyS 5 155 = (-120435 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-155/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1228):
`singleClusterMaxEnergyS 5 155 = 120125/4 = zS²` for `S = 155/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftyfive :
    singleClusterMaxEnergyS 5 155 = (120125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-155/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1229):
`singleClusterGSEnergyS 6 155 = -36115 = -S(1+zS)` for `S = 155/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftyfive :
    singleClusterGSEnergyS 6 155 = (-36115 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-155/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1229):
`singleClusterMaxEnergyS 6 155 = 72075/2 = zS²` for `S = 155/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftyfive :
    singleClusterMaxEnergyS 6 155 = (72075 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-78 2-vertex (dimer) ground-state energy** (γ-5 step 1230):
`singleClusterGSEnergyS 1 156 = -6162 = -S(S+1)` for `S = 78`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftysix :
    singleClusterGSEnergyS 1 156 = (-6162 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-78 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1230):
`singleClusterMaxEnergyS 1 156 = 6084 = S²` for `S = 78`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftysix :
    singleClusterMaxEnergyS 1 156 = (6084 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-78 3-vertex (trimer) ground-state energy** (γ-5 step 1231):
`singleClusterGSEnergyS 2 156 = -12246 = -S(1+zS)` for `S = 78, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftysix :
    singleClusterGSEnergyS 2 156 = (-12246 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-78 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1231):
`singleClusterMaxEnergyS 2 156 = 12168 = zS²` for `S = 78, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftysix :
    singleClusterMaxEnergyS 2 156 = (12168 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-78 4-vertex (quartet) ground-state energy** (γ-5 step 1232):
`singleClusterGSEnergyS 3 156 = -18330 = -S(1+zS)` for `S = 78, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftysix :
    singleClusterGSEnergyS 3 156 = (-18330 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-78 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1232):
`singleClusterMaxEnergyS 3 156 = 18252 = zS²` for `S = 78, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftysix :
    singleClusterMaxEnergyS 3 156 = (18252 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-78 5-vertex (pentamer) ground-state energy** (γ-5 step 1233):
`singleClusterGSEnergyS 4 156 = -24414 = -S(1+zS)` for `S = 78, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftysix :
    singleClusterGSEnergyS 4 156 = (-24414 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-78 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1233):
`singleClusterMaxEnergyS 4 156 = 24336 = zS²` for `S = 78, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftysix :
    singleClusterMaxEnergyS 4 156 = (24336 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-78 6-vertex (hexamer) ground-state energy** (γ-5 step 1234):
`singleClusterGSEnergyS 5 156 = -30498 = -S(1+zS)` for `S = 78, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftysix :
    singleClusterGSEnergyS 5 156 = (-30498 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-78 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1234):
`singleClusterMaxEnergyS 5 156 = 30420 = zS²` for `S = 78, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftysix :
    singleClusterMaxEnergyS 5 156 = (30420 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-78 7-vertex (heptamer) ground-state energy** (γ-5 step 1235):
`singleClusterGSEnergyS 6 156 = -36582 = -S(1+zS)` for `S = 78, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftysix :
    singleClusterGSEnergyS 6 156 = (-36582 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-78 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1235):
`singleClusterMaxEnergyS 6 156 = 36504 = zS²` for `S = 78, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftysix :
    singleClusterMaxEnergyS 6 156 = (36504 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-157/2 2-vertex (dimer) ground-state energy** (γ-5 step 1236):
`singleClusterGSEnergyS 1 157 = -24963/4 = -S(S+1)` for `S = 157/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftyseven :
    singleClusterGSEnergyS 1 157 = (-24963 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-157/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1236):
`singleClusterMaxEnergyS 1 157 = 24649/4 = S²` for `S = 157/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftyseven :
    singleClusterMaxEnergyS 1 157 = (24649 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-157/2 3-vertex (trimer) ground-state energy** (γ-5 step 1237):
`singleClusterGSEnergyS 2 157 = -12403 = -S(1+zS)` for `S = 157/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftyseven :
    singleClusterGSEnergyS 2 157 = (-12403 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-157/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1237):
`singleClusterMaxEnergyS 2 157 = 24649/2 = zS²` for `S = 157/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftyseven :
    singleClusterMaxEnergyS 2 157 = (24649 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-157/2 4-vertex (quartet) ground-state energy** (γ-5 step 1238):
`singleClusterGSEnergyS 3 157 = -74261/4 = -S(1+zS)` for `S = 157/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftyseven :
    singleClusterGSEnergyS 3 157 = (-74261 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-157/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1238):
`singleClusterMaxEnergyS 3 157 = 73947/4 = zS²` for `S = 157/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftyseven :
    singleClusterMaxEnergyS 3 157 = (73947 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-157/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1239):
`singleClusterGSEnergyS 4 157 = -49455/2 = -S(1+zS)` for `S = 157/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftyseven :
    singleClusterGSEnergyS 4 157 = (-49455 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-157/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1239):
`singleClusterMaxEnergyS 4 157 = 24649 = zS²` for `S = 157/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftyseven :
    singleClusterMaxEnergyS 4 157 = (24649 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-157/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1240):
`singleClusterGSEnergyS 5 157 = -123559/4 = -S(1+zS)` for `S = 157/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftyseven :
    singleClusterGSEnergyS 5 157 = (-123559 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-157/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1240):
`singleClusterMaxEnergyS 5 157 = 123245/4 = zS²` for `S = 157/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftyseven :
    singleClusterMaxEnergyS 5 157 = (123245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-157/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1241):
`singleClusterGSEnergyS 6 157 = -37052 = -S(1+zS)` for `S = 157/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftyseven :
    singleClusterGSEnergyS 6 157 = (-37052 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-157/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1241):
`singleClusterMaxEnergyS 6 157 = 73947/2 = zS²` for `S = 157/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftyseven :
    singleClusterMaxEnergyS 6 157 = (73947 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79 2-vertex (dimer) ground-state energy** (γ-5 step 1242):
`singleClusterGSEnergyS 1 158 = -6320 = -S(S+1)` for `S = 79`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftyeight :
    singleClusterGSEnergyS 1 158 = (-6320 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1242):
`singleClusterMaxEnergyS 1 158 = 6241 = S²` for `S = 79`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftyeight :
    singleClusterMaxEnergyS 1 158 = (6241 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79 3-vertex (trimer) ground-state energy** (γ-5 step 1243):
`singleClusterGSEnergyS 2 158 = -12561 = -S(1+zS)` for `S = 79, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftyeight :
    singleClusterGSEnergyS 2 158 = (-12561 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1243):
`singleClusterMaxEnergyS 2 158 = 12482 = zS²` for `S = 79, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftyeight :
    singleClusterMaxEnergyS 2 158 = (12482 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79 4-vertex (quartet) ground-state energy** (γ-5 step 1244):
`singleClusterGSEnergyS 3 158 = -18802 = -S(1+zS)` for `S = 79, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftyeight :
    singleClusterGSEnergyS 3 158 = (-18802 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1244):
`singleClusterMaxEnergyS 3 158 = 18723 = zS²` for `S = 79, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftyeight :
    singleClusterMaxEnergyS 3 158 = (18723 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79 5-vertex (pentamer) ground-state energy** (γ-5 step 1245):
`singleClusterGSEnergyS 4 158 = -25043 = -S(1+zS)` for `S = 79, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftyeight :
    singleClusterGSEnergyS 4 158 = (-25043 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1245):
`singleClusterMaxEnergyS 4 158 = 24964 = zS²` for `S = 79, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftyeight :
    singleClusterMaxEnergyS 4 158 = (24964 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79 6-vertex (hexamer) ground-state energy** (γ-5 step 1246):
`singleClusterGSEnergyS 5 158 = -31284 = -S(1+zS)` for `S = 79, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftyeight :
    singleClusterGSEnergyS 5 158 = (-31284 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1246):
`singleClusterMaxEnergyS 5 158 = 31205 = zS²` for `S = 79, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftyeight :
    singleClusterMaxEnergyS 5 158 = (31205 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-79 7-vertex (heptamer) ground-state energy** (γ-5 step 1247):
`singleClusterGSEnergyS 6 158 = -37525 = -S(1+zS)` for `S = 79, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftyeight :
    singleClusterGSEnergyS 6 158 = (-37525 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-79 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1247):
`singleClusterMaxEnergyS 6 158 = 37446 = zS²` for `S = 79, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftyeight :
    singleClusterMaxEnergyS 6 158 = (37446 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-159/2 2-vertex (dimer) ground-state energy** (γ-5 step 1248):
`singleClusterGSEnergyS 1 159 = -25599/4 = -S(S+1)` for `S = 159/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfiftynine :
    singleClusterGSEnergyS 1 159 = (-25599 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-159/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1248):
`singleClusterMaxEnergyS 1 159 = 25281/4 = S²` for `S = 159/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfiftynine :
    singleClusterMaxEnergyS 1 159 = (25281 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-159/2 3-vertex (trimer) ground-state energy** (γ-5 step 1249):
`singleClusterGSEnergyS 2 159 = -12720 = -S(1+zS)` for `S = 159/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfiftynine :
    singleClusterGSEnergyS 2 159 = (-12720 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-159/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1249):
`singleClusterMaxEnergyS 2 159 = 25281/2 = zS²` for `S = 159/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfiftynine :
    singleClusterMaxEnergyS 2 159 = (25281 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-159/2 4-vertex (quartet) ground-state energy** (γ-5 step 1250):
`singleClusterGSEnergyS 3 159 = -76161/4 = -S(1+zS)` for `S = 159/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfiftynine :
    singleClusterGSEnergyS 3 159 = (-76161 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-159/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1250):
`singleClusterMaxEnergyS 3 159 = 75843/4 = zS²` for `S = 159/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfiftynine :
    singleClusterMaxEnergyS 3 159 = (75843 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-159/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1251):
`singleClusterGSEnergyS 4 159 = -50721/2 = -S(1+zS)` for `S = 159/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfiftynine :
    singleClusterGSEnergyS 4 159 = (-50721 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-159/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1251):
`singleClusterMaxEnergyS 4 159 = 25281 = zS²` for `S = 159/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfiftynine :
    singleClusterMaxEnergyS 4 159 = (25281 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-159/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1252):
`singleClusterGSEnergyS 5 159 = -126723/4 = -S(1+zS)` for `S = 159/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfiftynine :
    singleClusterGSEnergyS 5 159 = (-126723 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-159/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1252):
`singleClusterMaxEnergyS 5 159 = 126405/4 = zS²` for `S = 159/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfiftynine :
    singleClusterMaxEnergyS 5 159 = (126405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-159/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1253):
`singleClusterGSEnergyS 6 159 = -38001 = -S(1+zS)` for `S = 159/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfiftynine :
    singleClusterGSEnergyS 6 159 = (-38001 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-159/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1253):
`singleClusterMaxEnergyS 6 159 = 75843/2 = zS²` for `S = 159/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfiftynine :
    singleClusterMaxEnergyS 6 159 = (75843 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-80 2-vertex (dimer) ground-state energy** (γ-5 step 1254):
`singleClusterGSEnergyS 1 160 = -6480 = -S(S+1)` for `S = 80`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixty :
    singleClusterGSEnergyS 1 160 = (-6480 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-80 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1254):
`singleClusterMaxEnergyS 1 160 = 6400 = S²` for `S = 80`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixty :
    singleClusterMaxEnergyS 1 160 = (6400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-80 3-vertex (trimer) ground-state energy** (γ-5 step 1255):
`singleClusterGSEnergyS 2 160 = -12880 = -S(1+zS)` for `S = 80, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixty :
    singleClusterGSEnergyS 2 160 = (-12880 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-80 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1255):
`singleClusterMaxEnergyS 2 160 = 12800 = zS²` for `S = 80, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixty :
    singleClusterMaxEnergyS 2 160 = (12800 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-80 4-vertex (quartet) ground-state energy** (γ-5 step 1256):
`singleClusterGSEnergyS 3 160 = -19280 = -S(1+zS)` for `S = 80, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixty :
    singleClusterGSEnergyS 3 160 = (-19280 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-80 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1256):
`singleClusterMaxEnergyS 3 160 = 19200 = zS²` for `S = 80, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixty :
    singleClusterMaxEnergyS 3 160 = (19200 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-80 5-vertex (pentamer) ground-state energy** (γ-5 step 1257):
`singleClusterGSEnergyS 4 160 = -25680 = -S(1+zS)` for `S = 80, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixty :
    singleClusterGSEnergyS 4 160 = (-25680 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-80 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1257):
`singleClusterMaxEnergyS 4 160 = 25600 = zS²` for `S = 80, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixty :
    singleClusterMaxEnergyS 4 160 = (25600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-80 6-vertex (hexamer) ground-state energy** (γ-5 step 1258):
`singleClusterGSEnergyS 5 160 = -32080 = -S(1+zS)` for `S = 80, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixty :
    singleClusterGSEnergyS 5 160 = (-32080 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-80 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1258):
`singleClusterMaxEnergyS 5 160 = 32000 = zS²` for `S = 80, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixty :
    singleClusterMaxEnergyS 5 160 = (32000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-80 7-vertex (heptamer) ground-state energy** (γ-5 step 1259):
`singleClusterGSEnergyS 6 160 = -38480 = -S(1+zS)` for `S = 80, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixty :
    singleClusterGSEnergyS 6 160 = (-38480 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-80 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1259):
`singleClusterMaxEnergyS 6 160 = 38400 = zS²` for `S = 80, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixty :
    singleClusterMaxEnergyS 6 160 = (38400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-161/2 2-vertex (dimer) ground-state energy** (γ-5 step 1260):
`singleClusterGSEnergyS 1 161 = -26243/4 = -S(S+1)` for `S = 161/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtyone :
    singleClusterGSEnergyS 1 161 = (-26243 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-161/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1260):
`singleClusterMaxEnergyS 1 161 = 25921/4 = S²` for `S = 161/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtyone :
    singleClusterMaxEnergyS 1 161 = (25921 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-161/2 3-vertex (trimer) ground-state energy** (γ-5 step 1261):
`singleClusterGSEnergyS 2 161 = -13041 = -S(1+zS)` for `S = 161/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtyone :
    singleClusterGSEnergyS 2 161 = (-13041 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-161/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1261):
`singleClusterMaxEnergyS 2 161 = 25921/2 = zS²` for `S = 161/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtyone :
    singleClusterMaxEnergyS 2 161 = (25921 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-161/2 4-vertex (quartet) ground-state energy** (γ-5 step 1262):
`singleClusterGSEnergyS 3 161 = -78085/4 = -S(1+zS)` for `S = 161/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtyone :
    singleClusterGSEnergyS 3 161 = (-78085 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-161/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1262):
`singleClusterMaxEnergyS 3 161 = 77763/4 = zS²` for `S = 161/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtyone :
    singleClusterMaxEnergyS 3 161 = (77763 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-161/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1263):
`singleClusterGSEnergyS 4 161 = -52003/2 = -S(1+zS)` for `S = 161/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtyone :
    singleClusterGSEnergyS 4 161 = (-52003 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-161/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1263):
`singleClusterMaxEnergyS 4 161 = 25921 = zS²` for `S = 161/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtyone :
    singleClusterMaxEnergyS 4 161 = (25921 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-161/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1264):
`singleClusterGSEnergyS 5 161 = -129927/4 = -S(1+zS)` for `S = 161/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtyone :
    singleClusterGSEnergyS 5 161 = (-129927 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-161/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1264):
`singleClusterMaxEnergyS 5 161 = 129605/4 = zS²` for `S = 161/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtyone :
    singleClusterMaxEnergyS 5 161 = (129605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-161/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1265):
`singleClusterGSEnergyS 6 161 = -38962 = -S(1+zS)` for `S = 161/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtyone :
    singleClusterGSEnergyS 6 161 = (-38962 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-161/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1265):
`singleClusterMaxEnergyS 6 161 = 77763/2 = zS²` for `S = 161/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtyone :
    singleClusterMaxEnergyS 6 161 = (77763 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81 2-vertex (dimer) ground-state energy** (γ-5 step 1266):
`singleClusterGSEnergyS 1 162 = -6642 = -S(S+1)` for `S = 81`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtytwo :
    singleClusterGSEnergyS 1 162 = (-6642 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1266):
`singleClusterMaxEnergyS 1 162 = 6561 = S²` for `S = 81`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtytwo :
    singleClusterMaxEnergyS 1 162 = (6561 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81 3-vertex (trimer) ground-state energy** (γ-5 step 1267):
`singleClusterGSEnergyS 2 162 = -13203 = -S(1+zS)` for `S = 81, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtytwo :
    singleClusterGSEnergyS 2 162 = (-13203 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1267):
`singleClusterMaxEnergyS 2 162 = 13122 = zS²` for `S = 81, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtytwo :
    singleClusterMaxEnergyS 2 162 = (13122 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81 4-vertex (quartet) ground-state energy** (γ-5 step 1268):
`singleClusterGSEnergyS 3 162 = -19764 = -S(1+zS)` for `S = 81, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtytwo :
    singleClusterGSEnergyS 3 162 = (-19764 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1268):
`singleClusterMaxEnergyS 3 162 = 19683 = zS²` for `S = 81, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtytwo :
    singleClusterMaxEnergyS 3 162 = (19683 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81 5-vertex (pentamer) ground-state energy** (γ-5 step 1269):
`singleClusterGSEnergyS 4 162 = -26325 = -S(1+zS)` for `S = 81, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtytwo :
    singleClusterGSEnergyS 4 162 = (-26325 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1269):
`singleClusterMaxEnergyS 4 162 = 26244 = zS²` for `S = 81, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtytwo :
    singleClusterMaxEnergyS 4 162 = (26244 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81 6-vertex (hexamer) ground-state energy** (γ-5 step 1270):
`singleClusterGSEnergyS 5 162 = -32886 = -S(1+zS)` for `S = 81, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtytwo :
    singleClusterGSEnergyS 5 162 = (-32886 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1270):
`singleClusterMaxEnergyS 5 162 = 32805 = zS²` for `S = 81, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtytwo :
    singleClusterMaxEnergyS 5 162 = (32805 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-81 7-vertex (heptamer) ground-state energy** (γ-5 step 1271):
`singleClusterGSEnergyS 6 162 = -39447 = -S(1+zS)` for `S = 81, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtytwo :
    singleClusterGSEnergyS 6 162 = (-39447 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-81 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1271):
`singleClusterMaxEnergyS 6 162 = 39366 = zS²` for `S = 81, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtytwo :
    singleClusterMaxEnergyS 6 162 = (39366 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-163/2 2-vertex (dimer) ground-state energy** (γ-5 step 1272):
`singleClusterGSEnergyS 1 163 = -26895/4 = -S(S+1)` for `S = 163/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtythree :
    singleClusterGSEnergyS 1 163 = (-26895 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-163/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1272):
`singleClusterMaxEnergyS 1 163 = 26569/4 = S²` for `S = 163/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtythree :
    singleClusterMaxEnergyS 1 163 = (26569 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-163/2 3-vertex (trimer) ground-state energy** (γ-5 step 1273):
`singleClusterGSEnergyS 2 163 = -13366 = -S(1+zS)` for `S = 163/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtythree :
    singleClusterGSEnergyS 2 163 = (-13366 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-163/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1273):
`singleClusterMaxEnergyS 2 163 = 26569/2 = zS²` for `S = 163/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtythree :
    singleClusterMaxEnergyS 2 163 = (26569 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-163/2 4-vertex (quartet) ground-state energy** (γ-5 step 1274):
`singleClusterGSEnergyS 3 163 = -80033/4 = -S(1+zS)` for `S = 163/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtythree :
    singleClusterGSEnergyS 3 163 = (-80033 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-163/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1274):
`singleClusterMaxEnergyS 3 163 = 79707/4 = zS²` for `S = 163/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtythree :
    singleClusterMaxEnergyS 3 163 = (79707 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-163/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1275):
`singleClusterGSEnergyS 4 163 = -53301/2 = -S(1+zS)` for `S = 163/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtythree :
    singleClusterGSEnergyS 4 163 = (-53301 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-163/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1275):
`singleClusterMaxEnergyS 4 163 = 26569 = zS²` for `S = 163/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtythree :
    singleClusterMaxEnergyS 4 163 = (26569 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-163/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1276):
`singleClusterGSEnergyS 5 163 = -133171/4 = -S(1+zS)` for `S = 163/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtythree :
    singleClusterGSEnergyS 5 163 = (-133171 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-163/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1276):
`singleClusterMaxEnergyS 5 163 = 132845/4 = zS²` for `S = 163/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtythree :
    singleClusterMaxEnergyS 5 163 = (132845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-163/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1277):
`singleClusterGSEnergyS 6 163 = -39935 = -S(1+zS)` for `S = 163/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtythree :
    singleClusterGSEnergyS 6 163 = (-39935 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-163/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1277):
`singleClusterMaxEnergyS 6 163 = 79707/2 = zS²` for `S = 163/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtythree :
    singleClusterMaxEnergyS 6 163 = (79707 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-82 2-vertex (dimer) ground-state energy** (γ-5 step 1278):
`singleClusterGSEnergyS 1 164 = -6806 = -S(S+1)` for `S = 82`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtyfour :
    singleClusterGSEnergyS 1 164 = (-6806 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-82 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1278):
`singleClusterMaxEnergyS 1 164 = 6724 = S²` for `S = 82`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtyfour :
    singleClusterMaxEnergyS 1 164 = (6724 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-82 3-vertex (trimer) ground-state energy** (γ-5 step 1279):
`singleClusterGSEnergyS 2 164 = -13530 = -S(1+zS)` for `S = 82, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtyfour :
    singleClusterGSEnergyS 2 164 = (-13530 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-82 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1279):
`singleClusterMaxEnergyS 2 164 = 13448 = zS²` for `S = 82, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtyfour :
    singleClusterMaxEnergyS 2 164 = (13448 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-82 4-vertex (quartet) ground-state energy** (γ-5 step 1280):
`singleClusterGSEnergyS 3 164 = -20254 = -S(1+zS)` for `S = 82, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtyfour :
    singleClusterGSEnergyS 3 164 = (-20254 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-82 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1280):
`singleClusterMaxEnergyS 3 164 = 20172 = zS²` for `S = 82, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtyfour :
    singleClusterMaxEnergyS 3 164 = (20172 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-82 5-vertex (pentamer) ground-state energy** (γ-5 step 1281):
`singleClusterGSEnergyS 4 164 = -26978 = -S(1+zS)` for `S = 82, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtyfour :
    singleClusterGSEnergyS 4 164 = (-26978 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-82 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1281):
`singleClusterMaxEnergyS 4 164 = 26896 = zS²` for `S = 82, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtyfour :
    singleClusterMaxEnergyS 4 164 = (26896 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-82 6-vertex (hexamer) ground-state energy** (γ-5 step 1282):
`singleClusterGSEnergyS 5 164 = -33702 = -S(1+zS)` for `S = 82, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtyfour :
    singleClusterGSEnergyS 5 164 = (-33702 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-82 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1282):
`singleClusterMaxEnergyS 5 164 = 33620 = zS²` for `S = 82, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtyfour :
    singleClusterMaxEnergyS 5 164 = (33620 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-82 7-vertex (heptamer) ground-state energy** (γ-5 step 1283):
`singleClusterGSEnergyS 6 164 = -40426 = -S(1+zS)` for `S = 82, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtyfour :
    singleClusterGSEnergyS 6 164 = (-40426 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-82 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1283):
`singleClusterMaxEnergyS 6 164 = 40344 = zS²` for `S = 82, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtyfour :
    singleClusterMaxEnergyS 6 164 = (40344 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-165/2 2-vertex (dimer) ground-state energy** (γ-5 step 1284):
`singleClusterGSEnergyS 1 165 = -27555/4 = -S(S+1)` for `S = 165/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtyfive :
    singleClusterGSEnergyS 1 165 = (-27555 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-165/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1284):
`singleClusterMaxEnergyS 1 165 = 27225/4 = S²` for `S = 165/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtyfive :
    singleClusterMaxEnergyS 1 165 = (27225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-165/2 3-vertex (trimer) ground-state energy** (γ-5 step 1285):
`singleClusterGSEnergyS 2 165 = -13695 = -S(1+zS)` for `S = 165/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtyfive :
    singleClusterGSEnergyS 2 165 = (-13695 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-165/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1285):
`singleClusterMaxEnergyS 2 165 = 27225/2 = zS²` for `S = 165/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtyfive :
    singleClusterMaxEnergyS 2 165 = (27225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-165/2 4-vertex (quartet) ground-state energy** (γ-5 step 1286):
`singleClusterGSEnergyS 3 165 = -82005/4 = -S(1+zS)` for `S = 165/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtyfive :
    singleClusterGSEnergyS 3 165 = (-82005 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-165/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1286):
`singleClusterMaxEnergyS 3 165 = 81675/4 = zS²` for `S = 165/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtyfive :
    singleClusterMaxEnergyS 3 165 = (81675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-165/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1287):
`singleClusterGSEnergyS 4 165 = -54615/2 = -S(1+zS)` for `S = 165/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtyfive :
    singleClusterGSEnergyS 4 165 = (-54615 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-165/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1287):
`singleClusterMaxEnergyS 4 165 = 27225 = zS²` for `S = 165/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtyfive :
    singleClusterMaxEnergyS 4 165 = (27225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-165/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1288):
`singleClusterGSEnergyS 5 165 = -136455/4 = -S(1+zS)` for `S = 165/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtyfive :
    singleClusterGSEnergyS 5 165 = (-136455 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-165/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1288):
`singleClusterMaxEnergyS 5 165 = 136125/4 = zS²` for `S = 165/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtyfive :
    singleClusterMaxEnergyS 5 165 = (136125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-165/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1289):
`singleClusterGSEnergyS 6 165 = -40920 = -S(1+zS)` for `S = 165/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtyfive :
    singleClusterGSEnergyS 6 165 = (-40920 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-165/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1289):
`singleClusterMaxEnergyS 6 165 = 81675/2 = zS²` for `S = 165/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtyfive :
    singleClusterMaxEnergyS 6 165 = (81675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83 2-vertex (dimer) ground-state energy** (γ-5 step 1290):
`singleClusterGSEnergyS 1 166 = -6972 = -S(S+1)` for `S = 83`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtysix :
    singleClusterGSEnergyS 1 166 = (-6972 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1290):
`singleClusterMaxEnergyS 1 166 = 6889 = S²` for `S = 83`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtysix :
    singleClusterMaxEnergyS 1 166 = (6889 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83 3-vertex (trimer) ground-state energy** (γ-5 step 1291):
`singleClusterGSEnergyS 2 166 = -13861 = -S(1+zS)` for `S = 83, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtysix :
    singleClusterGSEnergyS 2 166 = (-13861 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1291):
`singleClusterMaxEnergyS 2 166 = 13778 = zS²` for `S = 83, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtysix :
    singleClusterMaxEnergyS 2 166 = (13778 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83 4-vertex (quartet) ground-state energy** (γ-5 step 1292):
`singleClusterGSEnergyS 3 166 = -20750 = -S(1+zS)` for `S = 83, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtysix :
    singleClusterGSEnergyS 3 166 = (-20750 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1292):
`singleClusterMaxEnergyS 3 166 = 20667 = zS²` for `S = 83, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtysix :
    singleClusterMaxEnergyS 3 166 = (20667 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83 5-vertex (pentamer) ground-state energy** (γ-5 step 1293):
`singleClusterGSEnergyS 4 166 = -27639 = -S(1+zS)` for `S = 83, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtysix :
    singleClusterGSEnergyS 4 166 = (-27639 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1293):
`singleClusterMaxEnergyS 4 166 = 27556 = zS²` for `S = 83, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtysix :
    singleClusterMaxEnergyS 4 166 = (27556 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83 6-vertex (hexamer) ground-state energy** (γ-5 step 1294):
`singleClusterGSEnergyS 5 166 = -34528 = -S(1+zS)` for `S = 83, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtysix :
    singleClusterGSEnergyS 5 166 = (-34528 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1294):
`singleClusterMaxEnergyS 5 166 = 34445 = zS²` for `S = 83, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtysix :
    singleClusterMaxEnergyS 5 166 = (34445 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-83 7-vertex (heptamer) ground-state energy** (γ-5 step 1295):
`singleClusterGSEnergyS 6 166 = -41417 = -S(1+zS)` for `S = 83, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtysix :
    singleClusterGSEnergyS 6 166 = (-41417 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-83 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1295):
`singleClusterMaxEnergyS 6 166 = 41334 = zS²` for `S = 83, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtysix :
    singleClusterMaxEnergyS 6 166 = (41334 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-167/2 2-vertex (dimer) ground-state energy** (γ-5 step 1296):
`singleClusterGSEnergyS 1 167 = -28223/4 = -S(S+1)` for `S = 167/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtyseven :
    singleClusterGSEnergyS 1 167 = (-28223 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-167/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1296):
`singleClusterMaxEnergyS 1 167 = 27889/4 = S²` for `S = 167/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtyseven :
    singleClusterMaxEnergyS 1 167 = (27889 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-167/2 3-vertex (trimer) ground-state energy** (γ-5 step 1297):
`singleClusterGSEnergyS 2 167 = -14028 = -S(1+zS)` for `S = 167/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtyseven :
    singleClusterGSEnergyS 2 167 = (-14028 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-167/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1297):
`singleClusterMaxEnergyS 2 167 = 27889/2 = zS²` for `S = 167/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtyseven :
    singleClusterMaxEnergyS 2 167 = (27889 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-167/2 4-vertex (quartet) ground-state energy** (γ-5 step 1298):
`singleClusterGSEnergyS 3 167 = -84001/4 = -S(1+zS)` for `S = 167/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtyseven :
    singleClusterGSEnergyS 3 167 = (-84001 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-167/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1298):
`singleClusterMaxEnergyS 3 167 = 83667/4 = zS²` for `S = 167/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtyseven :
    singleClusterMaxEnergyS 3 167 = (83667 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-167/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1299):
`singleClusterGSEnergyS 4 167 = -55945/2 = -S(1+zS)` for `S = 167/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtyseven :
    singleClusterGSEnergyS 4 167 = (-55945 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-167/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1299):
`singleClusterMaxEnergyS 4 167 = 27889 = zS²` for `S = 167/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtyseven :
    singleClusterMaxEnergyS 4 167 = (27889 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-167/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1300):
`singleClusterGSEnergyS 5 167 = -139779/4 = -S(1+zS)` for `S = 167/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtyseven :
    singleClusterGSEnergyS 5 167 = (-139779 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-167/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1300):
`singleClusterMaxEnergyS 5 167 = 139445/4 = zS²` for `S = 167/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtyseven :
    singleClusterMaxEnergyS 5 167 = (139445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-167/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1301):
`singleClusterGSEnergyS 6 167 = -41917 = -S(1+zS)` for `S = 167/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtyseven :
    singleClusterGSEnergyS 6 167 = (-41917 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-167/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1301):
`singleClusterMaxEnergyS 6 167 = 83667/2 = zS²` for `S = 167/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtyseven :
    singleClusterMaxEnergyS 6 167 = (83667 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-84 2-vertex (dimer) ground-state energy** (γ-5 step 1302):
`singleClusterGSEnergyS 1 168 = -7140 = -S(S+1)` for `S = 84`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtyeight :
    singleClusterGSEnergyS 1 168 = (-7140 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-84 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1302):
`singleClusterMaxEnergyS 1 168 = 7056 = S²` for `S = 84`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtyeight :
    singleClusterMaxEnergyS 1 168 = (7056 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-84 3-vertex (trimer) ground-state energy** (γ-5 step 1303):
`singleClusterGSEnergyS 2 168 = -14196 = -S(1+zS)` for `S = 84, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtyeight :
    singleClusterGSEnergyS 2 168 = (-14196 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-84 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1303):
`singleClusterMaxEnergyS 2 168 = 14112 = zS²` for `S = 84, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtyeight :
    singleClusterMaxEnergyS 2 168 = (14112 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-84 4-vertex (quartet) ground-state energy** (γ-5 step 1304):
`singleClusterGSEnergyS 3 168 = -21252 = -S(1+zS)` for `S = 84, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtyeight :
    singleClusterGSEnergyS 3 168 = (-21252 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-84 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1304):
`singleClusterMaxEnergyS 3 168 = 21168 = zS²` for `S = 84, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtyeight :
    singleClusterMaxEnergyS 3 168 = (21168 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-84 5-vertex (pentamer) ground-state energy** (γ-5 step 1305):
`singleClusterGSEnergyS 4 168 = -28308 = -S(1+zS)` for `S = 84, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtyeight :
    singleClusterGSEnergyS 4 168 = (-28308 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-84 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1305):
`singleClusterMaxEnergyS 4 168 = 28224 = zS²` for `S = 84, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtyeight :
    singleClusterMaxEnergyS 4 168 = (28224 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-84 6-vertex (hexamer) ground-state energy** (γ-5 step 1306):
`singleClusterGSEnergyS 5 168 = -35364 = -S(1+zS)` for `S = 84, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtyeight :
    singleClusterGSEnergyS 5 168 = (-35364 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-84 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1306):
`singleClusterMaxEnergyS 5 168 = 35280 = zS²` for `S = 84, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtyeight :
    singleClusterMaxEnergyS 5 168 = (35280 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-84 7-vertex (heptamer) ground-state energy** (γ-5 step 1307):
`singleClusterGSEnergyS 6 168 = -42420 = -S(1+zS)` for `S = 84, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtyeight :
    singleClusterGSEnergyS 6 168 = (-42420 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-84 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1307):
`singleClusterMaxEnergyS 6 168 = 42336 = zS²` for `S = 84, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtyeight :
    singleClusterMaxEnergyS 6 168 = (42336 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-169/2 2-vertex (dimer) ground-state energy** (γ-5 step 1308):
`singleClusterGSEnergyS 1 169 = -28899/4 = -S(S+1)` for `S = 169/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredsixtynine :
    singleClusterGSEnergyS 1 169 = (-28899 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-169/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1308):
`singleClusterMaxEnergyS 1 169 = 28561/4 = S²` for `S = 169/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredsixtynine :
    singleClusterMaxEnergyS 1 169 = (28561 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-169/2 3-vertex (trimer) ground-state energy** (γ-5 step 1309):
`singleClusterGSEnergyS 2 169 = -14365 = -S(1+zS)` for `S = 169/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredsixtynine :
    singleClusterGSEnergyS 2 169 = (-14365 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-169/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1309):
`singleClusterMaxEnergyS 2 169 = 28561/2 = zS²` for `S = 169/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredsixtynine :
    singleClusterMaxEnergyS 2 169 = (28561 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-169/2 4-vertex (quartet) ground-state energy** (γ-5 step 1310):
`singleClusterGSEnergyS 3 169 = -86021/4 = -S(1+zS)` for `S = 169/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredsixtynine :
    singleClusterGSEnergyS 3 169 = (-86021 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-169/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1310):
`singleClusterMaxEnergyS 3 169 = 85683/4 = zS²` for `S = 169/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredsixtynine :
    singleClusterMaxEnergyS 3 169 = (85683 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-169/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1311):
`singleClusterGSEnergyS 4 169 = -57291/2 = -S(1+zS)` for `S = 169/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredsixtynine :
    singleClusterGSEnergyS 4 169 = (-57291 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-169/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1311):
`singleClusterMaxEnergyS 4 169 = 28561 = zS²` for `S = 169/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredsixtynine :
    singleClusterMaxEnergyS 4 169 = (28561 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-169/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1312):
`singleClusterGSEnergyS 5 169 = -143143/4 = -S(1+zS)` for `S = 169/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredsixtynine :
    singleClusterGSEnergyS 5 169 = (-143143 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-169/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1312):
`singleClusterMaxEnergyS 5 169 = 142805/4 = zS²` for `S = 169/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredsixtynine :
    singleClusterMaxEnergyS 5 169 = (142805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-169/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1313):
`singleClusterGSEnergyS 6 169 = -42926 = -S(1+zS)` for `S = 169/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredsixtynine :
    singleClusterGSEnergyS 6 169 = (-42926 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-169/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1313):
`singleClusterMaxEnergyS 6 169 = 85683/2 = zS²` for `S = 169/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredsixtynine :
    singleClusterMaxEnergyS 6 169 = (85683 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85 2-vertex (dimer) ground-state energy** (γ-5 step 1314):
`singleClusterGSEnergyS 1 170 = -7310 = -S(S+1)` for `S = 85`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventy :
    singleClusterGSEnergyS 1 170 = (-7310 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1314):
`singleClusterMaxEnergyS 1 170 = 7225 = S²` for `S = 85`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventy :
    singleClusterMaxEnergyS 1 170 = (7225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85 3-vertex (trimer) ground-state energy** (γ-5 step 1315):
`singleClusterGSEnergyS 2 170 = -14535 = -S(1+zS)` for `S = 85, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventy :
    singleClusterGSEnergyS 2 170 = (-14535 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1315):
`singleClusterMaxEnergyS 2 170 = 14450 = zS²` for `S = 85, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventy :
    singleClusterMaxEnergyS 2 170 = (14450 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85 4-vertex (quartet) ground-state energy** (γ-5 step 1316):
`singleClusterGSEnergyS 3 170 = -21760 = -S(1+zS)` for `S = 85, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventy :
    singleClusterGSEnergyS 3 170 = (-21760 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1316):
`singleClusterMaxEnergyS 3 170 = 21675 = zS²` for `S = 85, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventy :
    singleClusterMaxEnergyS 3 170 = (21675 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85 5-vertex (pentamer) ground-state energy** (γ-5 step 1317):
`singleClusterGSEnergyS 4 170 = -28985 = -S(1+zS)` for `S = 85, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventy :
    singleClusterGSEnergyS 4 170 = (-28985 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1317):
`singleClusterMaxEnergyS 4 170 = 28900 = zS²` for `S = 85, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventy :
    singleClusterMaxEnergyS 4 170 = (28900 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85 6-vertex (hexamer) ground-state energy** (γ-5 step 1318):
`singleClusterGSEnergyS 5 170 = -36210 = -S(1+zS)` for `S = 85, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventy :
    singleClusterGSEnergyS 5 170 = (-36210 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1318):
`singleClusterMaxEnergyS 5 170 = 36125 = zS²` for `S = 85, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventy :
    singleClusterMaxEnergyS 5 170 = (36125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-85 7-vertex (heptamer) ground-state energy** (γ-5 step 1319):
`singleClusterGSEnergyS 6 170 = -43435 = -S(1+zS)` for `S = 85, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventy :
    singleClusterGSEnergyS 6 170 = (-43435 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-85 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1319):
`singleClusterMaxEnergyS 6 170 = 43350 = zS²` for `S = 85, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventy :
    singleClusterMaxEnergyS 6 170 = (43350 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-171/2 2-vertex (dimer) ground-state energy** (γ-5 step 1320):
`singleClusterGSEnergyS 1 171 = -29583/4 = -S(S+1)` for `S = 171/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventyone :
    singleClusterGSEnergyS 1 171 = (-29583 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-171/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1320):
`singleClusterMaxEnergyS 1 171 = 29241/4 = S²` for `S = 171/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventyone :
    singleClusterMaxEnergyS 1 171 = (29241 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-171/2 3-vertex (trimer) ground-state energy** (γ-5 step 1321):
`singleClusterGSEnergyS 2 171 = -14706 = -S(zS+1)` for `S = 171/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventyone :
    singleClusterGSEnergyS 2 171 = (-14706 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-171/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1321):
`singleClusterMaxEnergyS 2 171 = 29241/2 = zS²` for `S = 171/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventyone :
    singleClusterMaxEnergyS 2 171 = (29241 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-171/2 4-vertex (quartet) ground-state energy** (γ-5 step 1322):
`singleClusterGSEnergyS 3 171 = -88065/4 = -S(1+zS)` for `S = 171/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventyone :
    singleClusterGSEnergyS 3 171 = (-88065 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-171/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1322):
`singleClusterMaxEnergyS 3 171 = 87723/4 = zS²` for `S = 171/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventyone :
    singleClusterMaxEnergyS 3 171 = (87723 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-171/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1323):
`singleClusterGSEnergyS 4 171 = -58653/2 = -S(1+zS)` for `S = 171/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventyone :
    singleClusterGSEnergyS 4 171 = (-58653 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-171/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1323):
`singleClusterMaxEnergyS 4 171 = 29241 = zS²` for `S = 171/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventyone :
    singleClusterMaxEnergyS 4 171 = (29241 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-171/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1324):
`singleClusterGSEnergyS 5 171 = -146547/4 = -S(1+zS)` for `S = 171/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventyone :
    singleClusterGSEnergyS 5 171 = (-146547 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-171/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1324):
`singleClusterMaxEnergyS 5 171 = 146205/4 = zS²` for `S = 171/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventyone :
    singleClusterMaxEnergyS 5 171 = (146205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-171/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1325):
`singleClusterGSEnergyS 6 171 = -43947 = -S(1+zS)` for `S = 171/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventyone :
    singleClusterGSEnergyS 6 171 = (-43947 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-171/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1325):
`singleClusterMaxEnergyS 6 171 = 87723/2 = zS²` for `S = 171/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventyone :
    singleClusterMaxEnergyS 6 171 = (87723 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-86 2-vertex (dimer) ground-state energy** (γ-5 step 1326):
`singleClusterGSEnergyS 1 172 = -7482 = -S(S+1)` for `S = 86`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventytwo :
    singleClusterGSEnergyS 1 172 = (-7482 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-86 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1326):
`singleClusterMaxEnergyS 1 172 = 7396 = S²` for `S = 86`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventytwo :
    singleClusterMaxEnergyS 1 172 = (7396 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-86 3-vertex (trimer) ground-state energy** (γ-5 step 1327):
`singleClusterGSEnergyS 2 172 = -14878 = -S(1+zS)` for `S = 86, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventytwo :
    singleClusterGSEnergyS 2 172 = (-14878 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-86 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1327):
`singleClusterMaxEnergyS 2 172 = 14792 = zS²` for `S = 86, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventytwo :
    singleClusterMaxEnergyS 2 172 = (14792 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-86 4-vertex (quartet) ground-state energy** (γ-5 step 1328):
`singleClusterGSEnergyS 3 172 = -22274 = -S(1+zS)` for `S = 86, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventytwo :
    singleClusterGSEnergyS 3 172 = (-22274 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-86 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1328):
`singleClusterMaxEnergyS 3 172 = 22188 = zS²` for `S = 86, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventytwo :
    singleClusterMaxEnergyS 3 172 = (22188 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-86 5-vertex (pentamer) ground-state energy** (γ-5 step 1329):
`singleClusterGSEnergyS 4 172 = -29670 = -S(1+zS)` for `S = 86, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventytwo :
    singleClusterGSEnergyS 4 172 = (-29670 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-86 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1329):
`singleClusterMaxEnergyS 4 172 = 29584 = zS²` for `S = 86, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventytwo :
    singleClusterMaxEnergyS 4 172 = (29584 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-86 6-vertex (hexamer) ground-state energy** (γ-5 step 1330):
`singleClusterGSEnergyS 5 172 = -37066 = -S(1+zS)` for `S = 86, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventytwo :
    singleClusterGSEnergyS 5 172 = (-37066 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-86 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1330):
`singleClusterMaxEnergyS 5 172 = 36980 = zS²` for `S = 86, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventytwo :
    singleClusterMaxEnergyS 5 172 = (36980 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-86 7-vertex (heptamer) ground-state energy** (γ-5 step 1331):
`singleClusterGSEnergyS 6 172 = -44462 = -S(1+zS)` for `S = 86, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventytwo :
    singleClusterGSEnergyS 6 172 = (-44462 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-86 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1331):
`singleClusterMaxEnergyS 6 172 = 44376 = zS²` for `S = 86, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventytwo :
    singleClusterMaxEnergyS 6 172 = (44376 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-173/2 2-vertex (dimer) ground-state energy** (γ-5 step 1332):
`singleClusterGSEnergyS 1 173 = -30275/4 = -S(S+1)` for `S = 173/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventythree :
    singleClusterGSEnergyS 1 173 = (-30275 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-173/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1332):
`singleClusterMaxEnergyS 1 173 = 29929/4 = S²` for `S = 173/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventythree :
    singleClusterMaxEnergyS 1 173 = (29929 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-173/2 3-vertex (trimer) ground-state energy** (γ-5 step 1333):
`singleClusterGSEnergyS 2 173 = -15051 = -S(1+zS)` for `S = 173/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventythree :
    singleClusterGSEnergyS 2 173 = (-15051 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-173/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1333):
`singleClusterMaxEnergyS 2 173 = 29929/2 = zS²` for `S = 173/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventythree :
    singleClusterMaxEnergyS 2 173 = (29929 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-173/2 4-vertex (quartet) ground-state energy** (γ-5 step 1334):
`singleClusterGSEnergyS 3 173 = -90133/4 = -S(1+zS)` for `S = 173/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventythree :
    singleClusterGSEnergyS 3 173 = (-90133 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-173/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1334):
`singleClusterMaxEnergyS 3 173 = 89787/4 = zS²` for `S = 173/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventythree :
    singleClusterMaxEnergyS 3 173 = (89787 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-173/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1335):
`singleClusterGSEnergyS 4 173 = -60031/2 = -S(1+zS)` for `S = 173/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventythree :
    singleClusterGSEnergyS 4 173 = (-60031 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-173/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1335):
`singleClusterMaxEnergyS 4 173 = 29929 = zS²` for `S = 173/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventythree :
    singleClusterMaxEnergyS 4 173 = (29929 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-173/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1336):
`singleClusterGSEnergyS 5 173 = -149991/4 = -S(1+zS)` for `S = 173/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventythree :
    singleClusterGSEnergyS 5 173 = (-149991 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-173/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1336):
`singleClusterMaxEnergyS 5 173 = 149645/4 = zS²` for `S = 173/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventythree :
    singleClusterMaxEnergyS 5 173 = (149645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-173/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1337):
`singleClusterGSEnergyS 6 173 = -44980 = -S(1+zS)` for `S = 173/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventythree :
    singleClusterGSEnergyS 6 173 = (-44980 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-173/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1337):
`singleClusterMaxEnergyS 6 173 = 89787/2 = zS²` for `S = 173/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventythree :
    singleClusterMaxEnergyS 6 173 = (89787 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
