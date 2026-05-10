/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Infinite-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 116`
(spin `S = N/2 ≥ 58`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
and the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all eight numerics files can elaborate
in parallel after the main file. The split from `HyperHigh` to
`InfiniteHigh` was introduced as the 50-PR build-performance cadence
refactor #13 when `HyperHigh` reached ~8.9 s user CPU after the
N=99..132 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

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

/-- **Spin-64 3-vertex (trimer) ground-state energy** (γ-5 step 1063):
`singleClusterGSEnergyS 2 128 = -8256 = -S(1+zS)` for `S = 64, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentyeight :
    singleClusterGSEnergyS 2 128 = (-8256 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-64 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1063):
`singleClusterMaxEnergyS 2 128 = 8192 = zS²` for `S = 64, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentyeight :
    singleClusterMaxEnergyS 2 128 = (8192 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-64 4-vertex (quartet) ground-state energy** (γ-5 step 1064):
`singleClusterGSEnergyS 3 128 = -12352 = -S(1+zS)` for `S = 64, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentyeight :
    singleClusterGSEnergyS 3 128 = (-12352 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-64 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1064):
`singleClusterMaxEnergyS 3 128 = 12288 = zS²` for `S = 64, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentyeight :
    singleClusterMaxEnergyS 3 128 = (12288 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-64 5-vertex (pentamer) ground-state energy** (γ-5 step 1065):
`singleClusterGSEnergyS 4 128 = -16448 = -S(1+zS)` for `S = 64, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentyeight :
    singleClusterGSEnergyS 4 128 = (-16448 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-64 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1065):
`singleClusterMaxEnergyS 4 128 = 16384 = zS²` for `S = 64, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentyeight :
    singleClusterMaxEnergyS 4 128 = (16384 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-64 6-vertex (hexamer) ground-state energy** (γ-5 step 1066):
`singleClusterGSEnergyS 5 128 = -20544 = -S(1+zS)` for `S = 64, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentyeight :
    singleClusterGSEnergyS 5 128 = (-20544 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-64 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1066):
`singleClusterMaxEnergyS 5 128 = 20480 = zS²` for `S = 64, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentyeight :
    singleClusterMaxEnergyS 5 128 = (20480 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-64 7-vertex (heptamer) ground-state energy** (γ-5 step 1067):
`singleClusterGSEnergyS 6 128 = -24640 = -S(1+zS)` for `S = 64, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentyeight :
    singleClusterGSEnergyS 6 128 = (-24640 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-64 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1067):
`singleClusterMaxEnergyS 6 128 = 24576 = zS²` for `S = 64, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentyeight :
    singleClusterMaxEnergyS 6 128 = (24576 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-129/2 2-vertex (dimer) ground-state energy** (γ-5 step 1068):
`singleClusterGSEnergyS 1 129 = -16899/4 = -S(S+1)` for `S = 129/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredtwentynine :
    singleClusterGSEnergyS 1 129 = (-16899 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-129/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1068):
`singleClusterMaxEnergyS 1 129 = 16641/4 = S²` for `S = 129/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredtwentynine :
    singleClusterMaxEnergyS 1 129 = (16641 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-129/2 3-vertex (trimer) ground-state energy** (γ-5 step 1069):
`singleClusterGSEnergyS 2 129 = -8385 = -S(1+zS)` for `S = 129/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredtwentynine :
    singleClusterGSEnergyS 2 129 = (-8385 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-129/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1069):
`singleClusterMaxEnergyS 2 129 = 16641/2 = zS²` for `S = 129/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredtwentynine :
    singleClusterMaxEnergyS 2 129 = (16641 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-129/2 4-vertex (quartet) ground-state energy** (γ-5 step 1070):
`singleClusterGSEnergyS 3 129 = -50181/4 = -S(1+zS)` for `S = 129/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredtwentynine :
    singleClusterGSEnergyS 3 129 = (-50181 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-129/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1070):
`singleClusterMaxEnergyS 3 129 = 49923/4 = zS²` for `S = 129/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredtwentynine :
    singleClusterMaxEnergyS 3 129 = (49923 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-129/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1071):
`singleClusterGSEnergyS 4 129 = -33411/2 = -S(1+zS)` for `S = 129/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredtwentynine :
    singleClusterGSEnergyS 4 129 = (-33411 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-129/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1071):
`singleClusterMaxEnergyS 4 129 = 16641 = zS²` for `S = 129/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredtwentynine :
    singleClusterMaxEnergyS 4 129 = (16641 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-129/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1072):
`singleClusterGSEnergyS 5 129 = -83463/4 = -S(1+zS)` for `S = 129/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredtwentynine :
    singleClusterGSEnergyS 5 129 = (-83463 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-129/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1072):
`singleClusterMaxEnergyS 5 129 = 83205/4 = zS²` for `S = 129/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredtwentynine :
    singleClusterMaxEnergyS 5 129 = (83205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-129/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1073):
`singleClusterGSEnergyS 6 129 = -25026 = -S(1+zS)` for `S = 129/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredtwentynine :
    singleClusterGSEnergyS 6 129 = (-25026 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-129/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1073):
`singleClusterMaxEnergyS 6 129 = 49923/2 = zS²` for `S = 129/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredtwentynine :
    singleClusterMaxEnergyS 6 129 = (49923 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65 2-vertex (dimer) ground-state energy** (γ-5 step 1074):
`singleClusterGSEnergyS 1 130 = -4290 = -S(S+1)` for `S = 65`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirty :
    singleClusterGSEnergyS 1 130 = (-4290 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1074):
`singleClusterMaxEnergyS 1 130 = 4225 = S²` for `S = 65`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirty :
    singleClusterMaxEnergyS 1 130 = (4225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65 3-vertex (trimer) ground-state energy** (γ-5 step 1075):
`singleClusterGSEnergyS 2 130 = -8515 = -S(1+zS)` for `S = 65, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirty :
    singleClusterGSEnergyS 2 130 = (-8515 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1075):
`singleClusterMaxEnergyS 2 130 = 8450 = zS²` for `S = 65, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirty :
    singleClusterMaxEnergyS 2 130 = (8450 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65 4-vertex (quartet) ground-state energy** (γ-5 step 1076):
`singleClusterGSEnergyS 3 130 = -12740 = -S(1+zS)` for `S = 65, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirty :
    singleClusterGSEnergyS 3 130 = (-12740 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1076):
`singleClusterMaxEnergyS 3 130 = 12675 = zS²` for `S = 65, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirty :
    singleClusterMaxEnergyS 3 130 = (12675 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65 5-vertex (pentamer) ground-state energy** (γ-5 step 1077):
`singleClusterGSEnergyS 4 130 = -16965 = -S(1+zS)` for `S = 65, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirty :
    singleClusterGSEnergyS 4 130 = (-16965 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1077):
`singleClusterMaxEnergyS 4 130 = 16900 = zS²` for `S = 65, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirty :
    singleClusterMaxEnergyS 4 130 = (16900 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65 6-vertex (hexamer) ground-state energy** (γ-5 step 1078):
`singleClusterGSEnergyS 5 130 = -21190 = -S(1+zS)` for `S = 65, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirty :
    singleClusterGSEnergyS 5 130 = (-21190 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1078):
`singleClusterMaxEnergyS 5 130 = 21125 = zS²` for `S = 65, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirty :
    singleClusterMaxEnergyS 5 130 = (21125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-65 7-vertex (heptamer) ground-state energy** (γ-5 step 1079):
`singleClusterGSEnergyS 6 130 = -25415 = -S(1+zS)` for `S = 65, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirty :
    singleClusterGSEnergyS 6 130 = (-25415 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-65 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1079):
`singleClusterMaxEnergyS 6 130 = 25350 = zS²` for `S = 65, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirty :
    singleClusterMaxEnergyS 6 130 = (25350 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-131/2 2-vertex (dimer) ground-state energy** (γ-5 step 1080):
`singleClusterGSEnergyS 1 131 = -17423/4 = -S(S+1)` for `S = 131/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtyone :
    singleClusterGSEnergyS 1 131 = (-17423 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-131/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1080):
`singleClusterMaxEnergyS 1 131 = 17161/4 = S²` for `S = 131/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtyone :
    singleClusterMaxEnergyS 1 131 = (17161 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-131/2 3-vertex (trimer) ground-state energy** (γ-5 step 1081):
`singleClusterGSEnergyS 2 131 = -8646 = -S(1+zS)` for `S = 131/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtyone :
    singleClusterGSEnergyS 2 131 = (-8646 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-131/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1081):
`singleClusterMaxEnergyS 2 131 = 17161/2 = zS²` for `S = 131/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtyone :
    singleClusterMaxEnergyS 2 131 = (17161 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-131/2 4-vertex (quartet) ground-state energy** (γ-5 step 1082):
`singleClusterGSEnergyS 3 131 = -51745/4 = -S(1+zS)` for `S = 131/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtyone :
    singleClusterGSEnergyS 3 131 = (-51745 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-131/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1082):
`singleClusterMaxEnergyS 3 131 = 51483/4 = zS²` for `S = 131/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtyone :
    singleClusterMaxEnergyS 3 131 = (51483 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-131/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1083):
`singleClusterGSEnergyS 4 131 = -34453/2 = -S(1+zS)` for `S = 131/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtyone :
    singleClusterGSEnergyS 4 131 = (-34453 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-131/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1083):
`singleClusterMaxEnergyS 4 131 = 17161 = zS²` for `S = 131/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtyone :
    singleClusterMaxEnergyS 4 131 = (17161 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-131/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1084):
`singleClusterGSEnergyS 5 131 = -86067/4 = -S(1+zS)` for `S = 131/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtyone :
    singleClusterGSEnergyS 5 131 = (-86067 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-131/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1084):
`singleClusterMaxEnergyS 5 131 = 85805/4 = zS²` for `S = 131/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtyone :
    singleClusterMaxEnergyS 5 131 = (85805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-131/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1085):
`singleClusterGSEnergyS 6 131 = -25807 = -S(1+zS)` for `S = 131/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtyone :
    singleClusterGSEnergyS 6 131 = (-25807 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-131/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1085):
`singleClusterMaxEnergyS 6 131 = 51483/2 = zS²` for `S = 131/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtyone :
    singleClusterMaxEnergyS 6 131 = (51483 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-66 2-vertex (dimer) ground-state energy** (γ-5 step 1086):
`singleClusterGSEnergyS 1 132 = -4422 = -S(S+1)` for `S = 66`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtytwo :
    singleClusterGSEnergyS 1 132 = (-4422 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-66 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1086):
`singleClusterMaxEnergyS 1 132 = 4356 = S²` for `S = 66`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtytwo :
    singleClusterMaxEnergyS 1 132 = (4356 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-66 3-vertex (trimer) ground-state energy** (γ-5 step 1087):
`singleClusterGSEnergyS 2 132 = -8778 = -S(1+zS)` for `S = 66, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtytwo :
    singleClusterGSEnergyS 2 132 = (-8778 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-66 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1087):
`singleClusterMaxEnergyS 2 132 = 8712 = zS²` for `S = 66, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtytwo :
    singleClusterMaxEnergyS 2 132 = (8712 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-66 4-vertex (quartet) ground-state energy** (γ-5 step 1088):
`singleClusterGSEnergyS 3 132 = -13134 = -S(1+zS)` for `S = 66, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtytwo :
    singleClusterGSEnergyS 3 132 = (-13134 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-66 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1088):
`singleClusterMaxEnergyS 3 132 = 13068 = zS²` for `S = 66, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtytwo :
    singleClusterMaxEnergyS 3 132 = (13068 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-66 5-vertex (pentamer) ground-state energy** (γ-5 step 1089):
`singleClusterGSEnergyS 4 132 = -17490 = -S(1+zS)` for `S = 66, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtytwo :
    singleClusterGSEnergyS 4 132 = (-17490 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-66 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1089):
`singleClusterMaxEnergyS 4 132 = 17424 = zS²` for `S = 66, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtytwo :
    singleClusterMaxEnergyS 4 132 = (17424 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-66 6-vertex (hexamer) ground-state energy** (γ-5 step 1090):
`singleClusterGSEnergyS 5 132 = -21846 = -S(1+zS)` for `S = 66, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtytwo :
    singleClusterGSEnergyS 5 132 = (-21846 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-66 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1090):
`singleClusterMaxEnergyS 5 132 = 21780 = zS²` for `S = 66, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtytwo :
    singleClusterMaxEnergyS 5 132 = (21780 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-66 7-vertex (heptamer) ground-state energy** (γ-5 step 1091):
`singleClusterGSEnergyS 6 132 = -26202 = -S(1+zS)` for `S = 66, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtytwo :
    singleClusterGSEnergyS 6 132 = (-26202 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-66 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1091):
`singleClusterMaxEnergyS 6 132 = 26136 = zS²` for `S = 66, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtytwo :
    singleClusterMaxEnergyS 6 132 = (26136 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-133/2 2-vertex (dimer) ground-state energy** (γ-5 step 1092):
`singleClusterGSEnergyS 1 133 = -17955/4 = -S(S+1)` for `S = 133/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtythree :
    singleClusterGSEnergyS 1 133 = (-17955 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-133/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1092):
`singleClusterMaxEnergyS 1 133 = 17689/4 = S²` for `S = 133/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtythree :
    singleClusterMaxEnergyS 1 133 = (17689 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-133/2 3-vertex (trimer) ground-state energy** (γ-5 step 1093):
`singleClusterGSEnergyS 2 133 = -8911 = -S(1+zS)` for `S = 133/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtythree :
    singleClusterGSEnergyS 2 133 = (-8911 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-133/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1093):
`singleClusterMaxEnergyS 2 133 = 17689/2 = zS²` for `S = 133/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtythree :
    singleClusterMaxEnergyS 2 133 = (17689 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-133/2 4-vertex (quartet) ground-state energy** (γ-5 step 1094):
`singleClusterGSEnergyS 3 133 = -53333/4 = -S(1+zS)` for `S = 133/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtythree :
    singleClusterGSEnergyS 3 133 = (-53333 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-133/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1094):
`singleClusterMaxEnergyS 3 133 = 53067/4 = zS²` for `S = 133/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtythree :
    singleClusterMaxEnergyS 3 133 = (53067 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-133/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1095):
`singleClusterGSEnergyS 4 133 = -35511/2 = -S(1+zS)` for `S = 133/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtythree :
    singleClusterGSEnergyS 4 133 = (-35511 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-133/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1095):
`singleClusterMaxEnergyS 4 133 = 17689 = zS²` for `S = 133/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtythree :
    singleClusterMaxEnergyS 4 133 = (17689 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-133/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1096):
`singleClusterGSEnergyS 5 133 = -88711/4 = -S(1+zS)` for `S = 133/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtythree :
    singleClusterGSEnergyS 5 133 = (-88711 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-133/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1096):
`singleClusterMaxEnergyS 5 133 = 88445/4 = zS²` for `S = 133/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtythree :
    singleClusterMaxEnergyS 5 133 = (88445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-133/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1097):
`singleClusterGSEnergyS 6 133 = -26600 = -S(1+zS)` for `S = 133/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtythree :
    singleClusterGSEnergyS 6 133 = (-26600 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-133/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1097):
`singleClusterMaxEnergyS 6 133 = 53067/2 = zS²` for `S = 133/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtythree :
    singleClusterMaxEnergyS 6 133 = (53067 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67 2-vertex (dimer) ground-state energy** (γ-5 step 1098):
`singleClusterGSEnergyS 1 134 = -4556 = -S(S+1)` for `S = 67`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtyfour :
    singleClusterGSEnergyS 1 134 = (-4556 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1098):
`singleClusterMaxEnergyS 1 134 = 4489 = S²` for `S = 67`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtyfour :
    singleClusterMaxEnergyS 1 134 = (4489 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67 3-vertex (trimer) ground-state energy** (γ-5 step 1099):
`singleClusterGSEnergyS 2 134 = -9045 = -S(1+zS)` for `S = 67, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtyfour :
    singleClusterGSEnergyS 2 134 = (-9045 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1099):
`singleClusterMaxEnergyS 2 134 = 8978 = zS²` for `S = 67, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtyfour :
    singleClusterMaxEnergyS 2 134 = (8978 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67 4-vertex (quartet) ground-state energy** (γ-5 step 1100):
`singleClusterGSEnergyS 3 134 = -13534 = -S(1+zS)` for `S = 67, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtyfour :
    singleClusterGSEnergyS 3 134 = (-13534 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1100):
`singleClusterMaxEnergyS 3 134 = 13467 = zS²` for `S = 67, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtyfour :
    singleClusterMaxEnergyS 3 134 = (13467 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67 5-vertex (pentamer) ground-state energy** (γ-5 step 1101):
`singleClusterGSEnergyS 4 134 = -18023 = -S(1+zS)` for `S = 67, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtyfour :
    singleClusterGSEnergyS 4 134 = (-18023 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1101):
`singleClusterMaxEnergyS 4 134 = 17956 = zS²` for `S = 67, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtyfour :
    singleClusterMaxEnergyS 4 134 = (17956 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67 6-vertex (hexamer) ground-state energy** (γ-5 step 1102):
`singleClusterGSEnergyS 5 134 = -22512 = -S(1+zS)` for `S = 67, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtyfour :
    singleClusterGSEnergyS 5 134 = (-22512 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1102):
`singleClusterMaxEnergyS 5 134 = 22445 = zS²` for `S = 67, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtyfour :
    singleClusterMaxEnergyS 5 134 = (22445 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-67 7-vertex (heptamer) ground-state energy** (γ-5 step 1103):
`singleClusterGSEnergyS 6 134 = -27001 = -S(1+zS)` for `S = 67, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtyfour :
    singleClusterGSEnergyS 6 134 = (-27001 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-67 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1103):
`singleClusterMaxEnergyS 6 134 = 26934 = zS²` for `S = 67, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtyfour :
    singleClusterMaxEnergyS 6 134 = (26934 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-135/2 2-vertex (dimer) ground-state energy** (γ-5 step 1104):
`singleClusterGSEnergyS 1 135 = -18495/4 = -S(S+1)` for `S = 135/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtyfive :
    singleClusterGSEnergyS 1 135 = (-18495 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-135/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1104):
`singleClusterMaxEnergyS 1 135 = 18225/4 = S²` for `S = 135/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtyfive :
    singleClusterMaxEnergyS 1 135 = (18225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-135/2 3-vertex (trimer) ground-state energy** (γ-5 step 1105):
`singleClusterGSEnergyS 2 135 = -9180 = -S(1+zS)` for `S = 135/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtyfive :
    singleClusterGSEnergyS 2 135 = (-9180 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-135/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1105):
`singleClusterMaxEnergyS 2 135 = 18225/2 = zS²` for `S = 135/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtyfive :
    singleClusterMaxEnergyS 2 135 = (18225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-135/2 4-vertex (quartet) ground-state energy** (γ-5 step 1106):
`singleClusterGSEnergyS 3 135 = -54945/4 = -S(1+zS)` for `S = 135/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtyfive :
    singleClusterGSEnergyS 3 135 = (-54945 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-135/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1106):
`singleClusterMaxEnergyS 3 135 = 54675/4 = zS²` for `S = 135/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtyfive :
    singleClusterMaxEnergyS 3 135 = (54675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-135/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1107):
`singleClusterGSEnergyS 4 135 = -36585/2 = -S(1+zS)` for `S = 135/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtyfive :
    singleClusterGSEnergyS 4 135 = (-36585 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-135/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1107):
`singleClusterMaxEnergyS 4 135 = 18225 = zS²` for `S = 135/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtyfive :
    singleClusterMaxEnergyS 4 135 = (18225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-135/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1108):
`singleClusterGSEnergyS 5 135 = -91395/4 = -S(1+zS)` for `S = 135/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtyfive :
    singleClusterGSEnergyS 5 135 = (-91395 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-135/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1108):
`singleClusterMaxEnergyS 5 135 = 91125/4 = zS²` for `S = 135/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtyfive :
    singleClusterMaxEnergyS 5 135 = (91125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-135/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1109):
`singleClusterGSEnergyS 6 135 = -27405 = -S(1+zS)` for `S = 135/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtyfive :
    singleClusterGSEnergyS 6 135 = (-27405 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-135/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1109):
`singleClusterMaxEnergyS 6 135 = 54675/2 = zS²` for `S = 135/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtyfive :
    singleClusterMaxEnergyS 6 135 = (54675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-68 2-vertex (dimer) ground-state energy** (γ-5 step 1110):
`singleClusterGSEnergyS 1 136 = -4692 = -S(S+1)` for `S = 68`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtysix :
    singleClusterGSEnergyS 1 136 = (-4692 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-68 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1110):
`singleClusterMaxEnergyS 1 136 = 4624 = S²` for `S = 68`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtysix :
    singleClusterMaxEnergyS 1 136 = (4624 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-68 3-vertex (trimer) ground-state energy** (γ-5 step 1111):
`singleClusterGSEnergyS 2 136 = -9316 = -S(1+zS)` for `S = 68, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtysix :
    singleClusterGSEnergyS 2 136 = (-9316 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-68 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1111):
`singleClusterMaxEnergyS 2 136 = 9248 = zS²` for `S = 68, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtysix :
    singleClusterMaxEnergyS 2 136 = (9248 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-68 4-vertex (quartet) ground-state energy** (γ-5 step 1112):
`singleClusterGSEnergyS 3 136 = -13940 = -S(1+zS)` for `S = 68, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtysix :
    singleClusterGSEnergyS 3 136 = (-13940 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-68 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1112):
`singleClusterMaxEnergyS 3 136 = 13872 = zS²` for `S = 68, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtysix :
    singleClusterMaxEnergyS 3 136 = (13872 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-68 5-vertex (pentamer) ground-state energy** (γ-5 step 1113):
`singleClusterGSEnergyS 4 136 = -18564 = -S(1+zS)` for `S = 68, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtysix :
    singleClusterGSEnergyS 4 136 = (-18564 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-68 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1113):
`singleClusterMaxEnergyS 4 136 = 18496 = zS²` for `S = 68, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtysix :
    singleClusterMaxEnergyS 4 136 = (18496 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-68 6-vertex (hexamer) ground-state energy** (γ-5 step 1114):
`singleClusterGSEnergyS 5 136 = -23188 = -S(1+zS)` for `S = 68, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtysix :
    singleClusterGSEnergyS 5 136 = (-23188 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-68 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1114):
`singleClusterMaxEnergyS 5 136 = 23120 = zS²` for `S = 68, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtysix :
    singleClusterMaxEnergyS 5 136 = (23120 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-68 7-vertex (heptamer) ground-state energy** (γ-5 step 1115):
`singleClusterGSEnergyS 6 136 = -27812 = -S(1+zS)` for `S = 68, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtysix :
    singleClusterGSEnergyS 6 136 = (-27812 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-68 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1115):
`singleClusterMaxEnergyS 6 136 = 27744 = zS²` for `S = 68, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtysix :
    singleClusterMaxEnergyS 6 136 = (27744 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-137/2 2-vertex (dimer) ground-state energy** (γ-5 step 1116):
`singleClusterGSEnergyS 1 137 = -19043/4 = -S(S+1)` for `S = 137/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtyseven :
    singleClusterGSEnergyS 1 137 = (-19043 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-137/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1116):
`singleClusterMaxEnergyS 1 137 = 18769/4 = S²` for `S = 137/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtyseven :
    singleClusterMaxEnergyS 1 137 = (18769 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-137/2 3-vertex (trimer) ground-state energy** (γ-5 step 1117):
`singleClusterGSEnergyS 2 137 = -9453 = -S(1+zS)` for `S = 137/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtyseven :
    singleClusterGSEnergyS 2 137 = (-9453 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-137/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1117):
`singleClusterMaxEnergyS 2 137 = 18769/2 = zS²` for `S = 137/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtyseven :
    singleClusterMaxEnergyS 2 137 = (18769 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-137/2 4-vertex (quartet) ground-state energy** (γ-5 step 1118):
`singleClusterGSEnergyS 3 137 = -56581/4 = -S(1+zS)` for `S = 137/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtyseven :
    singleClusterGSEnergyS 3 137 = (-56581 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-137/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1118):
`singleClusterMaxEnergyS 3 137 = 56307/4 = zS²` for `S = 137/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtyseven :
    singleClusterMaxEnergyS 3 137 = (56307 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-137/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1119):
`singleClusterGSEnergyS 4 137 = -37675/2 = -S(1+zS)` for `S = 137/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtyseven :
    singleClusterGSEnergyS 4 137 = (-37675 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-137/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1119):
`singleClusterMaxEnergyS 4 137 = 18769 = zS²` for `S = 137/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtyseven :
    singleClusterMaxEnergyS 4 137 = (18769 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-137/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1120):
`singleClusterGSEnergyS 5 137 = -94119/4 = -S(1+zS)` for `S = 137/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtyseven :
    singleClusterGSEnergyS 5 137 = (-94119 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-137/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1120):
`singleClusterMaxEnergyS 5 137 = 93845/4 = zS²` for `S = 137/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtyseven :
    singleClusterMaxEnergyS 5 137 = (93845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
