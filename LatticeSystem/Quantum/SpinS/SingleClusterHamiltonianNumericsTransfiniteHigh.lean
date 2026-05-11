/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Transfinite-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 132`
(spin `S = N/2 ≥ 66`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`,
and the `N = 116..131` in `SingleClusterHamiltonianNumericsInfiniteHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all nine numerics files can elaborate
in parallel after the main file. The split from `InfiniteHigh` to
`TransfiniteHigh` was introduced as the 50-PR build-performance
cadence refactor #15 when `InfiniteHigh` reached ~8.6 s user CPU
after the N=116..148 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).

Refactor #16 (after spin-157/2 trimer at γ-5 step 1237) was an
evaluate-only iteration: `TransfiniteHigh` measured ~7.6 s user CPU
at 2466 lines (N=132..157, 50 γ-5 sweep PRs since refactor #15
PR #2249), still well under the historical ~8.6 s split trigger.
Growth rate ~60 ms / N matches the refactor #15 projection, so the
next split (to a new file taking the high-N tail) will be needed
around N ≈ 170 ± 5.
-/

namespace LatticeSystem.Quantum

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

/-- **Spin-137/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1121):
`singleClusterGSEnergyS 6 137 = -28222 = -S(1+zS)` for `S = 137/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtyseven :
    singleClusterGSEnergyS 6 137 = (-28222 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-137/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1121):
`singleClusterMaxEnergyS 6 137 = 56307/2 = zS²` for `S = 137/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtyseven :
    singleClusterMaxEnergyS 6 137 = (56307 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69 2-vertex (dimer) ground-state energy** (γ-5 step 1122):
`singleClusterGSEnergyS 1 138 = -4830 = -S(S+1)` for `S = 69`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtyeight :
    singleClusterGSEnergyS 1 138 = (-4830 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1122):
`singleClusterMaxEnergyS 1 138 = 4761 = S²` for `S = 69`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtyeight :
    singleClusterMaxEnergyS 1 138 = (4761 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69 3-vertex (trimer) ground-state energy** (γ-5 step 1123):
`singleClusterGSEnergyS 2 138 = -9591 = -S(1+zS)` for `S = 69, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtyeight :
    singleClusterGSEnergyS 2 138 = (-9591 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1123):
`singleClusterMaxEnergyS 2 138 = 9522 = zS²` for `S = 69, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtyeight :
    singleClusterMaxEnergyS 2 138 = (9522 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69 4-vertex (quartet) ground-state energy** (γ-5 step 1124):
`singleClusterGSEnergyS 3 138 = -14352 = -S(1+zS)` for `S = 69, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtyeight :
    singleClusterGSEnergyS 3 138 = (-14352 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1124):
`singleClusterMaxEnergyS 3 138 = 14283 = zS²` for `S = 69, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtyeight :
    singleClusterMaxEnergyS 3 138 = (14283 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69 5-vertex (pentamer) ground-state energy** (γ-5 step 1125):
`singleClusterGSEnergyS 4 138 = -19113 = -S(1+zS)` for `S = 69, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtyeight :
    singleClusterGSEnergyS 4 138 = (-19113 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1125):
`singleClusterMaxEnergyS 4 138 = 19044 = zS²` for `S = 69, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtyeight :
    singleClusterMaxEnergyS 4 138 = (19044 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69 6-vertex (hexamer) ground-state energy** (γ-5 step 1126):
`singleClusterGSEnergyS 5 138 = -23874 = -S(1+zS)` for `S = 69, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtyeight :
    singleClusterGSEnergyS 5 138 = (-23874 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1126):
`singleClusterMaxEnergyS 5 138 = 23805 = zS²` for `S = 69, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtyeight :
    singleClusterMaxEnergyS 5 138 = (23805 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-69 7-vertex (heptamer) ground-state energy** (γ-5 step 1127):
`singleClusterGSEnergyS 6 138 = -28635 = -S(1+zS)` for `S = 69, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtyeight :
    singleClusterGSEnergyS 6 138 = (-28635 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-69 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1127):
`singleClusterMaxEnergyS 6 138 = 28566 = zS²` for `S = 69, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtyeight :
    singleClusterMaxEnergyS 6 138 = (28566 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-139/2 2-vertex (dimer) ground-state energy** (γ-5 step 1128):
`singleClusterGSEnergyS 1 139 = -19599/4 = -S(S+1)` for `S = 139/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredthirtynine :
    singleClusterGSEnergyS 1 139 = (-19599 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-139/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1128):
`singleClusterMaxEnergyS 1 139 = 19321/4 = S²` for `S = 139/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredthirtynine :
    singleClusterMaxEnergyS 1 139 = (19321 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-139/2 3-vertex (trimer) ground-state energy** (γ-5 step 1129):
`singleClusterGSEnergyS 2 139 = -9730 = -S(1+zS)` for `S = 139/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredthirtynine :
    singleClusterGSEnergyS 2 139 = (-9730 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-139/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1129):
`singleClusterMaxEnergyS 2 139 = 19321/2 = zS²` for `S = 139/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredthirtynine :
    singleClusterMaxEnergyS 2 139 = (19321 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-139/2 4-vertex (quartet) ground-state energy** (γ-5 step 1130):
`singleClusterGSEnergyS 3 139 = -58241/4 = -S(1+zS)` for `S = 139/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredthirtynine :
    singleClusterGSEnergyS 3 139 = (-58241 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-139/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1130):
`singleClusterMaxEnergyS 3 139 = 57963/4 = zS²` for `S = 139/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredthirtynine :
    singleClusterMaxEnergyS 3 139 = (57963 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-139/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1131):
`singleClusterGSEnergyS 4 139 = -38781/2 = -S(1+zS)` for `S = 139/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredthirtynine :
    singleClusterGSEnergyS 4 139 = (-38781 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-139/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1131):
`singleClusterMaxEnergyS 4 139 = 19321 = zS²` for `S = 139/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredthirtynine :
    singleClusterMaxEnergyS 4 139 = (19321 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-139/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1132):
`singleClusterGSEnergyS 5 139 = -96883/4 = -S(1+zS)` for `S = 139/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredthirtynine :
    singleClusterGSEnergyS 5 139 = (-96883 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-139/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1132):
`singleClusterMaxEnergyS 5 139 = 96605/4 = zS²` for `S = 139/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredthirtynine :
    singleClusterMaxEnergyS 5 139 = (96605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-139/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1133):
`singleClusterGSEnergyS 6 139 = -29051 = -S(1+zS)` for `S = 139/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredthirtynine :
    singleClusterGSEnergyS 6 139 = (-29051 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-139/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1133):
`singleClusterMaxEnergyS 6 139 = 57963/2 = zS²` for `S = 139/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredthirtynine :
    singleClusterMaxEnergyS 6 139 = (57963 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-70 2-vertex (dimer) ground-state energy** (γ-5 step 1134):
`singleClusterGSEnergyS 1 140 = -4970 = -S(S+1)` for `S = 70`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredforty :
    singleClusterGSEnergyS 1 140 = (-4970 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-70 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1134):
`singleClusterMaxEnergyS 1 140 = 4900 = S²` for `S = 70`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredforty :
    singleClusterMaxEnergyS 1 140 = (4900 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-70 3-vertex (trimer) ground-state energy** (γ-5 step 1135):
`singleClusterGSEnergyS 2 140 = -9870 = -S(1+zS)` for `S = 70, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredforty :
    singleClusterGSEnergyS 2 140 = (-9870 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-70 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1135):
`singleClusterMaxEnergyS 2 140 = 9800 = zS²` for `S = 70, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredforty :
    singleClusterMaxEnergyS 2 140 = (9800 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-70 4-vertex (quartet) ground-state energy** (γ-5 step 1136):
`singleClusterGSEnergyS 3 140 = -14770 = -S(1+zS)` for `S = 70, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredforty :
    singleClusterGSEnergyS 3 140 = (-14770 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-70 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1136):
`singleClusterMaxEnergyS 3 140 = 14700 = zS²` for `S = 70, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredforty :
    singleClusterMaxEnergyS 3 140 = (14700 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-70 5-vertex (pentamer) ground-state energy** (γ-5 step 1137):
`singleClusterGSEnergyS 4 140 = -19670 = -S(1+zS)` for `S = 70, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredforty :
    singleClusterGSEnergyS 4 140 = (-19670 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-70 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1137):
`singleClusterMaxEnergyS 4 140 = 19600 = zS²` for `S = 70, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredforty :
    singleClusterMaxEnergyS 4 140 = (19600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-70 6-vertex (hexamer) ground-state energy** (γ-5 step 1138):
`singleClusterGSEnergyS 5 140 = -24570 = -S(1+zS)` for `S = 70, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredforty :
    singleClusterGSEnergyS 5 140 = (-24570 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-70 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1138):
`singleClusterMaxEnergyS 5 140 = 24500 = zS²` for `S = 70, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredforty :
    singleClusterMaxEnergyS 5 140 = (24500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-70 7-vertex (heptamer) ground-state energy** (γ-5 step 1139):
`singleClusterGSEnergyS 6 140 = -29470 = -S(1+zS)` for `S = 70, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredforty :
    singleClusterGSEnergyS 6 140 = (-29470 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-70 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1139):
`singleClusterMaxEnergyS 6 140 = 29400 = zS²` for `S = 70, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredforty :
    singleClusterMaxEnergyS 6 140 = (29400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-141/2 2-vertex (dimer) ground-state energy** (γ-5 step 1140):
`singleClusterGSEnergyS 1 141 = -20163/4 = -S(S+1)` for `S = 141/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortyone :
    singleClusterGSEnergyS 1 141 = (-20163 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-141/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1140):
`singleClusterMaxEnergyS 1 141 = 19881/4 = S²` for `S = 141/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortyone :
    singleClusterMaxEnergyS 1 141 = (19881 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-141/2 3-vertex (trimer) ground-state energy** (γ-5 step 1141):
`singleClusterGSEnergyS 2 141 = -10011 = -S(1+zS)` for `S = 141/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortyone :
    singleClusterGSEnergyS 2 141 = (-10011 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-141/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1141):
`singleClusterMaxEnergyS 2 141 = 19881/2 = zS²` for `S = 141/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortyone :
    singleClusterMaxEnergyS 2 141 = (19881 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-141/2 4-vertex (quartet) ground-state energy** (γ-5 step 1142):
`singleClusterGSEnergyS 3 141 = -59925/4 = -S(1+zS)` for `S = 141/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortyone :
    singleClusterGSEnergyS 3 141 = (-59925 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-141/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1142):
`singleClusterMaxEnergyS 3 141 = 59643/4 = zS²` for `S = 141/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortyone :
    singleClusterMaxEnergyS 3 141 = (59643 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-141/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1143):
`singleClusterGSEnergyS 4 141 = -39903/2 = -S(1+zS)` for `S = 141/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortyone :
    singleClusterGSEnergyS 4 141 = (-39903 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-141/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1143):
`singleClusterMaxEnergyS 4 141 = 19881 = zS²` for `S = 141/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortyone :
    singleClusterMaxEnergyS 4 141 = (19881 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-141/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1144):
`singleClusterGSEnergyS 5 141 = -99687/4 = -S(1+zS)` for `S = 141/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortyone :
    singleClusterGSEnergyS 5 141 = (-99687 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-141/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1144):
`singleClusterMaxEnergyS 5 141 = 99405/4 = zS²` for `S = 141/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortyone :
    singleClusterMaxEnergyS 5 141 = (99405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-141/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1145):
`singleClusterGSEnergyS 6 141 = -29892 = -S(1+zS)` for `S = 141/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortyone :
    singleClusterGSEnergyS 6 141 = (-29892 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-141/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1145):
`singleClusterMaxEnergyS 6 141 = 59643/2 = zS²` for `S = 141/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortyone :
    singleClusterMaxEnergyS 6 141 = (59643 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71 2-vertex (dimer) ground-state energy** (γ-5 step 1146):
`singleClusterGSEnergyS 1 142 = -5112 = -S(S+1)` for `S = 71`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortytwo :
    singleClusterGSEnergyS 1 142 = (-5112 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1146):
`singleClusterMaxEnergyS 1 142 = 5041 = S²` for `S = 71`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortytwo :
    singleClusterMaxEnergyS 1 142 = (5041 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71 3-vertex (trimer) ground-state energy** (γ-5 step 1147):
`singleClusterGSEnergyS 2 142 = -10153 = -S(1+zS)` for `S = 71, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortytwo :
    singleClusterGSEnergyS 2 142 = (-10153 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1147):
`singleClusterMaxEnergyS 2 142 = 10082 = zS²` for `S = 71, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortytwo :
    singleClusterMaxEnergyS 2 142 = (10082 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71 4-vertex (quartet) ground-state energy** (γ-5 step 1148):
`singleClusterGSEnergyS 3 142 = -15194 = -S(1+zS)` for `S = 71, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortytwo :
    singleClusterGSEnergyS 3 142 = (-15194 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1148):
`singleClusterMaxEnergyS 3 142 = 15123 = zS²` for `S = 71, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortytwo :
    singleClusterMaxEnergyS 3 142 = (15123 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71 5-vertex (pentamer) ground-state energy** (γ-5 step 1149):
`singleClusterGSEnergyS 4 142 = -20235 = -S(1+zS)` for `S = 71, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortytwo :
    singleClusterGSEnergyS 4 142 = (-20235 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1149):
`singleClusterMaxEnergyS 4 142 = 20164 = zS²` for `S = 71, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortytwo :
    singleClusterMaxEnergyS 4 142 = (20164 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71 6-vertex (hexamer) ground-state energy** (γ-5 step 1150):
`singleClusterGSEnergyS 5 142 = -25276 = -S(1+zS)` for `S = 71, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortytwo :
    singleClusterGSEnergyS 5 142 = (-25276 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1150):
`singleClusterMaxEnergyS 5 142 = 25205 = zS²` for `S = 71, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortytwo :
    singleClusterMaxEnergyS 5 142 = (25205 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-71 7-vertex (heptamer) ground-state energy** (γ-5 step 1151):
`singleClusterGSEnergyS 6 142 = -30317 = -S(1+zS)` for `S = 71, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortytwo :
    singleClusterGSEnergyS 6 142 = (-30317 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-71 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1151):
`singleClusterMaxEnergyS 6 142 = 30246 = zS²` for `S = 71, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortytwo :
    singleClusterMaxEnergyS 6 142 = (30246 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-143/2 2-vertex (dimer) ground-state energy** (γ-5 step 1152):
`singleClusterGSEnergyS 1 143 = -20735/4 = -S(S+1)` for `S = 143/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortythree :
    singleClusterGSEnergyS 1 143 = (-20735 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-143/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1152):
`singleClusterMaxEnergyS 1 143 = 20449/4 = S²` for `S = 143/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortythree :
    singleClusterMaxEnergyS 1 143 = (20449 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-143/2 3-vertex (trimer) ground-state energy** (γ-5 step 1153):
`singleClusterGSEnergyS 2 143 = -10296 = -S(1+zS)` for `S = 143/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortythree :
    singleClusterGSEnergyS 2 143 = (-10296 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-143/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1153):
`singleClusterMaxEnergyS 2 143 = 20449/2 = zS²` for `S = 143/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortythree :
    singleClusterMaxEnergyS 2 143 = (20449 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-143/2 4-vertex (quartet) ground-state energy** (γ-5 step 1154):
`singleClusterGSEnergyS 3 143 = -61633/4 = -S(1+zS)` for `S = 143/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortythree :
    singleClusterGSEnergyS 3 143 = (-61633 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-143/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1154):
`singleClusterMaxEnergyS 3 143 = 61347/4 = zS²` for `S = 143/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortythree :
    singleClusterMaxEnergyS 3 143 = (61347 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-143/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1155):
`singleClusterGSEnergyS 4 143 = -41041/2 = -S(1+zS)` for `S = 143/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortythree :
    singleClusterGSEnergyS 4 143 = (-41041 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-143/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1155):
`singleClusterMaxEnergyS 4 143 = 20449 = zS²` for `S = 143/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortythree :
    singleClusterMaxEnergyS 4 143 = (20449 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-143/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1156):
`singleClusterGSEnergyS 5 143 = -102531/4 = -S(1+zS)` for `S = 143/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortythree :
    singleClusterGSEnergyS 5 143 = (-102531 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-143/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1156):
`singleClusterMaxEnergyS 5 143 = 102245/4 = zS²` for `S = 143/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortythree :
    singleClusterMaxEnergyS 5 143 = (102245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-143/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1157):
`singleClusterGSEnergyS 6 143 = -30745 = -S(1+zS)` for `S = 143/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortythree :
    singleClusterGSEnergyS 6 143 = (-30745 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-143/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1157):
`singleClusterMaxEnergyS 6 143 = 61347/2 = zS²` for `S = 143/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortythree :
    singleClusterMaxEnergyS 6 143 = (61347 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-72 2-vertex (dimer) ground-state energy** (γ-5 step 1158):
`singleClusterGSEnergyS 1 144 = -5256 = -S(S+1)` for `S = 72`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortyfour :
    singleClusterGSEnergyS 1 144 = (-5256 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-72 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1158):
`singleClusterMaxEnergyS 1 144 = 5184 = S²` for `S = 72`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortyfour :
    singleClusterMaxEnergyS 1 144 = (5184 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-72 3-vertex (trimer) ground-state energy** (γ-5 step 1159):
`singleClusterGSEnergyS 2 144 = -10440 = -S(1+zS)` for `S = 72, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortyfour :
    singleClusterGSEnergyS 2 144 = (-10440 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-72 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1159):
`singleClusterMaxEnergyS 2 144 = 10368 = zS²` for `S = 72, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortyfour :
    singleClusterMaxEnergyS 2 144 = (10368 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-72 4-vertex (quartet) ground-state energy** (γ-5 step 1160):
`singleClusterGSEnergyS 3 144 = -15624 = -S(1+zS)` for `S = 72, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortyfour :
    singleClusterGSEnergyS 3 144 = (-15624 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-72 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1160):
`singleClusterMaxEnergyS 3 144 = 15552 = zS²` for `S = 72, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortyfour :
    singleClusterMaxEnergyS 3 144 = (15552 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-72 5-vertex (pentamer) ground-state energy** (γ-5 step 1161):
`singleClusterGSEnergyS 4 144 = -20808 = -S(1+zS)` for `S = 72, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortyfour :
    singleClusterGSEnergyS 4 144 = (-20808 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-72 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1161):
`singleClusterMaxEnergyS 4 144 = 20736 = zS²` for `S = 72, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortyfour :
    singleClusterMaxEnergyS 4 144 = (20736 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-72 6-vertex (hexamer) ground-state energy** (γ-5 step 1162):
`singleClusterGSEnergyS 5 144 = -25992 = -S(1+zS)` for `S = 72, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortyfour :
    singleClusterGSEnergyS 5 144 = (-25992 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-72 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1162):
`singleClusterMaxEnergyS 5 144 = 25920 = zS²` for `S = 72, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortyfour :
    singleClusterMaxEnergyS 5 144 = (25920 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-72 7-vertex (heptamer) ground-state energy** (γ-5 step 1163):
`singleClusterGSEnergyS 6 144 = -31176 = -S(1+zS)` for `S = 72, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortyfour :
    singleClusterGSEnergyS 6 144 = (-31176 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-72 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1163):
`singleClusterMaxEnergyS 6 144 = 31104 = zS²` for `S = 72, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortyfour :
    singleClusterMaxEnergyS 6 144 = (31104 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-145/2 2-vertex (dimer) ground-state energy** (γ-5 step 1164):
`singleClusterGSEnergyS 1 145 = -21315/4 = -S(S+1)` for `S = 145/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortyfive :
    singleClusterGSEnergyS 1 145 = (-21315 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-145/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1164):
`singleClusterMaxEnergyS 1 145 = 21025/4 = S²` for `S = 145/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortyfive :
    singleClusterMaxEnergyS 1 145 = (21025 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-145/2 3-vertex (trimer) ground-state energy** (γ-5 step 1165):
`singleClusterGSEnergyS 2 145 = -10585 = -S(1+zS)` for `S = 145/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortyfive :
    singleClusterGSEnergyS 2 145 = (-10585 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-145/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1165):
`singleClusterMaxEnergyS 2 145 = 21025/2 = zS²` for `S = 145/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortyfive :
    singleClusterMaxEnergyS 2 145 = (21025 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-145/2 4-vertex (quartet) ground-state energy** (γ-5 step 1166):
`singleClusterGSEnergyS 3 145 = -63365/4 = -S(1+zS)` for `S = 145/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortyfive :
    singleClusterGSEnergyS 3 145 = (-63365 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-145/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1166):
`singleClusterMaxEnergyS 3 145 = 63075/4 = zS²` for `S = 145/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortyfive :
    singleClusterMaxEnergyS 3 145 = (63075 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-145/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1167):
`singleClusterGSEnergyS 4 145 = -42195/2 = -S(1+zS)` for `S = 145/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortyfive :
    singleClusterGSEnergyS 4 145 = (-42195 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-145/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1167):
`singleClusterMaxEnergyS 4 145 = 21025 = zS²` for `S = 145/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortyfive :
    singleClusterMaxEnergyS 4 145 = (21025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-145/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1168):
`singleClusterGSEnergyS 5 145 = -105415/4 = -S(1+zS)` for `S = 145/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortyfive :
    singleClusterGSEnergyS 5 145 = (-105415 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-145/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1168):
`singleClusterMaxEnergyS 5 145 = 105125/4 = zS²` for `S = 145/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortyfive :
    singleClusterMaxEnergyS 5 145 = (105125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-145/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1169):
`singleClusterGSEnergyS 6 145 = -31610 = -S(1+zS)` for `S = 145/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortyfive :
    singleClusterGSEnergyS 6 145 = (-31610 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-145/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1169):
`singleClusterMaxEnergyS 6 145 = 63075/2 = zS²` for `S = 145/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortyfive :
    singleClusterMaxEnergyS 6 145 = (63075 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73 2-vertex (dimer) ground-state energy** (γ-5 step 1170):
`singleClusterGSEnergyS 1 146 = -5402 = -S(S+1)` for `S = 73`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortysix :
    singleClusterGSEnergyS 1 146 = (-5402 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1170):
`singleClusterMaxEnergyS 1 146 = 5329 = S²` for `S = 73`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortysix :
    singleClusterMaxEnergyS 1 146 = (5329 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73 3-vertex (trimer) ground-state energy** (γ-5 step 1171):
`singleClusterGSEnergyS 2 146 = -10731 = -S(1+zS)` for `S = 73, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortysix :
    singleClusterGSEnergyS 2 146 = (-10731 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1171):
`singleClusterMaxEnergyS 2 146 = 10658 = zS²` for `S = 73, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortysix :
    singleClusterMaxEnergyS 2 146 = (10658 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73 4-vertex (quartet) ground-state energy** (γ-5 step 1172):
`singleClusterGSEnergyS 3 146 = -16060 = -S(1+zS)` for `S = 73, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortysix :
    singleClusterGSEnergyS 3 146 = (-16060 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1172):
`singleClusterMaxEnergyS 3 146 = 15987 = zS²` for `S = 73, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortysix :
    singleClusterMaxEnergyS 3 146 = (15987 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73 5-vertex (pentamer) ground-state energy** (γ-5 step 1173):
`singleClusterGSEnergyS 4 146 = -21389 = -S(1+zS)` for `S = 73, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortysix :
    singleClusterGSEnergyS 4 146 = (-21389 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1173):
`singleClusterMaxEnergyS 4 146 = 21316 = zS²` for `S = 73, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortysix :
    singleClusterMaxEnergyS 4 146 = (21316 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73 6-vertex (hexamer) ground-state energy** (γ-5 step 1174):
`singleClusterGSEnergyS 5 146 = -26718 = -S(1+zS)` for `S = 73, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortysix :
    singleClusterGSEnergyS 5 146 = (-26718 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1174):
`singleClusterMaxEnergyS 5 146 = 26645 = zS²` for `S = 73, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortysix :
    singleClusterMaxEnergyS 5 146 = (26645 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-73 7-vertex (heptamer) ground-state energy** (γ-5 step 1175):
`singleClusterGSEnergyS 6 146 = -32047 = -S(1+zS)` for `S = 73, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortysix :
    singleClusterGSEnergyS 6 146 = (-32047 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-73 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1175):
`singleClusterMaxEnergyS 6 146 = 31974 = zS²` for `S = 73, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortysix :
    singleClusterMaxEnergyS 6 146 = (31974 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-147/2 2-vertex (dimer) ground-state energy** (γ-5 step 1176):
`singleClusterGSEnergyS 1 147 = -21903/4 = -S(S+1)` for `S = 147/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortyseven :
    singleClusterGSEnergyS 1 147 = (-21903 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-147/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1176):
`singleClusterMaxEnergyS 1 147 = 21609/4 = S²` for `S = 147/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortyseven :
    singleClusterMaxEnergyS 1 147 = (21609 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-147/2 3-vertex (trimer) ground-state energy** (γ-5 step 1177):
`singleClusterGSEnergyS 2 147 = -10878 = -S(1+zS)` for `S = 147/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortyseven :
    singleClusterGSEnergyS 2 147 = (-10878 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-147/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1177):
`singleClusterMaxEnergyS 2 147 = 21609/2 = zS²` for `S = 147/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortyseven :
    singleClusterMaxEnergyS 2 147 = (21609 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-147/2 4-vertex (quartet) ground-state energy** (γ-5 step 1178):
`singleClusterGSEnergyS 3 147 = -65121/4 = -S(1+zS)` for `S = 147/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortyseven :
    singleClusterGSEnergyS 3 147 = (-65121 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-147/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1178):
`singleClusterMaxEnergyS 3 147 = 64827/4 = zS²` for `S = 147/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortyseven :
    singleClusterMaxEnergyS 3 147 = (64827 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-147/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1179):
`singleClusterGSEnergyS 4 147 = -43365/2 = -S(1+zS)` for `S = 147/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortyseven :
    singleClusterGSEnergyS 4 147 = (-43365 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-147/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1179):
`singleClusterMaxEnergyS 4 147 = 21609 = zS²` for `S = 147/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortyseven :
    singleClusterMaxEnergyS 4 147 = (21609 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-147/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1180):
`singleClusterGSEnergyS 5 147 = -108339/4 = -S(1+zS)` for `S = 147/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortyseven :
    singleClusterGSEnergyS 5 147 = (-108339 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-147/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1180):
`singleClusterMaxEnergyS 5 147 = 108045/4 = zS²` for `S = 147/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortyseven :
    singleClusterMaxEnergyS 5 147 = (108045 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-147/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1181):
`singleClusterGSEnergyS 6 147 = -32487 = -S(1+zS)` for `S = 147/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortyseven :
    singleClusterGSEnergyS 6 147 = (-32487 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-147/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1181):
`singleClusterMaxEnergyS 6 147 = 64827/2 = zS²` for `S = 147/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortyseven :
    singleClusterMaxEnergyS 6 147 = (64827 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-74 2-vertex (dimer) ground-state energy** (γ-5 step 1182):
`singleClusterGSEnergyS 1 148 = -5550 = -S(S+1)` for `S = 74`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredfortyeight :
    singleClusterGSEnergyS 1 148 = (-5550 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-74 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1182):
`singleClusterMaxEnergyS 1 148 = 5476 = S²` for `S = 74`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredfortyeight :
    singleClusterMaxEnergyS 1 148 = (5476 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-74 3-vertex (trimer) ground-state energy** (γ-5 step 1183):
`singleClusterGSEnergyS 2 148 = -11026 = -S(1+zS)` for `S = 74, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredfortyeight :
    singleClusterGSEnergyS 2 148 = (-11026 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-74 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1183):
`singleClusterMaxEnergyS 2 148 = 10952 = zS²` for `S = 74, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredfortyeight :
    singleClusterMaxEnergyS 2 148 = (10952 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-74 4-vertex (quartet) ground-state energy** (γ-5 step 1184):
`singleClusterGSEnergyS 3 148 = -16502 = -S(1+zS)` for `S = 74, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredfortyeight :
    singleClusterGSEnergyS 3 148 = (-16502 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-74 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1184):
`singleClusterMaxEnergyS 3 148 = 16428 = zS²` for `S = 74, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredfortyeight :
    singleClusterMaxEnergyS 3 148 = (16428 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-74 5-vertex (pentamer) ground-state energy** (γ-5 step 1185):
`singleClusterGSEnergyS 4 148 = -21978 = -S(1+zS)` for `S = 74, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredfortyeight :
    singleClusterGSEnergyS 4 148 = (-21978 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-74 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1185):
`singleClusterMaxEnergyS 4 148 = 21904 = zS²` for `S = 74, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredfortyeight :
    singleClusterMaxEnergyS 4 148 = (21904 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-74 6-vertex (hexamer) ground-state energy** (γ-5 step 1186):
`singleClusterGSEnergyS 5 148 = -27454 = -S(1+zS)` for `S = 74, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredfortyeight :
    singleClusterGSEnergyS 5 148 = (-27454 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-74 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1186):
`singleClusterMaxEnergyS 5 148 = 27380 = zS²` for `S = 74, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredfortyeight :
    singleClusterMaxEnergyS 5 148 = (27380 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-74 7-vertex (heptamer) ground-state energy** (γ-5 step 1187):
`singleClusterGSEnergyS 6 148 = -32930 = -S(1+zS)` for `S = 74, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredfortyeight :
    singleClusterGSEnergyS 6 148 = (-32930 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-74 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1187):
`singleClusterMaxEnergyS 6 148 = 32856 = zS²` for `S = 74, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredfortyeight :
    singleClusterMaxEnergyS 6 148 = (32856 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

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

end LatticeSystem.Quantum
