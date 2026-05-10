/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Higher-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for
`29 ≤ N ≤ 38` (spin `29/2 ≤ S ≤ 19`). The pre-`N=29`
specialisations live in `SingleClusterHamiltonianNumerics.lean`,
the `N = 39..47` in `SingleClusterHamiltonianNumericsVeryHigh.lean`,
the `N = 48..59` in `SingleClusterHamiltonianNumericsUltraHigh.lean`,
the `N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
and the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
  and the `N ≥ 99` in `SingleClusterHamiltonianNumericsHyperHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics file) so all numerics files can elaborate in
parallel after the main file. Splitting was introduced as part of the
50-PR build-performance cadence (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

/-- **Spin-29/2 dimer ground-state energy** (γ-5 step 468):
`singleClusterGSEnergyS 1 29 = -899/4 = -S(S+1)` for `S = 29/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentynine :
    singleClusterGSEnergyS 1 29 = (-899 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29/2 dimer maximum-Casimir-sector energy** (γ-5 step 468):
`singleClusterMaxEnergyS 1 29 = 841/4 = S²` for `S = 29/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentynine :
    singleClusterMaxEnergyS 1 29 = (841 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29/2 3-vertex-star ground-state energy** (γ-5 step 469):
`singleClusterGSEnergyS 2 29 = -435 = -S(1+zS)` for `S = 29/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentynine :
    singleClusterGSEnergyS 2 29 = (-435 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 469):
`singleClusterMaxEnergyS 2 29 = 841/2 = zS²` for `S = 29/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentynine :
    singleClusterMaxEnergyS 2 29 = (841 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29/2 4-vertex-star ground-state energy** (γ-5 step 470):
`singleClusterGSEnergyS 3 29 = -2581/4 = -S(1+zS)` for `S = 29/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentynine :
    singleClusterGSEnergyS 3 29 = (-2581 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 470):
`singleClusterMaxEnergyS 3 29 = 2523/4 = zS²` for `S = 29/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentynine :
    singleClusterMaxEnergyS 3 29 = (2523 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29/2 5-vertex-star ground-state energy** (γ-5 step 471):
`singleClusterGSEnergyS 4 29 = -1711/2 = -S(1+zS)` for `S = 29/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentynine :
    singleClusterGSEnergyS 4 29 = (-1711 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 471):
`singleClusterMaxEnergyS 4 29 = 841 = zS²` for `S = 29/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentynine :
    singleClusterMaxEnergyS 4 29 = (841 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29/2 6-vertex-star ground-state energy** (γ-5 step 472):
`singleClusterGSEnergyS 5 29 = -4263/4 = -S(1+zS)` for `S = 29/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentynine :
    singleClusterGSEnergyS 5 29 = (-4263 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 472):
`singleClusterMaxEnergyS 5 29 = 4205/4 = zS²` for `S = 29/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentynine :
    singleClusterMaxEnergyS 5 29 = (4205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-29/2 7-vertex-star ground-state energy** (γ-5 step 473):
`singleClusterGSEnergyS 6 29 = -1276 = -S(1+zS)` for `S = 29/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentynine :
    singleClusterGSEnergyS 6 29 = (-1276 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-29/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 473):
`singleClusterMaxEnergyS 6 29 = 2523/2 = zS²` for `S = 29/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentynine :
    singleClusterMaxEnergyS 6 29 = (2523 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15 dimer ground-state energy** (γ-5 step 474):
`singleClusterGSEnergyS 1 30 = -240 = -S(S+1)` for `S = 15`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirty :
    singleClusterGSEnergyS 1 30 = (-240 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15 dimer maximum-Casimir-sector energy** (γ-5 step 474):
`singleClusterMaxEnergyS 1 30 = 225 = S²` for `S = 15`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirty :
    singleClusterMaxEnergyS 1 30 = (225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15 3-vertex-star ground-state energy** (γ-5 step 475):
`singleClusterGSEnergyS 2 30 = -465 = -S(1+zS)` for `S = 15, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirty :
    singleClusterGSEnergyS 2 30 = (-465 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 475):
`singleClusterMaxEnergyS 2 30 = 450 = zS²` for `S = 15, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirty :
    singleClusterMaxEnergyS 2 30 = (450 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15 4-vertex-star ground-state energy** (γ-5 step 476):
`singleClusterGSEnergyS 3 30 = -690 = -S(1+zS)` for `S = 15, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirty :
    singleClusterGSEnergyS 3 30 = (-690 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 476):
`singleClusterMaxEnergyS 3 30 = 675 = zS²` for `S = 15, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirty :
    singleClusterMaxEnergyS 3 30 = (675 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15 5-vertex-star ground-state energy** (γ-5 step 477):
`singleClusterGSEnergyS 4 30 = -915 = -S(1+zS)` for `S = 15, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirty :
    singleClusterGSEnergyS 4 30 = (-915 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 477):
`singleClusterMaxEnergyS 4 30 = 900 = zS²` for `S = 15, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirty :
    singleClusterMaxEnergyS 4 30 = (900 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15 6-vertex-star ground-state energy** (γ-5 step 478):
`singleClusterGSEnergyS 5 30 = -1140 = -S(1+zS)` for `S = 15, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirty :
    singleClusterGSEnergyS 5 30 = (-1140 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 478):
`singleClusterMaxEnergyS 5 30 = 1125 = zS²` for `S = 15, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirty :
    singleClusterMaxEnergyS 5 30 = (1125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15 7-vertex-star ground-state energy** (γ-5 step 479):
`singleClusterGSEnergyS 6 30 = -1365 = -S(1+zS)` for `S = 15, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirty :
    singleClusterGSEnergyS 6 30 = (-1365 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 479):
`singleClusterMaxEnergyS 6 30 = 1350 = zS²` for `S = 15, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirty :
    singleClusterMaxEnergyS 6 30 = (1350 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31/2 dimer ground-state energy** (γ-5 step 480):
`singleClusterGSEnergyS 1 31 = -1023/4 = -S(S+1)` for `S = 31/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtyone :
    singleClusterGSEnergyS 1 31 = (-1023 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31/2 dimer maximum-Casimir-sector energy** (γ-5 step 480):
`singleClusterMaxEnergyS 1 31 = 961/4 = S²` for `S = 31/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtyone :
    singleClusterMaxEnergyS 1 31 = (961 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31/2 3-vertex-star ground-state energy** (γ-5 step 481):
`singleClusterGSEnergyS 2 31 = -496 = -S(1+zS)` for `S = 31/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtyone :
    singleClusterGSEnergyS 2 31 = (-496 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 481):
`singleClusterMaxEnergyS 2 31 = 961/2 = zS²` for `S = 31/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtyone :
    singleClusterMaxEnergyS 2 31 = (961 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31/2 4-vertex-star ground-state energy** (γ-5 step 482):
`singleClusterGSEnergyS 3 31 = -2945/4 = -S(1+zS)` for `S = 31/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtyone :
    singleClusterGSEnergyS 3 31 = (-2945 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 482):
`singleClusterMaxEnergyS 3 31 = 2883/4 = zS²` for `S = 31/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtyone :
    singleClusterMaxEnergyS 3 31 = (2883 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31/2 5-vertex-star ground-state energy** (γ-5 step 483):
`singleClusterGSEnergyS 4 31 = -1953/2 = -S(1+zS)` for `S = 31/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtyone :
    singleClusterGSEnergyS 4 31 = (-1953 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 483):
`singleClusterMaxEnergyS 4 31 = 961 = zS²` for `S = 31/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtyone :
    singleClusterMaxEnergyS 4 31 = (961 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31/2 6-vertex-star ground-state energy** (γ-5 step 484):
`singleClusterGSEnergyS 5 31 = -4867/4 = -S(1+zS)` for `S = 31/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtyone :
    singleClusterGSEnergyS 5 31 = (-4867 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 484):
`singleClusterMaxEnergyS 5 31 = 4805/4 = zS²` for `S = 31/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtyone :
    singleClusterMaxEnergyS 5 31 = (4805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-31/2 7-vertex-star ground-state energy** (γ-5 step 485):
`singleClusterGSEnergyS 6 31 = -1457 = -S(1+zS)` for `S = 31/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtyone :
    singleClusterGSEnergyS 6 31 = (-1457 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-31/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 485):
`singleClusterMaxEnergyS 6 31 = 2883/2 = zS²` for `S = 31/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtyone :
    singleClusterMaxEnergyS 6 31 = (2883 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-16 dimer ground-state energy** (γ-5 step 486):
`singleClusterGSEnergyS 1 32 = -272 = -S(S+1)` for `S = 16`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtytwo :
    singleClusterGSEnergyS 1 32 = (-272 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-16 dimer maximum-Casimir-sector energy** (γ-5 step 486):
`singleClusterMaxEnergyS 1 32 = 256 = S²` for `S = 16`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtytwo :
    singleClusterMaxEnergyS 1 32 = (256 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-16 3-vertex-star ground-state energy** (γ-5 step 487):
`singleClusterGSEnergyS 2 32 = -528 = -S(1+zS)` for `S = 16, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtytwo :
    singleClusterGSEnergyS 2 32 = (-528 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-16 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 487):
`singleClusterMaxEnergyS 2 32 = 512 = zS²` for `S = 16, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtytwo :
    singleClusterMaxEnergyS 2 32 = (512 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-16 4-vertex-star ground-state energy** (γ-5 step 488):
`singleClusterGSEnergyS 3 32 = -784 = -S(1+zS)` for `S = 16, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtytwo :
    singleClusterGSEnergyS 3 32 = (-784 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-16 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 488):
`singleClusterMaxEnergyS 3 32 = 768 = zS²` for `S = 16, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtytwo :
    singleClusterMaxEnergyS 3 32 = (768 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-16 5-vertex-star ground-state energy** (γ-5 step 489):
`singleClusterGSEnergyS 4 32 = -1040 = -S(1+zS)` for `S = 16, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtytwo :
    singleClusterGSEnergyS 4 32 = (-1040 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-16 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 489):
`singleClusterMaxEnergyS 4 32 = 1024 = zS²` for `S = 16, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtytwo :
    singleClusterMaxEnergyS 4 32 = (1024 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-16 6-vertex-star ground-state energy** (γ-5 step 490):
`singleClusterGSEnergyS 5 32 = -1296 = -S(1+zS)` for `S = 16, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtytwo :
    singleClusterGSEnergyS 5 32 = (-1296 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-16 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 490):
`singleClusterMaxEnergyS 5 32 = 1280 = zS²` for `S = 16, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtytwo :
    singleClusterMaxEnergyS 5 32 = (1280 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-16 7-vertex-star ground-state energy** (γ-5 step 491):
`singleClusterGSEnergyS 6 32 = -1552 = -S(1+zS)` for `S = 16, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtytwo :
    singleClusterGSEnergyS 6 32 = (-1552 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-16 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 491):
`singleClusterMaxEnergyS 6 32 = 1536 = zS²` for `S = 16, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtytwo :
    singleClusterMaxEnergyS 6 32 = (1536 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33/2 dimer ground-state energy** (γ-5 step 492):
`singleClusterGSEnergyS 1 33 = -1155/4 = -S(S+1)` for `S = 33/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtythree :
    singleClusterGSEnergyS 1 33 = (-1155 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33/2 dimer maximum-Casimir-sector energy** (γ-5 step 492):
`singleClusterMaxEnergyS 1 33 = 1089/4 = S²` for `S = 33/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtythree :
    singleClusterMaxEnergyS 1 33 = (1089 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33/2 3-vertex-star ground-state energy** (γ-5 step 493):
`singleClusterGSEnergyS 2 33 = -561 = -S(1+zS)` for `S = 33/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtythree :
    singleClusterGSEnergyS 2 33 = (-561 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 493):
`singleClusterMaxEnergyS 2 33 = 1089/2 = zS²` for `S = 33/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtythree :
    singleClusterMaxEnergyS 2 33 = (1089 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33/2 4-vertex-star ground-state energy** (γ-5 step 494):
`singleClusterGSEnergyS 3 33 = -3333/4 = -S(1+zS)` for `S = 33/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtythree :
    singleClusterGSEnergyS 3 33 = (-3333 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 494):
`singleClusterMaxEnergyS 3 33 = 3267/4 = zS²` for `S = 33/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtythree :
    singleClusterMaxEnergyS 3 33 = (3267 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33/2 5-vertex-star ground-state energy** (γ-5 step 495):
`singleClusterGSEnergyS 4 33 = -2211/2 = -S(1+zS)` for `S = 33/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtythree :
    singleClusterGSEnergyS 4 33 = (-2211 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 495):
`singleClusterMaxEnergyS 4 33 = 1089 = zS²` for `S = 33/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtythree :
    singleClusterMaxEnergyS 4 33 = (1089 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33/2 6-vertex-star ground-state energy** (γ-5 step 496):
`singleClusterGSEnergyS 5 33 = -5511/4 = -S(1+zS)` for `S = 33/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtythree :
    singleClusterGSEnergyS 5 33 = (-5511 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 496):
`singleClusterMaxEnergyS 5 33 = 5445/4 = zS²` for `S = 33/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtythree :
    singleClusterMaxEnergyS 5 33 = (5445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-33/2 7-vertex-star ground-state energy** (γ-5 step 497):
`singleClusterGSEnergyS 6 33 = -1650 = -S(1+zS)` for `S = 33/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtythree :
    singleClusterGSEnergyS 6 33 = (-1650 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-33/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 497):
`singleClusterMaxEnergyS 6 33 = 3267/2 = zS²` for `S = 33/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtythree :
    singleClusterMaxEnergyS 6 33 = (3267 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17 dimer ground-state energy** (γ-5 step 498):
`singleClusterGSEnergyS 1 34 = -306 = -S(S+1)` for `S = 17`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtyfour :
    singleClusterGSEnergyS 1 34 = (-306 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17 dimer maximum-Casimir-sector energy** (γ-5 step 498):
`singleClusterMaxEnergyS 1 34 = 289 = S²` for `S = 17`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtyfour :
    singleClusterMaxEnergyS 1 34 = (289 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17 3-vertex-star ground-state energy** (γ-5 step 499):
`singleClusterGSEnergyS 2 34 = -595 = -S(1+zS)` for `S = 17, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtyfour :
    singleClusterGSEnergyS 2 34 = (-595 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 499):
`singleClusterMaxEnergyS 2 34 = 578 = zS²` for `S = 17, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtyfour :
    singleClusterMaxEnergyS 2 34 = (578 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17 4-vertex-star ground-state energy** (γ-5 step 500):
`singleClusterGSEnergyS 3 34 = -884 = -S(1+zS)` for `S = 17, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtyfour :
    singleClusterGSEnergyS 3 34 = (-884 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 500):
`singleClusterMaxEnergyS 3 34 = 867 = zS²` for `S = 17, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtyfour :
    singleClusterMaxEnergyS 3 34 = (867 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17 5-vertex-star ground-state energy** (γ-5 step 501):
`singleClusterGSEnergyS 4 34 = -1173 = -S(1+zS)` for `S = 17, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtyfour :
    singleClusterGSEnergyS 4 34 = (-1173 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 501):
`singleClusterMaxEnergyS 4 34 = 1156 = zS²` for `S = 17, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtyfour :
    singleClusterMaxEnergyS 4 34 = (1156 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17 6-vertex-star ground-state energy** (γ-5 step 502):
`singleClusterGSEnergyS 5 34 = -1462 = -S(1+zS)` for `S = 17, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtyfour :
    singleClusterGSEnergyS 5 34 = (-1462 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 502):
`singleClusterMaxEnergyS 5 34 = 1445 = zS²` for `S = 17, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtyfour :
    singleClusterMaxEnergyS 5 34 = (1445 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17 7-vertex-star ground-state energy** (γ-5 step 503):
`singleClusterGSEnergyS 6 34 = -1751 = -S(1+zS)` for `S = 17, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtyfour :
    singleClusterGSEnergyS 6 34 = (-1751 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 503):
`singleClusterMaxEnergyS 6 34 = 1734 = zS²` for `S = 17, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtyfour :
    singleClusterMaxEnergyS 6 34 = (1734 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35/2 dimer ground-state energy** (γ-5 step 504):
`singleClusterGSEnergyS 1 35 = -1295/4 = -S(S+1)` for `S = 35/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtyfive :
    singleClusterGSEnergyS 1 35 = (-1295 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35/2 dimer maximum-Casimir-sector energy** (γ-5 step 504):
`singleClusterMaxEnergyS 1 35 = 1225/4 = S²` for `S = 35/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtyfive :
    singleClusterMaxEnergyS 1 35 = (1225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35/2 3-vertex-star ground-state energy** (γ-5 step 505):
`singleClusterGSEnergyS 2 35 = -630 = -S(1+zS)` for `S = 35/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtyfive :
    singleClusterGSEnergyS 2 35 = (-630 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 505):
`singleClusterMaxEnergyS 2 35 = 1225/2 = zS²` for `S = 35/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtyfive :
    singleClusterMaxEnergyS 2 35 = (1225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35/2 4-vertex-star ground-state energy** (γ-5 step 506):
`singleClusterGSEnergyS 3 35 = -3745/4 = -S(1+zS)` for `S = 35/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtyfive :
    singleClusterGSEnergyS 3 35 = (-3745 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 506):
`singleClusterMaxEnergyS 3 35 = 3675/4 = zS²` for `S = 35/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtyfive :
    singleClusterMaxEnergyS 3 35 = (3675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35/2 5-vertex-star ground-state energy** (γ-5 step 507):
`singleClusterGSEnergyS 4 35 = -2485/2 = -S(1+zS)` for `S = 35/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtyfive :
    singleClusterGSEnergyS 4 35 = (-2485 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 507):
`singleClusterMaxEnergyS 4 35 = 1225 = zS²` for `S = 35/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtyfive :
    singleClusterMaxEnergyS 4 35 = (1225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35/2 6-vertex-star ground-state energy** (γ-5 step 508):
`singleClusterGSEnergyS 5 35 = -6195/4 = -S(1+zS)` for `S = 35/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtyfive :
    singleClusterGSEnergyS 5 35 = (-6195 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 508):
`singleClusterMaxEnergyS 5 35 = 6125/4 = zS²` for `S = 35/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtyfive :
    singleClusterMaxEnergyS 5 35 = (6125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-35/2 7-vertex-star ground-state energy** (γ-5 step 509):
`singleClusterGSEnergyS 6 35 = -1855 = -S(1+zS)` for `S = 35/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtyfive :
    singleClusterGSEnergyS 6 35 = (-1855 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-35/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 509):
`singleClusterMaxEnergyS 6 35 = 3675/2 = zS²` for `S = 35/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtyfive :
    singleClusterMaxEnergyS 6 35 = (3675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-18 dimer ground-state energy** (γ-5 step 510):
`singleClusterGSEnergyS 1 36 = -342 = -S(S+1)` for `S = 18`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtysix :
    singleClusterGSEnergyS 1 36 = (-342 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-18 dimer maximum-Casimir-sector energy** (γ-5 step 510):
`singleClusterMaxEnergyS 1 36 = 324 = S²` for `S = 18`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtysix :
    singleClusterMaxEnergyS 1 36 = (324 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-18 3-vertex-star ground-state energy** (γ-5 step 511):
`singleClusterGSEnergyS 2 36 = -666 = -S(1+zS)` for `S = 18, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtysix :
    singleClusterGSEnergyS 2 36 = (-666 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-18 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 511):
`singleClusterMaxEnergyS 2 36 = 648 = zS²` for `S = 18, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtysix :
    singleClusterMaxEnergyS 2 36 = (648 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-18 4-vertex-star ground-state energy** (γ-5 step 512):
`singleClusterGSEnergyS 3 36 = -990 = -S(1+zS)` for `S = 18, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtysix :
    singleClusterGSEnergyS 3 36 = (-990 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-18 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 512):
`singleClusterMaxEnergyS 3 36 = 972 = zS²` for `S = 18, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtysix :
    singleClusterMaxEnergyS 3 36 = (972 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-18 5-vertex-star ground-state energy** (γ-5 step 513):
`singleClusterGSEnergyS 4 36 = -1314 = -S(1+zS)` for `S = 18, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtysix :
    singleClusterGSEnergyS 4 36 = (-1314 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-18 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 513):
`singleClusterMaxEnergyS 4 36 = 1296 = zS²` for `S = 18, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtysix :
    singleClusterMaxEnergyS 4 36 = (1296 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-18 6-vertex-star ground-state energy** (γ-5 step 514):
`singleClusterGSEnergyS 5 36 = -1638 = -S(1+zS)` for `S = 18, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtysix :
    singleClusterGSEnergyS 5 36 = (-1638 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-18 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 514):
`singleClusterMaxEnergyS 5 36 = 1620 = zS²` for `S = 18, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtysix :
    singleClusterMaxEnergyS 5 36 = (1620 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-18 7-vertex-star ground-state energy** (γ-5 step 515):
`singleClusterGSEnergyS 6 36 = -1962 = -S(1+zS)` for `S = 18, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtysix :
    singleClusterGSEnergyS 6 36 = (-1962 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-18 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 515):
`singleClusterMaxEnergyS 6 36 = 1944 = zS²` for `S = 18, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtysix :
    singleClusterMaxEnergyS 6 36 = (1944 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37/2 dimer ground-state energy** (γ-5 step 516):
`singleClusterGSEnergyS 1 37 = -1443/4 = -S(S+1)` for `S = 37/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtyseven :
    singleClusterGSEnergyS 1 37 = (-1443 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37/2 dimer maximum-Casimir-sector energy** (γ-5 step 516):
`singleClusterMaxEnergyS 1 37 = 1369/4 = S²` for `S = 37/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtyseven :
    singleClusterMaxEnergyS 1 37 = (1369 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37/2 3-vertex-star ground-state energy** (γ-5 step 517):
`singleClusterGSEnergyS 2 37 = -703 = -S(1+zS)` for `S = 37/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtyseven :
    singleClusterGSEnergyS 2 37 = (-703 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 517):
`singleClusterMaxEnergyS 2 37 = 1369/2 = zS²` for `S = 37/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtyseven :
    singleClusterMaxEnergyS 2 37 = (1369 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37/2 4-vertex-star ground-state energy** (γ-5 step 518):
`singleClusterGSEnergyS 3 37 = -4181/4 = -S(1+zS)` for `S = 37/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtyseven :
    singleClusterGSEnergyS 3 37 = (-4181 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 518):
`singleClusterMaxEnergyS 3 37 = 4107/4 = zS²` for `S = 37/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtyseven :
    singleClusterMaxEnergyS 3 37 = (4107 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37/2 5-vertex-star ground-state energy** (γ-5 step 519):
`singleClusterGSEnergyS 4 37 = -2775/2 = -S(1+zS)` for `S = 37/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtyseven :
    singleClusterGSEnergyS 4 37 = (-2775 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 519):
`singleClusterMaxEnergyS 4 37 = 1369 = zS²` for `S = 37/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtyseven :
    singleClusterMaxEnergyS 4 37 = (1369 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37/2 6-vertex-star ground-state energy** (γ-5 step 520):
`singleClusterGSEnergyS 5 37 = -6919/4 = -S(1+zS)` for `S = 37/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtyseven :
    singleClusterGSEnergyS 5 37 = (-6919 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 520):
`singleClusterMaxEnergyS 5 37 = 6845/4 = zS²` for `S = 37/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtyseven :
    singleClusterMaxEnergyS 5 37 = (6845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-37/2 7-vertex-star ground-state energy** (γ-5 step 521):
`singleClusterGSEnergyS 6 37 = -2072 = -S(1+zS)` for `S = 37/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtyseven :
    singleClusterGSEnergyS 6 37 = (-2072 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-37/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 521):
`singleClusterMaxEnergyS 6 37 = 4107/2 = zS²` for `S = 37/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtyseven :
    singleClusterMaxEnergyS 6 37 = (4107 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19 dimer ground-state energy** (γ-5 step 522):
`singleClusterGSEnergyS 1 38 = -380 = -S(S+1)` for `S = 19`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirtyeight :
    singleClusterGSEnergyS 1 38 = (-380 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19 dimer maximum-Casimir-sector energy** (γ-5 step 522):
`singleClusterMaxEnergyS 1 38 = 361 = S²` for `S = 19`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirtyeight :
    singleClusterMaxEnergyS 1 38 = (361 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19 3-vertex-star ground-state energy** (γ-5 step 523):
`singleClusterGSEnergyS 2 38 = -741 = -S(1+zS)` for `S = 19, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirtyeight :
    singleClusterGSEnergyS 2 38 = (-741 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 523):
`singleClusterMaxEnergyS 2 38 = 722 = zS²` for `S = 19, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirtyeight :
    singleClusterMaxEnergyS 2 38 = (722 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19 4-vertex-star ground-state energy** (γ-5 step 524):
`singleClusterGSEnergyS 3 38 = -1102 = -S(1+zS)` for `S = 19, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirtyeight :
    singleClusterGSEnergyS 3 38 = (-1102 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 524):
`singleClusterMaxEnergyS 3 38 = 1083 = zS²` for `S = 19, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirtyeight :
    singleClusterMaxEnergyS 3 38 = (1083 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19 5-vertex-star ground-state energy** (γ-5 step 525):
`singleClusterGSEnergyS 4 38 = -1463 = -S(1+zS)` for `S = 19, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirtyeight :
    singleClusterGSEnergyS 4 38 = (-1463 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 525):
`singleClusterMaxEnergyS 4 38 = 1444 = zS²` for `S = 19, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirtyeight :
    singleClusterMaxEnergyS 4 38 = (1444 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19 6-vertex-star ground-state energy** (γ-5 step 526):
`singleClusterGSEnergyS 5 38 = -1824 = -S(1+zS)` for `S = 19, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirtyeight :
    singleClusterGSEnergyS 5 38 = (-1824 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 526):
`singleClusterMaxEnergyS 5 38 = 1805 = zS²` for `S = 19, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirtyeight :
    singleClusterMaxEnergyS 5 38 = (1805 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19 7-vertex-star ground-state energy** (γ-5 step 527):
`singleClusterGSEnergyS 6 38 = -2185 = -S(1+zS)` for `S = 19, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirtyeight :
    singleClusterGSEnergyS 6 38 = (-2185 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 527):
`singleClusterMaxEnergyS 6 38 = 2166 = zS²` for `S = 19, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirtyeight :
    singleClusterMaxEnergyS 6 38 = (2166 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
