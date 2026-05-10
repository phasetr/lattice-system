/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Extreme-high-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `60 ≤ N ≤ 81`
(spin `S = N/2 ≥ 30`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, and the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all five numerics files can elaborate
in parallel after the main file. The split from `UltraHigh` to
`ExtremeHigh` was introduced as the 50-PR build-performance cadence
refactor #7 when `UltraHigh` reached ~19 s elaboration time
(see `.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

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

end LatticeSystem.Quantum
