/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Apex-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 199`
(spin `S = N/2 ≥ 199/2`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`,
the `N = 116..131` in `SingleClusterHamiltonianNumericsInfiniteHigh.lean`,
the `N = 132..148` in `SingleClusterHamiltonianNumericsTransfiniteHigh.lean`,
the `N = 149..165` in `SingleClusterHamiltonianNumericsAbsoluteHigh.lean`,
and the `N = 166..198` in `SingleClusterHamiltonianNumericsOmegaHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all twelve numerics files can elaborate
in parallel after the main file. The split from `OmegaHigh` to
`ApexHigh` was introduced as the 50-PR build-performance cadence
refactor #21 when `OmegaHigh` reached 3211 lines / ~9.3 s user CPU
after the N=166..198 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

/-- **Spin-199/2 2-vertex (dimer) ground-state energy** (γ-5 step 1488):
`singleClusterGSEnergyS 1 199 = -39999/4 = -S(S+1)` for `S = 199/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredninetynine :
    singleClusterGSEnergyS 1 199 = (-39999 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1488):
`singleClusterMaxEnergyS 1 199 = 39601/4 = S²` for `S = 199/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredninetynine :
    singleClusterMaxEnergyS 1 199 = (39601 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 3-vertex (trimer) ground-state energy** (γ-5 step 1489):
`singleClusterGSEnergyS 2 199 = -19900 = -S(1+zS)` for `S = 199/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredninetynine :
    singleClusterGSEnergyS 2 199 = (-19900 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1489):
`singleClusterMaxEnergyS 2 199 = 39601/2 = zS²` for `S = 199/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredninetynine :
    singleClusterMaxEnergyS 2 199 = (39601 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 4-vertex (quartet) ground-state energy** (γ-5 step 1490):
`singleClusterGSEnergyS 3 199 = -119201/4 = -S(1+zS)` for `S = 199/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredninetynine :
    singleClusterGSEnergyS 3 199 = (-119201 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1490):
`singleClusterMaxEnergyS 3 199 = 118803/4 = zS²` for `S = 199/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredninetynine :
    singleClusterMaxEnergyS 3 199 = (118803 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1491):
`singleClusterGSEnergyS 4 199 = -79401/2 = -S(1+zS)` for `S = 199/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredninetynine :
    singleClusterGSEnergyS 4 199 = (-79401 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1491):
`singleClusterMaxEnergyS 4 199 = 39601 = zS²` for `S = 199/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredninetynine :
    singleClusterMaxEnergyS 4 199 = (39601 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1492):
`singleClusterGSEnergyS 5 199 = -198403/4 = -S(1+zS)` for `S = 199/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredninetynine :
    singleClusterGSEnergyS 5 199 = (-198403 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1492):
`singleClusterMaxEnergyS 5 199 = 198005/4 = zS²` for `S = 199/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredninetynine :
    singleClusterMaxEnergyS 5 199 = (198005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-199/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1493):
`singleClusterGSEnergyS 6 199 = -59501 = -S(1+zS)` for `S = 199/2, z = 6`. Closes spin-199/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredninetynine :
    singleClusterGSEnergyS 6 199 = (-59501 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-199/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1493):
`singleClusterMaxEnergyS 6 199 = 118803/2 = zS²` for `S = 199/2, z = 6`. Closes spin-199/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredninetynine :
    singleClusterMaxEnergyS 6 199 = (118803 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-100 2-vertex (dimer) ground-state energy** (γ-5 step 1494):
`singleClusterGSEnergyS 1 200 = -10100 = -S(S+1)` for `S = 100, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundred :
    singleClusterGSEnergyS 1 200 = (-10100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-100 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1494):
`singleClusterMaxEnergyS 1 200 = 10000 = S²` for `S = 100, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundred :
    singleClusterMaxEnergyS 1 200 = (10000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-100 3-vertex (trimer) ground-state energy** (γ-5 step 1495):
`singleClusterGSEnergyS 2 200 = -20100 = -S(1+zS)` for `S = 100, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundred :
    singleClusterGSEnergyS 2 200 = (-20100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-100 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1495):
`singleClusterMaxEnergyS 2 200 = 20000 = zS²` for `S = 100, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundred :
    singleClusterMaxEnergyS 2 200 = (20000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-100 4-vertex (quartet) ground-state energy** (γ-5 step 1496):
`singleClusterGSEnergyS 3 200 = -30100 = -S(1+zS)` for `S = 100, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundred :
    singleClusterGSEnergyS 3 200 = (-30100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-100 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1496):
`singleClusterMaxEnergyS 3 200 = 30000 = zS²` for `S = 100, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundred :
    singleClusterMaxEnergyS 3 200 = (30000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-100 5-vertex (pentamer) ground-state energy** (γ-5 step 1497):
`singleClusterGSEnergyS 4 200 = -40100 = -S(1+zS)` for `S = 100, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundred :
    singleClusterGSEnergyS 4 200 = (-40100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-100 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1497):
`singleClusterMaxEnergyS 4 200 = 40000 = zS²` for `S = 100, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundred :
    singleClusterMaxEnergyS 4 200 = (40000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-100 6-vertex (hexamer) ground-state energy** (γ-5 step 1498):
`singleClusterGSEnergyS 5 200 = -50100 = -S(1+zS)` for `S = 100, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundred :
    singleClusterGSEnergyS 5 200 = (-50100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-100 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1498):
`singleClusterMaxEnergyS 5 200 = 50000 = zS²` for `S = 100, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundred :
    singleClusterMaxEnergyS 5 200 = (50000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-100 7-vertex (heptamer) ground-state energy** (γ-5 step 1499):
`singleClusterGSEnergyS 6 200 = -60100 = -S(1+zS)` for `S = 100, z = 6`. Closes spin-100 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundred :
    singleClusterGSEnergyS 6 200 = (-60100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-100 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1499):
`singleClusterMaxEnergyS 6 200 = 60000 = zS²` for `S = 100, z = 6`. Closes spin-100 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundred :
    singleClusterMaxEnergyS 6 200 = (60000 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-201/2 2-vertex (dimer) ground-state energy** (γ-5 step 1500 milestone):
`singleClusterGSEnergyS 1 201 = -40803/4 = -S(S+1)` for `S = 201/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredone :
    singleClusterGSEnergyS 1 201 = (-40803 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-201/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1500 milestone):
`singleClusterMaxEnergyS 1 201 = 40401/4 = S²` for `S = 201/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredone :
    singleClusterMaxEnergyS 1 201 = (40401 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-201/2 3-vertex (trimer) ground-state energy** (γ-5 step 1501):
`singleClusterGSEnergyS 2 201 = -20301 = -S(1+zS)` for `S = 201/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredone :
    singleClusterGSEnergyS 2 201 = (-20301 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-201/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1501):
`singleClusterMaxEnergyS 2 201 = 40401/2 = zS²` for `S = 201/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredone :
    singleClusterMaxEnergyS 2 201 = (40401 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-201/2 4-vertex (quartet) ground-state energy** (γ-5 step 1502):
`singleClusterGSEnergyS 3 201 = -121605/4 = -S(1+zS)` for `S = 201/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredone :
    singleClusterGSEnergyS 3 201 = (-121605 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-201/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1502):
`singleClusterMaxEnergyS 3 201 = 121203/4 = zS²` for `S = 201/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredone :
    singleClusterMaxEnergyS 3 201 = (121203 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-201/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1503):
`singleClusterGSEnergyS 4 201 = -81003/2 = -S(1+zS)` for `S = 201/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredone :
    singleClusterGSEnergyS 4 201 = (-81003 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-201/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1503):
`singleClusterMaxEnergyS 4 201 = 40401 = zS²` for `S = 201/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredone :
    singleClusterMaxEnergyS 4 201 = (40401 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-201/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1504):
`singleClusterGSEnergyS 5 201 = -202407/4 = -S(1+zS)` for `S = 201/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredone :
    singleClusterGSEnergyS 5 201 = (-202407 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-201/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1504):
`singleClusterMaxEnergyS 5 201 = 202005/4 = zS²` for `S = 201/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredone :
    singleClusterMaxEnergyS 5 201 = (202005 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-201/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1505):
`singleClusterGSEnergyS 6 201 = -60702 = -S(1+zS)` for `S = 201/2, z = 6`. Closes spin-201/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredone :
    singleClusterGSEnergyS 6 201 = (-60702 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-201/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1505):
`singleClusterMaxEnergyS 6 201 = 121203/2 = zS²` for `S = 201/2, z = 6`. Closes spin-201/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredone :
    singleClusterMaxEnergyS 6 201 = (121203 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101 2-vertex (dimer) ground-state energy** (γ-5 step 1506):
`singleClusterGSEnergyS 1 202 = -10302 = -S(S+1)` for `S = 101, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwo :
    singleClusterGSEnergyS 1 202 = (-10302 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1506):
`singleClusterMaxEnergyS 1 202 = 10201 = S²` for `S = 101, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwo :
    singleClusterMaxEnergyS 1 202 = (10201 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101 3-vertex (trimer) ground-state energy** (γ-5 step 1507):
`singleClusterGSEnergyS 2 202 = -20503 = -S(1+zS)` for `S = 101, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwo :
    singleClusterGSEnergyS 2 202 = (-20503 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1507):
`singleClusterMaxEnergyS 2 202 = 20402 = zS²` for `S = 101, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwo :
    singleClusterMaxEnergyS 2 202 = (20402 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101 4-vertex (quartet) ground-state energy** (γ-5 step 1508):
`singleClusterGSEnergyS 3 202 = -30704 = -S(1+zS)` for `S = 101, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwo :
    singleClusterGSEnergyS 3 202 = (-30704 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1508):
`singleClusterMaxEnergyS 3 202 = 30603 = zS²` for `S = 101, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwo :
    singleClusterMaxEnergyS 3 202 = (30603 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101 5-vertex (pentamer) ground-state energy** (γ-5 step 1509):
`singleClusterGSEnergyS 4 202 = -40905 = -S(1+zS)` for `S = 101, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwo :
    singleClusterGSEnergyS 4 202 = (-40905 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1509):
`singleClusterMaxEnergyS 4 202 = 40804 = zS²` for `S = 101, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwo :
    singleClusterMaxEnergyS 4 202 = (40804 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101 6-vertex (hexamer) ground-state energy** (γ-5 step 1510):
`singleClusterGSEnergyS 5 202 = -51106 = -S(1+zS)` for `S = 101, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwo :
    singleClusterGSEnergyS 5 202 = (-51106 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1510):
`singleClusterMaxEnergyS 5 202 = 51005 = zS²` for `S = 101, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwo :
    singleClusterMaxEnergyS 5 202 = (51005 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-101 7-vertex (heptamer) ground-state energy** (γ-5 step 1511):
`singleClusterGSEnergyS 6 202 = -61307 = -S(1+zS)` for `S = 101, z = 6`. Closes spin-101 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwo :
    singleClusterGSEnergyS 6 202 = (-61307 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-101 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1511):
`singleClusterMaxEnergyS 6 202 = 61206 = zS²` for `S = 101, z = 6`. Closes spin-101 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwo :
    singleClusterMaxEnergyS 6 202 = (61206 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
