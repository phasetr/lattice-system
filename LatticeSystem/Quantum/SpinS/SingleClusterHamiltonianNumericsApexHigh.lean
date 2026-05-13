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

**Refactor #22 (evaluate-only, γ-5 step 1535 close):** measured
`ApexHigh` at 805 lines / 3.58 s user CPU after N=199..206 entries
had been appended. Well below the refactor #17/#19 split threshold
(3213–3274 lines / 8.7–9.1 s); kept as a single file. Matches
refactor #16/#18/#20 evaluate-only precedent.

**Refactor #23 (evaluate-only, γ-5 step 1583 close):** measured
`ApexHigh` at 1581 lines / 5.45 s user CPU after N=199..214 entries
had been appended (16 spin rows). Still well below the split
threshold; kept as a single file. Future split (refactor #24 or
later) anticipated once `ApexHigh` approaches ~3000 lines
(~12-14 more spin rows of growth, around N=230+).
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

/-- **Spin-203/2 2-vertex (dimer) ground-state energy** (γ-5 step 1512):
`singleClusterGSEnergyS 1 203 = -41615/4 = -S(S+1)` for `S = 203/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredthree :
    singleClusterGSEnergyS 1 203 = (-41615 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-203/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1512):
`singleClusterMaxEnergyS 1 203 = 41209/4 = S²` for `S = 203/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredthree :
    singleClusterMaxEnergyS 1 203 = (41209 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-203/2 3-vertex (trimer) ground-state energy** (γ-5 step 1513):
`singleClusterGSEnergyS 2 203 = -20706 = -S(1+zS)` for `S = 203/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredthree :
    singleClusterGSEnergyS 2 203 = (-20706 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-203/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1513):
`singleClusterMaxEnergyS 2 203 = 41209/2 = zS²` for `S = 203/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredthree :
    singleClusterMaxEnergyS 2 203 = (41209 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-203/2 4-vertex (quartet) ground-state energy** (γ-5 step 1514):
`singleClusterGSEnergyS 3 203 = -124033/4 = -S(1+zS)` for `S = 203/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredthree :
    singleClusterGSEnergyS 3 203 = (-124033 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-203/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1514):
`singleClusterMaxEnergyS 3 203 = 123627/4 = zS²` for `S = 203/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredthree :
    singleClusterMaxEnergyS 3 203 = (123627 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-203/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1515):
`singleClusterGSEnergyS 4 203 = -82621/2 = -S(1+zS)` for `S = 203/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredthree :
    singleClusterGSEnergyS 4 203 = (-82621 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-203/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1515):
`singleClusterMaxEnergyS 4 203 = 41209 = zS²` for `S = 203/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredthree :
    singleClusterMaxEnergyS 4 203 = (41209 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-203/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1516):
`singleClusterGSEnergyS 5 203 = -206451/4 = -S(1+zS)` for `S = 203/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredthree :
    singleClusterGSEnergyS 5 203 = (-206451 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-203/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1516):
`singleClusterMaxEnergyS 5 203 = 206045/4 = zS²` for `S = 203/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredthree :
    singleClusterMaxEnergyS 5 203 = (206045 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-203/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1517):
`singleClusterGSEnergyS 6 203 = -61915 = -S(1+zS)` for `S = 203/2, z = 6`. Closes spin-203/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredthree :
    singleClusterGSEnergyS 6 203 = (-61915 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-203/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1517):
`singleClusterMaxEnergyS 6 203 = 123627/2 = zS²` for `S = 203/2, z = 6`. Closes spin-203/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredthree :
    singleClusterMaxEnergyS 6 203 = (123627 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-102 2-vertex (dimer) ground-state energy** (γ-5 step 1518):
`singleClusterGSEnergyS 1 204 = -10506 = -S(S+1)` for `S = 102, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredfour :
    singleClusterGSEnergyS 1 204 = (-10506 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-102 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1518):
`singleClusterMaxEnergyS 1 204 = 10404 = S²` for `S = 102, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredfour :
    singleClusterMaxEnergyS 1 204 = (10404 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-102 3-vertex (trimer) ground-state energy** (γ-5 step 1519):
`singleClusterGSEnergyS 2 204 = -20910 = -S(1+zS)` for `S = 102, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredfour :
    singleClusterGSEnergyS 2 204 = (-20910 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-102 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1519):
`singleClusterMaxEnergyS 2 204 = 20808 = zS²` for `S = 102, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredfour :
    singleClusterMaxEnergyS 2 204 = (20808 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-102 4-vertex (quartet) ground-state energy** (γ-5 step 1520):
`singleClusterGSEnergyS 3 204 = -31314 = -S(1+zS)` for `S = 102, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredfour :
    singleClusterGSEnergyS 3 204 = (-31314 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-102 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1520):
`singleClusterMaxEnergyS 3 204 = 31212 = zS²` for `S = 102, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredfour :
    singleClusterMaxEnergyS 3 204 = (31212 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-102 5-vertex (pentamer) ground-state energy** (γ-5 step 1521):
`singleClusterGSEnergyS 4 204 = -41718 = -S(1+zS)` for `S = 102, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredfour :
    singleClusterGSEnergyS 4 204 = (-41718 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-102 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1521):
`singleClusterMaxEnergyS 4 204 = 41616 = zS²` for `S = 102, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredfour :
    singleClusterMaxEnergyS 4 204 = (41616 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-102 6-vertex (hexamer) ground-state energy** (γ-5 step 1522):
`singleClusterGSEnergyS 5 204 = -52122 = -S(1+zS)` for `S = 102, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredfour :
    singleClusterGSEnergyS 5 204 = (-52122 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-102 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1522):
`singleClusterMaxEnergyS 5 204 = 52020 = zS²` for `S = 102, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredfour :
    singleClusterMaxEnergyS 5 204 = (52020 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-102 7-vertex (heptamer) ground-state energy** (γ-5 step 1523):
`singleClusterGSEnergyS 6 204 = -62526 = -S(1+zS)` for `S = 102, z = 6`. Closes spin-102 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredfour :
    singleClusterGSEnergyS 6 204 = (-62526 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-102 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1523):
`singleClusterMaxEnergyS 6 204 = 62424 = zS²` for `S = 102, z = 6`. Closes spin-102 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredfour :
    singleClusterMaxEnergyS 6 204 = (62424 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-205/2 2-vertex (dimer) ground-state energy** (γ-5 step 1524):
`singleClusterGSEnergyS 1 205 = -42435/4 = -S(S+1)` for `S = 205/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredfive :
    singleClusterGSEnergyS 1 205 = (-42435 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-205/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1524):
`singleClusterMaxEnergyS 1 205 = 42025/4 = S²` for `S = 205/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredfive :
    singleClusterMaxEnergyS 1 205 = (42025 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-205/2 3-vertex (trimer) ground-state energy** (γ-5 step 1525):
`singleClusterGSEnergyS 2 205 = -21115 = -S(1+zS)` for `S = 205/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredfive :
    singleClusterGSEnergyS 2 205 = (-21115 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-205/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1525):
`singleClusterMaxEnergyS 2 205 = 42025/2 = zS²` for `S = 205/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredfive :
    singleClusterMaxEnergyS 2 205 = (42025 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-205/2 4-vertex (quartet) ground-state energy** (γ-5 step 1526):
`singleClusterGSEnergyS 3 205 = -126485/4 = -S(1+zS)` for `S = 205/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredfive :
    singleClusterGSEnergyS 3 205 = (-126485 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-205/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1526):
`singleClusterMaxEnergyS 3 205 = 126075/4 = zS²` for `S = 205/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredfive :
    singleClusterMaxEnergyS 3 205 = (126075 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-205/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1527):
`singleClusterGSEnergyS 4 205 = -84255/2 = -S(1+zS)` for `S = 205/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredfive :
    singleClusterGSEnergyS 4 205 = (-84255 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-205/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1527):
`singleClusterMaxEnergyS 4 205 = 42025 = zS²` for `S = 205/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredfive :
    singleClusterMaxEnergyS 4 205 = (42025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-205/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1528):
`singleClusterGSEnergyS 5 205 = -210535/4 = -S(1+zS)` for `S = 205/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredfive :
    singleClusterGSEnergyS 5 205 = (-210535 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-205/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1528):
`singleClusterMaxEnergyS 5 205 = 210125/4 = zS²` for `S = 205/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredfive :
    singleClusterMaxEnergyS 5 205 = (210125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-205/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1529):
`singleClusterGSEnergyS 6 205 = -63140 = -S(1+zS)` for `S = 205/2, z = 6`. Closes spin-205/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredfive :
    singleClusterGSEnergyS 6 205 = (-63140 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-205/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1529):
`singleClusterMaxEnergyS 6 205 = 126075/2 = zS²` for `S = 205/2, z = 6`. Closes spin-205/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredfive :
    singleClusterMaxEnergyS 6 205 = (126075 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103 2-vertex (dimer) ground-state energy** (γ-5 step 1530):
`singleClusterGSEnergyS 1 206 = -10712 = -S(S+1)` for `S = 103, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredsix :
    singleClusterGSEnergyS 1 206 = (-10712 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1530):
`singleClusterMaxEnergyS 1 206 = 10609 = S²` for `S = 103, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredsix :
    singleClusterMaxEnergyS 1 206 = (10609 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103 3-vertex (trimer) ground-state energy** (γ-5 step 1531):
`singleClusterGSEnergyS 2 206 = -21321 = -S(1+zS)` for `S = 103, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredsix :
    singleClusterGSEnergyS 2 206 = (-21321 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1531):
`singleClusterMaxEnergyS 2 206 = 21218 = zS²` for `S = 103, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredsix :
    singleClusterMaxEnergyS 2 206 = (21218 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103 4-vertex (quartet) ground-state energy** (γ-5 step 1532):
`singleClusterGSEnergyS 3 206 = -31930 = -S(1+zS)` for `S = 103, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredsix :
    singleClusterGSEnergyS 3 206 = (-31930 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1532):
`singleClusterMaxEnergyS 3 206 = 31827 = zS²` for `S = 103, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredsix :
    singleClusterMaxEnergyS 3 206 = (31827 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103 5-vertex (pentamer) ground-state energy** (γ-5 step 1533):
`singleClusterGSEnergyS 4 206 = -42539 = -S(1+zS)` for `S = 103, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredsix :
    singleClusterGSEnergyS 4 206 = (-42539 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1533):
`singleClusterMaxEnergyS 4 206 = 42436 = zS²` for `S = 103, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredsix :
    singleClusterMaxEnergyS 4 206 = (42436 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103 6-vertex (hexamer) ground-state energy** (γ-5 step 1534):
`singleClusterGSEnergyS 5 206 = -53148 = -S(1+zS)` for `S = 103, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredsix :
    singleClusterGSEnergyS 5 206 = (-53148 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1534):
`singleClusterMaxEnergyS 5 206 = 53045 = zS²` for `S = 103, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredsix :
    singleClusterMaxEnergyS 5 206 = (53045 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-103 7-vertex (heptamer) ground-state energy** (γ-5 step 1535):
`singleClusterGSEnergyS 6 206 = -63757 = -S(1+zS)` for `S = 103, z = 6`. Closes spin-103 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredsix :
    singleClusterGSEnergyS 6 206 = (-63757 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-103 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1535):
`singleClusterMaxEnergyS 6 206 = 63654 = zS²` for `S = 103, z = 6`. Closes spin-103 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredsix :
    singleClusterMaxEnergyS 6 206 = (63654 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-207/2 2-vertex (dimer) ground-state energy** (γ-5 step 1536):
`singleClusterGSEnergyS 1 207 = -43263/4 = -S(S+1)` for `S = 207/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredseven :
    singleClusterGSEnergyS 1 207 = (-43263 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-207/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1536):
`singleClusterMaxEnergyS 1 207 = 42849/4 = S²` for `S = 207/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredseven :
    singleClusterMaxEnergyS 1 207 = (42849 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-207/2 3-vertex (trimer) ground-state energy** (γ-5 step 1537):
`singleClusterGSEnergyS 2 207 = -21528 = -S(1+zS)` for `S = 207/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredseven :
    singleClusterGSEnergyS 2 207 = (-21528 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-207/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1537):
`singleClusterMaxEnergyS 2 207 = 42849/2 = zS²` for `S = 207/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredseven :
    singleClusterMaxEnergyS 2 207 = (42849 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-207/2 4-vertex (quartet) ground-state energy** (γ-5 step 1538):
`singleClusterGSEnergyS 3 207 = -128961/4 = -S(1+zS)` for `S = 207/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredseven :
    singleClusterGSEnergyS 3 207 = (-128961 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-207/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1538):
`singleClusterMaxEnergyS 3 207 = 128547/4 = zS²` for `S = 207/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredseven :
    singleClusterMaxEnergyS 3 207 = (128547 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-207/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1539):
`singleClusterGSEnergyS 4 207 = -85905/2 = -S(1+zS)` for `S = 207/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredseven :
    singleClusterGSEnergyS 4 207 = (-85905 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-207/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1539):
`singleClusterMaxEnergyS 4 207 = 42849 = zS²` for `S = 207/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredseven :
    singleClusterMaxEnergyS 4 207 = (42849 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-207/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1540):
`singleClusterGSEnergyS 5 207 = -214659/4 = -S(1+zS)` for `S = 207/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredseven :
    singleClusterGSEnergyS 5 207 = (-214659 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-207/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1540):
`singleClusterMaxEnergyS 5 207 = 214245/4 = zS²` for `S = 207/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredseven :
    singleClusterMaxEnergyS 5 207 = (214245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-207/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1541):
`singleClusterGSEnergyS 6 207 = -64377 = -S(1+zS)` for `S = 207/2, z = 6`. Closes spin-207/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredseven :
    singleClusterGSEnergyS 6 207 = (-64377 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-207/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1541):
`singleClusterMaxEnergyS 6 207 = 128547/2 = zS²` for `S = 207/2, z = 6`. Closes spin-207/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredseven :
    singleClusterMaxEnergyS 6 207 = (128547 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-104 2-vertex (dimer) ground-state energy** (γ-5 step 1542):
`singleClusterGSEnergyS 1 208 = -10920 = -S(S+1)` for `S = 104, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredeight :
    singleClusterGSEnergyS 1 208 = (-10920 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-104 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1542):
`singleClusterMaxEnergyS 1 208 = 10816 = S²` for `S = 104, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredeight :
    singleClusterMaxEnergyS 1 208 = (10816 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-104 3-vertex (trimer) ground-state energy** (γ-5 step 1543):
`singleClusterGSEnergyS 2 208 = -21736 = -S(1+zS)` for `S = 104, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredeight :
    singleClusterGSEnergyS 2 208 = (-21736 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-104 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1543):
`singleClusterMaxEnergyS 2 208 = 21632 = zS²` for `S = 104, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredeight :
    singleClusterMaxEnergyS 2 208 = (21632 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-104 4-vertex (quartet) ground-state energy** (γ-5 step 1544):
`singleClusterGSEnergyS 3 208 = -32552 = -S(1+zS)` for `S = 104, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredeight :
    singleClusterGSEnergyS 3 208 = (-32552 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-104 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1544):
`singleClusterMaxEnergyS 3 208 = 32448 = zS²` for `S = 104, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredeight :
    singleClusterMaxEnergyS 3 208 = (32448 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-104 5-vertex (pentamer) ground-state energy** (γ-5 step 1545):
`singleClusterGSEnergyS 4 208 = -43368 = -S(1+zS)` for `S = 104, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredeight :
    singleClusterGSEnergyS 4 208 = (-43368 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-104 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1545):
`singleClusterMaxEnergyS 4 208 = 43264 = zS²` for `S = 104, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredeight :
    singleClusterMaxEnergyS 4 208 = (43264 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-104 6-vertex (hexamer) ground-state energy** (γ-5 step 1546):
`singleClusterGSEnergyS 5 208 = -54184 = -S(1+zS)` for `S = 104, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredeight :
    singleClusterGSEnergyS 5 208 = (-54184 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-104 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1546):
`singleClusterMaxEnergyS 5 208 = 54080 = zS²` for `S = 104, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredeight :
    singleClusterMaxEnergyS 5 208 = (54080 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-104 7-vertex (heptamer) ground-state energy** (γ-5 step 1547):
`singleClusterGSEnergyS 6 208 = -65000 = -S(1+zS)` for `S = 104, z = 6`. Closes spin-104 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredeight :
    singleClusterGSEnergyS 6 208 = (-65000 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-104 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1547):
`singleClusterMaxEnergyS 6 208 = 64896 = zS²` for `S = 104, z = 6`. Closes spin-104 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredeight :
    singleClusterMaxEnergyS 6 208 = (64896 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-209/2 2-vertex (dimer) ground-state energy** (γ-5 step 1548):
`singleClusterGSEnergyS 1 209 = -44099/4 = -S(S+1)` for `S = 209/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundrednine :
    singleClusterGSEnergyS 1 209 = (-44099 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-209/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1548):
`singleClusterMaxEnergyS 1 209 = 43681/4 = S²` for `S = 209/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundrednine :
    singleClusterMaxEnergyS 1 209 = (43681 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-209/2 3-vertex (trimer) ground-state energy** (γ-5 step 1549):
`singleClusterGSEnergyS 2 209 = -21945 = -S(1+zS)` for `S = 209/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundrednine :
    singleClusterGSEnergyS 2 209 = (-21945 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-209/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1549):
`singleClusterMaxEnergyS 2 209 = 43681/2 = zS²` for `S = 209/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundrednine :
    singleClusterMaxEnergyS 2 209 = (43681 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-209/2 4-vertex (quartet) ground-state energy** (γ-5 step 1550):
`singleClusterGSEnergyS 3 209 = -131461/4 = -S(1+zS)` for `S = 209/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundrednine :
    singleClusterGSEnergyS 3 209 = (-131461 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-209/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1550):
`singleClusterMaxEnergyS 3 209 = 131043/4 = zS²` for `S = 209/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundrednine :
    singleClusterMaxEnergyS 3 209 = (131043 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-209/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1551):
`singleClusterGSEnergyS 4 209 = -87571/2 = -S(1+zS)` for `S = 209/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundrednine :
    singleClusterGSEnergyS 4 209 = (-87571 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-209/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1551):
`singleClusterMaxEnergyS 4 209 = 43681 = zS²` for `S = 209/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundrednine :
    singleClusterMaxEnergyS 4 209 = (43681 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-209/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1552):
`singleClusterGSEnergyS 5 209 = -218823/4 = -S(1+zS)` for `S = 209/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundrednine :
    singleClusterGSEnergyS 5 209 = (-218823 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-209/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1552):
`singleClusterMaxEnergyS 5 209 = 218405/4 = zS²` for `S = 209/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundrednine :
    singleClusterMaxEnergyS 5 209 = (218405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-209/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1553):
`singleClusterGSEnergyS 6 209 = -65626 = -S(1+zS)` for `S = 209/2, z = 6`. Closes spin-209/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundrednine :
    singleClusterGSEnergyS 6 209 = (-65626 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-209/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1553):
`singleClusterMaxEnergyS 6 209 = 131043/2 = zS²` for `S = 209/2, z = 6`. Closes spin-209/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundrednine :
    singleClusterMaxEnergyS 6 209 = (131043 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105 2-vertex (dimer) ground-state energy** (γ-5 step 1554):
`singleClusterGSEnergyS 1 210 = -11130 = -S(S+1)` for `S = 105, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredten :
    singleClusterGSEnergyS 1 210 = (-11130 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1554):
`singleClusterMaxEnergyS 1 210 = 11025 = S²` for `S = 105, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredten :
    singleClusterMaxEnergyS 1 210 = (11025 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105 3-vertex (trimer) ground-state energy** (γ-5 step 1555):
`singleClusterGSEnergyS 2 210 = -22155 = -S(1+zS)` for `S = 105, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredten :
    singleClusterGSEnergyS 2 210 = (-22155 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1555):
`singleClusterMaxEnergyS 2 210 = 22050 = zS²` for `S = 105, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredten :
    singleClusterMaxEnergyS 2 210 = (22050 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105 4-vertex (quartet) ground-state energy** (γ-5 step 1556):
`singleClusterGSEnergyS 3 210 = -33180 = -S(1+zS)` for `S = 105, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredten :
    singleClusterGSEnergyS 3 210 = (-33180 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1556):
`singleClusterMaxEnergyS 3 210 = 33075 = zS²` for `S = 105, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredten :
    singleClusterMaxEnergyS 3 210 = (33075 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105 5-vertex (pentamer) ground-state energy** (γ-5 step 1557):
`singleClusterGSEnergyS 4 210 = -44205 = -S(1+zS)` for `S = 105, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredten :
    singleClusterGSEnergyS 4 210 = (-44205 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1557):
`singleClusterMaxEnergyS 4 210 = 44100 = zS²` for `S = 105, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredten :
    singleClusterMaxEnergyS 4 210 = (44100 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105 6-vertex (hexamer) ground-state energy** (γ-5 step 1558):
`singleClusterGSEnergyS 5 210 = -55230 = -S(1+zS)` for `S = 105, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredten :
    singleClusterGSEnergyS 5 210 = (-55230 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1558):
`singleClusterMaxEnergyS 5 210 = 55125 = zS²` for `S = 105, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredten :
    singleClusterMaxEnergyS 5 210 = (55125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-105 7-vertex (heptamer) ground-state energy** (γ-5 step 1559):
`singleClusterGSEnergyS 6 210 = -66255 = -S(1+zS)` for `S = 105, z = 6`. Closes spin-105 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredten :
    singleClusterGSEnergyS 6 210 = (-66255 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-105 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1559):
`singleClusterMaxEnergyS 6 210 = 66150 = zS²` for `S = 105, z = 6`. Closes spin-105 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredten :
    singleClusterMaxEnergyS 6 210 = (66150 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-211/2 2-vertex (dimer) ground-state energy** (γ-5 step 1560):
`singleClusterGSEnergyS 1 211 = -44943/4 = -S(S+1)` for `S = 211/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredeleven :
    singleClusterGSEnergyS 1 211 = (-44943 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-211/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1560):
`singleClusterMaxEnergyS 1 211 = 44521/4 = S²` for `S = 211/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredeleven :
    singleClusterMaxEnergyS 1 211 = (44521 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-211/2 3-vertex (trimer) ground-state energy** (γ-5 step 1561):
`singleClusterGSEnergyS 2 211 = -22366 = -S(1+zS)` for `S = 211/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredeleven :
    singleClusterGSEnergyS 2 211 = (-22366 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-211/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1561):
`singleClusterMaxEnergyS 2 211 = 44521/2 = zS²` for `S = 211/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredeleven :
    singleClusterMaxEnergyS 2 211 = (44521 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-211/2 4-vertex (quartet) ground-state energy** (γ-5 step 1562):
`singleClusterGSEnergyS 3 211 = -133985/4 = -S(1+zS)` for `S = 211/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredeleven :
    singleClusterGSEnergyS 3 211 = (-133985 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-211/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1562):
`singleClusterMaxEnergyS 3 211 = 133563/4 = zS²` for `S = 211/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredeleven :
    singleClusterMaxEnergyS 3 211 = (133563 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-211/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1563):
`singleClusterGSEnergyS 4 211 = -89253/2 = -S(1+zS)` for `S = 211/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredeleven :
    singleClusterGSEnergyS 4 211 = (-89253 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-211/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1563):
`singleClusterMaxEnergyS 4 211 = 44521 = zS²` for `S = 211/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredeleven :
    singleClusterMaxEnergyS 4 211 = (44521 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-211/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1564):
`singleClusterGSEnergyS 5 211 = -223027/4 = -S(1+zS)` for `S = 211/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredeleven :
    singleClusterGSEnergyS 5 211 = (-223027 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-211/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1564):
`singleClusterMaxEnergyS 5 211 = 222605/4 = zS²` for `S = 211/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredeleven :
    singleClusterMaxEnergyS 5 211 = (222605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-211/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1565):
`singleClusterGSEnergyS 6 211 = -66887 = -S(1+zS)` for `S = 211/2, z = 6`. Closes spin-211/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredeleven :
    singleClusterGSEnergyS 6 211 = (-66887 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-211/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1565):
`singleClusterMaxEnergyS 6 211 = 133563/2 = zS²` for `S = 211/2, z = 6`. Closes spin-211/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredeleven :
    singleClusterMaxEnergyS 6 211 = (133563 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-106 2-vertex (dimer) ground-state energy** (γ-5 step 1566):
`singleClusterGSEnergyS 1 212 = -11342 = -S(S+1)` for `S = 106, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwelve :
    singleClusterGSEnergyS 1 212 = (-11342 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-106 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1566):
`singleClusterMaxEnergyS 1 212 = 11236 = S²` for `S = 106, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwelve :
    singleClusterMaxEnergyS 1 212 = (11236 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-106 3-vertex (trimer) ground-state energy** (γ-5 step 1567):
`singleClusterGSEnergyS 2 212 = -22578 = -S(1+zS)` for `S = 106, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwelve :
    singleClusterGSEnergyS 2 212 = (-22578 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-106 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1567):
`singleClusterMaxEnergyS 2 212 = 22472 = zS²` for `S = 106, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwelve :
    singleClusterMaxEnergyS 2 212 = (22472 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-106 4-vertex (quartet) ground-state energy** (γ-5 step 1568):
`singleClusterGSEnergyS 3 212 = -33814 = -S(1+zS)` for `S = 106, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwelve :
    singleClusterGSEnergyS 3 212 = (-33814 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-106 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1568):
`singleClusterMaxEnergyS 3 212 = 33708 = zS²` for `S = 106, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwelve :
    singleClusterMaxEnergyS 3 212 = (33708 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-106 5-vertex (pentamer) ground-state energy** (γ-5 step 1569):
`singleClusterGSEnergyS 4 212 = -45050 = -S(1+zS)` for `S = 106, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwelve :
    singleClusterGSEnergyS 4 212 = (-45050 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-106 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1569):
`singleClusterMaxEnergyS 4 212 = 44944 = zS²` for `S = 106, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwelve :
    singleClusterMaxEnergyS 4 212 = (44944 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-106 6-vertex (hexamer) ground-state energy** (γ-5 step 1570):
`singleClusterGSEnergyS 5 212 = -56286 = -S(1+zS)` for `S = 106, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwelve :
    singleClusterGSEnergyS 5 212 = (-56286 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-106 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1570):
`singleClusterMaxEnergyS 5 212 = 56180 = zS²` for `S = 106, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwelve :
    singleClusterMaxEnergyS 5 212 = (56180 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-106 7-vertex (heptamer) ground-state energy** (γ-5 step 1571):
`singleClusterGSEnergyS 6 212 = -67522 = -S(1+zS)` for `S = 106, z = 6`. Closes spin-106 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwelve :
    singleClusterGSEnergyS 6 212 = (-67522 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-106 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1571):
`singleClusterMaxEnergyS 6 212 = 67416 = zS²` for `S = 106, z = 6`. Closes spin-106 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwelve :
    singleClusterMaxEnergyS 6 212 = (67416 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-213/2 2-vertex (dimer) ground-state energy** (γ-5 step 1572):
`singleClusterGSEnergyS 1 213 = -45795/4 = -S(S+1)` for `S = 213/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredthirteen :
    singleClusterGSEnergyS 1 213 = (-45795 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-213/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1572):
`singleClusterMaxEnergyS 1 213 = 45369/4 = S²` for `S = 213/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredthirteen :
    singleClusterMaxEnergyS 1 213 = (45369 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-213/2 3-vertex (trimer) ground-state energy** (γ-5 step 1573):
`singleClusterGSEnergyS 2 213 = -22791 = -S(1+zS)` for `S = 213/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredthirteen :
    singleClusterGSEnergyS 2 213 = (-22791 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-213/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1573):
`singleClusterMaxEnergyS 2 213 = 45369/2 = zS²` for `S = 213/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredthirteen :
    singleClusterMaxEnergyS 2 213 = (45369 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-213/2 4-vertex (quartet) ground-state energy** (γ-5 step 1574):
`singleClusterGSEnergyS 3 213 = -136533/4 = -S(1+zS)` for `S = 213/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredthirteen :
    singleClusterGSEnergyS 3 213 = (-136533 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-213/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1574):
`singleClusterMaxEnergyS 3 213 = 136107/4 = zS²` for `S = 213/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredthirteen :
    singleClusterMaxEnergyS 3 213 = (136107 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-213/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1575):
`singleClusterGSEnergyS 4 213 = -90951/2 = -S(1+zS)` for `S = 213/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredthirteen :
    singleClusterGSEnergyS 4 213 = (-90951 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-213/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1575):
`singleClusterMaxEnergyS 4 213 = 45369 = zS²` for `S = 213/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredthirteen :
    singleClusterMaxEnergyS 4 213 = (45369 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-213/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1576):
`singleClusterGSEnergyS 5 213 = -227271/4 = -S(1+zS)` for `S = 213/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredthirteen :
    singleClusterGSEnergyS 5 213 = (-227271 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-213/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1576):
`singleClusterMaxEnergyS 5 213 = 226845/4 = zS²` for `S = 213/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredthirteen :
    singleClusterMaxEnergyS 5 213 = (226845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-213/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1577):
`singleClusterGSEnergyS 6 213 = -68160 = -S(1+zS)` for `S = 213/2, z = 6`. Closes spin-213/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredthirteen :
    singleClusterGSEnergyS 6 213 = (-68160 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-213/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1577):
`singleClusterMaxEnergyS 6 213 = 136107/2 = zS²` for `S = 213/2, z = 6`. Closes spin-213/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredthirteen :
    singleClusterMaxEnergyS 6 213 = (136107 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107 2-vertex (dimer) ground-state energy** (γ-5 step 1578):
`singleClusterGSEnergyS 1 214 = -11556 = -S(S+1)` for `S = 107, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredfourteen :
    singleClusterGSEnergyS 1 214 = (-11556 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1578):
`singleClusterMaxEnergyS 1 214 = 11449 = S²` for `S = 107, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredfourteen :
    singleClusterMaxEnergyS 1 214 = (11449 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107 3-vertex (trimer) ground-state energy** (γ-5 step 1579):
`singleClusterGSEnergyS 2 214 = -23005 = -S(1+zS)` for `S = 107, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredfourteen :
    singleClusterGSEnergyS 2 214 = (-23005 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1579):
`singleClusterMaxEnergyS 2 214 = 22898 = zS²` for `S = 107, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredfourteen :
    singleClusterMaxEnergyS 2 214 = (22898 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107 4-vertex (quartet) ground-state energy** (γ-5 step 1580):
`singleClusterGSEnergyS 3 214 = -34454 = -S(1+zS)` for `S = 107, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredfourteen :
    singleClusterGSEnergyS 3 214 = (-34454 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1580):
`singleClusterMaxEnergyS 3 214 = 34347 = zS²` for `S = 107, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredfourteen :
    singleClusterMaxEnergyS 3 214 = (34347 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107 5-vertex (pentamer) ground-state energy** (γ-5 step 1581):
`singleClusterGSEnergyS 4 214 = -45903 = -S(1+zS)` for `S = 107, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredfourteen :
    singleClusterGSEnergyS 4 214 = (-45903 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1581):
`singleClusterMaxEnergyS 4 214 = 45796 = zS²` for `S = 107, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredfourteen :
    singleClusterMaxEnergyS 4 214 = (45796 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107 6-vertex (hexamer) ground-state energy** (γ-5 step 1582):
`singleClusterGSEnergyS 5 214 = -57352 = -S(1+zS)` for `S = 107, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredfourteen :
    singleClusterGSEnergyS 5 214 = (-57352 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1582):
`singleClusterMaxEnergyS 5 214 = 57245 = zS²` for `S = 107, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredfourteen :
    singleClusterMaxEnergyS 5 214 = (57245 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-107 7-vertex (heptamer) ground-state energy** (γ-5 step 1583):
`singleClusterGSEnergyS 6 214 = -68801 = -S(1+zS)` for `S = 107, z = 6`. Closes spin-107 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredfourteen :
    singleClusterGSEnergyS 6 214 = (-68801 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-107 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1583):
`singleClusterMaxEnergyS 6 214 = 68694 = zS²` for `S = 107, z = 6`. Closes spin-107 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredfourteen :
    singleClusterMaxEnergyS 6 214 = (68694 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-215/2 2-vertex (dimer) ground-state energy** (γ-5 step 1584):
`singleClusterGSEnergyS 1 215 = -46655/4 = -S(S+1)` for `S = 215/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredfifteen :
    singleClusterGSEnergyS 1 215 = (-46655 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-215/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1584):
`singleClusterMaxEnergyS 1 215 = 46225/4 = S²` for `S = 215/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredfifteen :
    singleClusterMaxEnergyS 1 215 = (46225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-215/2 3-vertex (trimer) ground-state energy** (γ-5 step 1585):
`singleClusterGSEnergyS 2 215 = -23220 = -S(1+zS)` for `S = 215/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredfifteen :
    singleClusterGSEnergyS 2 215 = (-23220 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-215/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1585):
`singleClusterMaxEnergyS 2 215 = 46225/2 = zS²` for `S = 215/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredfifteen :
    singleClusterMaxEnergyS 2 215 = (46225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-215/2 4-vertex (quartet) ground-state energy** (γ-5 step 1586):
`singleClusterGSEnergyS 3 215 = -139105/4 = -S(1+zS)` for `S = 215/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredfifteen :
    singleClusterGSEnergyS 3 215 = (-139105 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-215/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1586):
`singleClusterMaxEnergyS 3 215 = 138675/4 = zS²` for `S = 215/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredfifteen :
    singleClusterMaxEnergyS 3 215 = (138675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-215/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1587):
`singleClusterGSEnergyS 4 215 = -92665/2 = -S(1+zS)` for `S = 215/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredfifteen :
    singleClusterGSEnergyS 4 215 = (-92665 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-215/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1587):
`singleClusterMaxEnergyS 4 215 = 46225 = zS²` for `S = 215/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredfifteen :
    singleClusterMaxEnergyS 4 215 = (46225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-215/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1588):
`singleClusterGSEnergyS 5 215 = -231555/4 = -S(1+zS)` for `S = 215/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredfifteen :
    singleClusterGSEnergyS 5 215 = (-231555 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-215/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1588):
`singleClusterMaxEnergyS 5 215 = 231125/4 = zS²` for `S = 215/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredfifteen :
    singleClusterMaxEnergyS 5 215 = (231125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-215/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1589):
`singleClusterGSEnergyS 6 215 = -69445 = -S(1+zS)` for `S = 215/2, z = 6`. Closes spin-215/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredfifteen :
    singleClusterGSEnergyS 6 215 = (-69445 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-215/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1589):
`singleClusterMaxEnergyS 6 215 = 138675/2 = zS²` for `S = 215/2, z = 6`. Closes spin-215/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredfifteen :
    singleClusterMaxEnergyS 6 215 = (138675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-108 2-vertex (dimer) ground-state energy** (γ-5 step 1590):
`singleClusterGSEnergyS 1 216 = -11772 = -S(S+1)` for `S = 108, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredsixteen :
    singleClusterGSEnergyS 1 216 = (-11772 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-108 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1590):
`singleClusterMaxEnergyS 1 216 = 11664 = S²` for `S = 108, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredsixteen :
    singleClusterMaxEnergyS 1 216 = (11664 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-108 3-vertex (trimer) ground-state energy** (γ-5 step 1591):
`singleClusterGSEnergyS 2 216 = -23436 = -S(1+zS)` for `S = 108, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredsixteen :
    singleClusterGSEnergyS 2 216 = (-23436 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-108 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1591):
`singleClusterMaxEnergyS 2 216 = 23328 = zS²` for `S = 108, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredsixteen :
    singleClusterMaxEnergyS 2 216 = (23328 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-108 4-vertex (quartet) ground-state energy** (γ-5 step 1592):
`singleClusterGSEnergyS 3 216 = -35100 = -S(1+zS)` for `S = 108, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredsixteen :
    singleClusterGSEnergyS 3 216 = (-35100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-108 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1592):
`singleClusterMaxEnergyS 3 216 = 34992 = zS²` for `S = 108, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredsixteen :
    singleClusterMaxEnergyS 3 216 = (34992 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-108 5-vertex (pentamer) ground-state energy** (γ-5 step 1593):
`singleClusterGSEnergyS 4 216 = -46764 = -S(1+zS)` for `S = 108, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredsixteen :
    singleClusterGSEnergyS 4 216 = (-46764 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-108 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1593):
`singleClusterMaxEnergyS 4 216 = 46656 = zS²` for `S = 108, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredsixteen :
    singleClusterMaxEnergyS 4 216 = (46656 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-108 6-vertex (hexamer) ground-state energy** (γ-5 step 1594):
`singleClusterGSEnergyS 5 216 = -58428 = -S(1+zS)` for `S = 108, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredsixteen :
    singleClusterGSEnergyS 5 216 = (-58428 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-108 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1594):
`singleClusterMaxEnergyS 5 216 = 58320 = zS²` for `S = 108, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredsixteen :
    singleClusterMaxEnergyS 5 216 = (58320 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-108 7-vertex (heptamer) ground-state energy** (γ-5 step 1595):
`singleClusterGSEnergyS 6 216 = -70092 = -S(1+zS)` for `S = 108, z = 6`. Closes spin-108 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredsixteen :
    singleClusterGSEnergyS 6 216 = (-70092 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-108 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1595):
`singleClusterMaxEnergyS 6 216 = 69984 = zS²` for `S = 108, z = 6`. Closes spin-108 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredsixteen :
    singleClusterMaxEnergyS 6 216 = (69984 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-217/2 2-vertex (dimer) ground-state energy** (γ-5 step 1596):
`singleClusterGSEnergyS 1 217 = -47523/4 = -S(S+1)` for `S = 217/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredseventeen :
    singleClusterGSEnergyS 1 217 = (-47523 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-217/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1596):
`singleClusterMaxEnergyS 1 217 = 47089/4 = S²` for `S = 217/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredseventeen :
    singleClusterMaxEnergyS 1 217 = (47089 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-217/2 3-vertex (trimer) ground-state energy** (γ-5 step 1597):
`singleClusterGSEnergyS 2 217 = -23653 = -S(1+zS)` for `S = 217/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredseventeen :
    singleClusterGSEnergyS 2 217 = (-23653 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-217/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1597):
`singleClusterMaxEnergyS 2 217 = 47089/2 = zS²` for `S = 217/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredseventeen :
    singleClusterMaxEnergyS 2 217 = (47089 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-217/2 4-vertex (quartet) ground-state energy** (γ-5 step 1598):
`singleClusterGSEnergyS 3 217 = -141701/4 = -S(1+zS)` for `S = 217/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredseventeen :
    singleClusterGSEnergyS 3 217 = (-141701 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-217/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1598):
`singleClusterMaxEnergyS 3 217 = 141267/4 = zS²` for `S = 217/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredseventeen :
    singleClusterMaxEnergyS 3 217 = (141267 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-217/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1599):
`singleClusterGSEnergyS 4 217 = -94395/2 = -S(1+zS)` for `S = 217/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredseventeen :
    singleClusterGSEnergyS 4 217 = (-94395 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-217/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1599):
`singleClusterMaxEnergyS 4 217 = 47089 = zS²` for `S = 217/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredseventeen :
    singleClusterMaxEnergyS 4 217 = (47089 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-217/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1600 milestone):
`singleClusterGSEnergyS 5 217 = -235879/4 = -S(1+zS)` for `S = 217/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredseventeen :
    singleClusterGSEnergyS 5 217 = (-235879 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-217/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1600 milestone):
`singleClusterMaxEnergyS 5 217 = 235445/4 = zS²` for `S = 217/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredseventeen :
    singleClusterMaxEnergyS 5 217 = (235445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-217/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1601):
`singleClusterGSEnergyS 6 217 = -70742 = -S(1+zS)` for `S = 217/2, z = 6`. Closes spin-217/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredseventeen :
    singleClusterGSEnergyS 6 217 = (-70742 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-217/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1601):
`singleClusterMaxEnergyS 6 217 = 141267/2 = zS²` for `S = 217/2, z = 6`. Closes spin-217/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredseventeen :
    singleClusterMaxEnergyS 6 217 = (141267 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109 2-vertex (dimer) ground-state energy** (γ-5 step 1602):
`singleClusterGSEnergyS 1 218 = -11990 = -S(S+1)` for `S = 109, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredeighteen :
    singleClusterGSEnergyS 1 218 = (-11990 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1602):
`singleClusterMaxEnergyS 1 218 = 11881 = S²` for `S = 109, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredeighteen :
    singleClusterMaxEnergyS 1 218 = (11881 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109 3-vertex (trimer) ground-state energy** (γ-5 step 1603):
`singleClusterGSEnergyS 2 218 = -23871 = -S(1+zS)` for `S = 109, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredeighteen :
    singleClusterGSEnergyS 2 218 = (-23871 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1603):
`singleClusterMaxEnergyS 2 218 = 23762 = zS²` for `S = 109, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredeighteen :
    singleClusterMaxEnergyS 2 218 = (23762 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109 4-vertex (quartet) ground-state energy** (γ-5 step 1604):
`singleClusterGSEnergyS 3 218 = -35752 = -S(1+zS)` for `S = 109, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredeighteen :
    singleClusterGSEnergyS 3 218 = (-35752 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1604):
`singleClusterMaxEnergyS 3 218 = 35643 = zS²` for `S = 109, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredeighteen :
    singleClusterMaxEnergyS 3 218 = (35643 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109 5-vertex (pentamer) ground-state energy** (γ-5 step 1605):
`singleClusterGSEnergyS 4 218 = -47633 = -S(1+zS)` for `S = 109, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredeighteen :
    singleClusterGSEnergyS 4 218 = (-47633 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1605):
`singleClusterMaxEnergyS 4 218 = 47524 = zS²` for `S = 109, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredeighteen :
    singleClusterMaxEnergyS 4 218 = (47524 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109 6-vertex (hexamer) ground-state energy** (γ-5 step 1606):
`singleClusterGSEnergyS 5 218 = -59514 = -S(1+zS)` for `S = 109, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredeighteen :
    singleClusterGSEnergyS 5 218 = (-59514 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1606):
`singleClusterMaxEnergyS 5 218 = 59405 = zS²` for `S = 109, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredeighteen :
    singleClusterMaxEnergyS 5 218 = (59405 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-109 7-vertex (heptamer) ground-state energy** (γ-5 step 1607):
`singleClusterGSEnergyS 6 218 = -71395 = -S(1+zS)` for `S = 109, z = 6`. Closes spin-109 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredeighteen :
    singleClusterGSEnergyS 6 218 = (-71395 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-109 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1607):
`singleClusterMaxEnergyS 6 218 = 71286 = zS²` for `S = 109, z = 6`. Closes spin-109 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredeighteen :
    singleClusterMaxEnergyS 6 218 = (71286 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-219/2 dimer ground-state energy** (γ-5 step 1608):
`singleClusterGSEnergyS 1 219 = -48399/4 = -S(S+1)` for `S = 219/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundrednineteen :
    singleClusterGSEnergyS 1 219 = (-48399 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-219/2 dimer maximum-Casimir-sector energy** (γ-5 step 1608):
`singleClusterMaxEnergyS 1 219 = 47961/4 = S²` for `S = 219/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundrednineteen :
    singleClusterMaxEnergyS 1 219 = (47961 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-219/2 trimer ground-state energy** (γ-5 step 1609):
`singleClusterGSEnergyS 2 219 = -24090 = -S(1+zS)` for `S = 219/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundrednineteen :
    singleClusterGSEnergyS 2 219 = (-24090 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-219/2 trimer maximum-Casimir-sector energy** (γ-5 step 1609):
`singleClusterMaxEnergyS 2 219 = 47961/2 = zS²` for `S = 219/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundrednineteen :
    singleClusterMaxEnergyS 2 219 = (47961 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-219/2 quartet ground-state energy** (γ-5 step 1610):
`singleClusterGSEnergyS 3 219 = -144321/4 = -S(1+zS)` for `S = 219/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundrednineteen :
    singleClusterGSEnergyS 3 219 = (-144321 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-219/2 quartet maximum-Casimir-sector energy** (γ-5 step 1610):
`singleClusterMaxEnergyS 3 219 = 143883/4 = zS²` for `S = 219/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundrednineteen :
    singleClusterMaxEnergyS 3 219 = (143883 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
