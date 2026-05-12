/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Omega-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 166`
(spin `S = N/2 ≥ 83`). The `N = 1..28` specialisations live in
`SingleClusterHamiltonianNumerics.lean`, the `N = 29..38` in
`SingleClusterHamiltonianNumericsHigh.lean`, the `N = 39..47` in
`SingleClusterHamiltonianNumericsVeryHigh.lean`, the `N = 48..59`
in `SingleClusterHamiltonianNumericsUltraHigh.lean`, the
`N = 60..77` in `SingleClusterHamiltonianNumericsExtremeHigh.lean`,
the `N = 78..98` in `SingleClusterHamiltonianNumericsMaxHigh.lean`,
the `N = 99..115` in `SingleClusterHamiltonianNumericsHyperHigh.lean`,
the `N = 116..131` in `SingleClusterHamiltonianNumericsInfiniteHigh.lean`,
the `N = 132..148` in `SingleClusterHamiltonianNumericsTransfiniteHigh.lean`,
and the `N = 149..165` in `SingleClusterHamiltonianNumericsAbsoluteHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all eleven numerics files can elaborate
in parallel after the main file. The split from `AbsoluteHigh` to
`OmegaHigh` was introduced as the 50-PR build-performance cadence
refactor #19 when `AbsoluteHigh` reached 3213 lines / ~9.08 s user CPU
after the N=149..181 entries had been appended (see
`.self-local/docs/refactoring-plan-2026-04-22.md` §A).
-/

namespace LatticeSystem.Quantum

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

/-- **Spin-87 2-vertex (dimer) ground-state energy** (γ-5 step 1338):
`singleClusterGSEnergyS 1 174 = -7656 = -S(S+1)` for `S = 87`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventyfour :
    singleClusterGSEnergyS 1 174 = (-7656 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1338):
`singleClusterMaxEnergyS 1 174 = 7569 = S²` for `S = 87`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventyfour :
    singleClusterMaxEnergyS 1 174 = (7569 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87 3-vertex (trimer) ground-state energy** (γ-5 step 1339):
`singleClusterGSEnergyS 2 174 = -15225 = -S(1+zS)` for `S = 87, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventyfour :
    singleClusterGSEnergyS 2 174 = (-15225 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1339):
`singleClusterMaxEnergyS 2 174 = 15138 = zS²` for `S = 87, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventyfour :
    singleClusterMaxEnergyS 2 174 = (15138 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87 4-vertex (quartet) ground-state energy** (γ-5 step 1340):
`singleClusterGSEnergyS 3 174 = -22794 = -S(1+zS)` for `S = 87, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventyfour :
    singleClusterGSEnergyS 3 174 = (-22794 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1340):
`singleClusterMaxEnergyS 3 174 = 22707 = zS²` for `S = 87, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventyfour :
    singleClusterMaxEnergyS 3 174 = (22707 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87 5-vertex (pentamer) ground-state energy** (γ-5 step 1341):
`singleClusterGSEnergyS 4 174 = -30363 = -S(1+zS)` for `S = 87, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventyfour :
    singleClusterGSEnergyS 4 174 = (-30363 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1341):
`singleClusterMaxEnergyS 4 174 = 30276 = zS²` for `S = 87, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventyfour :
    singleClusterMaxEnergyS 4 174 = (30276 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87 6-vertex (hexamer) ground-state energy** (γ-5 step 1342):
`singleClusterGSEnergyS 5 174 = -37932 = -S(1+zS)` for `S = 87, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventyfour :
    singleClusterGSEnergyS 5 174 = (-37932 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1342):
`singleClusterMaxEnergyS 5 174 = 37845 = zS²` for `S = 87, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventyfour :
    singleClusterMaxEnergyS 5 174 = (37845 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-87 7-vertex (heptamer) ground-state energy** (γ-5 step 1343):
`singleClusterGSEnergyS 6 174 = -45501 = -S(1+zS)` for `S = 87, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventyfour :
    singleClusterGSEnergyS 6 174 = (-45501 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-87 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1343):
`singleClusterMaxEnergyS 6 174 = 45414 = zS²` for `S = 87, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventyfour :
    singleClusterMaxEnergyS 6 174 = (45414 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-175/2 2-vertex (dimer) ground-state energy** (γ-5 step 1344):
`singleClusterGSEnergyS 1 175 = -30975/4 = -S(S+1)` for `S = 175/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventyfive :
    singleClusterGSEnergyS 1 175 = (-30975 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-175/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1344):
`singleClusterMaxEnergyS 1 175 = 30625/4 = S²` for `S = 175/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventyfive :
    singleClusterMaxEnergyS 1 175 = (30625 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-175/2 3-vertex (trimer) ground-state energy** (γ-5 step 1345):
`singleClusterGSEnergyS 2 175 = -15400 = -S(1+zS)` for `S = 175/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventyfive :
    singleClusterGSEnergyS 2 175 = (-15400 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-175/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1345):
`singleClusterMaxEnergyS 2 175 = 30625/2 = zS²` for `S = 175/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventyfive :
    singleClusterMaxEnergyS 2 175 = (30625 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-175/2 4-vertex (quartet) ground-state energy** (γ-5 step 1346):
`singleClusterGSEnergyS 3 175 = -92225/4 = -S(1+zS)` for `S = 175/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventyfive :
    singleClusterGSEnergyS 3 175 = (-92225 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-175/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1346):
`singleClusterMaxEnergyS 3 175 = 91875/4 = zS²` for `S = 175/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventyfive :
    singleClusterMaxEnergyS 3 175 = (91875 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-175/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1347):
`singleClusterGSEnergyS 4 175 = -61425/2 = -S(1+zS)` for `S = 175/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventyfive :
    singleClusterGSEnergyS 4 175 = (-61425 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-175/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1347):
`singleClusterMaxEnergyS 4 175 = 30625 = zS²` for `S = 175/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventyfive :
    singleClusterMaxEnergyS 4 175 = (30625 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-175/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1348):
`singleClusterGSEnergyS 5 175 = -153475/4 = -S(1+zS)` for `S = 175/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventyfive :
    singleClusterGSEnergyS 5 175 = (-153475 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-175/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1348):
`singleClusterMaxEnergyS 5 175 = 153125/4 = zS²` for `S = 175/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventyfive :
    singleClusterMaxEnergyS 5 175 = (153125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-175/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1349):
`singleClusterGSEnergyS 6 175 = -46025 = -S(1+zS)` for `S = 175/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventyfive :
    singleClusterGSEnergyS 6 175 = (-46025 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-175/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1349):
`singleClusterMaxEnergyS 6 175 = 91875/2 = zS²` for `S = 175/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventyfive :
    singleClusterMaxEnergyS 6 175 = (91875 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-88 2-vertex (dimer) ground-state energy** (γ-5 step 1350):
`singleClusterGSEnergyS 1 176 = -7832 = -S(S+1)` for `S = 88`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventysix :
    singleClusterGSEnergyS 1 176 = (-7832 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-88 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1350):
`singleClusterMaxEnergyS 1 176 = 7744 = S²` for `S = 88`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventysix :
    singleClusterMaxEnergyS 1 176 = (7744 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-88 3-vertex (trimer) ground-state energy** (γ-5 step 1351):
`singleClusterGSEnergyS 2 176 = -15576 = -S(1+zS)` for `S = 88, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventysix :
    singleClusterGSEnergyS 2 176 = (-15576 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-88 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1351):
`singleClusterMaxEnergyS 2 176 = 15488 = zS²` for `S = 88, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventysix :
    singleClusterMaxEnergyS 2 176 = (15488 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-88 4-vertex (quartet) ground-state energy** (γ-5 step 1352):
`singleClusterGSEnergyS 3 176 = -23320 = -S(1+zS)` for `S = 88, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventysix :
    singleClusterGSEnergyS 3 176 = (-23320 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-88 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1352):
`singleClusterMaxEnergyS 3 176 = 23232 = zS²` for `S = 88, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventysix :
    singleClusterMaxEnergyS 3 176 = (23232 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-88 5-vertex (pentamer) ground-state energy** (γ-5 step 1353):
`singleClusterGSEnergyS 4 176 = -31064 = -S(1+zS)` for `S = 88, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventysix :
    singleClusterGSEnergyS 4 176 = (-31064 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-88 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1353):
`singleClusterMaxEnergyS 4 176 = 30976 = zS²` for `S = 88, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventysix :
    singleClusterMaxEnergyS 4 176 = (30976 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-88 6-vertex (hexamer) ground-state energy** (γ-5 step 1354):
`singleClusterGSEnergyS 5 176 = -38808 = -S(1+zS)` for `S = 88, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventysix :
    singleClusterGSEnergyS 5 176 = (-38808 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-88 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1354):
`singleClusterMaxEnergyS 5 176 = 38720 = zS²` for `S = 88, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventysix :
    singleClusterMaxEnergyS 5 176 = (38720 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-88 7-vertex (heptamer) ground-state energy** (γ-5 step 1355):
`singleClusterGSEnergyS 6 176 = -46552 = -S(1+zS)` for `S = 88, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventysix :
    singleClusterGSEnergyS 6 176 = (-46552 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-88 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1355):
`singleClusterMaxEnergyS 6 176 = 46464 = zS²` for `S = 88, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventysix :
    singleClusterMaxEnergyS 6 176 = (46464 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-177/2 2-vertex (dimer) ground-state energy** (γ-5 step 1356):
`singleClusterGSEnergyS 1 177 = -31683/4 = -S(S+1)` for `S = 177/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventyseven :
    singleClusterGSEnergyS 1 177 = (-31683 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-177/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1356):
`singleClusterMaxEnergyS 1 177 = 31329/4 = S²` for `S = 177/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventyseven :
    singleClusterMaxEnergyS 1 177 = (31329 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-177/2 3-vertex (trimer) ground-state energy** (γ-5 step 1357):
`singleClusterGSEnergyS 2 177 = -15753 = -S(1+zS)` for `S = 177/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventyseven :
    singleClusterGSEnergyS 2 177 = (-15753 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-177/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1357):
`singleClusterMaxEnergyS 2 177 = 31329/2 = zS²` for `S = 177/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventyseven :
    singleClusterMaxEnergyS 2 177 = (31329 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-177/2 4-vertex (quartet) ground-state energy** (γ-5 step 1358):
`singleClusterGSEnergyS 3 177 = -94341/4 = -S(1+zS)` for `S = 177/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventyseven :
    singleClusterGSEnergyS 3 177 = (-94341 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-177/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1358):
`singleClusterMaxEnergyS 3 177 = 93987/4 = zS²` for `S = 177/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventyseven :
    singleClusterMaxEnergyS 3 177 = (93987 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-177/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1359):
`singleClusterGSEnergyS 4 177 = -62835/2 = -S(1+zS)` for `S = 177/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventyseven :
    singleClusterGSEnergyS 4 177 = (-62835 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-177/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1359):
`singleClusterMaxEnergyS 4 177 = 31329 = zS²` for `S = 177/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventyseven :
    singleClusterMaxEnergyS 4 177 = (31329 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-177/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1360):
`singleClusterGSEnergyS 5 177 = -156999/4 = -S(1+zS)` for `S = 177/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventyseven :
    singleClusterGSEnergyS 5 177 = (-156999 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-177/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1360):
`singleClusterMaxEnergyS 5 177 = 156645/4 = zS²` for `S = 177/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventyseven :
    singleClusterMaxEnergyS 5 177 = (156645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-177/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1361):
`singleClusterGSEnergyS 6 177 = -47082 = -S(1+zS)` for `S = 177/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventyseven :
    singleClusterGSEnergyS 6 177 = (-47082 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-177/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1361):
`singleClusterMaxEnergyS 6 177 = 93987/2 = zS²` for `S = 177/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventyseven :
    singleClusterMaxEnergyS 6 177 = (93987 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89 2-vertex (dimer) ground-state energy** (γ-5 step 1362):
`singleClusterGSEnergyS 1 178 = -8010 = -S(S+1)` for `S = 89`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventyeight :
    singleClusterGSEnergyS 1 178 = (-8010 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1362):
`singleClusterMaxEnergyS 1 178 = 7921 = S²` for `S = 89`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventyeight :
    singleClusterMaxEnergyS 1 178 = (7921 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89 3-vertex (trimer) ground-state energy** (γ-5 step 1363):
`singleClusterGSEnergyS 2 178 = -15931 = -S(1+zS)` for `S = 89, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventyeight :
    singleClusterGSEnergyS 2 178 = (-15931 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1363):
`singleClusterMaxEnergyS 2 178 = 15842 = zS²` for `S = 89, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventyeight :
    singleClusterMaxEnergyS 2 178 = (15842 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89 4-vertex (quartet) ground-state energy** (γ-5 step 1364):
`singleClusterGSEnergyS 3 178 = -23852 = -S(1+zS)` for `S = 89, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventyeight :
    singleClusterGSEnergyS 3 178 = (-23852 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1364):
`singleClusterMaxEnergyS 3 178 = 23763 = zS²` for `S = 89, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventyeight :
    singleClusterMaxEnergyS 3 178 = (23763 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89 5-vertex (pentamer) ground-state energy** (γ-5 step 1365):
`singleClusterGSEnergyS 4 178 = -31773 = -S(1+zS)` for `S = 89, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventyeight :
    singleClusterGSEnergyS 4 178 = (-31773 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1365):
`singleClusterMaxEnergyS 4 178 = 31684 = zS²` for `S = 89, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventyeight :
    singleClusterMaxEnergyS 4 178 = (31684 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89 6-vertex (hexamer) ground-state energy** (γ-5 step 1366):
`singleClusterGSEnergyS 5 178 = -39694 = -S(1+zS)` for `S = 89, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventyeight :
    singleClusterGSEnergyS 5 178 = (-39694 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1366):
`singleClusterMaxEnergyS 5 178 = 39605 = zS²` for `S = 89, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventyeight :
    singleClusterMaxEnergyS 5 178 = (39605 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-89 7-vertex (heptamer) ground-state energy** (γ-5 step 1367):
`singleClusterGSEnergyS 6 178 = -47615 = -S(1+zS)` for `S = 89, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventyeight :
    singleClusterGSEnergyS 6 178 = (-47615 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-89 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1367):
`singleClusterMaxEnergyS 6 178 = 47526 = zS²` for `S = 89, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventyeight :
    singleClusterMaxEnergyS 6 178 = (47526 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-179/2 2-vertex (dimer) ground-state energy** (γ-5 step 1368):
`singleClusterGSEnergyS 1 179 = -32399/4 = -S(S+1)` for `S = 179/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredseventynine :
    singleClusterGSEnergyS 1 179 = (-32399 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-179/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1368):
`singleClusterMaxEnergyS 1 179 = 32041/4 = S²` for `S = 179/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredseventynine :
    singleClusterMaxEnergyS 1 179 = (32041 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-179/2 3-vertex (trimer) ground-state energy** (γ-5 step 1369):
`singleClusterGSEnergyS 2 179 = -16110 = -S(1+zS)` for `S = 179/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredseventynine :
    singleClusterGSEnergyS 2 179 = (-16110 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-179/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1369):
`singleClusterMaxEnergyS 2 179 = 32041/2 = zS²` for `S = 179/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredseventynine :
    singleClusterMaxEnergyS 2 179 = (32041 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-179/2 4-vertex (quartet) ground-state energy** (γ-5 step 1370):
`singleClusterGSEnergyS 3 179 = -96481/4 = -S(1+zS)` for `S = 179/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredseventynine :
    singleClusterGSEnergyS 3 179 = (-96481 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-179/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1370):
`singleClusterMaxEnergyS 3 179 = 96123/4 = zS²` for `S = 179/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredseventynine :
    singleClusterMaxEnergyS 3 179 = (96123 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-179/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1371):
`singleClusterGSEnergyS 4 179 = -64261/2 = -S(1+zS)` for `S = 179/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredseventynine :
    singleClusterGSEnergyS 4 179 = (-64261 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-179/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1371):
`singleClusterMaxEnergyS 4 179 = 32041 = zS²` for `S = 179/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredseventynine :
    singleClusterMaxEnergyS 4 179 = (32041 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-179/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1372):
`singleClusterGSEnergyS 5 179 = -160563/4 = -S(1+zS)` for `S = 179/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredseventynine :
    singleClusterGSEnergyS 5 179 = (-160563 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-179/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1372):
`singleClusterMaxEnergyS 5 179 = 160205/4 = zS²` for `S = 179/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredseventynine :
    singleClusterMaxEnergyS 5 179 = (160205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-179/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1373):
`singleClusterGSEnergyS 6 179 = -48151 = -S(1+zS)` for `S = 179/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredseventynine :
    singleClusterGSEnergyS 6 179 = (-48151 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-179/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1373):
`singleClusterMaxEnergyS 6 179 = 96123/2 = zS²` for `S = 179/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredseventynine :
    singleClusterMaxEnergyS 6 179 = (96123 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-90 2-vertex (dimer) ground-state energy** (γ-5 step 1374):
`singleClusterGSEnergyS 1 180 = -8190 = -S(S+1)` for `S = 90`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeighty :
    singleClusterGSEnergyS 1 180 = (-8190 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-90 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1374):
`singleClusterMaxEnergyS 1 180 = 8100 = S²` for `S = 90`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeighty :
    singleClusterMaxEnergyS 1 180 = (8100 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-90 3-vertex (trimer) ground-state energy** (γ-5 step 1375):
`singleClusterGSEnergyS 2 180 = -16290 = -S(1+zS)` for `S = 90, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeighty :
    singleClusterGSEnergyS 2 180 = (-16290 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-90 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1375):
`singleClusterMaxEnergyS 2 180 = 16200 = zS²` for `S = 90, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeighty :
    singleClusterMaxEnergyS 2 180 = (16200 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-90 4-vertex (quartet) ground-state energy** (γ-5 step 1376):
`singleClusterGSEnergyS 3 180 = -24390 = -S(1+zS)` for `S = 90, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeighty :
    singleClusterGSEnergyS 3 180 = (-24390 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-90 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1376):
`singleClusterMaxEnergyS 3 180 = 24300 = zS²` for `S = 90, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeighty :
    singleClusterMaxEnergyS 3 180 = (24300 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-90 5-vertex (pentamer) ground-state energy** (γ-5 step 1377):
`singleClusterGSEnergyS 4 180 = -32490 = -S(1+zS)` for `S = 90, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeighty :
    singleClusterGSEnergyS 4 180 = (-32490 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-90 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1377):
`singleClusterMaxEnergyS 4 180 = 32400 = zS²` for `S = 90, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeighty :
    singleClusterMaxEnergyS 4 180 = (32400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-90 6-vertex (hexamer) ground-state energy** (γ-5 step 1378):
`singleClusterGSEnergyS 5 180 = -40590 = -S(1+zS)` for `S = 90, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeighty :
    singleClusterGSEnergyS 5 180 = (-40590 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-90 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1378):
`singleClusterMaxEnergyS 5 180 = 40500 = zS²` for `S = 90, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeighty :
    singleClusterMaxEnergyS 5 180 = (40500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-90 7-vertex (heptamer) ground-state energy** (γ-5 step 1379):
`singleClusterGSEnergyS 6 180 = -48690 = -S(1+zS)` for `S = 90, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeighty :
    singleClusterGSEnergyS 6 180 = (-48690 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-90 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1379):
`singleClusterMaxEnergyS 6 180 = 48600 = zS²` for `S = 90, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeighty :
    singleClusterMaxEnergyS 6 180 = (48600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-181/2 2-vertex (dimer) ground-state energy** (γ-5 step 1380):
`singleClusterGSEnergyS 1 181 = -33123/4 = -S(S+1)` for `S = 181/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeightyone :
    singleClusterGSEnergyS 1 181 = (-33123 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-181/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1380):
`singleClusterMaxEnergyS 1 181 = 32761/4 = S²` for `S = 181/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeightyone :
    singleClusterMaxEnergyS 1 181 = (32761 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-181/2 3-vertex (trimer) ground-state energy** (γ-5 step 1381):
`singleClusterGSEnergyS 2 181 = -16471 = -S(1+zS)` for `S = 181/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeightyone :
    singleClusterGSEnergyS 2 181 = (-16471 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-181/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1381):
`singleClusterMaxEnergyS 2 181 = 32761/2 = zS²` for `S = 181/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeightyone :
    singleClusterMaxEnergyS 2 181 = (32761 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-181/2 4-vertex (quartet) ground-state energy** (γ-5 step 1382):
`singleClusterGSEnergyS 3 181 = -98645/4 = -S(1+zS)` for `S = 181/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeightyone :
    singleClusterGSEnergyS 3 181 = (-98645 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-181/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1382):
`singleClusterMaxEnergyS 3 181 = 98283/4 = zS²` for `S = 181/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeightyone :
    singleClusterMaxEnergyS 3 181 = (98283 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-181/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1383):
`singleClusterGSEnergyS 4 181 = -65703/2 = -S(1+zS)` for `S = 181/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeightyone :
    singleClusterGSEnergyS 4 181 = (-65703 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-181/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1383):
`singleClusterMaxEnergyS 4 181 = 32761 = zS²` for `S = 181/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeightyone :
    singleClusterMaxEnergyS 4 181 = (32761 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-181/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1384):
`singleClusterGSEnergyS 5 181 = -164167/4 = -S(1+zS)` for `S = 181/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeightyone :
    singleClusterGSEnergyS 5 181 = (-164167 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-181/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1384):
`singleClusterMaxEnergyS 5 181 = 163805/4 = zS²` for `S = 181/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeightyone :
    singleClusterMaxEnergyS 5 181 = (163805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-181/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1385):
`singleClusterGSEnergyS 6 181 = -49232 = -S(1+zS)` for `S = 181/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeightyone :
    singleClusterGSEnergyS 6 181 = (-49232 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-181/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1385):
`singleClusterMaxEnergyS 6 181 = 98283/2 = zS²` for `S = 181/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeightyone :
    singleClusterMaxEnergyS 6 181 = (98283 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91 2-vertex (dimer) ground-state energy** (γ-5 step 1386):
`singleClusterGSEnergyS 1 182 = -8372 = -S(S+1)` for `S = 91`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeightytwo :
    singleClusterGSEnergyS 1 182 = (-8372 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1386):
`singleClusterMaxEnergyS 1 182 = 8281 = S²` for `S = 91`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeightytwo :
    singleClusterMaxEnergyS 1 182 = (8281 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91 3-vertex (trimer) ground-state energy** (γ-5 step 1387):
`singleClusterGSEnergyS 2 182 = -16653 = -S(1+zS)` for `S = 91, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeightytwo :
    singleClusterGSEnergyS 2 182 = (-16653 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1387):
`singleClusterMaxEnergyS 2 182 = 16562 = zS²` for `S = 91, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeightytwo :
    singleClusterMaxEnergyS 2 182 = (16562 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91 4-vertex (quartet) ground-state energy** (γ-5 step 1388):
`singleClusterGSEnergyS 3 182 = -24934 = -S(1+zS)` for `S = 91, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeightytwo :
    singleClusterGSEnergyS 3 182 = (-24934 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1388):
`singleClusterMaxEnergyS 3 182 = 24843 = zS²` for `S = 91, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeightytwo :
    singleClusterMaxEnergyS 3 182 = (24843 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91 5-vertex (pentamer) ground-state energy** (γ-5 step 1389):
`singleClusterGSEnergyS 4 182 = -33215 = -S(1+zS)` for `S = 91, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeightytwo :
    singleClusterGSEnergyS 4 182 = (-33215 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1389):
`singleClusterMaxEnergyS 4 182 = 33124 = zS²` for `S = 91, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeightytwo :
    singleClusterMaxEnergyS 4 182 = (33124 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91 6-vertex (hexamer) ground-state energy** (γ-5 step 1390):
`singleClusterGSEnergyS 5 182 = -41496 = -S(1+zS)` for `S = 91, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeightytwo :
    singleClusterGSEnergyS 5 182 = (-41496 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1390):
`singleClusterMaxEnergyS 5 182 = 41405 = zS²` for `S = 91, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeightytwo :
    singleClusterMaxEnergyS 5 182 = (41405 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-91 7-vertex (heptamer) ground-state energy** (γ-5 step 1391):
`singleClusterGSEnergyS 6 182 = -49777 = -S(1+zS)` for `S = 91, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeightytwo :
    singleClusterGSEnergyS 6 182 = (-49777 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-91 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1391):
`singleClusterMaxEnergyS 6 182 = 49686 = zS²` for `S = 91, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeightytwo :
    singleClusterMaxEnergyS 6 182 = (49686 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-183/2 2-vertex (dimer) ground-state energy** (γ-5 step 1392):
`singleClusterGSEnergyS 1 183 = -33855/4 = -S(S+1)` for `S = 183/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeightythree :
    singleClusterGSEnergyS 1 183 = (-33855 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-183/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1392):
`singleClusterMaxEnergyS 1 183 = 33489/4 = S²` for `S = 183/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeightythree :
    singleClusterMaxEnergyS 1 183 = (33489 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-183/2 3-vertex (trimer) ground-state energy** (γ-5 step 1393):
`singleClusterGSEnergyS 2 183 = -16836 = -S(1+zS)` for `S = 183/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeightythree :
    singleClusterGSEnergyS 2 183 = (-16836 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-183/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1393):
`singleClusterMaxEnergyS 2 183 = 33489/2 = zS²` for `S = 183/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeightythree :
    singleClusterMaxEnergyS 2 183 = (33489 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-183/2 4-vertex (quartet) ground-state energy** (γ-5 step 1394):
`singleClusterGSEnergyS 3 183 = -100833/4 = -S(1+zS)` for `S = 183/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeightythree :
    singleClusterGSEnergyS 3 183 = (-100833 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-183/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1394):
`singleClusterMaxEnergyS 3 183 = 100467/4 = zS²` for `S = 183/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeightythree :
    singleClusterMaxEnergyS 3 183 = (100467 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-183/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1395):
`singleClusterGSEnergyS 4 183 = -67161/2 = -S(1+zS)` for `S = 183/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeightythree :
    singleClusterGSEnergyS 4 183 = (-67161 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-183/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1395):
`singleClusterMaxEnergyS 4 183 = 33489 = zS²` for `S = 183/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeightythree :
    singleClusterMaxEnergyS 4 183 = (33489 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-183/2 6-vertex (hexamer) ground-state energy** (γ-5 step 1396):
`singleClusterGSEnergyS 5 183 = -167811/4 = -S(1+zS)` for `S = 183/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeightythree :
    singleClusterGSEnergyS 5 183 = (-167811 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-183/2 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1396):
`singleClusterMaxEnergyS 5 183 = 167445/4 = zS²` for `S = 183/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeightythree :
    singleClusterMaxEnergyS 5 183 = (167445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-183/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1397):
`singleClusterGSEnergyS 6 183 = -50325 = -S(1+zS)` for `S = 183/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeightythree :
    singleClusterGSEnergyS 6 183 = (-50325 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-183/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1397):
`singleClusterMaxEnergyS 6 183 = 100467/2 = zS²` for `S = 183/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeightythree :
    singleClusterMaxEnergyS 6 183 = (100467 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-92 2-vertex (dimer) ground-state energy** (γ-5 step 1398):
`singleClusterGSEnergyS 1 184 = -8556 = -S(S+1)` for `S = 92`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeightyfour :
    singleClusterGSEnergyS 1 184 = (-8556 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-92 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1398):
`singleClusterMaxEnergyS 1 184 = 8464 = S²` for `S = 92`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeightyfour :
    singleClusterMaxEnergyS 1 184 = (8464 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-92 3-vertex (trimer) ground-state energy** (γ-5 step 1399):
`singleClusterGSEnergyS 2 184 = -17020 = -S(1+zS)` for `S = 92, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeightyfour :
    singleClusterGSEnergyS 2 184 = (-17020 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-92 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1399):
`singleClusterMaxEnergyS 2 184 = 16928 = zS²` for `S = 92, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeightyfour :
    singleClusterMaxEnergyS 2 184 = (16928 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-92 4-vertex (quartet) ground-state energy** (γ-5 step 1400):
`singleClusterGSEnergyS 3 184 = -25484 = -S(1+zS)` for `S = 92, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeightyfour :
    singleClusterGSEnergyS 3 184 = (-25484 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-92 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1400):
`singleClusterMaxEnergyS 3 184 = 25392 = zS²` for `S = 92, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeightyfour :
    singleClusterMaxEnergyS 3 184 = (25392 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-92 5-vertex (pentamer) ground-state energy** (γ-5 step 1401):
`singleClusterGSEnergyS 4 184 = -33948 = -S(1+zS)` for `S = 92, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeightyfour :
    singleClusterGSEnergyS 4 184 = (-33948 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-92 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1401):
`singleClusterMaxEnergyS 4 184 = 33856 = zS²` for `S = 92, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeightyfour :
    singleClusterMaxEnergyS 4 184 = (33856 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-92 6-vertex (hexamer) ground-state energy** (γ-5 step 1402):
`singleClusterGSEnergyS 5 184 = -42412 = -S(1+zS)` for `S = 92, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_hundredeightyfour :
    singleClusterGSEnergyS 5 184 = (-42412 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-92 6-vertex (hexamer) maximum-Casimir-sector energy** (γ-5 step 1402):
`singleClusterMaxEnergyS 5 184 = 42320 = zS²` for `S = 92, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_hundredeightyfour :
    singleClusterMaxEnergyS 5 184 = (42320 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-92 7-vertex (heptamer) ground-state energy** (γ-5 step 1403):
`singleClusterGSEnergyS 6 184 = -50876 = -S(1+zS)` for `S = 92, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_hundredeightyfour :
    singleClusterGSEnergyS 6 184 = (-50876 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-92 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1403):
`singleClusterMaxEnergyS 6 184 = 50784 = zS²` for `S = 92, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_hundredeightyfour :
    singleClusterMaxEnergyS 6 184 = (50784 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-185/2 2-vertex (dimer) ground-state energy** (γ-5 step 1404):
`singleClusterGSEnergyS 1 185 = -34595/4 = -S(S+1)` for `S = 185/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_hundredeightyfive :
    singleClusterGSEnergyS 1 185 = (-34595 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-185/2 2-vertex (dimer) maximum-Casimir-sector energy** (γ-5 step 1404):
`singleClusterMaxEnergyS 1 185 = 34225/4 = S²` for `S = 185/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_hundredeightyfive :
    singleClusterMaxEnergyS 1 185 = (34225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-185/2 3-vertex (trimer) ground-state energy** (γ-5 step 1405):
`singleClusterGSEnergyS 2 185 = -17205 = -S(1+zS)` for `S = 185/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_hundredeightyfive :
    singleClusterGSEnergyS 2 185 = (-17205 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-185/2 3-vertex (trimer) maximum-Casimir-sector energy** (γ-5 step 1405):
`singleClusterMaxEnergyS 2 185 = 34225/2 = zS²` for `S = 185/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_hundredeightyfive :
    singleClusterMaxEnergyS 2 185 = (34225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-185/2 4-vertex (quartet) ground-state energy** (γ-5 step 1406):
`singleClusterGSEnergyS 3 185 = -103045/4 = -S(1+zS)` for `S = 185/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_hundredeightyfive :
    singleClusterGSEnergyS 3 185 = (-103045 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-185/2 4-vertex (quartet) maximum-Casimir-sector energy** (γ-5 step 1406):
`singleClusterMaxEnergyS 3 185 = 102675/4 = zS²` for `S = 185/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_hundredeightyfive :
    singleClusterMaxEnergyS 3 185 = (102675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-185/2 5-vertex (pentamer) ground-state energy** (γ-5 step 1407):
`singleClusterGSEnergyS 4 185 = -68635/2 = -S(1+zS)` for `S = 185/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_hundredeightyfive :
    singleClusterGSEnergyS 4 185 = (-68635 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-185/2 5-vertex (pentamer) maximum-Casimir-sector energy** (γ-5 step 1407):
`singleClusterMaxEnergyS 4 185 = 34225 = zS²` for `S = 185/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_hundredeightyfive :
    singleClusterMaxEnergyS 4 185 = (34225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
