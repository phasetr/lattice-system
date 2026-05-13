/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Zenith-spin numerical specialisations of single-cluster Heisenberg energies

This file holds fixed-`(z, N)` numerical specialisations of
`singleClusterGSEnergyS` and `singleClusterMaxEnergyS` for `N ≥ 215`
(spin `S = N/2 ≥ 215/2`). The `N = 1..28` specialisations live in
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
the `N = 166..198` in `SingleClusterHamiltonianNumericsOmegaHigh.lean`,
and the `N = 199..214` in `SingleClusterHamiltonianNumericsApexHigh.lean`.

This file imports the main `SingleClusterHamiltonian` directly (not
the lower-N numerics files) so all thirteen numerics files can elaborate
in parallel after the main file. The split from `ApexHigh` to
`ZenithHigh` was introduced as the 50-PR build-performance cadence
refactor #25 when `ApexHigh` reached 3133 lines / 8.50 s user CPU
after the N=199..230 entries had been appended (48 numerics PRs since
refactor #24: PRs #2703..#2750). Split aligned cleanly to the
spin-115 row boundary (after spin-115 closes at z=6, N=230, before
spin-231/2 opens). Frozen `ApexHigh`: N=199..214 (16 spin rows).
New `ZenithHigh`: N=215..230 (16 spin rows; will continue from
N=231 onward).
-/

namespace LatticeSystem.Quantum

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

/-- **Spin-219/2 pentamer ground-state energy** (γ-5 step 1611):
`singleClusterGSEnergyS 4 219 = -96141/2 = -S(1+zS)` for `S = 219/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundrednineteen :
    singleClusterGSEnergyS 4 219 = (-96141 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-219/2 pentamer maximum-Casimir-sector energy** (γ-5 step 1611):
`singleClusterMaxEnergyS 4 219 = 47961 = zS²` for `S = 219/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundrednineteen :
    singleClusterMaxEnergyS 4 219 = (47961 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-219/2 hexamer ground-state energy** (γ-5 step 1612):
`singleClusterGSEnergyS 5 219 = -240243/4 = -S(1+zS)` for `S = 219/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundrednineteen :
    singleClusterGSEnergyS 5 219 = (-240243 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-219/2 hexamer maximum-Casimir-sector energy** (γ-5 step 1612):
`singleClusterMaxEnergyS 5 219 = 239805/4 = zS²` for `S = 219/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundrednineteen :
    singleClusterMaxEnergyS 5 219 = (239805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-219/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1613):
`singleClusterGSEnergyS 6 219 = -72051 = -S(1+zS)` for `S = 219/2, z = 6`. Closes spin-219/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundrednineteen :
    singleClusterGSEnergyS 6 219 = (-72051 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-219/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1613):
`singleClusterMaxEnergyS 6 219 = 143883/2 = zS²` for `S = 219/2, z = 6`. Closes spin-219/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundrednineteen :
    singleClusterMaxEnergyS 6 219 = (143883 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-110 dimer ground-state energy** (γ-5 step 1614):
`singleClusterGSEnergyS 1 220 = -12210 = -S(S+1)` for `S = 110, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwenty :
    singleClusterGSEnergyS 1 220 = (-12210 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-110 dimer maximum-Casimir-sector energy** (γ-5 step 1614):
`singleClusterMaxEnergyS 1 220 = 12100 = S²` for `S = 110, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwenty :
    singleClusterMaxEnergyS 1 220 = (12100 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-110 trimer ground-state energy** (γ-5 step 1615):
`singleClusterGSEnergyS 2 220 = -24310 = -S(1+zS)` for `S = 110, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwenty :
    singleClusterGSEnergyS 2 220 = (-24310 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-110 trimer maximum-Casimir-sector energy** (γ-5 step 1615):
`singleClusterMaxEnergyS 2 220 = 24200 = zS²` for `S = 110, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwenty :
    singleClusterMaxEnergyS 2 220 = (24200 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-110 quartet ground-state energy** (γ-5 step 1616):
`singleClusterGSEnergyS 3 220 = -36410 = -S(1+zS)` for `S = 110, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwenty :
    singleClusterGSEnergyS 3 220 = (-36410 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-110 quartet maximum-Casimir-sector energy** (γ-5 step 1616):
`singleClusterMaxEnergyS 3 220 = 36300 = zS²` for `S = 110, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwenty :
    singleClusterMaxEnergyS 3 220 = (36300 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-110 pentamer ground-state energy** (γ-5 step 1617):
`singleClusterGSEnergyS 4 220 = -48510 = -S(1+zS)` for `S = 110, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwenty :
    singleClusterGSEnergyS 4 220 = (-48510 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-110 pentamer maximum-Casimir-sector energy** (γ-5 step 1617):
`singleClusterMaxEnergyS 4 220 = 48400 = zS²` for `S = 110, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwenty :
    singleClusterMaxEnergyS 4 220 = (48400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-110 hexamer ground-state energy** (γ-5 step 1618):
`singleClusterGSEnergyS 5 220 = -60610 = -S(1+zS)` for `S = 110, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwenty :
    singleClusterGSEnergyS 5 220 = (-60610 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-110 hexamer maximum-Casimir-sector energy** (γ-5 step 1618):
`singleClusterMaxEnergyS 5 220 = 60500 = zS²` for `S = 110, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwenty :
    singleClusterMaxEnergyS 5 220 = (60500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-110 7-vertex (heptamer) ground-state energy** (γ-5 step 1619):
`singleClusterGSEnergyS 6 220 = -72710 = -S(1+zS)` for `S = 110, z = 6`. Closes spin-110 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwenty :
    singleClusterGSEnergyS 6 220 = (-72710 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-110 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1619):
`singleClusterMaxEnergyS 6 220 = 72600 = zS²` for `S = 110, z = 6`. Closes spin-110 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwenty :
    singleClusterMaxEnergyS 6 220 = (72600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-221/2 dimer ground-state energy** (γ-5 step 1620):
`singleClusterGSEnergyS 1 221 = -49283/4 = -S(S+1)` for `S = 221/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentyone :
    singleClusterGSEnergyS 1 221 = (-49283 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-221/2 dimer maximum-Casimir-sector energy** (γ-5 step 1620):
`singleClusterMaxEnergyS 1 221 = 48841/4 = S²` for `S = 221/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentyone :
    singleClusterMaxEnergyS 1 221 = (48841 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-221/2 trimer ground-state energy** (γ-5 step 1621):
`singleClusterGSEnergyS 2 221 = -24531 = -S(1+zS)` for `S = 221/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentyone :
    singleClusterGSEnergyS 2 221 = (-24531 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-221/2 trimer maximum-Casimir-sector energy** (γ-5 step 1621):
`singleClusterMaxEnergyS 2 221 = 48841/2 = zS²` for `S = 221/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentyone :
    singleClusterMaxEnergyS 2 221 = (48841 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-221/2 quartet ground-state energy** (γ-5 step 1622):
`singleClusterGSEnergyS 3 221 = -146965/4 = -S(1+zS)` for `S = 221/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentyone :
    singleClusterGSEnergyS 3 221 = (-146965 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-221/2 quartet maximum-Casimir-sector energy** (γ-5 step 1622):
`singleClusterMaxEnergyS 3 221 = 146523/4 = zS²` for `S = 221/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentyone :
    singleClusterMaxEnergyS 3 221 = (146523 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-221/2 pentamer ground-state energy** (γ-5 step 1623):
`singleClusterGSEnergyS 4 221 = -97903/2 = -S(1+zS)` for `S = 221/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentyone :
    singleClusterGSEnergyS 4 221 = (-97903 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-221/2 pentamer maximum-Casimir-sector energy** (γ-5 step 1623):
`singleClusterMaxEnergyS 4 221 = 48841 = zS²` for `S = 221/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentyone :
    singleClusterMaxEnergyS 4 221 = (48841 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-221/2 hexamer ground-state energy** (γ-5 step 1624):
`singleClusterGSEnergyS 5 221 = -244647/4 = -S(1+zS)` for `S = 221/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentyone :
    singleClusterGSEnergyS 5 221 = (-244647 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-221/2 hexamer maximum-Casimir-sector energy** (γ-5 step 1624):
`singleClusterMaxEnergyS 5 221 = 244205/4 = zS²` for `S = 221/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentyone :
    singleClusterMaxEnergyS 5 221 = (244205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-221/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1625):
`singleClusterGSEnergyS 6 221 = -73372 = -S(1+zS)` for `S = 221/2, z = 6`. Closes spin-221/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentyone :
    singleClusterGSEnergyS 6 221 = (-73372 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-221/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1625):
`singleClusterMaxEnergyS 6 221 = 146523/2 = zS²` for `S = 221/2, z = 6`. Closes spin-221/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentyone :
    singleClusterMaxEnergyS 6 221 = (146523 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111 dimer ground-state energy** (γ-5 step 1626):
`singleClusterGSEnergyS 1 222 = -12432 = -S(S+1)` for `S = 111, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentytwo :
    singleClusterGSEnergyS 1 222 = (-12432 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111 dimer maximum-Casimir-sector energy** (γ-5 step 1626):
`singleClusterMaxEnergyS 1 222 = 12321 = S²` for `S = 111, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentytwo :
    singleClusterMaxEnergyS 1 222 = (12321 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111 trimer ground-state energy** (γ-5 step 1627):
`singleClusterGSEnergyS 2 222 = -24753 = -S(1+zS)` for `S = 111, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentytwo :
    singleClusterGSEnergyS 2 222 = (-24753 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111 trimer maximum-Casimir-sector energy** (γ-5 step 1627):
`singleClusterMaxEnergyS 2 222 = 24642 = zS²` for `S = 111, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentytwo :
    singleClusterMaxEnergyS 2 222 = (24642 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111 quartet ground-state energy** (γ-5 step 1628):
`singleClusterGSEnergyS 3 222 = -37074 = -S(1+zS)` for `S = 111, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentytwo :
    singleClusterGSEnergyS 3 222 = (-37074 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111 quartet maximum-Casimir-sector energy** (γ-5 step 1628):
`singleClusterMaxEnergyS 3 222 = 36963 = zS²` for `S = 111, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentytwo :
    singleClusterMaxEnergyS 3 222 = (36963 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111 pentamer ground-state energy** (γ-5 step 1629):
`singleClusterGSEnergyS 4 222 = -49395 = -S(1+zS)` for `S = 111, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentytwo :
    singleClusterGSEnergyS 4 222 = (-49395 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111 pentamer maximum-Casimir-sector energy** (γ-5 step 1629):
`singleClusterMaxEnergyS 4 222 = 49284 = zS²` for `S = 111, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentytwo :
    singleClusterMaxEnergyS 4 222 = (49284 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111 hexamer ground-state energy** (γ-5 step 1630):
`singleClusterGSEnergyS 5 222 = -61716 = -S(1+zS)` for `S = 111, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentytwo :
    singleClusterGSEnergyS 5 222 = (-61716 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111 hexamer maximum-Casimir-sector energy** (γ-5 step 1630):
`singleClusterMaxEnergyS 5 222 = 61605 = zS²` for `S = 111, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentytwo :
    singleClusterMaxEnergyS 5 222 = (61605 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-111 7-vertex (heptamer) ground-state energy** (γ-5 step 1631):
`singleClusterGSEnergyS 6 222 = -74037 = -S(1+zS)` for `S = 111, z = 6`. Closes spin-111 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentytwo :
    singleClusterGSEnergyS 6 222 = (-74037 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-111 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1631):
`singleClusterMaxEnergyS 6 222 = 73926 = zS²` for `S = 111, z = 6`. Closes spin-111 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentytwo :
    singleClusterMaxEnergyS 6 222 = (73926 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-223/2 dimer ground-state energy** (γ-5 step 1632):
`singleClusterGSEnergyS 1 223 = -50175/4 = -S(S+1)` for `S = 223/2, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentythree :
    singleClusterGSEnergyS 1 223 = (-50175 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-223/2 dimer maximum-Casimir-sector energy** (γ-5 step 1632):
`singleClusterMaxEnergyS 1 223 = 49729/4 = S²` for `S = 223/2, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentythree :
    singleClusterMaxEnergyS 1 223 = (49729 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-223/2 trimer ground-state energy** (γ-5 step 1633):
`singleClusterGSEnergyS 2 223 = -24976 = -S(1+zS)` for `S = 223/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentythree :
    singleClusterGSEnergyS 2 223 = (-24976 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-223/2 trimer maximum-Casimir-sector energy** (γ-5 step 1633):
`singleClusterMaxEnergyS 2 223 = 49729/2 = zS²` for `S = 223/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentythree :
    singleClusterMaxEnergyS 2 223 = (49729 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-223/2 quartet ground-state energy** (γ-5 step 1634):
`singleClusterGSEnergyS 3 223 = -149633/4 = -S(1+zS)` for `S = 223/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentythree :
    singleClusterGSEnergyS 3 223 = (-149633 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-223/2 quartet maximum-Casimir-sector energy** (γ-5 step 1634):
`singleClusterMaxEnergyS 3 223 = 149187/4 = zS²` for `S = 223/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentythree :
    singleClusterMaxEnergyS 3 223 = (149187 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-223/2 pentamer ground-state energy** (γ-5 step 1635):
`singleClusterGSEnergyS 4 223 = -99681/2 = -S(1+zS)` for `S = 223/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentythree :
    singleClusterGSEnergyS 4 223 = (-99681 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-223/2 pentamer maximum-Casimir-sector energy** (γ-5 step 1635):
`singleClusterMaxEnergyS 4 223 = 49729 = zS²` for `S = 223/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentythree :
    singleClusterMaxEnergyS 4 223 = (49729 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-223/2 hexamer ground-state energy** (γ-5 step 1636):
`singleClusterGSEnergyS 5 223 = -249091/4 = -S(1+zS)` for `S = 223/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentythree :
    singleClusterGSEnergyS 5 223 = (-249091 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-223/2 hexamer maximum-Casimir-sector energy** (γ-5 step 1636):
`singleClusterMaxEnergyS 5 223 = 248645/4 = zS²` for `S = 223/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentythree :
    singleClusterMaxEnergyS 5 223 = (248645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-223/2 7-vertex (heptamer) ground-state energy** (γ-5 step 1637):
`singleClusterGSEnergyS 6 223 = -74705 = -S(1+zS)` for `S = 223/2, z = 6`. Closes spin-223/2 row. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentythree :
    singleClusterGSEnergyS 6 223 = (-74705 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-223/2 7-vertex (heptamer) maximum-Casimir-sector energy** (γ-5 step 1637):
`singleClusterMaxEnergyS 6 223 = 149187/2 = zS²` for `S = 223/2, z = 6`. Closes spin-223/2 row. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentythree :
    singleClusterMaxEnergyS 6 223 = (149187 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-112 dimer ground-state energy** (γ-5 step 1638):
`singleClusterGSEnergyS 1 224 = -12656 = -S(S+1)` for `S = 112, z = 1`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentyfour :
    singleClusterGSEnergyS 1 224 = (-12656 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-112 dimer maximum-Casimir-sector energy** (γ-5 step 1638):
`singleClusterMaxEnergyS 1 224 = 12544 = S²` for `S = 112, z = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentyfour :
    singleClusterMaxEnergyS 1 224 = (12544 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-112 trimer ground-state energy** (γ-5 step 1639):
`singleClusterGSEnergyS 2 224 = -25200 = -S(1+zS)` for `S = 112, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentyfour :
    singleClusterGSEnergyS 2 224 = (-25200 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-112 trimer maximum-Casimir-sector energy** (γ-5 step 1639):
`singleClusterMaxEnergyS 2 224 = 25088 = zS²` for `S = 112, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentyfour :
    singleClusterMaxEnergyS 2 224 = (25088 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-112 quartet ground-state energy** (γ-5 step 1640):
`singleClusterGSEnergyS 3 224 = -37744 = -S(1+zS)` for `S = 112, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentyfour :
    singleClusterGSEnergyS 3 224 = (-37744 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-112 quartet maximum-Casimir-sector energy** (γ-5 step 1640):
`singleClusterMaxEnergyS 3 224 = 37632 = zS²` for `S = 112, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentyfour :
    singleClusterMaxEnergyS 3 224 = (37632 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-112 pentamer ground-state energy** (γ-5 step 1641):
`singleClusterGSEnergyS 4 224 = -50288 = -S(1+zS)` for `S = 112, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentyfour :
    singleClusterGSEnergyS 4 224 = (-50288 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-112 pentamer maximum-Casimir-sector energy** (γ-5 step 1641):
`singleClusterMaxEnergyS 4 224 = 50176 = zS²` for `S = 112, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentyfour :
    singleClusterMaxEnergyS 4 224 = (50176 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-112 hexamer ground-state energy** (γ-5 step 1642):
`singleClusterGSEnergyS 5 224 = -62832 = -S(1+zS)` for `S = 112, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentyfour :
    singleClusterGSEnergyS 5 224 = (-62832 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-112 hexamer maximum-Casimir-sector energy** (γ-5 step 1642):
`singleClusterMaxEnergyS 5 224 = 62720 = zS²` for `S = 112, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentyfour :
    singleClusterMaxEnergyS 5 224 = (62720 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-112 heptamer ground-state energy** (γ-5 step 1643):
`singleClusterGSEnergyS 6 224 = -75376 = -S(1+zS)` for `S = 112, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentyfour :
    singleClusterGSEnergyS 6 224 = (-75376 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-112 heptamer maximum-Casimir-sector energy** (γ-5 step 1643):
`singleClusterMaxEnergyS 6 224 = 75264 = zS²` for `S = 112, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentyfour :
    singleClusterMaxEnergyS 6 224 = (75264 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-225/2 dimer ground-state energy** (γ-5 step 1644):
`singleClusterGSEnergyS 1 225 = -51075/4 = -S(S+1)` for `S = 225/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentyfive :
    singleClusterGSEnergyS 1 225 = (-51075 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-225/2 dimer maximum-Casimir-sector energy** (γ-5 step 1644):
`singleClusterMaxEnergyS 1 225 = 50625/4 = S²` for `S = 225/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentyfive :
    singleClusterMaxEnergyS 1 225 = (50625 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-225/2 trimer ground-state energy** (γ-5 step 1645):
`singleClusterGSEnergyS 2 225 = -25425 = -S(1+zS)` for `S = 225/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentyfive :
    singleClusterGSEnergyS 2 225 = (-25425 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-225/2 trimer maximum-Casimir-sector energy** (γ-5 step 1645):
`singleClusterMaxEnergyS 2 225 = 50625/2 = zS²` for `S = 225/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentyfive :
    singleClusterMaxEnergyS 2 225 = (50625 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-225/2 quartet ground-state energy** (γ-5 step 1646):
`singleClusterGSEnergyS 3 225 = -152325/4 = -S(1+zS)` for `S = 225/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentyfive :
    singleClusterGSEnergyS 3 225 = (-152325 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-225/2 quartet maximum-Casimir-sector energy** (γ-5 step 1646):
`singleClusterMaxEnergyS 3 225 = 151875/4 = zS²` for `S = 225/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentyfive :
    singleClusterMaxEnergyS 3 225 = (151875 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-225/2 pentamer ground-state energy** (γ-5 step 1647):
`singleClusterGSEnergyS 4 225 = -101475/2 = -S(1+zS)` for `S = 225/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentyfive :
    singleClusterGSEnergyS 4 225 = (-101475 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-225/2 pentamer maximum-Casimir-sector energy** (γ-5 step 1647):
`singleClusterMaxEnergyS 4 225 = 50625 = zS²` for `S = 225/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentyfive :
    singleClusterMaxEnergyS 4 225 = (50625 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-225/2 hexamer ground-state energy** (γ-5 step 1648):
`singleClusterGSEnergyS 5 225 = -253575/4 = -S(1+zS)` for `S = 225/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentyfive :
    singleClusterGSEnergyS 5 225 = (-253575 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-225/2 hexamer maximum-Casimir-sector energy** (γ-5 step 1648):
`singleClusterMaxEnergyS 5 225 = 253125/4 = zS²` for `S = 225/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentyfive :
    singleClusterMaxEnergyS 5 225 = (253125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-225/2 heptamer ground-state energy** (γ-5 step 1649):
`singleClusterGSEnergyS 6 225 = -76050 = -S(1+zS)` for `S = 225/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentyfive :
    singleClusterGSEnergyS 6 225 = (-76050 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-225/2 heptamer maximum-Casimir-sector energy** (γ-5 step 1649):
`singleClusterMaxEnergyS 6 225 = 151875/2 = zS²` for `S = 225/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentyfive :
    singleClusterMaxEnergyS 6 225 = (151875 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113 dimer ground-state energy** (γ-5 step 1650):
`singleClusterGSEnergyS 1 226 = -12882 = -S(S+1)` for `S = 113`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentysix :
    singleClusterGSEnergyS 1 226 = (-12882 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113 dimer maximum-Casimir-sector energy** (γ-5 step 1650):
`singleClusterMaxEnergyS 1 226 = 12769 = S²` for `S = 113`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentysix :
    singleClusterMaxEnergyS 1 226 = (12769 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113 trimer ground-state energy** (γ-5 step 1651):
`singleClusterGSEnergyS 2 226 = -25651 = -S(1+zS)` for `S = 113, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentysix :
    singleClusterGSEnergyS 2 226 = (-25651 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113 trimer maximum-Casimir-sector energy** (γ-5 step 1651):
`singleClusterMaxEnergyS 2 226 = 25538 = zS²` for `S = 113, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentysix :
    singleClusterMaxEnergyS 2 226 = (25538 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113 quartet ground-state energy** (γ-5 step 1652):
`singleClusterGSEnergyS 3 226 = -38420 = -S(1+zS)` for `S = 113, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentysix :
    singleClusterGSEnergyS 3 226 = (-38420 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113 quartet maximum-Casimir-sector energy** (γ-5 step 1652):
`singleClusterMaxEnergyS 3 226 = 38307 = zS²` for `S = 113, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentysix :
    singleClusterMaxEnergyS 3 226 = (38307 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113 pentamer ground-state energy** (γ-5 step 1653):
`singleClusterGSEnergyS 4 226 = -51189 = -S(1+zS)` for `S = 113, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentysix :
    singleClusterGSEnergyS 4 226 = (-51189 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113 pentamer maximum-Casimir-sector energy** (γ-5 step 1653):
`singleClusterMaxEnergyS 4 226 = 51076 = zS²` for `S = 113, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentysix :
    singleClusterMaxEnergyS 4 226 = (51076 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113 hexamer ground-state energy** (γ-5 step 1654):
`singleClusterGSEnergyS 5 226 = -63958 = -S(1+zS)` for `S = 113, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentysix :
    singleClusterGSEnergyS 5 226 = (-63958 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113 hexamer maximum-Casimir-sector energy** (γ-5 step 1654):
`singleClusterMaxEnergyS 5 226 = 63845 = zS²` for `S = 113, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentysix :
    singleClusterMaxEnergyS 5 226 = (63845 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-113 heptamer ground-state energy** (γ-5 step 1655):
`singleClusterGSEnergyS 6 226 = -76727 = -S(1+zS)` for `S = 113, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentysix :
    singleClusterGSEnergyS 6 226 = (-76727 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-113 heptamer maximum-Casimir-sector energy** (γ-5 step 1655):
`singleClusterMaxEnergyS 6 226 = 76614 = zS²` for `S = 113, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentysix :
    singleClusterMaxEnergyS 6 226 = (76614 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-227/2 dimer ground-state energy** (γ-5 step 1656):
`singleClusterGSEnergyS 1 227 = -51983/4 = -S(S+1)` for `S = 227/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentyseven :
    singleClusterGSEnergyS 1 227 = (-51983 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-227/2 dimer maximum-Casimir-sector energy** (γ-5 step 1656):
`singleClusterMaxEnergyS 1 227 = 51529/4 = S²` for `S = 227/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentyseven :
    singleClusterMaxEnergyS 1 227 = (51529 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-227/2 trimer ground-state energy** (γ-5 step 1657):
`singleClusterGSEnergyS 2 227 = -25878 = -S(1+zS)` for `S = 227/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentyseven :
    singleClusterGSEnergyS 2 227 = (-25878 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-227/2 trimer maximum-Casimir-sector energy** (γ-5 step 1657):
`singleClusterMaxEnergyS 2 227 = 51529/2 = zS²` for `S = 227/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentyseven :
    singleClusterMaxEnergyS 2 227 = (51529 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-227/2 quartet ground-state energy** (γ-5 step 1658):
`singleClusterGSEnergyS 3 227 = -155041/4 = -S(1+zS)` for `S = 227/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentyseven :
    singleClusterGSEnergyS 3 227 = (-155041 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-227/2 quartet maximum-Casimir-sector energy** (γ-5 step 1658):
`singleClusterMaxEnergyS 3 227 = 154587/4 = zS²` for `S = 227/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentyseven :
    singleClusterMaxEnergyS 3 227 = (154587 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-227/2 pentamer ground-state energy** (γ-5 step 1659):
`singleClusterGSEnergyS 4 227 = -103285/2 = -S(1+zS)` for `S = 227/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentyseven :
    singleClusterGSEnergyS 4 227 = (-103285 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-227/2 pentamer maximum-Casimir-sector energy** (γ-5 step 1659):
`singleClusterMaxEnergyS 4 227 = 51529 = zS²` for `S = 227/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentyseven :
    singleClusterMaxEnergyS 4 227 = (51529 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-227/2 hexamer ground-state energy** (γ-5 step 1660):
`singleClusterGSEnergyS 5 227 = -258099/4 = -S(1+zS)` for `S = 227/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentyseven :
    singleClusterGSEnergyS 5 227 = (-258099 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-227/2 hexamer maximum-Casimir-sector energy** (γ-5 step 1660):
`singleClusterMaxEnergyS 5 227 = 257645/4 = zS²` for `S = 227/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentyseven :
    singleClusterMaxEnergyS 5 227 = (257645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-227/2 heptamer ground-state energy** (γ-5 step 1661):
`singleClusterGSEnergyS 6 227 = -77407 = -S(1+zS)` for `S = 227/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentyseven :
    singleClusterGSEnergyS 6 227 = (-77407 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-227/2 heptamer maximum-Casimir-sector energy** (γ-5 step 1661):
`singleClusterMaxEnergyS 6 227 = 154587/2 = zS²` for `S = 227/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentyseven :
    singleClusterMaxEnergyS 6 227 = (154587 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-114 dimer ground-state energy** (γ-5 step 1662):
`singleClusterGSEnergyS 1 228 = -13110 = -S(S+1)` for `S = 114`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentyeight :
    singleClusterGSEnergyS 1 228 = (-13110 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-114 dimer maximum-Casimir-sector energy** (γ-5 step 1662):
`singleClusterMaxEnergyS 1 228 = 12996 = S²` for `S = 114`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentyeight :
    singleClusterMaxEnergyS 1 228 = (12996 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-114 trimer ground-state energy** (γ-5 step 1663):
`singleClusterGSEnergyS 2 228 = -26106 = -S(1+zS)` for `S = 114, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentyeight :
    singleClusterGSEnergyS 2 228 = (-26106 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-114 trimer maximum-Casimir-sector energy** (γ-5 step 1663):
`singleClusterMaxEnergyS 2 228 = 25992 = zS²` for `S = 114, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentyeight :
    singleClusterMaxEnergyS 2 228 = (25992 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-114 quartet ground-state energy** (γ-5 step 1664):
`singleClusterGSEnergyS 3 228 = -39102 = -S(1+zS)` for `S = 114, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentyeight :
    singleClusterGSEnergyS 3 228 = (-39102 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-114 quartet maximum-Casimir-sector energy** (γ-5 step 1664):
`singleClusterMaxEnergyS 3 228 = 38988 = zS²` for `S = 114, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentyeight :
    singleClusterMaxEnergyS 3 228 = (38988 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-114 pentamer ground-state energy** (γ-5 step 1665):
`singleClusterGSEnergyS 4 228 = -52098 = -S(1+zS)` for `S = 114, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentyeight :
    singleClusterGSEnergyS 4 228 = (-52098 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-114 pentamer maximum-Casimir-sector energy** (γ-5 step 1665):
`singleClusterMaxEnergyS 4 228 = 51984 = zS²` for `S = 114, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentyeight :
    singleClusterMaxEnergyS 4 228 = (51984 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-114 hexamer ground-state energy** (γ-5 step 1666):
`singleClusterGSEnergyS 5 228 = -65094 = -S(1+zS)` for `S = 114, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentyeight :
    singleClusterGSEnergyS 5 228 = (-65094 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-114 hexamer maximum-Casimir-sector energy** (γ-5 step 1666):
`singleClusterMaxEnergyS 5 228 = 64980 = zS²` for `S = 114, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentyeight :
    singleClusterMaxEnergyS 5 228 = (64980 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-114 heptamer ground-state energy** (γ-5 step 1667):
`singleClusterGSEnergyS 6 228 = -78090 = -S(1+zS)` for `S = 114, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentyeight :
    singleClusterGSEnergyS 6 228 = (-78090 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-114 heptamer maximum-Casimir-sector energy** (γ-5 step 1667):
`singleClusterMaxEnergyS 6 228 = 77976 = zS²` for `S = 114, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentyeight :
    singleClusterMaxEnergyS 6 228 = (77976 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-229/2 dimer ground-state energy** (γ-5 step 1668):
`singleClusterGSEnergyS 1 229 = -52899/4 = -S(S+1)` for `S = 229/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredtwentynine :
    singleClusterGSEnergyS 1 229 = (-52899 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-229/2 dimer maximum-Casimir-sector energy** (γ-5 step 1668):
`singleClusterMaxEnergyS 1 229 = 52441/4 = S²` for `S = 229/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredtwentynine :
    singleClusterMaxEnergyS 1 229 = (52441 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-229/2 trimer ground-state energy** (γ-5 step 1669):
`singleClusterGSEnergyS 2 229 = -26335 = -S(1+zS)` for `S = 229/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredtwentynine :
    singleClusterGSEnergyS 2 229 = (-26335 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-229/2 trimer maximum-Casimir-sector energy** (γ-5 step 1669):
`singleClusterMaxEnergyS 2 229 = 52441/2 = zS²` for `S = 229/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredtwentynine :
    singleClusterMaxEnergyS 2 229 = (52441 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-229/2 quartet ground-state energy** (γ-5 step 1670):
`singleClusterGSEnergyS 3 229 = -157781/4 = -S(1+zS)` for `S = 229/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredtwentynine :
    singleClusterGSEnergyS 3 229 = (-157781 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-229/2 quartet maximum-Casimir-sector energy** (γ-5 step 1670):
`singleClusterMaxEnergyS 3 229 = 157323/4 = zS²` for `S = 229/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredtwentynine :
    singleClusterMaxEnergyS 3 229 = (157323 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-229/2 pentamer ground-state energy** (γ-5 step 1671):
`singleClusterGSEnergyS 4 229 = -105111/2 = -S(1+zS)` for `S = 229/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredtwentynine :
    singleClusterGSEnergyS 4 229 = (-105111 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-229/2 pentamer maximum-Casimir-sector energy** (γ-5 step 1671):
`singleClusterMaxEnergyS 4 229 = 52441 = zS²` for `S = 229/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredtwentynine :
    singleClusterMaxEnergyS 4 229 = (52441 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-229/2 hexamer ground-state energy** (γ-5 step 1672):
`singleClusterGSEnergyS 5 229 = -262663/4 = -S(1+zS)` for `S = 229/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredtwentynine :
    singleClusterGSEnergyS 5 229 = (-262663 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-229/2 hexamer maximum-Casimir-sector energy** (γ-5 step 1672):
`singleClusterMaxEnergyS 5 229 = 262205/4 = zS²` for `S = 229/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredtwentynine :
    singleClusterMaxEnergyS 5 229 = (262205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-229/2 heptamer ground-state energy** (γ-5 step 1673):
`singleClusterGSEnergyS 6 229 = -78776 = -S(1+zS)` for `S = 229/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredtwentynine :
    singleClusterGSEnergyS 6 229 = (-78776 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-229/2 heptamer maximum-Casimir-sector energy** (γ-5 step 1673):
`singleClusterMaxEnergyS 6 229 = 157323/2 = zS²` for `S = 229/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredtwentynine :
    singleClusterMaxEnergyS 6 229 = (157323 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115 dimer ground-state energy** (γ-5 step 1674):
`singleClusterGSEnergyS 1 230 = -13340 = -S(S+1)` for `S = 115`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredthirty :
    singleClusterGSEnergyS 1 230 = (-13340 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115 dimer maximum-Casimir-sector energy** (γ-5 step 1674):
`singleClusterMaxEnergyS 1 230 = 13225 = S²` for `S = 115`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredthirty :
    singleClusterMaxEnergyS 1 230 = (13225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115 trimer ground-state energy** (γ-5 step 1675):
`singleClusterGSEnergyS 2 230 = -26565 = -S(1+zS)` for `S = 115, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twohundredthirty :
    singleClusterGSEnergyS 2 230 = (-26565 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115 trimer maximum-Casimir-sector energy** (γ-5 step 1675):
`singleClusterMaxEnergyS 2 230 = 26450 = zS²` for `S = 115, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twohundredthirty :
    singleClusterMaxEnergyS 2 230 = (26450 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115 quartet ground-state energy** (γ-5 step 1676):
`singleClusterGSEnergyS 3 230 = -39790 = -S(1+zS)` for `S = 115, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twohundredthirty :
    singleClusterGSEnergyS 3 230 = (-39790 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115 quartet maximum-Casimir-sector energy** (γ-5 step 1676):
`singleClusterMaxEnergyS 3 230 = 39675 = zS²` for `S = 115, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twohundredthirty :
    singleClusterMaxEnergyS 3 230 = (39675 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115 pentamer ground-state energy** (γ-5 step 1677):
`singleClusterGSEnergyS 4 230 = -53015 = -S(1+zS)` for `S = 115, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twohundredthirty :
    singleClusterGSEnergyS 4 230 = (-53015 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115 pentamer maximum-Casimir-sector energy** (γ-5 step 1677):
`singleClusterMaxEnergyS 4 230 = 52900 = zS²` for `S = 115, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twohundredthirty :
    singleClusterMaxEnergyS 4 230 = (52900 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115 hexamer ground-state energy** (γ-5 step 1678):
`singleClusterGSEnergyS 5 230 = -66240 = -S(1+zS)` for `S = 115, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twohundredthirty :
    singleClusterGSEnergyS 5 230 = (-66240 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115 hexamer maximum-Casimir-sector energy** (γ-5 step 1678):
`singleClusterMaxEnergyS 5 230 = 66125 = zS²` for `S = 115, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twohundredthirty :
    singleClusterMaxEnergyS 5 230 = (66125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-115 heptamer ground-state energy** (γ-5 step 1679):
`singleClusterGSEnergyS 6 230 = -79465 = -S(1+zS)` for `S = 115, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twohundredthirty :
    singleClusterGSEnergyS 6 230 = (-79465 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-115 heptamer maximum-Casimir-sector energy** (γ-5 step 1679):
`singleClusterMaxEnergyS 6 230 = 79350 = zS²` for `S = 115, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twohundredthirty :
    singleClusterMaxEnergyS 6 230 = (79350 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-231/2 dimer ground-state energy** (γ-5 step 1680):
`singleClusterGSEnergyS 1 231 = -53823/4 = -S(S+1)` for `S = 231/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twohundredthirtyone :
    singleClusterGSEnergyS 1 231 = (-53823 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-231/2 dimer maximum-Casimir-sector energy** (γ-5 step 1680):
`singleClusterMaxEnergyS 1 231 = 53361/4 = S²` for `S = 231/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twohundredthirtyone :
    singleClusterMaxEnergyS 1 231 = (53361 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

end LatticeSystem.Quantum
