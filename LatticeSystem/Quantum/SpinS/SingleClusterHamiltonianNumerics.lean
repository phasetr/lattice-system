/-
Copyright (c) 2026 Yoshitsugu Sekine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoshitsugu Sekine
-/
import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Numerical specialisations of single-cluster Heisenberg energies

This file collects fixed-`(z, N)` numerical specialisations of the named
energies `singleClusterGSEnergyS` and `singleClusterMaxEnergyS` defined
in `LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian`. The general
lemmas (parametrised by `z`, `N`, or in `Re` / `Im` form) live in the
main file; this companion file holds the long catalogue of concrete
values used in the γ-5 numerical sweep of Tasaki Problem 2.5.a.

Splitting them out keeps the main file's elaboration time manageable as
the catalogue grows.
-/

namespace LatticeSystem.Quantum

/-- **Spin-1/2 dimer ground-state energy** (γ-5 step 277):
`singleClusterGSEnergyS 1 1 = -3/4`.

The canonical singlet eigenvalue `−3/4` of `Ŝ_0 · Ŝ_1` for two spin-`1/2`
sites: the most familiar concrete case of the Tasaki Problem 2.5.a
formula, doubly-specialised at `z = 1`, `N = 1` (so `S = 1/2`). -/
@[simp] theorem singleClusterGSEnergyS_one_one :
    singleClusterGSEnergyS 1 1 = (-3 / 4 : ℂ) := by
  rw [singleClusterGSEnergyS_one_eq]
  push_cast
  ring

/-- **Spin-1/2 dimer maximum-Casimir-sector energy** (γ-5 step 277):
`singleClusterMaxEnergyS 1 1 = 1/4`.

The canonical triplet eigenvalue `1/4` of `Ŝ_0 · Ŝ_1` for two spin-`1/2`
sites. -/
@[simp] theorem singleClusterMaxEnergyS_one_one :
    singleClusterMaxEnergyS 1 1 = (1 / 4 : ℂ) := by
  rw [singleClusterMaxEnergyS_one_eq]
  push_cast
  ring

/-- **Spin-1/2 3-vertex-star ground-state energy** (γ-5 step 279):
`singleClusterGSEnergyS 2 1 = -1`.

Concrete numerical value of `−S(1+zS)` for `z=2, N=1` (i.e. `S=1/2`).
The simplest non-dimer cluster: a central spin-1/2 with two leaves.
Direct check: spectrum of `Ŝ_0·Ŝ_1 + Ŝ_0·Ŝ_2` for three spin-1/2 sites
is `{−1, 0, 1/2}` (multiplicities 2, 2, 4 from the `1/2 ⊗ 1 = 1/2 ⊕ 3/2`
plus `1/2 ⊗ 0 = 1/2` decomposition); the ground state energy is `−1`. -/
@[simp] theorem singleClusterGSEnergyS_two_one :
    singleClusterGSEnergyS 2 1 = (-1 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1/2 3-vertex-star max-Casimir-sector energy** (γ-5 step 279):
`singleClusterMaxEnergyS 2 1 = 1/2`.

Top eigenvalue (spin-`3/2` quadruplet) of `Ŝ_0·Ŝ_1 + Ŝ_0·Ŝ_2` for three
spin-1/2 sites. -/
@[simp] theorem singleClusterMaxEnergyS_two_one :
    singleClusterMaxEnergyS 2 1 = (1 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1 dimer ground-state energy** (γ-5 step 282):
`singleClusterGSEnergyS 1 2 = -2 = -S(S+1)` for `S = 1`.

Concrete numerical value of `−S(1+zS)` for two spin-1 sites coupled by
`Ŝ_0 · Ŝ_1`. The well-known Haldane-chain dimer baseline. -/
@[simp] theorem singleClusterGSEnergyS_one_two :
    singleClusterGSEnergyS 1 2 = (-2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1 dimer maximum-Casimir-sector energy** (γ-5 step 282):
`singleClusterMaxEnergyS 1 2 = 1 = S²` for `S = 1`. -/
@[simp] theorem singleClusterMaxEnergyS_one_two :
    singleClusterMaxEnergyS 1 2 = (1 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1 3-vertex-star ground-state energy** (γ-5 step 282):
`singleClusterGSEnergyS 2 2 = -3 = -S(1 + 2S)` for `S = 1, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_two :
    singleClusterGSEnergyS 2 2 = (-3 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 282):
`singleClusterMaxEnergyS 2 2 = 2 = zS²` for `S = 1, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_two :
    singleClusterMaxEnergyS 2 2 = (2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3/2 dimer ground-state energy** (γ-5 step 284):
`singleClusterGSEnergyS 1 3 = -15/4 = -S(S+1)` for `S = 3/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_three :
    singleClusterGSEnergyS 1 3 = (-15 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3/2 dimer maximum-Casimir-sector energy** (γ-5 step 284):
`singleClusterMaxEnergyS 1 3 = 9/4 = S²` for `S = 3/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_three :
    singleClusterMaxEnergyS 1 3 = (9 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3/2 3-vertex-star ground-state energy** (γ-5 step 284):
`singleClusterGSEnergyS 2 3 = -6 = -S(1+2S)` for `S = 3/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_three :
    singleClusterGSEnergyS 2 3 = (-6 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 284):
`singleClusterMaxEnergyS 2 3 = 9/2 = zS²` for `S = 3/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_three :
    singleClusterMaxEnergyS 2 3 = (9 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-2 dimer ground-state energy** (γ-5 step 289):
`singleClusterGSEnergyS 1 4 = -6 = -S(S+1)` for `S = 2`. -/
@[simp] theorem singleClusterGSEnergyS_one_four :
    singleClusterGSEnergyS 1 4 = (-6 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-2 dimer maximum-Casimir-sector energy** (γ-5 step 289):
`singleClusterMaxEnergyS 1 4 = 4 = S²` for `S = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_four :
    singleClusterMaxEnergyS 1 4 = (4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-2 3-vertex-star ground-state energy** (γ-5 step 290):
`singleClusterGSEnergyS 2 4 = -10 = -S(1+2S)` for `S = 2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_four :
    singleClusterGSEnergyS 2 4 = (-10 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 290):
`singleClusterMaxEnergyS 2 4 = 8 = zS²` for `S = 2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_four :
    singleClusterMaxEnergyS 2 4 = (8 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5/2 dimer ground-state energy** (γ-5 step 291):
`singleClusterGSEnergyS 1 5 = -35/4 = -S(S+1)` for `S = 5/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_five :
    singleClusterGSEnergyS 1 5 = (-35 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5/2 dimer maximum-Casimir-sector energy** (γ-5 step 291):
`singleClusterMaxEnergyS 1 5 = 25/4 = S²` for `S = 5/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_five :
    singleClusterMaxEnergyS 1 5 = (25 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1 4-vertex-star ground-state energy** (γ-5 step 297):
`singleClusterGSEnergyS 3 2 = -4 = -S(1+zS)` for `S = 1, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_two :
    singleClusterGSEnergyS 3 2 = (-4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 297):
`singleClusterMaxEnergyS 3 2 = 3 = zS²` for `S = 1, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_two :
    singleClusterMaxEnergyS 3 2 = (3 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1/2 4-vertex-star ground-state energy** (γ-5 step 298):
`singleClusterGSEnergyS 3 1 = -5/4 = -S(1+zS)` for `S = 1/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_one :
    singleClusterGSEnergyS 3 1 = (-5 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 298):
`singleClusterMaxEnergyS 3 1 = 3/4 = zS²` for `S = 1/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_one :
    singleClusterMaxEnergyS 3 1 = (3 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3 dimer ground-state energy** (γ-5 step 300):
`singleClusterGSEnergyS 1 6 = -12 = -S(S+1)` for `S = 3`. -/
@[simp] theorem singleClusterGSEnergyS_one_six :
    singleClusterGSEnergyS 1 6 = (-12 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3 dimer maximum-Casimir-sector energy** (γ-5 step 300):
`singleClusterMaxEnergyS 1 6 = 9 = S²` for `S = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_one_six :
    singleClusterMaxEnergyS 1 6 = (9 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3/2 4-vertex-star ground-state energy** (γ-5 step 301):
`singleClusterGSEnergyS 3 3 = -33/4 = -S(1+zS)` for `S = 3/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_three :
    singleClusterGSEnergyS 3 3 = (-33 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 301):
`singleClusterMaxEnergyS 3 3 = 27/4 = zS²` for `S = 3/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_three :
    singleClusterMaxEnergyS 3 3 = (27 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-2 4-vertex-star ground-state energy** (γ-5 step 302):
`singleClusterGSEnergyS 3 4 = -14 = -S(1+zS)` for `S = 2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_four :
    singleClusterGSEnergyS 3 4 = (-14 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 302):
`singleClusterMaxEnergyS 3 4 = 12 = zS²` for `S = 2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_four :
    singleClusterMaxEnergyS 3 4 = (12 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3 3-vertex-star ground-state energy** (γ-5 step 307):
`singleClusterGSEnergyS 2 6 = -21 = -S(1+zS)` for `S = 3, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_six :
    singleClusterGSEnergyS 2 6 = (-21 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 307):
`singleClusterMaxEnergyS 2 6 = 18 = zS²` for `S = 3, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_six :
    singleClusterMaxEnergyS 2 6 = (18 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1/2 5-vertex-star ground-state energy** (γ-5 step 308):
`singleClusterGSEnergyS 4 1 = -3/2 = -S(1+zS)` for `S = 1/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_one :
    singleClusterGSEnergyS 4 1 = (-3 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 308):
`singleClusterMaxEnergyS 4 1 = 1 = zS²` for `S = 1/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_one :
    singleClusterMaxEnergyS 4 1 = (1 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1 5-vertex-star ground-state energy** (γ-5 step 309):
`singleClusterGSEnergyS 4 2 = -5 = -S(1+zS)` for `S = 1, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_two :
    singleClusterGSEnergyS 4 2 = (-5 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 309):
`singleClusterMaxEnergyS 4 2 = 4 = zS²` for `S = 1, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_two :
    singleClusterMaxEnergyS 4 2 = (4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1/2 6-vertex-star ground-state energy** (γ-5 step 310):
`singleClusterGSEnergyS 5 1 = -7/4 = -S(1+zS)` for `S = 1/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_one :
    singleClusterGSEnergyS 5 1 = (-7 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 310):
`singleClusterMaxEnergyS 5 1 = 5/4 = zS²` for `S = 1/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_one :
    singleClusterMaxEnergyS 5 1 = (5 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-2 5-vertex-star ground-state energy** (γ-5 step 311):
`singleClusterGSEnergyS 4 4 = -18 = -S(1+zS)` for `S = 2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_four :
    singleClusterGSEnergyS 4 4 = (-18 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 311):
`singleClusterMaxEnergyS 4 4 = 16 = zS²` for `S = 2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_four :
    singleClusterMaxEnergyS 4 4 = (16 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3 4-vertex-star ground-state energy** (γ-5 step 316):
`singleClusterGSEnergyS 3 6 = -30 = -S(1+zS)` for `S = 3, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_six :
    singleClusterGSEnergyS 3 6 = (-30 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 316):
`singleClusterMaxEnergyS 3 6 = 27 = zS²` for `S = 3, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_six :
    singleClusterMaxEnergyS 3 6 = (27 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3/2 6-vertex-star ground-state energy** (γ-5 step 317):
`singleClusterGSEnergyS 5 3 = -51/4 = -S(1+zS)` for `S = 3/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_three :
    singleClusterGSEnergyS 5 3 = (-51 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 317):
`singleClusterMaxEnergyS 5 3 = 45/4 = zS²` for `S = 3/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_three :
    singleClusterMaxEnergyS 5 3 = (45 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-2 6-vertex-star ground-state energy** (γ-5 step 318):
`singleClusterGSEnergyS 5 4 = -22 = -S(1+zS)` for `S = 2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_four :
    singleClusterGSEnergyS 5 4 = (-22 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 318):
`singleClusterMaxEnergyS 5 4 = 20 = zS²` for `S = 2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_four :
    singleClusterMaxEnergyS 5 4 = (20 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-4 dimer ground-state energy** (γ-5 step 319):
`singleClusterGSEnergyS 1 8 = -20 = -S(S+1)` for `S = 4`. -/
@[simp] theorem singleClusterGSEnergyS_one_eight :
    singleClusterGSEnergyS 1 8 = (-20 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-4 dimer maximum-Casimir-sector energy** (γ-5 step 319):
`singleClusterMaxEnergyS 1 8 = 16 = S²` for `S = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eight :
    singleClusterMaxEnergyS 1 8 = (16 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1 6-vertex-star ground-state energy** (γ-5 step 320):
`singleClusterGSEnergyS 5 2 = -6 = -S(1+zS)` for `S = 1, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_two :
    singleClusterGSEnergyS 5 2 = (-6 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 320):
`singleClusterMaxEnergyS 5 2 = 5 = zS²` for `S = 1, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_two :
    singleClusterMaxEnergyS 5 2 = (5 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3/2 5-vertex-star ground-state energy** (γ-5 step 324):
`singleClusterGSEnergyS 4 3 = -21/2 = -S(1+zS)` for `S = 3/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_three :
    singleClusterGSEnergyS 4 3 = (-21 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 324):
`singleClusterMaxEnergyS 4 3 = 9 = zS²` for `S = 3/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_three :
    singleClusterMaxEnergyS 4 3 = (9 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1/2 7-vertex-star ground-state energy** (γ-5 step 325):
`singleClusterGSEnergyS 6 1 = -2 = -S(1+zS)` for `S = 1/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_one :
    singleClusterGSEnergyS 6 1 = (-2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 325):
`singleClusterMaxEnergyS 6 1 = 3/2 = zS²` for `S = 1/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_one :
    singleClusterMaxEnergyS 6 1 = (3 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-1 7-vertex-star ground-state energy** (γ-5 step 326):
`singleClusterGSEnergyS 6 2 = -7 = -S(1+zS)` for `S = 1, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_two :
    singleClusterGSEnergyS 6 2 = (-7 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-1 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 326):
`singleClusterMaxEnergyS 6 2 = 6 = zS²` for `S = 1, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_two :
    singleClusterMaxEnergyS 6 2 = (6 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3/2 7-vertex-star ground-state energy** (γ-5 step 327):
`singleClusterGSEnergyS 6 3 = -15 = -S(1+zS)` for `S = 3/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_three :
    singleClusterGSEnergyS 6 3 = (-15 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 327):
`singleClusterMaxEnergyS 6 3 = 27/2 = zS²` for `S = 3/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_three :
    singleClusterMaxEnergyS 6 3 = (27 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-2 7-vertex-star ground-state energy** (γ-5 step 328):
`singleClusterGSEnergyS 6 4 = -26 = -S(1+zS)` for `S = 2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_four :
    singleClusterGSEnergyS 6 4 = (-26 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 328):
`singleClusterMaxEnergyS 6 4 = 24 = zS²` for `S = 2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_four :
    singleClusterMaxEnergyS 6 4 = (24 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5/2 3-vertex-star ground-state energy** (γ-5 step 329):
`singleClusterGSEnergyS 2 5 = -15 = -S(1+zS)` for `S = 5/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_five :
    singleClusterGSEnergyS 2 5 = (-15 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 329):
`singleClusterMaxEnergyS 2 5 = 25/2 = zS²` for `S = 5/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_five :
    singleClusterMaxEnergyS 2 5 = (25 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5/2 4-vertex-star ground-state energy** (γ-5 step 330):
`singleClusterGSEnergyS 3 5 = -85/4 = -S(1+zS)` for `S = 5/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_five :
    singleClusterGSEnergyS 3 5 = (-85 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 330):
`singleClusterMaxEnergyS 3 5 = 75/4 = zS²` for `S = 5/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_five :
    singleClusterMaxEnergyS 3 5 = (75 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5/2 5-vertex-star ground-state energy** (γ-5 step 331):
`singleClusterGSEnergyS 4 5 = -55/2 = -S(1+zS)` for `S = 5/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_five :
    singleClusterGSEnergyS 4 5 = (-55 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 331):
`singleClusterMaxEnergyS 4 5 = 25 = zS²` for `S = 5/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_five :
    singleClusterMaxEnergyS 4 5 = (25 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5/2 6-vertex-star ground-state energy** (γ-5 step 332):
`singleClusterGSEnergyS 5 5 = -135/4 = -S(1+zS)` for `S = 5/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_five :
    singleClusterGSEnergyS 5 5 = (-135 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 332):
`singleClusterMaxEnergyS 5 5 = 125/4 = zS²` for `S = 5/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_five :
    singleClusterMaxEnergyS 5 5 = (125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5/2 7-vertex-star ground-state energy** (γ-5 step 333):
`singleClusterGSEnergyS 6 5 = -40 = -S(1+zS)` for `S = 5/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_five :
    singleClusterGSEnergyS 6 5 = (-40 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 333):
`singleClusterMaxEnergyS 6 5 = 75/2 = zS²` for `S = 5/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_five :
    singleClusterMaxEnergyS 6 5 = (75 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3 5-vertex-star ground-state energy** (γ-5 step 334):
`singleClusterGSEnergyS 4 6 = -39 = -S(1+zS)` for `S = 3, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_six :
    singleClusterGSEnergyS 4 6 = (-39 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 334):
`singleClusterMaxEnergyS 4 6 = 36 = zS²` for `S = 3, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_six :
    singleClusterMaxEnergyS 4 6 = (36 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3 6-vertex-star ground-state energy** (γ-5 step 335):
`singleClusterGSEnergyS 5 6 = -48 = -S(1+zS)` for `S = 3, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_six :
    singleClusterGSEnergyS 5 6 = (-48 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 335):
`singleClusterMaxEnergyS 5 6 = 45 = zS²` for `S = 3, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_six :
    singleClusterMaxEnergyS 5 6 = (45 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-3 7-vertex-star ground-state energy** (γ-5 step 336):
`singleClusterGSEnergyS 6 6 = -57 = -S(1+zS)` for `S = 3, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_six :
    singleClusterGSEnergyS 6 6 = (-57 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-3 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 336):
`singleClusterMaxEnergyS 6 6 = 54 = zS²` for `S = 3, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_six :
    singleClusterMaxEnergyS 6 6 = (54 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7/2 dimer ground-state energy** (γ-5 step 337):
`singleClusterGSEnergyS 1 7 = -63/4 = -S(S+1)` for `S = 7/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_seven :
    singleClusterGSEnergyS 1 7 = (-63 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7/2 dimer maximum-Casimir-sector energy** (γ-5 step 337):
`singleClusterMaxEnergyS 1 7 = 49/4 = S²` for `S = 7/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seven :
    singleClusterMaxEnergyS 1 7 = (49 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7/2 3-vertex-star ground-state energy** (γ-5 step 338):
`singleClusterGSEnergyS 2 7 = -28 = -S(1+zS)` for `S = 7/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seven :
    singleClusterGSEnergyS 2 7 = (-28 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 338):
`singleClusterMaxEnergyS 2 7 = 49/2 = zS²` for `S = 7/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seven :
    singleClusterMaxEnergyS 2 7 = (49 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-4 3-vertex-star ground-state energy** (γ-5 step 339):
`singleClusterGSEnergyS 2 8 = -36 = -S(1+zS)` for `S = 4, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eight :
    singleClusterGSEnergyS 2 8 = (-36 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-4 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 339):
`singleClusterMaxEnergyS 2 8 = 32 = zS²` for `S = 4, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eight :
    singleClusterMaxEnergyS 2 8 = (32 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-4 4-vertex-star ground-state energy** (γ-5 step 340):
`singleClusterGSEnergyS 3 8 = -52 = -S(1+zS)` for `S = 4, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eight :
    singleClusterGSEnergyS 3 8 = (-52 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-4 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 340):
`singleClusterMaxEnergyS 3 8 = 48 = zS²` for `S = 4, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eight :
    singleClusterMaxEnergyS 3 8 = (48 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-4 5-vertex-star ground-state energy** (γ-5 step 341):
`singleClusterGSEnergyS 4 8 = -68 = -S(1+zS)` for `S = 4, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eight :
    singleClusterGSEnergyS 4 8 = (-68 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-4 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 341):
`singleClusterMaxEnergyS 4 8 = 64 = zS²` for `S = 4, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eight :
    singleClusterMaxEnergyS 4 8 = (64 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-4 6-vertex-star ground-state energy** (γ-5 step 342):
`singleClusterGSEnergyS 5 8 = -84 = -S(1+zS)` for `S = 4, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eight :
    singleClusterGSEnergyS 5 8 = (-84 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-4 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 342):
`singleClusterMaxEnergyS 5 8 = 80 = zS²` for `S = 4, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eight :
    singleClusterMaxEnergyS 5 8 = (80 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-4 7-vertex-star ground-state energy** (γ-5 step 343):
`singleClusterGSEnergyS 6 8 = -100 = -S(1+zS)` for `S = 4, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eight :
    singleClusterGSEnergyS 6 8 = (-100 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-4 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 343):
`singleClusterMaxEnergyS 6 8 = 96 = zS²` for `S = 4, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eight :
    singleClusterMaxEnergyS 6 8 = (96 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7/2 4-vertex-star ground-state energy** (γ-5 step 344):
`singleClusterGSEnergyS 3 7 = -161/4 = -S(1+zS)` for `S = 7/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seven :
    singleClusterGSEnergyS 3 7 = (-161 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 344):
`singleClusterMaxEnergyS 3 7 = 147/4 = zS²` for `S = 7/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seven :
    singleClusterMaxEnergyS 3 7 = (147 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7/2 5-vertex-star ground-state energy** (γ-5 step 345):
`singleClusterGSEnergyS 4 7 = -105/2 = -S(1+zS)` for `S = 7/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seven :
    singleClusterGSEnergyS 4 7 = (-105 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 345):
`singleClusterMaxEnergyS 4 7 = 49 = zS²` for `S = 7/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seven :
    singleClusterMaxEnergyS 4 7 = (49 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7/2 6-vertex-star ground-state energy** (γ-5 step 346):
`singleClusterGSEnergyS 5 7 = -259/4 = -S(1+zS)` for `S = 7/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seven :
    singleClusterGSEnergyS 5 7 = (-259 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 346):
`singleClusterMaxEnergyS 5 7 = 245/4 = zS²` for `S = 7/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seven :
    singleClusterMaxEnergyS 5 7 = (245 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7/2 7-vertex-star ground-state energy** (γ-5 step 347):
`singleClusterGSEnergyS 6 7 = -77 = -S(1+zS)` for `S = 7/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seven :
    singleClusterGSEnergyS 6 7 = (-77 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 347):
`singleClusterMaxEnergyS 6 7 = 147/2 = zS²` for `S = 7/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seven :
    singleClusterMaxEnergyS 6 7 = (147 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9/2 dimer ground-state energy** (γ-5 step 348):
`singleClusterGSEnergyS 1 9 = -99/4 = -S(S+1)` for `S = 9/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_nine :
    singleClusterGSEnergyS 1 9 = (-99 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9/2 dimer maximum-Casimir-sector energy** (γ-5 step 348):
`singleClusterMaxEnergyS 1 9 = 81/4 = S²` for `S = 9/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_nine :
    singleClusterMaxEnergyS 1 9 = (81 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9/2 3-vertex-star ground-state energy** (γ-5 step 349):
`singleClusterGSEnergyS 2 9 = -45 = -S(1+zS)` for `S = 9/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_nine :
    singleClusterGSEnergyS 2 9 = (-45 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 349):
`singleClusterMaxEnergyS 2 9 = 81/2 = zS²` for `S = 9/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_nine :
    singleClusterMaxEnergyS 2 9 = (81 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9/2 4-vertex-star ground-state energy** (γ-5 step 350):
`singleClusterGSEnergyS 3 9 = -261/4 = -S(1+zS)` for `S = 9/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_nine :
    singleClusterGSEnergyS 3 9 = (-261 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 350):
`singleClusterMaxEnergyS 3 9 = 243/4 = zS²` for `S = 9/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_nine :
    singleClusterMaxEnergyS 3 9 = (243 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9/2 5-vertex-star ground-state energy** (γ-5 step 351):
`singleClusterGSEnergyS 4 9 = -171/2 = -S(1+zS)` for `S = 9/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_nine :
    singleClusterGSEnergyS 4 9 = (-171 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 351):
`singleClusterMaxEnergyS 4 9 = 81 = zS²` for `S = 9/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_nine :
    singleClusterMaxEnergyS 4 9 = (81 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9/2 6-vertex-star ground-state energy** (γ-5 step 352):
`singleClusterGSEnergyS 5 9 = -423/4 = -S(1+zS)` for `S = 9/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_nine :
    singleClusterGSEnergyS 5 9 = (-423 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 352):
`singleClusterMaxEnergyS 5 9 = 405/4 = zS²` for `S = 9/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_nine :
    singleClusterMaxEnergyS 5 9 = (405 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9/2 7-vertex-star ground-state energy** (γ-5 step 353):
`singleClusterGSEnergyS 6 9 = -126 = -S(1+zS)` for `S = 9/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_nine :
    singleClusterGSEnergyS 6 9 = (-126 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 353):
`singleClusterMaxEnergyS 6 9 = 243/2 = zS²` for `S = 9/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_nine :
    singleClusterMaxEnergyS 6 9 = (243 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5 dimer ground-state energy** (γ-5 step 354):
`singleClusterGSEnergyS 1 10 = -30 = -S(S+1)` for `S = 5`. -/
@[simp] theorem singleClusterGSEnergyS_one_ten :
    singleClusterGSEnergyS 1 10 = (-30 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5 dimer maximum-Casimir-sector energy** (γ-5 step 354):
`singleClusterMaxEnergyS 1 10 = 25 = S²` for `S = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_one_ten :
    singleClusterMaxEnergyS 1 10 = (25 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5 3-vertex-star ground-state energy** (γ-5 step 355):
`singleClusterGSEnergyS 2 10 = -55 = -S(1+zS)` for `S = 5, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_ten :
    singleClusterGSEnergyS 2 10 = (-55 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 355):
`singleClusterMaxEnergyS 2 10 = 50 = zS²` for `S = 5, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_ten :
    singleClusterMaxEnergyS 2 10 = (50 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5 4-vertex-star ground-state energy** (γ-5 step 356):
`singleClusterGSEnergyS 3 10 = -80 = -S(1+zS)` for `S = 5, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_ten :
    singleClusterGSEnergyS 3 10 = (-80 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 356):
`singleClusterMaxEnergyS 3 10 = 75 = zS²` for `S = 5, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_ten :
    singleClusterMaxEnergyS 3 10 = (75 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5 5-vertex-star ground-state energy** (γ-5 step 357):
`singleClusterGSEnergyS 4 10 = -105 = -S(1+zS)` for `S = 5, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_ten :
    singleClusterGSEnergyS 4 10 = (-105 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 357):
`singleClusterMaxEnergyS 4 10 = 100 = zS²` for `S = 5, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_ten :
    singleClusterMaxEnergyS 4 10 = (100 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5 6-vertex-star ground-state energy** (γ-5 step 358):
`singleClusterGSEnergyS 5 10 = -130 = -S(1+zS)` for `S = 5, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_ten :
    singleClusterGSEnergyS 5 10 = (-130 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 358):
`singleClusterMaxEnergyS 5 10 = 125 = zS²` for `S = 5, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_ten :
    singleClusterMaxEnergyS 5 10 = (125 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-5 7-vertex-star ground-state energy** (γ-5 step 359):
`singleClusterGSEnergyS 6 10 = -155 = -S(1+zS)` for `S = 5, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_ten :
    singleClusterGSEnergyS 6 10 = (-155 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-5 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 359):
`singleClusterMaxEnergyS 6 10 = 150 = zS²` for `S = 5, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_ten :
    singleClusterMaxEnergyS 6 10 = (150 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11/2 dimer ground-state energy** (γ-5 step 360):
`singleClusterGSEnergyS 1 11 = -143/4 = -S(S+1)` for `S = 11/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_eleven :
    singleClusterGSEnergyS 1 11 = (-143 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11/2 dimer maximum-Casimir-sector energy** (γ-5 step 360):
`singleClusterMaxEnergyS 1 11 = 121/4 = S²` for `S = 11/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eleven :
    singleClusterMaxEnergyS 1 11 = (121 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11/2 3-vertex-star ground-state energy** (γ-5 step 361):
`singleClusterGSEnergyS 2 11 = -66 = -S(1+zS)` for `S = 11/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eleven :
    singleClusterGSEnergyS 2 11 = (-66 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 361):
`singleClusterMaxEnergyS 2 11 = 121/2 = zS²` for `S = 11/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eleven :
    singleClusterMaxEnergyS 2 11 = (121 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11/2 4-vertex-star ground-state energy** (γ-5 step 362):
`singleClusterGSEnergyS 3 11 = -385/4 = -S(1+zS)` for `S = 11/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eleven :
    singleClusterGSEnergyS 3 11 = (-385 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 362):
`singleClusterMaxEnergyS 3 11 = 363/4 = zS²` for `S = 11/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eleven :
    singleClusterMaxEnergyS 3 11 = (363 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11/2 5-vertex-star ground-state energy** (γ-5 step 363):
`singleClusterGSEnergyS 4 11 = -253/2 = -S(1+zS)` for `S = 11/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eleven :
    singleClusterGSEnergyS 4 11 = (-253 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 363):
`singleClusterMaxEnergyS 4 11 = 121 = zS²` for `S = 11/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eleven :
    singleClusterMaxEnergyS 4 11 = (121 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11/2 6-vertex-star ground-state energy** (γ-5 step 364):
`singleClusterGSEnergyS 5 11 = -627/4 = -S(1+zS)` for `S = 11/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eleven :
    singleClusterGSEnergyS 5 11 = (-627 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 364):
`singleClusterMaxEnergyS 5 11 = 605/4 = zS²` for `S = 11/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eleven :
    singleClusterMaxEnergyS 5 11 = (605 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11/2 7-vertex-star ground-state energy** (γ-5 step 365):
`singleClusterGSEnergyS 6 11 = -187 = -S(1+zS)` for `S = 11/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eleven :
    singleClusterGSEnergyS 6 11 = (-187 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 365):
`singleClusterMaxEnergyS 6 11 = 363/2 = zS²` for `S = 11/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eleven :
    singleClusterMaxEnergyS 6 11 = (363 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-6 dimer ground-state energy** (γ-5 step 366):
`singleClusterGSEnergyS 1 12 = -42 = -S(S+1)` for `S = 6`. -/
@[simp] theorem singleClusterGSEnergyS_one_twelve :
    singleClusterGSEnergyS 1 12 = (-42 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-6 dimer maximum-Casimir-sector energy** (γ-5 step 366):
`singleClusterMaxEnergyS 1 12 = 36 = S²` for `S = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twelve :
    singleClusterMaxEnergyS 1 12 = (36 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-6 3-vertex-star ground-state energy** (γ-5 step 367):
`singleClusterGSEnergyS 2 12 = -78 = -S(1+zS)` for `S = 6, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twelve :
    singleClusterGSEnergyS 2 12 = (-78 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-6 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 367):
`singleClusterMaxEnergyS 2 12 = 72 = zS²` for `S = 6, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twelve :
    singleClusterMaxEnergyS 2 12 = (72 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-6 4-vertex-star ground-state energy** (γ-5 step 368):
`singleClusterGSEnergyS 3 12 = -114 = -S(1+zS)` for `S = 6, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twelve :
    singleClusterGSEnergyS 3 12 = (-114 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-6 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 368):
`singleClusterMaxEnergyS 3 12 = 108 = zS²` for `S = 6, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twelve :
    singleClusterMaxEnergyS 3 12 = (108 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-6 5-vertex-star ground-state energy** (γ-5 step 369):
`singleClusterGSEnergyS 4 12 = -150 = -S(1+zS)` for `S = 6, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twelve :
    singleClusterGSEnergyS 4 12 = (-150 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-6 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 369):
`singleClusterMaxEnergyS 4 12 = 144 = zS²` for `S = 6, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twelve :
    singleClusterMaxEnergyS 4 12 = (144 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-6 6-vertex-star ground-state energy** (γ-5 step 370):
`singleClusterGSEnergyS 5 12 = -186 = -S(1+zS)` for `S = 6, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twelve :
    singleClusterGSEnergyS 5 12 = (-186 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-6 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 370):
`singleClusterMaxEnergyS 5 12 = 180 = zS²` for `S = 6, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twelve :
    singleClusterMaxEnergyS 5 12 = (180 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-6 7-vertex-star ground-state energy** (γ-5 step 371):
`singleClusterGSEnergyS 6 12 = -222 = -S(1+zS)` for `S = 6, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twelve :
    singleClusterGSEnergyS 6 12 = (-222 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-6 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 371):
`singleClusterMaxEnergyS 6 12 = 216 = zS²` for `S = 6, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twelve :
    singleClusterMaxEnergyS 6 12 = (216 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13/2 dimer ground-state energy** (γ-5 step 372):
`singleClusterGSEnergyS 1 13 = -195/4 = -S(S+1)` for `S = 13/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_thirteen :
    singleClusterGSEnergyS 1 13 = (-195 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13/2 dimer maximum-Casimir-sector energy** (γ-5 step 372):
`singleClusterMaxEnergyS 1 13 = 169/4 = S²` for `S = 13/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_thirteen :
    singleClusterMaxEnergyS 1 13 = (169 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7 dimer ground-state energy** (γ-5 step 373):
`singleClusterGSEnergyS 1 14 = -56 = -S(S+1)` for `S = 7`. -/
@[simp] theorem singleClusterGSEnergyS_one_fourteen :
    singleClusterGSEnergyS 1 14 = (-56 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7 dimer maximum-Casimir-sector energy** (γ-5 step 373):
`singleClusterMaxEnergyS 1 14 = 49 = S²` for `S = 7`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fourteen :
    singleClusterMaxEnergyS 1 14 = (49 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15/2 dimer ground-state energy** (γ-5 step 374):
`singleClusterGSEnergyS 1 15 = -255/4 = -S(S+1)` for `S = 15/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_fifteen :
    singleClusterGSEnergyS 1 15 = (-255 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15/2 dimer maximum-Casimir-sector energy** (γ-5 step 374):
`singleClusterMaxEnergyS 1 15 = 225/4 = S²` for `S = 15/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_fifteen :
    singleClusterMaxEnergyS 1 15 = (225 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-8 dimer ground-state energy** (γ-5 step 375):
`singleClusterGSEnergyS 1 16 = -72 = -S(S+1)` for `S = 8`. -/
@[simp] theorem singleClusterGSEnergyS_one_sixteen :
    singleClusterGSEnergyS 1 16 = (-72 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-8 dimer maximum-Casimir-sector energy** (γ-5 step 375):
`singleClusterMaxEnergyS 1 16 = 64 = S²` for `S = 8`. -/
@[simp] theorem singleClusterMaxEnergyS_one_sixteen :
    singleClusterMaxEnergyS 1 16 = (64 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-8 3-vertex-star ground-state energy** (γ-5 step 391):
`singleClusterGSEnergyS 2 16 = -136 = -S(1+zS)` for `S = 8, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_sixteen :
    singleClusterGSEnergyS 2 16 = (-136 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-8 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 391):
`singleClusterMaxEnergyS 2 16 = 128 = zS²` for `S = 8, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_sixteen :
    singleClusterMaxEnergyS 2 16 = (128 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-8 4-vertex-star ground-state energy** (γ-5 step 392):
`singleClusterGSEnergyS 3 16 = -200 = -S(1+zS)` for `S = 8, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_sixteen :
    singleClusterGSEnergyS 3 16 = (-200 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-8 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 392):
`singleClusterMaxEnergyS 3 16 = 192 = zS²` for `S = 8, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_sixteen :
    singleClusterMaxEnergyS 3 16 = (192 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-8 5-vertex-star ground-state energy** (γ-5 step 393):
`singleClusterGSEnergyS 4 16 = -264 = -S(1+zS)` for `S = 8, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_sixteen :
    singleClusterGSEnergyS 4 16 = (-264 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-8 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 393):
`singleClusterMaxEnergyS 4 16 = 256 = zS²` for `S = 8, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_sixteen :
    singleClusterMaxEnergyS 4 16 = (256 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-8 6-vertex-star ground-state energy** (γ-5 step 394):
`singleClusterGSEnergyS 5 16 = -328 = -S(1+zS)` for `S = 8, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_sixteen :
    singleClusterGSEnergyS 5 16 = (-328 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-8 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 394):
`singleClusterMaxEnergyS 5 16 = 320 = zS²` for `S = 8, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_sixteen :
    singleClusterMaxEnergyS 5 16 = (320 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-8 7-vertex-star ground-state energy** (γ-5 step 395):
`singleClusterGSEnergyS 6 16 = -392 = -S(1+zS)` for `S = 8, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_sixteen :
    singleClusterGSEnergyS 6 16 = (-392 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-8 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 395):
`singleClusterMaxEnergyS 6 16 = 384 = zS²` for `S = 8, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_sixteen :
    singleClusterMaxEnergyS 6 16 = (384 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7 3-vertex-star ground-state energy** (γ-5 step 376):
`singleClusterGSEnergyS 2 14 = -105 = -S(1+zS)` for `S = 7, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fourteen :
    singleClusterGSEnergyS 2 14 = (-105 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 376):
`singleClusterMaxEnergyS 2 14 = 98 = zS²` for `S = 7, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fourteen :
    singleClusterMaxEnergyS 2 14 = (98 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7 4-vertex-star ground-state energy** (γ-5 step 377):
`singleClusterGSEnergyS 3 14 = -154 = -S(1+zS)` for `S = 7, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fourteen :
    singleClusterGSEnergyS 3 14 = (-154 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 377):
`singleClusterMaxEnergyS 3 14 = 147 = zS²` for `S = 7, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fourteen :
    singleClusterMaxEnergyS 3 14 = (147 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7 5-vertex-star ground-state energy** (γ-5 step 378):
`singleClusterGSEnergyS 4 14 = -203 = -S(1+zS)` for `S = 7, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fourteen :
    singleClusterGSEnergyS 4 14 = (-203 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 378):
`singleClusterMaxEnergyS 4 14 = 196 = zS²` for `S = 7, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fourteen :
    singleClusterMaxEnergyS 4 14 = (196 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7 6-vertex-star ground-state energy** (γ-5 step 379):
`singleClusterGSEnergyS 5 14 = -252 = -S(1+zS)` for `S = 7, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fourteen :
    singleClusterGSEnergyS 5 14 = (-252 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 379):
`singleClusterMaxEnergyS 5 14 = 245 = zS²` for `S = 7, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fourteen :
    singleClusterMaxEnergyS 5 14 = (245 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-7 7-vertex-star ground-state energy** (γ-5 step 380):
`singleClusterGSEnergyS 6 14 = -301 = -S(1+zS)` for `S = 7, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fourteen :
    singleClusterGSEnergyS 6 14 = (-301 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-7 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 380):
`singleClusterMaxEnergyS 6 14 = 294 = zS²` for `S = 7, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fourteen :
    singleClusterMaxEnergyS 6 14 = (294 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13/2 3-vertex-star ground-state energy** (γ-5 step 381):
`singleClusterGSEnergyS 2 13 = -91 = -S(1+zS)` for `S = 13/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_thirteen :
    singleClusterGSEnergyS 2 13 = (-91 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 381):
`singleClusterMaxEnergyS 2 13 = 169/2 = zS²` for `S = 13/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_thirteen :
    singleClusterMaxEnergyS 2 13 = (169 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13/2 4-vertex-star ground-state energy** (γ-5 step 382):
`singleClusterGSEnergyS 3 13 = -533/4 = -S(1+zS)` for `S = 13/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_thirteen :
    singleClusterGSEnergyS 3 13 = (-533 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 382):
`singleClusterMaxEnergyS 3 13 = 507/4 = zS²` for `S = 13/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_thirteen :
    singleClusterMaxEnergyS 3 13 = (507 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13/2 5-vertex-star ground-state energy** (γ-5 step 383):
`singleClusterGSEnergyS 4 13 = -351/2 = -S(1+zS)` for `S = 13/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_thirteen :
    singleClusterGSEnergyS 4 13 = (-351 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 383):
`singleClusterMaxEnergyS 4 13 = 169 = zS²` for `S = 13/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_thirteen :
    singleClusterMaxEnergyS 4 13 = (169 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13/2 6-vertex-star ground-state energy** (γ-5 step 384):
`singleClusterGSEnergyS 5 13 = -871/4 = -S(1+zS)` for `S = 13/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_thirteen :
    singleClusterGSEnergyS 5 13 = (-871 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 384):
`singleClusterMaxEnergyS 5 13 = 845/4 = zS²` for `S = 13/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_thirteen :
    singleClusterMaxEnergyS 5 13 = (845 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13/2 7-vertex-star ground-state energy** (γ-5 step 385):
`singleClusterGSEnergyS 6 13 = -260 = -S(1+zS)` for `S = 13/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_thirteen :
    singleClusterGSEnergyS 6 13 = (-260 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 385):
`singleClusterMaxEnergyS 6 13 = 507/2 = zS²` for `S = 13/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_thirteen :
    singleClusterMaxEnergyS 6 13 = (507 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15/2 3-vertex-star ground-state energy** (γ-5 step 386):
`singleClusterGSEnergyS 2 15 = -120 = -S(1+zS)` for `S = 15/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_fifteen :
    singleClusterGSEnergyS 2 15 = (-120 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 386):
`singleClusterMaxEnergyS 2 15 = 225/2 = zS²` for `S = 15/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_fifteen :
    singleClusterMaxEnergyS 2 15 = (225 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15/2 4-vertex-star ground-state energy** (γ-5 step 387):
`singleClusterGSEnergyS 3 15 = -705/4 = -S(1+zS)` for `S = 15/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_fifteen :
    singleClusterGSEnergyS 3 15 = (-705 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 387):
`singleClusterMaxEnergyS 3 15 = 675/4 = zS²` for `S = 15/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_fifteen :
    singleClusterMaxEnergyS 3 15 = (675 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15/2 5-vertex-star ground-state energy** (γ-5 step 388):
`singleClusterGSEnergyS 4 15 = -465/2 = -S(1+zS)` for `S = 15/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_fifteen :
    singleClusterGSEnergyS 4 15 = (-465 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 388):
`singleClusterMaxEnergyS 4 15 = 225 = zS²` for `S = 15/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_fifteen :
    singleClusterMaxEnergyS 4 15 = (225 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15/2 6-vertex-star ground-state energy** (γ-5 step 389):
`singleClusterGSEnergyS 5 15 = -1155/4 = -S(1+zS)` for `S = 15/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_fifteen :
    singleClusterGSEnergyS 5 15 = (-1155 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 389):
`singleClusterMaxEnergyS 5 15 = 1125/4 = zS²` for `S = 15/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_fifteen :
    singleClusterMaxEnergyS 5 15 = (1125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-15/2 7-vertex-star ground-state energy** (γ-5 step 390):
`singleClusterGSEnergyS 6 15 = -345 = -S(1+zS)` for `S = 15/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_fifteen :
    singleClusterGSEnergyS 6 15 = (-345 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-15/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 390):
`singleClusterMaxEnergyS 6 15 = 675/2 = zS²` for `S = 15/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_fifteen :
    singleClusterMaxEnergyS 6 15 = (675 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17/2 dimer ground-state energy** (γ-5 step 396):
`singleClusterGSEnergyS 1 17 = -323/4 = -S(S+1)` for `S = 17/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_seventeen :
    singleClusterGSEnergyS 1 17 = (-323 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17/2 dimer maximum-Casimir-sector energy** (γ-5 step 396):
`singleClusterMaxEnergyS 1 17 = 289/4 = S²` for `S = 17/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_seventeen :
    singleClusterMaxEnergyS 1 17 = (289 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17/2 3-vertex-star ground-state energy** (γ-5 step 397):
`singleClusterGSEnergyS 2 17 = -153 = -S(1+zS)` for `S = 17/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_seventeen :
    singleClusterGSEnergyS 2 17 = (-153 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 397):
`singleClusterMaxEnergyS 2 17 = 289/2 = zS²` for `S = 17/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_seventeen :
    singleClusterMaxEnergyS 2 17 = (289 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17/2 4-vertex-star ground-state energy** (γ-5 step 398):
`singleClusterGSEnergyS 3 17 = -901/4 = -S(1+zS)` for `S = 17/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_seventeen :
    singleClusterGSEnergyS 3 17 = (-901 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 398):
`singleClusterMaxEnergyS 3 17 = 867/4 = zS²` for `S = 17/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_seventeen :
    singleClusterMaxEnergyS 3 17 = (867 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17/2 5-vertex-star ground-state energy** (γ-5 step 399):
`singleClusterGSEnergyS 4 17 = -595/2 = -S(1+zS)` for `S = 17/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_seventeen :
    singleClusterGSEnergyS 4 17 = (-595 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 399):
`singleClusterMaxEnergyS 4 17 = 289 = zS²` for `S = 17/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_seventeen :
    singleClusterMaxEnergyS 4 17 = (289 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17/2 6-vertex-star ground-state energy** (γ-5 step 400):
`singleClusterGSEnergyS 5 17 = -1479/4 = -S(1+zS)` for `S = 17/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_seventeen :
    singleClusterGSEnergyS 5 17 = (-1479 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 400):
`singleClusterMaxEnergyS 5 17 = 1445/4 = zS²` for `S = 17/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_seventeen :
    singleClusterMaxEnergyS 5 17 = (1445 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-17/2 7-vertex-star ground-state energy** (γ-5 step 401):
`singleClusterGSEnergyS 6 17 = -442 = -S(1+zS)` for `S = 17/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_seventeen :
    singleClusterGSEnergyS 6 17 = (-442 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-17/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 401):
`singleClusterMaxEnergyS 6 17 = 867/2 = zS²` for `S = 17/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_seventeen :
    singleClusterMaxEnergyS 6 17 = (867 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9 dimer ground-state energy** (γ-5 step 402):
`singleClusterGSEnergyS 1 18 = -90 = -S(S+1)` for `S = 9`. -/
@[simp] theorem singleClusterGSEnergyS_one_eighteen :
    singleClusterGSEnergyS 1 18 = (-90 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9 dimer maximum-Casimir-sector energy** (γ-5 step 402):
`singleClusterMaxEnergyS 1 18 = 81 = S²` for `S = 9`. -/
@[simp] theorem singleClusterMaxEnergyS_one_eighteen :
    singleClusterMaxEnergyS 1 18 = (81 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9 3-vertex-star ground-state energy** (γ-5 step 403):
`singleClusterGSEnergyS 2 18 = -171 = -S(1+zS)` for `S = 9, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_eighteen :
    singleClusterGSEnergyS 2 18 = (-171 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 403):
`singleClusterMaxEnergyS 2 18 = 162 = zS²` for `S = 9, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_eighteen :
    singleClusterMaxEnergyS 2 18 = (162 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9 4-vertex-star ground-state energy** (γ-5 step 404):
`singleClusterGSEnergyS 3 18 = -252 = -S(1+zS)` for `S = 9, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_eighteen :
    singleClusterGSEnergyS 3 18 = (-252 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 404):
`singleClusterMaxEnergyS 3 18 = 243 = zS²` for `S = 9, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_eighteen :
    singleClusterMaxEnergyS 3 18 = (243 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9 5-vertex-star ground-state energy** (γ-5 step 405):
`singleClusterGSEnergyS 4 18 = -333 = -S(1+zS)` for `S = 9, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_eighteen :
    singleClusterGSEnergyS 4 18 = (-333 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 405):
`singleClusterMaxEnergyS 4 18 = 324 = zS²` for `S = 9, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_eighteen :
    singleClusterMaxEnergyS 4 18 = (324 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9 6-vertex-star ground-state energy** (γ-5 step 406):
`singleClusterGSEnergyS 5 18 = -414 = -S(1+zS)` for `S = 9, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_eighteen :
    singleClusterGSEnergyS 5 18 = (-414 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 406):
`singleClusterMaxEnergyS 5 18 = 405 = zS²` for `S = 9, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_eighteen :
    singleClusterMaxEnergyS 5 18 = (405 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-9 7-vertex-star ground-state energy** (γ-5 step 407):
`singleClusterGSEnergyS 6 18 = -495 = -S(1+zS)` for `S = 9, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_eighteen :
    singleClusterGSEnergyS 6 18 = (-495 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-9 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 407):
`singleClusterMaxEnergyS 6 18 = 486 = zS²` for `S = 9, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_eighteen :
    singleClusterMaxEnergyS 6 18 = (486 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19/2 dimer ground-state energy** (γ-5 step 408):
`singleClusterGSEnergyS 1 19 = -399/4 = -S(S+1)` for `S = 19/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_nineteen :
    singleClusterGSEnergyS 1 19 = (-399 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19/2 dimer maximum-Casimir-sector energy** (γ-5 step 408):
`singleClusterMaxEnergyS 1 19 = 361/4 = S²` for `S = 19/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_nineteen :
    singleClusterMaxEnergyS 1 19 = (361 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19/2 3-vertex-star ground-state energy** (γ-5 step 409):
`singleClusterGSEnergyS 2 19 = -190 = -S(1+zS)` for `S = 19/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_nineteen :
    singleClusterGSEnergyS 2 19 = (-190 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 409):
`singleClusterMaxEnergyS 2 19 = 361/2 = zS²` for `S = 19/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_nineteen :
    singleClusterMaxEnergyS 2 19 = (361 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19/2 4-vertex-star ground-state energy** (γ-5 step 410):
`singleClusterGSEnergyS 3 19 = -1121/4 = -S(1+zS)` for `S = 19/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_nineteen :
    singleClusterGSEnergyS 3 19 = (-1121 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 410):
`singleClusterMaxEnergyS 3 19 = 1083/4 = zS²` for `S = 19/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_nineteen :
    singleClusterMaxEnergyS 3 19 = (1083 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19/2 5-vertex-star ground-state energy** (γ-5 step 411):
`singleClusterGSEnergyS 4 19 = -741/2 = -S(1+zS)` for `S = 19/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_nineteen :
    singleClusterGSEnergyS 4 19 = (-741 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 411):
`singleClusterMaxEnergyS 4 19 = 361 = zS²` for `S = 19/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_nineteen :
    singleClusterMaxEnergyS 4 19 = (361 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19/2 6-vertex-star ground-state energy** (γ-5 step 412):
`singleClusterGSEnergyS 5 19 = -1843/4 = -S(1+zS)` for `S = 19/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_nineteen :
    singleClusterGSEnergyS 5 19 = (-1843 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 412):
`singleClusterMaxEnergyS 5 19 = 1805/4 = zS²` for `S = 19/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_nineteen :
    singleClusterMaxEnergyS 5 19 = (1805 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-19/2 7-vertex-star ground-state energy** (γ-5 step 413):
`singleClusterGSEnergyS 6 19 = -551 = -S(1+zS)` for `S = 19/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_nineteen :
    singleClusterGSEnergyS 6 19 = (-551 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-19/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 413):
`singleClusterMaxEnergyS 6 19 = 1083/2 = zS²` for `S = 19/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_nineteen :
    singleClusterMaxEnergyS 6 19 = (1083 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-10 dimer ground-state energy** (γ-5 step 414):
`singleClusterGSEnergyS 1 20 = -110 = -S(S+1)` for `S = 10`. -/
@[simp] theorem singleClusterGSEnergyS_one_twenty :
    singleClusterGSEnergyS 1 20 = (-110 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-10 dimer maximum-Casimir-sector energy** (γ-5 step 414):
`singleClusterMaxEnergyS 1 20 = 100 = S²` for `S = 10`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twenty :
    singleClusterMaxEnergyS 1 20 = (100 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-10 3-vertex-star ground-state energy** (γ-5 step 415):
`singleClusterGSEnergyS 2 20 = -210 = -S(1+zS)` for `S = 10, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twenty :
    singleClusterGSEnergyS 2 20 = (-210 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-10 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 415):
`singleClusterMaxEnergyS 2 20 = 200 = zS²` for `S = 10, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twenty :
    singleClusterMaxEnergyS 2 20 = (200 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-10 4-vertex-star ground-state energy** (γ-5 step 416):
`singleClusterGSEnergyS 3 20 = -310 = -S(1+zS)` for `S = 10, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twenty :
    singleClusterGSEnergyS 3 20 = (-310 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-10 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 416):
`singleClusterMaxEnergyS 3 20 = 300 = zS²` for `S = 10, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twenty :
    singleClusterMaxEnergyS 3 20 = (300 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-10 5-vertex-star ground-state energy** (γ-5 step 417):
`singleClusterGSEnergyS 4 20 = -410 = -S(1+zS)` for `S = 10, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twenty :
    singleClusterGSEnergyS 4 20 = (-410 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-10 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 417):
`singleClusterMaxEnergyS 4 20 = 400 = zS²` for `S = 10, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twenty :
    singleClusterMaxEnergyS 4 20 = (400 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-10 6-vertex-star ground-state energy** (γ-5 step 418):
`singleClusterGSEnergyS 5 20 = -510 = -S(1+zS)` for `S = 10, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twenty :
    singleClusterGSEnergyS 5 20 = (-510 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-10 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 418):
`singleClusterMaxEnergyS 5 20 = 500 = zS²` for `S = 10, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twenty :
    singleClusterMaxEnergyS 5 20 = (500 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-10 7-vertex-star ground-state energy** (γ-5 step 419):
`singleClusterGSEnergyS 6 20 = -610 = -S(1+zS)` for `S = 10, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twenty :
    singleClusterGSEnergyS 6 20 = (-610 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-10 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 419):
`singleClusterMaxEnergyS 6 20 = 600 = zS²` for `S = 10, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twenty :
    singleClusterMaxEnergyS 6 20 = (600 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21/2 dimer ground-state energy** (γ-5 step 420):
`singleClusterGSEnergyS 1 21 = -483/4 = -S(S+1)` for `S = 21/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentyone :
    singleClusterGSEnergyS 1 21 = (-483 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21/2 dimer maximum-Casimir-sector energy** (γ-5 step 420):
`singleClusterMaxEnergyS 1 21 = 441/4 = S²` for `S = 21/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentyone :
    singleClusterMaxEnergyS 1 21 = (441 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21/2 3-vertex-star ground-state energy** (γ-5 step 421):
`singleClusterGSEnergyS 2 21 = -231 = -S(1+zS)` for `S = 21/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentyone :
    singleClusterGSEnergyS 2 21 = (-231 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 421):
`singleClusterMaxEnergyS 2 21 = 441/2 = zS²` for `S = 21/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentyone :
    singleClusterMaxEnergyS 2 21 = (441 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21/2 4-vertex-star ground-state energy** (γ-5 step 422):
`singleClusterGSEnergyS 3 21 = -1365/4 = -S(1+zS)` for `S = 21/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentyone :
    singleClusterGSEnergyS 3 21 = (-1365 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 422):
`singleClusterMaxEnergyS 3 21 = 1323/4 = zS²` for `S = 21/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentyone :
    singleClusterMaxEnergyS 3 21 = (1323 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21/2 5-vertex-star ground-state energy** (γ-5 step 423):
`singleClusterGSEnergyS 4 21 = -903/2 = -S(1+zS)` for `S = 21/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentyone :
    singleClusterGSEnergyS 4 21 = (-903 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 423):
`singleClusterMaxEnergyS 4 21 = 441 = zS²` for `S = 21/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentyone :
    singleClusterMaxEnergyS 4 21 = (441 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21/2 6-vertex-star ground-state energy** (γ-5 step 424):
`singleClusterGSEnergyS 5 21 = -2247/4 = -S(1+zS)` for `S = 21/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentyone :
    singleClusterGSEnergyS 5 21 = (-2247 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 424):
`singleClusterMaxEnergyS 5 21 = 2205/4 = zS²` for `S = 21/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentyone :
    singleClusterMaxEnergyS 5 21 = (2205 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-21/2 7-vertex-star ground-state energy** (γ-5 step 425):
`singleClusterGSEnergyS 6 21 = -672 = -S(1+zS)` for `S = 21/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentyone :
    singleClusterGSEnergyS 6 21 = (-672 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-21/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 425):
`singleClusterMaxEnergyS 6 21 = 1323/2 = zS²` for `S = 21/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentyone :
    singleClusterMaxEnergyS 6 21 = (1323 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11 dimer ground-state energy** (γ-5 step 426):
`singleClusterGSEnergyS 1 22 = -132 = -S(S+1)` for `S = 11`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentytwo :
    singleClusterGSEnergyS 1 22 = (-132 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11 dimer maximum-Casimir-sector energy** (γ-5 step 426):
`singleClusterMaxEnergyS 1 22 = 121 = S²` for `S = 11`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentytwo :
    singleClusterMaxEnergyS 1 22 = (121 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11 3-vertex-star ground-state energy** (γ-5 step 427):
`singleClusterGSEnergyS 2 22 = -253 = -S(1+zS)` for `S = 11, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentytwo :
    singleClusterGSEnergyS 2 22 = (-253 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 427):
`singleClusterMaxEnergyS 2 22 = 242 = zS²` for `S = 11, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentytwo :
    singleClusterMaxEnergyS 2 22 = (242 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11 4-vertex-star ground-state energy** (γ-5 step 428):
`singleClusterGSEnergyS 3 22 = -374 = -S(1+zS)` for `S = 11, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentytwo :
    singleClusterGSEnergyS 3 22 = (-374 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 428):
`singleClusterMaxEnergyS 3 22 = 363 = zS²` for `S = 11, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentytwo :
    singleClusterMaxEnergyS 3 22 = (363 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11 5-vertex-star ground-state energy** (γ-5 step 429):
`singleClusterGSEnergyS 4 22 = -495 = -S(1+zS)` for `S = 11, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentytwo :
    singleClusterGSEnergyS 4 22 = (-495 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 429):
`singleClusterMaxEnergyS 4 22 = 484 = zS²` for `S = 11, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentytwo :
    singleClusterMaxEnergyS 4 22 = (484 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11 6-vertex-star ground-state energy** (γ-5 step 430):
`singleClusterGSEnergyS 5 22 = -616 = -S(1+zS)` for `S = 11, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentytwo :
    singleClusterGSEnergyS 5 22 = (-616 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 430):
`singleClusterMaxEnergyS 5 22 = 605 = zS²` for `S = 11, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentytwo :
    singleClusterMaxEnergyS 5 22 = (605 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-11 7-vertex-star ground-state energy** (γ-5 step 431):
`singleClusterGSEnergyS 6 22 = -737 = -S(1+zS)` for `S = 11, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentytwo :
    singleClusterGSEnergyS 6 22 = (-737 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-11 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 431):
`singleClusterMaxEnergyS 6 22 = 726 = zS²` for `S = 11, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentytwo :
    singleClusterMaxEnergyS 6 22 = (726 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23/2 dimer ground-state energy** (γ-5 step 432):
`singleClusterGSEnergyS 1 23 = -575/4 = -S(S+1)` for `S = 23/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentythree :
    singleClusterGSEnergyS 1 23 = (-575 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23/2 dimer maximum-Casimir-sector energy** (γ-5 step 432):
`singleClusterMaxEnergyS 1 23 = 529/4 = S²` for `S = 23/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentythree :
    singleClusterMaxEnergyS 1 23 = (529 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23/2 3-vertex-star ground-state energy** (γ-5 step 433):
`singleClusterGSEnergyS 2 23 = -276 = -S(1+zS)` for `S = 23/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentythree :
    singleClusterGSEnergyS 2 23 = (-276 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 433):
`singleClusterMaxEnergyS 2 23 = 529/2 = zS²` for `S = 23/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentythree :
    singleClusterMaxEnergyS 2 23 = (529 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23/2 4-vertex-star ground-state energy** (γ-5 step 434):
`singleClusterGSEnergyS 3 23 = -1633/4 = -S(1+zS)` for `S = 23/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentythree :
    singleClusterGSEnergyS 3 23 = (-1633 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 434):
`singleClusterMaxEnergyS 3 23 = 1587/4 = zS²` for `S = 23/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentythree :
    singleClusterMaxEnergyS 3 23 = (1587 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23/2 5-vertex-star ground-state energy** (γ-5 step 435):
`singleClusterGSEnergyS 4 23 = -1081/2 = -S(1+zS)` for `S = 23/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentythree :
    singleClusterGSEnergyS 4 23 = (-1081 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 435):
`singleClusterMaxEnergyS 4 23 = 529 = zS²` for `S = 23/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentythree :
    singleClusterMaxEnergyS 4 23 = (529 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23/2 6-vertex-star ground-state energy** (γ-5 step 436):
`singleClusterGSEnergyS 5 23 = -2691/4 = -S(1+zS)` for `S = 23/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentythree :
    singleClusterGSEnergyS 5 23 = (-2691 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 436):
`singleClusterMaxEnergyS 5 23 = 2645/4 = zS²` for `S = 23/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentythree :
    singleClusterMaxEnergyS 5 23 = (2645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-23/2 7-vertex-star ground-state energy** (γ-5 step 437):
`singleClusterGSEnergyS 6 23 = -805 = -S(1+zS)` for `S = 23/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentythree :
    singleClusterGSEnergyS 6 23 = (-805 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-23/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 437):
`singleClusterMaxEnergyS 6 23 = 1587/2 = zS²` for `S = 23/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentythree :
    singleClusterMaxEnergyS 6 23 = (1587 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-12 dimer ground-state energy** (γ-5 step 438):
`singleClusterGSEnergyS 1 24 = -156 = -S(S+1)` for `S = 12`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentyfour :
    singleClusterGSEnergyS 1 24 = (-156 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-12 dimer maximum-Casimir-sector energy** (γ-5 step 438):
`singleClusterMaxEnergyS 1 24 = 144 = S²` for `S = 12`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentyfour :
    singleClusterMaxEnergyS 1 24 = (144 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-12 3-vertex-star ground-state energy** (γ-5 step 439):
`singleClusterGSEnergyS 2 24 = -300 = -S(1+zS)` for `S = 12, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentyfour :
    singleClusterGSEnergyS 2 24 = (-300 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-12 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 439):
`singleClusterMaxEnergyS 2 24 = 288 = zS²` for `S = 12, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentyfour :
    singleClusterMaxEnergyS 2 24 = (288 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-12 4-vertex-star ground-state energy** (γ-5 step 440):
`singleClusterGSEnergyS 3 24 = -444 = -S(1+zS)` for `S = 12, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentyfour :
    singleClusterGSEnergyS 3 24 = (-444 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-12 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 440):
`singleClusterMaxEnergyS 3 24 = 432 = zS²` for `S = 12, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentyfour :
    singleClusterMaxEnergyS 3 24 = (432 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-12 5-vertex-star ground-state energy** (γ-5 step 441):
`singleClusterGSEnergyS 4 24 = -588 = -S(1+zS)` for `S = 12, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentyfour :
    singleClusterGSEnergyS 4 24 = (-588 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-12 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 441):
`singleClusterMaxEnergyS 4 24 = 576 = zS²` for `S = 12, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentyfour :
    singleClusterMaxEnergyS 4 24 = (576 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-12 6-vertex-star ground-state energy** (γ-5 step 442):
`singleClusterGSEnergyS 5 24 = -732 = -S(1+zS)` for `S = 12, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentyfour :
    singleClusterGSEnergyS 5 24 = (-732 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-12 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 442):
`singleClusterMaxEnergyS 5 24 = 720 = zS²` for `S = 12, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentyfour :
    singleClusterMaxEnergyS 5 24 = (720 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-12 7-vertex-star ground-state energy** (γ-5 step 443):
`singleClusterGSEnergyS 6 24 = -876 = -S(1+zS)` for `S = 12, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentyfour :
    singleClusterGSEnergyS 6 24 = (-876 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-12 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 443):
`singleClusterMaxEnergyS 6 24 = 864 = zS²` for `S = 12, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentyfour :
    singleClusterMaxEnergyS 6 24 = (864 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25/2 dimer ground-state energy** (γ-5 step 444):
`singleClusterGSEnergyS 1 25 = -675/4 = -S(S+1)` for `S = 25/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentyfive :
    singleClusterGSEnergyS 1 25 = (-675 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25/2 dimer maximum-Casimir-sector energy** (γ-5 step 444):
`singleClusterMaxEnergyS 1 25 = 625/4 = S²` for `S = 25/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentyfive :
    singleClusterMaxEnergyS 1 25 = (625 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25/2 3-vertex-star ground-state energy** (γ-5 step 445):
`singleClusterGSEnergyS 2 25 = -325 = -S(1+zS)` for `S = 25/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentyfive :
    singleClusterGSEnergyS 2 25 = (-325 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 445):
`singleClusterMaxEnergyS 2 25 = 625/2 = zS²` for `S = 25/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentyfive :
    singleClusterMaxEnergyS 2 25 = (625 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25/2 4-vertex-star ground-state energy** (γ-5 step 446):
`singleClusterGSEnergyS 3 25 = -1925/4 = -S(1+zS)` for `S = 25/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentyfive :
    singleClusterGSEnergyS 3 25 = (-1925 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 446):
`singleClusterMaxEnergyS 3 25 = 1875/4 = zS²` for `S = 25/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentyfive :
    singleClusterMaxEnergyS 3 25 = (1875 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25/2 5-vertex-star ground-state energy** (γ-5 step 447):
`singleClusterGSEnergyS 4 25 = -1275/2 = -S(1+zS)` for `S = 25/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentyfive :
    singleClusterGSEnergyS 4 25 = (-1275 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 447):
`singleClusterMaxEnergyS 4 25 = 625 = zS²` for `S = 25/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentyfive :
    singleClusterMaxEnergyS 4 25 = (625 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25/2 6-vertex-star ground-state energy** (γ-5 step 448):
`singleClusterGSEnergyS 5 25 = -3175/4 = -S(1+zS)` for `S = 25/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentyfive :
    singleClusterGSEnergyS 5 25 = (-3175 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 448):
`singleClusterMaxEnergyS 5 25 = 3125/4 = zS²` for `S = 25/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentyfive :
    singleClusterMaxEnergyS 5 25 = (3125 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-25/2 7-vertex-star ground-state energy** (γ-5 step 449):
`singleClusterGSEnergyS 6 25 = -950 = -S(1+zS)` for `S = 25/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentyfive :
    singleClusterGSEnergyS 6 25 = (-950 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-25/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 449):
`singleClusterMaxEnergyS 6 25 = 1875/2 = zS²` for `S = 25/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentyfive :
    singleClusterMaxEnergyS 6 25 = (1875 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13 dimer ground-state energy** (γ-5 step 450):
`singleClusterGSEnergyS 1 26 = -182 = -S(S+1)` for `S = 13`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentysix :
    singleClusterGSEnergyS 1 26 = (-182 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13 dimer maximum-Casimir-sector energy** (γ-5 step 450):
`singleClusterMaxEnergyS 1 26 = 169 = S²` for `S = 13`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentysix :
    singleClusterMaxEnergyS 1 26 = (169 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13 3-vertex-star ground-state energy** (γ-5 step 451):
`singleClusterGSEnergyS 2 26 = -351 = -S(1+zS)` for `S = 13, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentysix :
    singleClusterGSEnergyS 2 26 = (-351 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 451):
`singleClusterMaxEnergyS 2 26 = 338 = zS²` for `S = 13, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentysix :
    singleClusterMaxEnergyS 2 26 = (338 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13 4-vertex-star ground-state energy** (γ-5 step 452):
`singleClusterGSEnergyS 3 26 = -520 = -S(1+zS)` for `S = 13, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentysix :
    singleClusterGSEnergyS 3 26 = (-520 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 452):
`singleClusterMaxEnergyS 3 26 = 507 = zS²` for `S = 13, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentysix :
    singleClusterMaxEnergyS 3 26 = (507 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13 5-vertex-star ground-state energy** (γ-5 step 453):
`singleClusterGSEnergyS 4 26 = -689 = -S(1+zS)` for `S = 13, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentysix :
    singleClusterGSEnergyS 4 26 = (-689 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 453):
`singleClusterMaxEnergyS 4 26 = 676 = zS²` for `S = 13, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentysix :
    singleClusterMaxEnergyS 4 26 = (676 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13 6-vertex-star ground-state energy** (γ-5 step 454):
`singleClusterGSEnergyS 5 26 = -858 = -S(1+zS)` for `S = 13, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentysix :
    singleClusterGSEnergyS 5 26 = (-858 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 454):
`singleClusterMaxEnergyS 5 26 = 845 = zS²` for `S = 13, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentysix :
    singleClusterMaxEnergyS 5 26 = (845 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-13 7-vertex-star ground-state energy** (γ-5 step 455):
`singleClusterGSEnergyS 6 26 = -1027 = -S(1+zS)` for `S = 13, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentysix :
    singleClusterGSEnergyS 6 26 = (-1027 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-13 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 455):
`singleClusterMaxEnergyS 6 26 = 1014 = zS²` for `S = 13, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentysix :
    singleClusterMaxEnergyS 6 26 = (1014 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27/2 dimer ground-state energy** (γ-5 step 456):
`singleClusterGSEnergyS 1 27 = -783/4 = -S(S+1)` for `S = 27/2`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentyseven :
    singleClusterGSEnergyS 1 27 = (-783 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27/2 dimer maximum-Casimir-sector energy** (γ-5 step 456):
`singleClusterMaxEnergyS 1 27 = 729/4 = S²` for `S = 27/2`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentyseven :
    singleClusterMaxEnergyS 1 27 = (729 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27/2 3-vertex-star ground-state energy** (γ-5 step 457):
`singleClusterGSEnergyS 2 27 = -378 = -S(1+zS)` for `S = 27/2, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentyseven :
    singleClusterGSEnergyS 2 27 = (-378 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27/2 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 457):
`singleClusterMaxEnergyS 2 27 = 729/2 = zS²` for `S = 27/2, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentyseven :
    singleClusterMaxEnergyS 2 27 = (729 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27/2 4-vertex-star ground-state energy** (γ-5 step 458):
`singleClusterGSEnergyS 3 27 = -2241/4 = -S(1+zS)` for `S = 27/2, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentyseven :
    singleClusterGSEnergyS 3 27 = (-2241 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27/2 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 458):
`singleClusterMaxEnergyS 3 27 = 2187/4 = zS²` for `S = 27/2, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentyseven :
    singleClusterMaxEnergyS 3 27 = (2187 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27/2 5-vertex-star ground-state energy** (γ-5 step 459):
`singleClusterGSEnergyS 4 27 = -1485/2 = -S(1+zS)` for `S = 27/2, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentyseven :
    singleClusterGSEnergyS 4 27 = (-1485 / 2 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27/2 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 459):
`singleClusterMaxEnergyS 4 27 = 729 = zS²` for `S = 27/2, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentyseven :
    singleClusterMaxEnergyS 4 27 = (729 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27/2 6-vertex-star ground-state energy** (γ-5 step 460):
`singleClusterGSEnergyS 5 27 = -3699/4 = -S(1+zS)` for `S = 27/2, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentyseven :
    singleClusterGSEnergyS 5 27 = (-3699 / 4 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27/2 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 460):
`singleClusterMaxEnergyS 5 27 = 3645/4 = zS²` for `S = 27/2, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentyseven :
    singleClusterMaxEnergyS 5 27 = (3645 / 4 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-27/2 7-vertex-star ground-state energy** (γ-5 step 461):
`singleClusterGSEnergyS 6 27 = -1107 = -S(1+zS)` for `S = 27/2, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentyseven :
    singleClusterGSEnergyS 6 27 = (-1107 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-27/2 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 461):
`singleClusterMaxEnergyS 6 27 = 2187/2 = zS²` for `S = 27/2, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentyseven :
    singleClusterMaxEnergyS 6 27 = (2187 / 2 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-14 dimer ground-state energy** (γ-5 step 462):
`singleClusterGSEnergyS 1 28 = -210 = -S(S+1)` for `S = 14`. -/
@[simp] theorem singleClusterGSEnergyS_one_twentyeight :
    singleClusterGSEnergyS 1 28 = (-210 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-14 dimer maximum-Casimir-sector energy** (γ-5 step 462):
`singleClusterMaxEnergyS 1 28 = 196 = S²` for `S = 14`. -/
@[simp] theorem singleClusterMaxEnergyS_one_twentyeight :
    singleClusterMaxEnergyS 1 28 = (196 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-14 3-vertex-star ground-state energy** (γ-5 step 463):
`singleClusterGSEnergyS 2 28 = -406 = -S(1+zS)` for `S = 14, z = 2`. -/
@[simp] theorem singleClusterGSEnergyS_two_twentyeight :
    singleClusterGSEnergyS 2 28 = (-406 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-14 3-vertex-star maximum-Casimir-sector energy** (γ-5 step 463):
`singleClusterMaxEnergyS 2 28 = 392 = zS²` for `S = 14, z = 2`. -/
@[simp] theorem singleClusterMaxEnergyS_two_twentyeight :
    singleClusterMaxEnergyS 2 28 = (392 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-14 4-vertex-star ground-state energy** (γ-5 step 464):
`singleClusterGSEnergyS 3 28 = -602 = -S(1+zS)` for `S = 14, z = 3`. -/
@[simp] theorem singleClusterGSEnergyS_three_twentyeight :
    singleClusterGSEnergyS 3 28 = (-602 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-14 4-vertex-star maximum-Casimir-sector energy** (γ-5 step 464):
`singleClusterMaxEnergyS 3 28 = 588 = zS²` for `S = 14, z = 3`. -/
@[simp] theorem singleClusterMaxEnergyS_three_twentyeight :
    singleClusterMaxEnergyS 3 28 = (588 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-14 5-vertex-star ground-state energy** (γ-5 step 465):
`singleClusterGSEnergyS 4 28 = -798 = -S(1+zS)` for `S = 14, z = 4`. -/
@[simp] theorem singleClusterGSEnergyS_four_twentyeight :
    singleClusterGSEnergyS 4 28 = (-798 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-14 5-vertex-star maximum-Casimir-sector energy** (γ-5 step 465):
`singleClusterMaxEnergyS 4 28 = 784 = zS²` for `S = 14, z = 4`. -/
@[simp] theorem singleClusterMaxEnergyS_four_twentyeight :
    singleClusterMaxEnergyS 4 28 = (784 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-14 6-vertex-star ground-state energy** (γ-5 step 466):
`singleClusterGSEnergyS 5 28 = -994 = -S(1+zS)` for `S = 14, z = 5`. -/
@[simp] theorem singleClusterGSEnergyS_five_twentyeight :
    singleClusterGSEnergyS 5 28 = (-994 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-14 6-vertex-star maximum-Casimir-sector energy** (γ-5 step 466):
`singleClusterMaxEnergyS 5 28 = 980 = zS²` for `S = 14, z = 5`. -/
@[simp] theorem singleClusterMaxEnergyS_five_twentyeight :
    singleClusterMaxEnergyS 5 28 = (980 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

/-- **Spin-14 7-vertex-star ground-state energy** (γ-5 step 467):
`singleClusterGSEnergyS 6 28 = -1190 = -S(1+zS)` for `S = 14, z = 6`. -/
@[simp] theorem singleClusterGSEnergyS_six_twentyeight :
    singleClusterGSEnergyS 6 28 = (-1190 : ℂ) := by
  unfold singleClusterGSEnergyS
  push_cast
  ring

/-- **Spin-14 7-vertex-star maximum-Casimir-sector energy** (γ-5 step 467):
`singleClusterMaxEnergyS 6 28 = 1176 = zS²` for `S = 14, z = 6`. -/
@[simp] theorem singleClusterMaxEnergyS_six_twentyeight :
    singleClusterMaxEnergyS 6 28 = (1176 : ℂ) := by
  unfold singleClusterMaxEnergyS
  push_cast
  ring

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

end LatticeSystem.Quantum
