import LatticeSystem.Quantum.SpinS.SingleClusterHamiltonian

/-!
# Concrete-cluster eigenvalue formulas for the single-cluster Heisenberg
Hamiltonian

Build-speed companion to `SingleClusterHamiltonian.lean`. Hosts the
concrete `z = 1` (dimer), `z = 2` (trimer), `z = 3` (quartet),
`z = 4` (pentamer), and leaf-singlet eigenvalue formulas (originally
lines 978..1525 of the parent file).

Splitting this trailing block out drops the parent file from
~1526 lines to ~977 lines. Downstream files that only need the
abstract framework can keep importing the parent.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Problem 2.5.a, p. 38.
-/

namespace LatticeSystem.Quantum

variable (z : ℕ)

/-- **Single-leaf leaf-Casimir reduces to single-site spinSDot** (γ-5 step 285):
`leafSpinSSquared 1 N = spinSDot 1 1 N` on `Fin 2`.

For the dimer (z=1), the leaf set is `{1}`, so each leaf-spin operator
`Ŝ_R^(α) = Σ_{j ∈ erase 0} onSiteS j Ŝ^(α)` reduces to a single
`onSiteS 1 Ŝ^(α)` term, and the leaf-Casimir
`Ŝ_R² = Σ_α (Ŝ_R^(α))²` collapses to the single-site Casimir
`spinSDot 1 1 = Σ_α (onSiteS 1 Ŝ^(α))²`. -/
theorem leafSpinSSquared_one (N : ℕ) :
    (leafSpinSSquared 1 N : ManyBodyOpS (Fin 2) N) = spinSDot 1 1 N := by
  unfold leafSpinSSquared leafSpinSOp1 leafSpinSOp2 leafSpinSOp3 spinSDot
  have h : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  rw [h]
  simp [Finset.sum_singleton]

/-- **Single-leaf leaf-Casimir scalar action** (γ-5 step 286, helper):
`leafSpinSSquared 1 N · v = (N(N+2)/4) • v` for any `v` on `Fin 2`.

Direct corollary of γ-5 step 285 + `spinSDot_self_mulVec_eq_smul`. The
single-leaf leaf-Casimir is the constant scalar `N(N+2)/4 = S(S+1)`. -/
theorem leafSpinSSquared_one_mulVec
    (N : ℕ) (v : (Fin 2 → Fin (N + 1)) → ℂ) :
    (leafSpinSSquared 1 N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) / 4) • v := by
  rw [leafSpinSSquared_one]
  exact spinSDot_self_mulVec_eq_smul N 1 v

/-- **Dimer eigenvalue from total Casimir alone** (γ-5 step 286):
for `z = 1`, the leaf-Casimir is the constant `N(N+2)/4` (γ-5 step 285),
so any total-Casimir eigenvector is automatically a joint eigenvector.
The H-eigenvalue depends only on the total-Casimir eigenvalue:
if `Ŝ_tot² · v = α · v`, then
`H · v = ((α − N(N+2)/2) / 2) • v`
on the dimer.

Specialisation of γ-5 step 259 to z=1, removing the SR² hypothesis. -/
theorem singleClusterHamiltonianS_eigenvalue_dimer
    (N : ℕ) {α : ℂ} {v : (Fin 2 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 2) N).mulVec v = α • v) :
    (singleClusterHamiltonianS 1 N).mulVec v =
      ((α - (N : ℂ) * ((N : ℂ) + 2) / 2) / 2) • v := by
  have hR : (leafSpinSSquared 1 N).mulVec v =
      ((1 : ℂ) * (N : ℂ) / 2 * ((1 : ℂ) * (N : ℂ) / 2 + 1)) • v := by
    rw [leafSpinSSquared_one_mulVec]
    congr 1
    ring
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 1) N htot hR
  rw [h]
  congr 1
  ring

/-- **Dimer singlet attains GS energy** (γ-5 step 287):
for `z = 1`, any `Stot² = 0` eigenvector is an `H`-eigenvector at the
predicted GS energy: `H · v = singleClusterGSEnergyS 1 N • v`.

Combines γ-5 step 286 (dimer eigenvalue from `Stot²` alone) with γ-5
step 275 (`singleClusterGSEnergyS 1 N = −(N/2)(N/2+1)` closed form).

This is the strongest concrete realisation of Tasaki Problem 2.5.a in
the dimer case: any singlet is an explicit GS eigenvector at the
predicted energy. The existence of a singlet (Clebsch–Gordan
construction) remains separate. -/
theorem singleClusterHamiltonianS_eigenvalue_dimer_singlet
    (N : ℕ) {v : (Fin 2 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 2) N).mulVec v = (0 : ℂ) • v) :
    (singleClusterHamiltonianS 1 N).mulVec v =
      singleClusterGSEnergyS 1 N • v := by
  rw [singleClusterGSEnergyS_one_eq]
  have h := singleClusterHamiltonianS_eigenvalue_dimer N htot
  rw [h]
  congr 1
  ring

/-- **Dimer top-spin attains Max energy** (γ-5 step 288):
for `z = 1`, any `Stot² = N(N+1)` eigenvector (i.e. total spin
`s_tot = N = 2S`) is an `H`-eigenvector at the predicted maximum
Casimir-sector energy: `H · v = singleClusterMaxEnergyS 1 N • v`.

Companion to γ-5 step 287 (singlet at the GS energy). Combines γ-5
step 286 with γ-5 step 275 (`singleClusterMaxEnergyS 1 N = (N/2)²`).
-/
theorem singleClusterHamiltonianS_eigenvalue_dimer_top
    (N : ℕ) {v : (Fin 2 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 2) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 1)) • v) :
    (singleClusterHamiltonianS 1 N).mulVec v =
      singleClusterMaxEnergyS 1 N • v := by
  rw [singleClusterMaxEnergyS_one_eq]
  have h := singleClusterHamiltonianS_eigenvalue_dimer N htot
  rw [h]
  congr 1
  ring

/-- **Trimer (z=2) leaf-Casimir decomposition** (γ-5 step 292):
`leafSpinSSquared 2 N = (N(N+2)/2) • 1 + 2 • spinSDot 1 2 N` on `Fin 3`.

For two leaves (`erase 0 = {1, 2}`), the leaf-Casimir double sum
`Σ_{j,k ∈ {1,2}} spinSDot j k` decomposes into two diagonal terms
(`spinSDot 1 1`, `spinSDot 2 2`, each scalar `N(N+2)/4 • 1`) and two
off-diagonal terms (`spinSDot 1 2`, `spinSDot 2 1`, equal by
`spinSDot_comm`). Bridges the leaf-Casimir machinery to direct
two-leaf coupling. -/
theorem leafSpinSSquared_two (N : ℕ) :
    (leafSpinSSquared 2 N : ManyBodyOpS (Fin 3) N) =
      ((N : ℂ) * ((N : ℂ) + 2) / 2) • 1 +
        (2 : ℂ) • spinSDot 1 2 N := by
  rw [leafSpinSSquared_eq_sum_spinSDot]
  have h12 : (Finset.univ.erase (0 : Fin 3)) = {1, 2} := by decide
  rw [h12]
  rw [show ({1, 2} : Finset (Fin 3)) = insert 1 {2} from rfl]
  rw [Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
  rw [Finset.sum_singleton]
  rw [Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
  rw [Finset.sum_singleton]
  rw [Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3)))]
  rw [Finset.sum_singleton]
  rw [spinSDot_self 1 N, spinSDot_self 2 N]
  rw [spinSDot_comm 2 1]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 2 : ℂ) =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4) from by ring]
  rw [add_smul, two_smul]
  abel

/-- **Trimer eigenvalue from `Stot²` + leaf-leaf coupling** (γ-5 step 293):
for `z = 2`, if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue `α`)
and the leaf-leaf coupling `spinSDot 1 2 N` (eigenvalue `β`), then `v`
is an `H`-eigenvector with eigenvalue
`(α − 3·N(N+2)/4 − 2β) / 2`.

Specialisation of γ-5 step 259 to z=2 using the trimer leaf-Casimir
decomposition (γ-5 step 292): `SR² = (N(N+2)/2)·I + 2·(Ŝ_1·Ŝ_2)`.
Substituting `Ŝ_1 · Ŝ_2 · v = β·v` gives `SR² · v = (N(N+2)/2 + 2β)·v`,
which combined with `S0² · v = (N(N+2)/4)·v` and the Casimir
decomposition `2H = Stot² − S0² − SR²` yields the formula. -/
theorem singleClusterHamiltonianS_eigenvalue_trimer
    (N : ℕ) {α β : ℂ} {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v = α • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v = β • v) :
    (singleClusterHamiltonianS 2 N).mulVec v =
      ((α - 3 * (N : ℂ) * ((N : ℂ) + 2) / 4 - 2 * β) / 2) • v := by
  have hR : (leafSpinSSquared 2 N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) / 2 + 2 * β) • v := by
    rw [leafSpinSSquared_two, Matrix.add_mulVec]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hLeafLeaf]
    rw [smul_smul, ← add_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 2) N htot hR
  rw [h]
  congr 1
  ring

/-- **Trimer GS-sector eigenvalue** (γ-5 step 294):
for `z = 2`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`) and the leaf-leaf
coupling `spinSDot 1 2 · v = (N²/4)·v` (i.e. leaf-pair at max coupling
in the triplet sector `s_R = N`), then `v` is an `H`-eigenvector at
the predicted GS energy `singleClusterGSEnergyS 2 N = -N(N+1)/2`.

This is the trimer analogue of γ-5 step 287 (dimer singlet attains GS).
The hypotheses correspond to the Tasaki Problem 2.5.a GS Casimir
sector for `z = 2`: leaves form a triplet (`s_R = N`, max), and the
total spin couples to the central spin to give `s_tot = (z−1)N/2 = N/2`. -/
theorem singleClusterHamiltonianS_eigenvalue_trimer_gs
    (N : ℕ) {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v = ((N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 2 N).mulVec v =
      singleClusterGSEnergyS 2 N • v := by
  unfold singleClusterGSEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_trimer N htot hLeafLeaf
  rw [h]
  congr 1
  ring

/-- **Trimer top-spin sector eigenvalue at Max energy** (γ-5 step 295):
for `z = 2`, if `v` is a joint eigenvector of `Stot²` at the maximum
total-spin sector (`Stot²·v = (3N/2)(3N/2+1)·v`, i.e. `s_tot = 3N/2`)
and the leaf-leaf coupling `spinSDot 1 2·v = (N²/4)·v` (leaf triplet,
`s_R = N`), then `v` is an `H`-eigenvector at the predicted maximum
Casimir-sector energy `singleClusterMaxEnergyS 2 N = N²/2`.

Trimer companion to γ-5 step 288 (dimer top-spin attains Max). -/
theorem singleClusterHamiltonianS_eigenvalue_trimer_top
    (N : ℕ) {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v =
        ((3 : ℂ) * (N : ℂ) / 2 * ((3 : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v = ((N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 2 N).mulVec v =
      singleClusterMaxEnergyS 2 N • v := by
  unfold singleClusterMaxEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_trimer N htot hLeafLeaf
  rw [h]
  congr 1
  ring

/-- **Trimer leaf-singlet sector eigenvalue = 0** (γ-5 step 296):
for `z = 2`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, the central spin alone)
and the leaf-leaf coupling at `spinSDot 1 2·v = -(N(N+2)/4)·v` (leaf
singlet, `s_R = 0`), then `H · v = 0`.

The leaf-singlet sector decouples: with leaves combined into a
total-spin-zero singlet, the central spin couples trivially to give
H = 0. The spin-1/2 trimer spectrum `{-1, 0, 1/2}` includes `0` from
exactly this sector. -/
theorem singleClusterHamiltonianS_eigenvalue_trimer_leaf_singlet
    (N : ℕ) {v : (Fin 3 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 3) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafLeaf : (spinSDot 1 2 N).mulVec v =
        (-((N : ℂ) * ((N : ℂ) + 2) / 4)) • v) :
    (singleClusterHamiltonianS 2 N).mulVec v = 0 := by
  have h := singleClusterHamiltonianS_eigenvalue_trimer N htot hLeafLeaf
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 -
        3 * (N : ℂ) * ((N : ℂ) + 2) / 4 -
        2 * -((N : ℂ) * ((N : ℂ) + 2) / 4)) / 2 = 0 from by ring]
  rw [zero_smul]

/-- **Quartet (z=3) leaf-Casimir decomposition** (γ-5 step 303):
`leafSpinSSquared 3 N = (3·N(N+2)/4) • 1 + 2 • (spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)`
on `Fin 4`.

For three leaves (`erase 0 = {1, 2, 3}`), the leaf-Casimir double sum
`Σ_{j,k ∈ {1,2,3}} spinSDot j k` decomposes into three diagonal
`spinSDot j j` terms (each scalar `N(N+2)/4 • 1`) and six off-diagonal
terms grouped into three `spinSDot j k` pairs (`(j,k) = (1,2), (1,3),
(2,3)`) related by `spinSDot_comm`. Generalises γ-5 step 292 (z=2) to
the quartet. -/
theorem leafSpinSSquared_three (N : ℕ) :
    (leafSpinSSquared 3 N : ManyBodyOpS (Fin 4) N) =
      (3 * (N : ℂ) * ((N : ℂ) + 2) / 4) • 1 +
        (2 : ℂ) • (spinSDot 1 2 N + spinSDot 1 3 N + spinSDot 2 3 N) := by
  rw [leafSpinSSquared_eq_sum_spinSDot]
  have h123 : (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} := by decide
  rw [h123]
  have hne12 : (1 : Fin 4) ∉ ({2, 3} : Finset (Fin 4)) := by decide
  have hne23 : (2 : Fin 4) ∉ ({3} : Finset (Fin 4)) := by decide
  rw [show ({1, 2, 3} : Finset (Fin 4)) = insert 1 (insert 2 {3}) from rfl]
  simp_rw [Finset.sum_insert hne12, Finset.sum_insert hne23, Finset.sum_singleton]
  rw [spinSDot_self 1 N, spinSDot_self 2 N, spinSDot_self 3 N]
  rw [spinSDot_comm 2 1, spinSDot_comm 3 1, spinSDot_comm 3 2]
  rw [show (3 * (N : ℂ) * ((N : ℂ) + 2) / 4 : ℂ) =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4) +
          ((N : ℂ) * ((N : ℂ) + 2) / 4) from by ring]
  rw [add_smul, add_smul, two_smul]
  abel

/-- **Quartet eigenvalue from `Stot²` + leaf-leaf sum** (γ-5 step 304):
for `z = 3`, if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue `α`)
and the leaf-leaf sum
`spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3` (eigenvalue `γ`), then
`v` is an `H`-eigenvector with eigenvalue
`(α − N(N+2) − 2γ)/2`.

Specialisation of γ-5 step 259 to z=3 using the quartet leaf-Casimir
decomposition (γ-5 step 303): `SR² = (3N(N+2)/4)·I +
2·(Ŝ_1·Ŝ_2 + Ŝ_1·Ŝ_3 + Ŝ_2·Ŝ_3)`. Substituting the hypothesis on
the leaf-leaf sum gives the leaf-Casimir eigenvalue
`3N(N+2)/4 + 2γ`, which combined with the central-Casimir scalar
action and the Casimir decomposition yields the formula. -/
theorem singleClusterHamiltonianS_eigenvalue_quartet
    (N : ℕ) {α γ : ℂ} {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v = α • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v = γ • v) :
    (singleClusterHamiltonianS 3 N).mulVec v =
      ((α - (N : ℂ) * ((N : ℂ) + 2) - 2 * γ) / 2) • v := by
  have hR : (leafSpinSSquared 3 N).mulVec v =
      (3 * (N : ℂ) * ((N : ℂ) + 2) / 4 + 2 * γ) • v := by
    rw [leafSpinSSquared_three]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hLeafSum]
    rw [smul_smul, ← add_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 3) N htot hR
  rw [h]
  congr 1
  ring

/-- **Quartet GS-sector eigenvalue at GS energy** (γ-5 step 305):
for `z = 3`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = N(N+1)·v` (i.e. `s_tot = N`) and the leaf-leaf sum at
`(spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)·v = (3N²/4)·v`
(corresponding to leaves at the maximum total leaf-spin
`s_R = 3N/2`), then `v` is an `H`-eigenvector at the predicted GS
energy `singleClusterGSEnergyS 3 N = -N(3N+2)/4`.

Quartet analogue of γ-5 step 294 (trimer GS sector). The hypotheses
correspond to the Tasaki Problem 2.5.a GS Casimir sector for `z = 3`:
leaves form the maximum leaf-spin sector `(s_R = 3N/2)` and couple
with the central spin to give `s_tot = (z−1)N/2 = N`. -/
theorem singleClusterHamiltonianS_eigenvalue_quartet_gs
    (N : ℕ) {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 3 N).mulVec v =
      singleClusterGSEnergyS 3 N • v := by
  unfold singleClusterGSEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_quartet N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Quartet top-spin sector eigenvalue at Max energy** (γ-5 step 306):
for `z = 3`, if `v` is a joint eigenvector of `Stot²` at the maximum
total-spin sector (`Stot²·v = 2N(2N+1)·v`, i.e. `s_tot = 2N = (z+1)N/2`)
and the leaf-leaf sum at `(spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)·v
= (3N²/4)·v` (max leaf-spin `s_R = 3N/2`), then `v` is an `H`-eigenvector
at the predicted maximum Casimir-sector energy
`singleClusterMaxEnergyS 3 N = 3N²/4`.

Quartet companion to γ-5 step 295 (trimer top sector). -/
theorem singleClusterHamiltonianS_eigenvalue_quartet_top
    (N : ℕ) {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v =
        ((2 : ℂ) * (N : ℂ) * ((2 : ℂ) * (N : ℂ) + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 4) • v) :
    (singleClusterHamiltonianS 3 N).mulVec v =
      singleClusterMaxEnergyS 3 N • v := by
  unfold singleClusterMaxEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_quartet N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Pentamer (z=4) leaf-Casimir decomposition** (γ-5 step 312):
`leafSpinSSquared 4 N = (N(N+2)) • 1 + 2 • (Σ_{1 ≤ j < k ≤ 4} spinSDot j k N)`
on `Fin 5`.

For four leaves (`erase 0 = {1, 2, 3, 4}`), the leaf-Casimir double sum
`Σ_{j,k ∈ {1,...,4}} spinSDot j k` decomposes into four diagonal
`spinSDot j j` terms (each scalar `N(N+2)/4 • 1`) and twelve
off-diagonal terms grouped into six `spinSDot j k` pairs related by
`spinSDot_comm`. Generalises γ-5 step 303 (z=3 quartet) to the
pentamer. -/
theorem leafSpinSSquared_four (N : ℕ) :
    (leafSpinSSquared 4 N : ManyBodyOpS (Fin 5) N) =
      ((N : ℂ) * ((N : ℂ) + 2)) • 1 +
        (2 : ℂ) • (spinSDot 1 2 N + spinSDot 1 3 N + spinSDot 1 4 N +
          spinSDot 2 3 N + spinSDot 2 4 N + spinSDot 3 4 N) := by
  rw [leafSpinSSquared_eq_sum_spinSDot]
  have h1234 : (Finset.univ.erase (0 : Fin 5)) = {1, 2, 3, 4} := by decide
  rw [h1234]
  have hne1 : (1 : Fin 5) ∉ ({2, 3, 4} : Finset (Fin 5)) := by decide
  have hne2 : (2 : Fin 5) ∉ ({3, 4} : Finset (Fin 5)) := by decide
  have hne3 : (3 : Fin 5) ∉ ({4} : Finset (Fin 5)) := by decide
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)) = insert 1 (insert 2 (insert 3 {4}))
        from rfl]
  simp_rw [Finset.sum_insert hne1, Finset.sum_insert hne2,
    Finset.sum_insert hne3, Finset.sum_singleton]
  rw [spinSDot_self 1 N, spinSDot_self 2 N, spinSDot_self 3 N, spinSDot_self 4 N]
  rw [spinSDot_comm 2 1, spinSDot_comm 3 1, spinSDot_comm 4 1]
  rw [spinSDot_comm 3 2, spinSDot_comm 4 2]
  rw [spinSDot_comm 4 3]
  conv_rhs =>
    rw [show ((N : ℂ) * ((N : ℂ) + 2) : ℂ) =
          ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4) +
            ((N : ℂ) * ((N : ℂ) + 2) / 4) + ((N : ℂ) * ((N : ℂ) + 2) / 4)
            from by ring]
    rw [add_smul, add_smul, add_smul, two_smul]
  abel

/-- **Pentamer eigenvalue from `Stot²` + leaf-leaf sum** (γ-5 step 313):
for `z = 4`, if `v` is a joint eigenvector of `Ŝ_tot²` (eigenvalue `α`)
and the leaf-leaf sum
`spinSDot 1 2 + spinSDot 1 3 + spinSDot 1 4 + spinSDot 2 3 +
spinSDot 2 4 + spinSDot 3 4` (eigenvalue `γ`), then `v` is an
`H`-eigenvector with eigenvalue `(α − 5N(N+2)/4 − 2γ)/2`.

Specialisation of γ-5 step 259 to z=4 using the pentamer leaf-Casimir
decomposition (γ-5 step 312): `SR² = N(N+2)·I + 2·(sum-of-6-pair-couplings)`.
-/
theorem singleClusterHamiltonianS_eigenvalue_pentamer
    (N : ℕ) {α γ : ℂ} {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v = α • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          γ • v) :
    (singleClusterHamiltonianS 4 N).mulVec v =
      ((α - 5 * (N : ℂ) * ((N : ℂ) + 2) / 4 - 2 * γ) / 2) • v := by
  have hR : (leafSpinSSquared 4 N).mulVec v =
      ((N : ℂ) * ((N : ℂ) + 2) + 2 * γ) • v := by
    rw [leafSpinSSquared_four]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hLeafSum]
    rw [smul_smul, ← add_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := 4) N htot hR
  rw [h]
  congr 1
  ring

/-- **Pentamer GS-sector eigenvalue at GS energy** (γ-5 step 314):
for `z = 4`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (3N/2)(3N/2+1)·v` (i.e. `s_tot = 3N/2 = (z-1)N/2`) and the
6-pair leaf-leaf sum at `(3N²/2)·v` (corresponding to leaves at the
maximum total leaf-spin `s_R = 2N`), then `v` is an `H`-eigenvector
at the predicted GS energy
`singleClusterGSEnergyS 4 N = -N(2N+1)/2`.

Pentamer analogue of γ-5 steps 294 (trimer GS) and 305 (quartet GS).
The hypotheses correspond to the Tasaki Problem 2.5.a GS Casimir
sector for `z = 4`: leaves form max leaf-spin sector and couple with
the central spin to give `s_tot = (z-1)N/2 = 3N/2`. -/
theorem singleClusterHamiltonianS_eigenvalue_pentamer_gs
    (N : ℕ) {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v =
        ((3 : ℂ) * (N : ℂ) / 2 * ((3 : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 2) • v) :
    (singleClusterHamiltonianS 4 N).mulVec v =
      singleClusterGSEnergyS 4 N • v := by
  unfold singleClusterGSEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_pentamer N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Pentamer top-spin sector eigenvalue at Max energy** (γ-5 step 315):
for `z = 4`, if `v` is a joint eigenvector of `Stot²` at the maximum
total-spin sector (`Stot²·v = (5N/2)(5N/2+1)·v`, i.e. `s_tot = 5N/2 =
(z+1)N/2`) and the 6-pair leaf-leaf sum at `(3N²/2)·v` (max leaf-spin
`s_R = 2N`), then `v` is an `H`-eigenvector at the predicted maximum
Casimir-sector energy `singleClusterMaxEnergyS 4 N = N²`.

Pentamer companion to γ-5 steps 295 (trimer top) and 306 (quartet top). -/
theorem singleClusterHamiltonianS_eigenvalue_pentamer_top
    (N : ℕ) {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v =
        ((5 : ℂ) * (N : ℂ) / 2 * ((5 : ℂ) * (N : ℂ) / 2 + 1)) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          (3 * (N : ℂ) ^ 2 / 2) • v) :
    (singleClusterHamiltonianS 4 N).mulVec v =
      singleClusterMaxEnergyS 4 N • v := by
  unfold singleClusterMaxEnergyS
  have h := singleClusterHamiltonianS_eigenvalue_pentamer N htot hLeafSum
  rw [h]
  congr 1
  ring

/-- **Quartet leaf-singlet sector eigenvalue = 0** (γ-5 step 321):
for `z = 3`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, central spin alone)
and the leaf-leaf sum at
`(spinSDot 1 2 + spinSDot 1 3 + spinSDot 2 3)·v = (-3N(N+2)/8)·v`
(corresponding to leaves in a singlet, `s_R = 0`), then `H · v = 0`.

The leaf-singlet sector decouples: with the three leaves combined
into a total-spin-zero singlet, the central spin couples trivially.
A 3-leaf singlet exists only for **integer** spin `S` (i.e. `N` even):
three half-integer spins sum to a half-integer total, never zero.
For `S = 1, 2, 3, ...` (i.e. `N = 2, 4, 6, ...`), three spins admit
`s_R = 0` with multiplicity `≥ 1`.

Quartet analogue of γ-5 step 296 (trimer leaf-singlet decoupling). -/
theorem singleClusterHamiltonianS_eigenvalue_quartet_leaf_singlet
    (N : ℕ) {v : (Fin 4 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 4) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 4) 2 N + spinSDot (1 : Fin 4) 3 N +
            spinSDot (2 : Fin 4) 3 N).mulVec v =
          (-3 * (N : ℂ) * ((N : ℂ) + 2) / 8) • v) :
    (singleClusterHamiltonianS 3 N).mulVec v = 0 := by
  have h := singleClusterHamiltonianS_eigenvalue_quartet N htot hLeafSum
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 - (N : ℂ) * ((N : ℂ) + 2) -
        2 * (-3 * (N : ℂ) * ((N : ℂ) + 2) / 8)) / 2 = 0 from by ring]
  rw [zero_smul]

/-- **Pentamer leaf-singlet sector eigenvalue = 0** (γ-5 step 322):
for `z = 4`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, central spin alone)
and the 6-pair leaf-leaf sum at
`(spinSDot 1 2 + ... + spinSDot 3 4)·v = (-N(N+2)/2)·v`
(corresponding to leaves in a singlet, `s_R = 0`), then `H · v = 0`.

The leaf-singlet sector decouples. A 4-leaf singlet exists for any
spin `S`: four spins of any magnitude can combine to total spin 0
(since four half-integers also sum to integer 0).

Pentamer analogue of γ-5 step 296 (trimer) and step 321 (quartet). -/
theorem singleClusterHamiltonianS_eigenvalue_pentamer_leaf_singlet
    (N : ℕ) {v : (Fin 5 → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin 5) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hLeafSum :
        (spinSDot (1 : Fin 5) 2 N + spinSDot (1 : Fin 5) 3 N +
            spinSDot (1 : Fin 5) 4 N + spinSDot (2 : Fin 5) 3 N +
            spinSDot (2 : Fin 5) 4 N + spinSDot (3 : Fin 5) 4 N).mulVec v =
          (-((N : ℂ) * ((N : ℂ) + 2) / 2)) • v) :
    (singleClusterHamiltonianS 4 N).mulVec v = 0 := by
  have h := singleClusterHamiltonianS_eigenvalue_pentamer N htot hLeafSum
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 -
        5 * (N : ℂ) * ((N : ℂ) + 2) / 4 -
        2 * (-((N : ℂ) * ((N : ℂ) + 2) / 2))) / 2 = 0 from by ring]
  rw [zero_smul]

/-- **Generic leaf-singlet sector eigenvalue = 0** (γ-5 step 323):
for any `z : ℕ`, if `v` is a joint eigenvector of `Stot²` at
`Stot²·v = (N(N+2)/4)·v` (i.e. `s_tot = N/2`, central spin alone)
and the leaf-Casimir at `leafSpinSSquared z N · v = 0` (leaves in a
total-spin-zero singlet), then `H · v = 0`.

The leaf-singlet sector decouples: with the leaves combined into a
total-spin-zero singlet, the central spin couples trivially via the
Casimir formula. Generalises γ-5 step 296 (z=2 trimer), γ-5 step 321
(z=3 quartet), γ-5 step 322 (z=4 pentamer) to arbitrary cluster size.

A `z`-leaf singlet exists when total spin 0 is achievable from `z`
spins of magnitude `S = N/2`: always for **even** `z`, and for **odd**
`z` only when `S` is integer (since odd-many half-integer spins sum
to a half-integer, never zero). -/
theorem singleClusterHamiltonianS_eigenvalue_leaf_singlet
    (N : ℕ) {v : (Fin (z + 1) → Fin (N + 1)) → ℂ}
    (htot : (totalSpinSSquared (Fin (z + 1)) N).mulVec v =
        ((N : ℂ) * ((N : ℂ) + 2) / 4) • v)
    (hR : (leafSpinSSquared z N).mulVec v = 0) :
    (singleClusterHamiltonianS z N).mulVec v = 0 := by
  have hR' : (leafSpinSSquared z N).mulVec v = (0 : ℂ) • v := by
    rw [hR, zero_smul]
  have h := singleClusterHamiltonianS_eigenvalue_of_joint_casimir_eigenvec
    (z := z) N htot hR'
  rw [h]
  rw [show ((N : ℂ) * ((N : ℂ) + 2) / 4 - (N : ℂ) * ((N : ℂ) + 2) / 4 - 0) / 2 =
        0 from by ring]
  rw [zero_smul]


end LatticeSystem.Quantum
