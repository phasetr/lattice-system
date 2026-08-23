import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveFermionSpinBridge
import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# Fermion-Spin bridge, total-spin Casimir (Theorem 10.4 arc, PR-9b)

Eleventh installment of the Theorem 10.4 discharge arc (issue #5320); second of the two-PR 9a/9b
split of "PR-9: Fermion-Spin bridge". This file supplies the ladder-vs-Cartesian Casimir bridge
that PR-9a's module docstring flagged as separate work. The fermionic Casimir
`fermionTotalSpinSquared` (the ladder form `Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z + 1)`) predates this arc: it comes from
the §11.1.1 saturated-ferromagnetism layer (`SaturatedFerromagnetism.lean`), and acts on the whole
Hubbard Fock space `Fin (2 * N + 2) → Fin 2`. The spin-`1/2` Cartesian Casimir `totalSpinSSquared`
(`Quantum/SpinS/TotalSquaredCore.lean`, `(Ŝ¹)² + (Ŝ²)² + (Ŝ³)²`) acts on spin configurations
`Fin (N + 1) → Fin 2`. The two are therefore **not** operators on a common space, and no identity
between them as operators is even well-typed.

What is proved here is an **entrywise** correspondence on the hard-core half-filled sector: every
matrix entry of the fermionic Casimir between two hard-core configurations equals the matrix entry
of the Cartesian Casimir between their images under PR-9a's sector `Equiv`
(`liebHardCoreHalfFillingSectorEquivS`, `LiebRepulsiveFermionSpinBridge.lean`). The restriction to
that sector is essential and not a convenience: off it the fermionic Casimir also sees empty and
doubly occupied sites, whose same-site dot vanishes instead of contributing the spin-`1/2` value
`3/4`.

## Route

Both Casimirs are re-expressed as the **same** double sum of two-site dots, which reduces the
entrywise comparison to PR-9a's two-site crux plus a same-site diagonal term.

* Spin side: `totalSpinSSquared_eq_sum_spinSDot` (`Quantum/SpinS/TotalSquared.lean`) gives
  `(Ŝ_tot)² = Σ_{x,y} Ŝ_x · Ŝ_y`, with same-site value `Ŝ_x · Ŝ_x = (3/4) · 1` at spin `1/2`
  (`spinSDot_self`).
* Fermionic side: `fermionTotalSpinSquared_eq_sum_fermionSpinDot` proves the mirror expansion
  `(Ŝ_tot)² = Σ_{x,y} Ŝ_x · Ŝ_y` for the Hubbard fermion spin operators. The ladder definition
  `Ŝ⁻_tot Ŝ⁺_tot + Ŝ³_tot(Ŝ³_tot + 1)` is reconciled with `½(Ŝ⁺_totŜ⁻_tot + Ŝ⁻_totŜ⁺_tot)
  + Ŝ³_totŜ³_tot` by the SU(2) ladder commutator `Ŝ⁺_totŜ⁻_tot − Ŝ⁻_totŜ⁺_tot = 2Ŝ³_tot`.
* The fermionic same-site dot is computed in closed form,
  `Ŝ_x · Ŝ_x = (3/4)(n̂_{x↑} + n̂_{x↓} − 2 n̂_{x↑}n̂_{x↓})` (`fermionSpinDot_self_eq`), out of the
  canonical anticommutation relation `ĉ ĉ† = 1 − n̂` and the idempotence `n̂² = n̂`. On a hard-core
  configuration this is the scalar `3/4`, matching `spinSDot_self` at `S = 1/2`.
* The off-diagonal terms are PR-9a's crux `fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied`
  verbatim.

## The capstone

`fermionTotalSpinSquared_apply_eq_totalSpinSSquared_of_singlyOccupied` is the crux entrywise
identity: on hard-core half-filled bra/ket Fock configurations, the fermionic Casimir's matrix
element equals the spin-`1/2` Cartesian Casimir's matrix element at the images under
`liebHardCoreDownOccupation`. It is stated directly on Fock-space matrix entries (no `submatrix`
plumbing), the same shape PR-9a's crux used.

`fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector` packages the crux into the
`submatrix`-along-the-sector-`Equiv` form matching PR-9a's capstone shape, restricting
`fermionTotalSpinSquared N` to the hard-core sub-sector (via `Subtype.val`) and reindexing onto
`totalSpinSSquared (Fin (N + 1)) 1` on the magnetization-`(N + 1 − nUp)` sector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1, eq. (10.1.10), p. 345; §2.5, Theorem 2.3, p. 42;
§11.1.1 (Casimir ladder form), p. 372.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-! ## The fermionic Casimir as a double sum of two-site dots -/

/-- **The fermionic Casimir expansion** `(Ŝ_tot)² = Σ_{x,y} Ŝ_x · Ŝ_y`, the fermionic mirror of
`totalSpinSSquared_eq_sum_spinSDot`. The ladder definition
`(Ŝ_tot)² = Ŝ⁻_totŜ⁺_tot + Ŝ³_tot(Ŝ³_tot + 1)` matches the Cartesian double sum
`½(Ŝ⁺_totŜ⁻_tot + Ŝ⁻_totŜ⁺_tot) + Ŝ³_totŜ³_tot` through the SU(2) ladder commutator
`Ŝ⁺_totŜ⁻_tot − Ŝ⁻_totŜ⁺_tot = 2Ŝ³_tot` (`fermionTotalSpinPlus_commutator_fermionTotalSpinMinus`).

Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinSquared_eq_sum_fermionSpinDot (N : ℕ) :
    fermionTotalSpinSquared N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinDot N x y := by
  have hexp : ∀ A B : Fin (N + 1) → ManyBodyOp (Fin (2 * N + 2)),
      (∑ x : Fin (N + 1), A x) * (∑ y : Fin (N + 1), B y)
        = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1), A x * B y := by
    intro A B
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.mul_sum _ _ _
  have hPM : fermionTotalSpinPlus N * fermionTotalSpinMinus N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          fermionSiteSpinPlus N x * fermionSiteSpinMinus N y :=
    hexp (fermionSiteSpinPlus N) (fermionSiteSpinMinus N)
  have hMP : fermionTotalSpinMinus N * fermionTotalSpinPlus N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          fermionSiteSpinMinus N x * fermionSiteSpinPlus N y :=
    hexp (fermionSiteSpinMinus N) (fermionSiteSpinPlus N)
  have hZZ : fermionTotalSpinZ N * fermionTotalSpinZ N
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          fermionSiteSpinZ N x * fermionSiteSpinZ N y := by
    rw [fermionTotalSpinZ_eq_sum_fermionSiteSpinZ]
    exact hexp (fermionSiteSpinZ N) (fermionSiteSpinZ N)
  have hsplit : (∑ x : Fin (N + 1), ∑ y : Fin (N + 1), fermionSpinDot N x y)
      = (1 / 2 : ℂ) • (fermionTotalSpinPlus N * fermionTotalSpinMinus N)
        + ((1 / 2 : ℂ) • (fermionTotalSpinMinus N * fermionTotalSpinPlus N)
          + fermionTotalSpinZ N * fermionTotalSpinZ N) := by
    rw [hPM, hMP, hZZ]
    simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [fermionSpinDot, smul_add, add_assoc]
  rw [hsplit, fermionTotalSpinSquared,
    show fermionTotalSpinPlus N * fermionTotalSpinMinus N
        = fermionTotalSpinMinus N * fermionTotalSpinPlus N + (2 : ℂ) • fermionTotalSpinZ N from
      sub_eq_iff_eq_add'.mp (fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N),
    mul_add, mul_one]
  module

/-! ## The same-site fermionic dot -/

/-- `Ŝ⁺_x Ŝ⁻_x = n̂_{x↑}(1 − n̂_{x↓})`: the raising-then-lowering product at a single site, from
`ĉ_{x↓} ĉ†_{x↓} = 1 − n̂_{x↓}` and the commutation of `n̂_{x↓}` with the up-spin modes. -/
private theorem fermionSiteSpinPlus_mul_fermionSiteSpinMinus_self (N : ℕ) (x : Fin (N + 1)) :
    fermionSiteSpinPlus N x * fermionSiteSpinMinus N x
      = fermionUpNumber N x - fermionUpNumber N x * fermionDownNumber N x := by
  have hne : spinfulIndex N x 1 ≠ spinfulIndex N x 0 := by
    rw [ne_eq, spinfulIndex_eq_iff]
    rintro ⟨-, h⟩
    exact absurd h (by decide)
  have hcc : fermionDownAnnihilation N x * fermionDownCreation N x = 1 - fermionDownNumber N x :=
    fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number (2 * N + 1)
      (spinfulIndex N x 1)
  have hcomm : fermionDownNumber N x * fermionUpAnnihilation N x
      = fermionUpAnnihilation N x * fermionDownNumber N x :=
    (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hne).eq
  have hnup : fermionUpCreation N x * fermionUpAnnihilation N x = fermionUpNumber N x := rfl
  calc fermionSiteSpinPlus N x * fermionSiteSpinMinus N x
      = fermionUpCreation N x * ((fermionDownAnnihilation N x * fermionDownCreation N x)
          * fermionUpAnnihilation N x) := by
        rw [fermionSiteSpinPlus, fermionSiteSpinMinus]
        simp only [mul_assoc]
    _ = fermionUpCreation N x * fermionUpAnnihilation N x
          - fermionUpCreation N x * (fermionDownNumber N x * fermionUpAnnihilation N x) := by
        rw [hcc, sub_mul, one_mul, mul_sub]
    _ = fermionUpNumber N x - fermionUpNumber N x * fermionDownNumber N x := by
        rw [hcomm, ← mul_assoc, hnup]

/-- `Ŝ⁻_x Ŝ⁺_x = n̂_{x↓}(1 − n̂_{x↑})`: the mirror of
`fermionSiteSpinPlus_mul_fermionSiteSpinMinus_self` with the two spin species exchanged. -/
private theorem fermionSiteSpinMinus_mul_fermionSiteSpinPlus_self (N : ℕ) (x : Fin (N + 1)) :
    fermionSiteSpinMinus N x * fermionSiteSpinPlus N x
      = fermionDownNumber N x - fermionUpNumber N x * fermionDownNumber N x := by
  have hne : spinfulIndex N x 0 ≠ spinfulIndex N x 1 := by
    rw [ne_eq, spinfulIndex_eq_iff]
    rintro ⟨-, h⟩
    exact absurd h (by decide)
  have hcc : fermionUpAnnihilation N x * fermionUpCreation N x = 1 - fermionUpNumber N x :=
    fermionMultiAnnihilation_mul_fermionMultiCreation_eq_one_sub_number (2 * N + 1)
      (spinfulIndex N x 0)
  have hcomm : fermionUpNumber N x * fermionDownAnnihilation N x
      = fermionDownAnnihilation N x * fermionUpNumber N x :=
    (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hne).eq
  have hndn : fermionDownCreation N x * fermionDownAnnihilation N x = fermionDownNumber N x := rfl
  have hnn : fermionDownNumber N x * fermionUpNumber N x
      = fermionUpNumber N x * fermionDownNumber N x :=
    (fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N x 1) (spinfulIndex N x 0)).eq
  calc fermionSiteSpinMinus N x * fermionSiteSpinPlus N x
      = fermionDownCreation N x * ((fermionUpAnnihilation N x * fermionUpCreation N x)
          * fermionDownAnnihilation N x) := by
        rw [fermionSiteSpinPlus, fermionSiteSpinMinus]
        simp only [mul_assoc]
    _ = fermionDownCreation N x * fermionDownAnnihilation N x
          - fermionDownCreation N x * (fermionUpNumber N x * fermionDownAnnihilation N x) := by
        rw [hcc, sub_mul, one_mul, mul_sub]
    _ = fermionDownNumber N x - fermionUpNumber N x * fermionDownNumber N x := by
        rw [hcomm, ← mul_assoc, hndn, hnn]

/-- `(Ŝ³_x)² = ¼(n̂_{x↑} + n̂_{x↓} − 2 n̂_{x↑}n̂_{x↓})`, using the idempotence `n̂² = n̂` of the
mode-number operators and their commutation. -/
private theorem fermionSiteSpinZ_mul_self (N : ℕ) (x : Fin (N + 1)) :
    fermionSiteSpinZ N x * fermionSiteSpinZ N x
      = (1 / 4 : ℂ) • (fermionUpNumber N x + fermionDownNumber N x
          - (2 : ℂ) • (fermionUpNumber N x * fermionDownNumber N x)) := by
  have hz : fermionSiteSpinZ N x
      = (1 / 2 : ℂ) • (fermionUpNumber N x - fermionDownNumber N x) := rfl
  have hup : fermionUpNumber N x * fermionUpNumber N x = fermionUpNumber N x :=
    fermionMultiNumber_sq (2 * N + 1) (spinfulIndex N x 0)
  have hdn : fermionDownNumber N x * fermionDownNumber N x = fermionDownNumber N x :=
    fermionMultiNumber_sq (2 * N + 1) (spinfulIndex N x 1)
  have hnn : fermionDownNumber N x * fermionUpNumber N x
      = fermionUpNumber N x * fermionDownNumber N x :=
    (fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N x 1) (spinfulIndex N x 0)).eq
  rw [hz, smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, mul_sub, hup, hdn, hnn]
  module

/-- **The same-site fermionic spin dot in closed form**:
`Ŝ_x · Ŝ_x = (3/4)(n̂_{x↑} + n̂_{x↓} − 2 n̂_{x↑}n̂_{x↓})`. On a singly occupied site the bracket is
`1`, giving the spin-`1/2` Casimir value `S(S+1) = 3/4`; on an empty or doubly occupied site it is
`0`, as it must be for a spinless configuration. -/
theorem fermionSpinDot_self_eq (N : ℕ) (x : Fin (N + 1)) :
    fermionSpinDot N x x
      = (3 / 4 : ℂ) • (fermionUpNumber N x + fermionDownNumber N x
          - (2 : ℂ) • (fermionUpNumber N x * fermionDownNumber N x)) := by
  rw [fermionSpinDot, fermionSiteSpinPlus_mul_fermionSiteSpinMinus_self,
    fermionSiteSpinMinus_mul_fermionSiteSpinPlus_self, fermionSiteSpinZ_mul_self]
  module

/-- The same-site fermionic dot acts as the scalar `3/4` on a hard-core basis configuration: every
site carries exactly one electron, so `n̂_{x↑} + n̂_{x↓} = 1` and `n̂_{x↑}n̂_{x↓} = 0` in
`fermionSpinDot_self_eq`. -/
private theorem fermionSpinDot_self_mulVec_basisVec_of_singlyOccupied (N : ℕ) (x : Fin (N + 1))
    {c : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1) :
    (fermionSpinDot N x x).mulVec (basisVec c) = (3 / 4 : ℂ) • basisVec c := by
  have hup : (fermionUpNumber N x).mulVec (basisVec c)
      = ((c (spinfulIndex N x 0)).val : ℂ) • basisVec c :=
    fermionMultiNumber_mulVec_basisVec (2 * N + 1) (spinfulIndex N x 0) c
  have hdn : (fermionDownNumber N x).mulVec (basisVec c)
      = ((c (spinfulIndex N x 1)).val : ℂ) • basisVec c :=
    fermionMultiNumber_mulVec_basisVec (2 * N + 1) (spinfulIndex N x 1) c
  have hsum : ((c (spinfulIndex N x 0)).val : ℂ) + ((c (spinfulIndex N x 1)).val : ℂ) = 1 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (hc x)
  have hprod : ((c (spinfulIndex N x 0)).val : ℂ) * ((c (spinfulIndex N x 1)).val : ℂ) = 0 := by
    rcases (show (c (spinfulIndex N x 0)).val = 0 ∨ (c (spinfulIndex N x 1)).val = 0 by
      have := hc x; omega) with h | h <;> rw [h] <;> simp
  rw [fermionSpinDot_self_eq, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hdn, Matrix.mulVec_smul, hup]
  match_scalars
  linear_combination (3 / 4 : ℂ) * hsum - (3 / 2 : ℂ) * hprod

/-- The same-site entrywise correspondence: on hard-core half-filled bra/ket configurations both
the fermionic `Ŝ_x · Ŝ_x` and the spin-`1/2` `Ŝ_x · Ŝ_x` are the scalar `3/4`, and the two Kronecker
deltas agree because a singly occupied configuration is determined by its down-orbital occupation
(`singlyOccupied_eq_iff_downOccupation`). -/
private theorem fermionSpinDot_self_apply_of_singlyOccupied (N nUp : ℕ) (x : Fin (N + 1))
    {c e : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (he : liebHardCoreHalfFillingPred N nUp e) :
    (fermionSpinDot N x x) e c =
      spinSDot x x 1 (liebHardCoreDownOccupation e) (liebHardCoreDownOccupation c) := by
  rw [← mulVec_basisVec_apply (fermionSpinDot N x x) e c,
    fermionSpinDot_self_mulVec_basisVec_of_singlyOccupied N x hc.2,
    spinSDot_self, Matrix.smul_apply, Matrix.one_apply]
  simp only [Pi.smul_apply, smul_eq_mul, basisVec_apply,
    singlyOccupied_eq_iff_downOccupation hc.2 he.2]
  norm_num

/-! ## The crux entrywise identity -/

/-- **The crux entrywise identity (PR-9b)**: on hard-core half-filled bra/ket configurations, the
fermionic total-spin Casimir's matrix element equals the spin-`1/2` Cartesian Casimir's matrix
element at the images under `liebHardCoreDownOccupation` (the down-orbital occupation read-off,
`LiebRepulsiveFermionSpinBridge.lean`).

Both Casimirs are first expanded as double sums of two-site dots
(`fermionTotalSpinSquared_eq_sum_fermionSpinDot`, `totalSpinSSquared_eq_sum_spinSDot`); the
off-diagonal terms are PR-9a's two-site crux and the diagonal terms are the common scalar `3/4`.

Reference: Tasaki §11.1.1, p. 372 (ladder form); §2.5, p. 42 (Cartesian form). -/
theorem fermionTotalSpinSquared_apply_eq_totalSpinSSquared_of_singlyOccupied (N nUp : ℕ)
    {c e : Fin (2 * N + 2) → Fin 2}
    (hc : liebHardCoreHalfFillingPred N nUp c) (he : liebHardCoreHalfFillingPred N nUp e) :
    (fermionTotalSpinSquared N) e c =
      (totalSpinSSquared (Fin (N + 1)) 1) (liebHardCoreDownOccupation e)
        (liebHardCoreDownOccupation c) := by
  rw [fermionTotalSpinSquared_eq_sum_fermionSpinDot, totalSpinSSquared_eq_sum_spinSDot]
  simp only [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  by_cases hxy : x = y
  · subst hxy
    exact fermionSpinDot_self_apply_of_singlyOccupied N nUp x hc he
  · exact fermionSpinDot_apply_eq_spinSDot_of_singlyOccupied N nUp hxy hc he

/-! ## The PR-9b capstone: reindexing onto the magnetization sector -/

/-- **PR-9b capstone**: `fermionTotalSpinSquared N`, restricted to the hard-core half-filling
sub-sector (`Subtype.val` inclusion into the ambient Fock space) and reindexed along PR-9a's sector
`Equiv` (`liebHardCoreHalfFillingSectorEquivS`), agrees with the spin-`1/2` Cartesian Casimir
`totalSpinSSquared (Fin (N + 1)) 1` on the magnetization-`(N + 1 − nUp)` sector.

This is the shape needed to transport the Casimir eigenvalue obtained from Theorem 2.3
(`tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive`,
`Quantum/SpinS/Theorem23StructuralGeneralFinal.lean`) back to the fermionic ground states in the
later PR-11/PR-12 assembly steps of the Theorem 10.4 arc. -/
theorem fermionTotalSpinSquared_reindex_eq_totalSpinSSquaredOnMagSector
    (N nUp : ℕ) (hnUp : nUp ≤ N + 1) :
    (fermionTotalSpinSquared N).submatrix
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
        (fun s : configSector N (liebHardCoreHalfFillingPred N nUp) => s.val)
      = (totalSpinSSquared (Fin (N + 1)) 1).submatrix
          (fun s => (liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val)
          (fun s => (liebHardCoreHalfFillingSectorEquivS N nUp hnUp s).val) := by
  ext s s'
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply]
  exact fermionTotalSpinSquared_apply_eq_totalSpinSSquared_of_singlyOccupied N nUp
    s'.property s.property

end LatticeSystem.Fermion
