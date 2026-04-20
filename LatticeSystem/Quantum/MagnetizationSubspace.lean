/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.TotalSpin
import LatticeSystem.Quantum.SpinDot
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Magnetization subspace `H_M` and direct sum decomposition
(Tasaki §2.2 eqs. (2.2.9)/(2.2.10))

The Hilbert space of a spin-1/2 system on lattice `Λ` decomposes as a
direct sum over total magnetization eigenvalues `M`:

```
H = ⊕_M H_M, where H_M := {|Φ⟩ : Ŝ_tot^(3) |Φ⟩ = M |Φ⟩}.
```

This module formalizes both pieces:

* `magnetizationSubspace M` — the eigenspace of `Ŝ_tot^(3)` for
  eigenvalue `M`, as a `Submodule ℂ ((Λ → Fin 2) → ℂ)`.
* `IsInMagnetizationSubspace M v` — the membership predicate (the
  underlying eigenvalue equation; kept as an alias for backwards
  compatibility with PR #16).
* `basisVec_mem_magnetizationSubspace` — every basis state lies in its
  magnetization sector (the carrier of Tasaki eq. (2.2.10)).
* `magnetizationSubspace_disjoint` — distinct sectors have trivial
  intersection.
* `iSup_magnetizationSubspace_eq_top` — every vector decomposes
  as a sum across sectors (because basisVec spans the full space and
  each basis state lies in some sector).
* `magnetizationSubspace_isInternal` — the family forms an internal
  direct sum (`DirectSum.IsInternal`).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ]

/-- The magnetization-`M` subspace `H_M`: the `Ŝ_tot^(3)`-eigenspace
for eigenvalue `M`, packaged as a `Submodule ℂ`. -/
noncomputable def magnetizationSubspace (M : ℂ) :
    Submodule ℂ ((Λ → Fin 2) → ℂ) where
  carrier := { v | (totalSpinHalfOp3 Λ).mulVec v = M • v }
  zero_mem' := by
    simp only [Set.mem_setOf_eq, Matrix.mulVec_zero, smul_zero]
  add_mem' := by
    intros v w hv hw
    simp only [Set.mem_setOf_eq] at hv hw ⊢
    rw [Matrix.mulVec_add, hv, hw, smul_add]
  smul_mem' := by
    intros c v hv
    simp only [Set.mem_setOf_eq] at hv ⊢
    rw [Matrix.mulVec_smul, hv, smul_comm]

/-- A vector `v` lies in the magnetization-`M` subspace `H_M` iff it is
an eigenvector of `Ŝ_tot^(3)` with eigenvalue `M`. -/
def IsInMagnetizationSubspace (M : ℂ) (v : (Λ → Fin 2) → ℂ) : Prop :=
  (totalSpinHalfOp3 Λ).mulVec v = M • v

/-- Membership in `magnetizationSubspace` unfolds to the eigenvalue equation. -/
@[simp]
theorem mem_magnetizationSubspace_iff (M : ℂ) (v : (Λ → Fin 2) → ℂ) :
    v ∈ magnetizationSubspace Λ M ↔ (totalSpinHalfOp3 Λ).mulVec v = M • v :=
  Iff.rfl

/-- Bridge between the predicate (PR #16) and the `Submodule`-membership
form. -/
theorem isInMagnetizationSubspace_iff_mem (M : ℂ) (v : (Λ → Fin 2) → ℂ) :
    IsInMagnetizationSubspace Λ M v ↔ v ∈ magnetizationSubspace Λ M :=
  Iff.rfl

/-- Every computational-basis state `|σ⟩` lies in `H_{|σ|/2}`, i.e. it is
an eigenvector of `Ŝ_tot^(3)` with eigenvalue `|σ|/2` (Tasaki eq. (2.2.10),
predicate form). -/
theorem basisVec_isInMagnetizationSubspace (σ : Λ → Fin 2) :
    IsInMagnetizationSubspace Λ ((magnetization Λ σ : ℂ) / 2) (basisVec σ) :=
  totalSpinHalfOp3_mulVec_basisVec_eq_magnetization Λ σ

/-- `Submodule`-form of `basisVec_isInMagnetizationSubspace`. -/
theorem basisVec_mem_magnetizationSubspace (σ : Λ → Fin 2) :
    (basisVec σ : (Λ → Fin 2) → ℂ) ∈
      magnetizationSubspace Λ ((magnetization Λ σ : ℂ) / 2) :=
  basisVec_isInMagnetizationSubspace Λ σ

/-! ## Disjointness of distinct sectors -/

/-- Distinct magnetization eigenvalues give disjoint subspaces.
The proof uses that an eigenvector with two distinct eigenvalues
must be zero: `(M - M') • v = 0` and `M ≠ M'` force `v = 0`. -/
theorem magnetizationSubspace_disjoint {M M' : ℂ} (hMM' : M ≠ M') :
    Disjoint (magnetizationSubspace Λ M) (magnetizationSubspace Λ M') := by
  rw [Submodule.disjoint_def]
  intros v hM hM'
  rw [mem_magnetizationSubspace_iff] at hM hM'
  -- Ŝ v = M v = M' v ⇒ (M - M') v = 0 ⇒ v = 0 (since M ≠ M').
  have heq : M • v = M' • v := hM.symm.trans hM'
  have hsub : (M - M') • v = 0 := by
    rw [sub_smul, heq, sub_self]
  have hne : M - M' ≠ 0 := sub_ne_zero.mpr hMM'
  exact (smul_eq_zero.mp hsub).resolve_left hne

/-! ## Spanning: every vector lies in the supremum of all sectors -/

/-- A vector expressed as a finite sum of basis states lies in the
supremum of all magnetization subspaces (each basis state lies in
its own sector, and the supremum is closed under sums). -/
private theorem sum_basisVec_mem_iSup
    (s : Finset (Λ → Fin 2)) (c : (Λ → Fin 2) → ℂ) :
    (∑ σ ∈ s, c σ • basisVec σ) ∈
      iSup (magnetizationSubspace Λ) := by
  refine Submodule.sum_mem _ ?_
  intros σ _
  refine Submodule.smul_mem _ _ ?_
  exact (le_iSup (magnetizationSubspace Λ) ((magnetization Λ σ : ℂ) / 2))
    (basisVec_mem_magnetizationSubspace Λ σ)

/-- Every vector decomposes as a finite sum over basis states (since
the index set `Λ → Fin 2` is finite). -/
private theorem eq_sum_basisVec (v : (Λ → Fin 2) → ℂ) :
    v = ∑ σ : Λ → Fin 2, v σ • basisVec σ := by
  funext τ
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  rw [Finset.sum_eq_single τ]
  · simp
  · intros σ _ hστ
    rw [if_neg (Ne.symm hστ), mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- The supremum of all magnetization subspaces is the full space:
every vector decomposes as a sum of basis states, and each basis state
lies in its own sector. -/
theorem iSup_magnetizationSubspace_eq_top :
    iSup (magnetizationSubspace Λ) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  rw [eq_sum_basisVec Λ v]
  exact sum_basisVec_mem_iSup Λ Finset.univ v

/-! ## Internal direct sum (`DirectSum.IsInternal`) -/

/-- The magnetization subspace coincides with the standard
`Module.End.eigenspace` of the total `Ŝ^(3)_tot` operator (viewed as
a `(Λ → Fin 2) → ℂ`-endomorphism via `Matrix.mulVecLin`). -/
theorem magnetizationSubspace_eq_eigenspace (M : ℂ) :
    magnetizationSubspace Λ M =
      Module.End.eigenspace ((totalSpinHalfOp3 Λ).mulVecLin) M := by
  ext v
  rw [mem_magnetizationSubspace_iff, Module.End.mem_eigenspace_iff,
    Matrix.mulVecLin_apply]

/-- The magnetization subspaces form an `iSupIndep` family: distinct
eigenvalues give linearly independent eigenspaces. Inherited from
`Module.End.eigenspaces_iSupIndep`. -/
theorem magnetizationSubspace_iSupIndep :
    iSupIndep (magnetizationSubspace Λ) := by
  have heq : magnetizationSubspace Λ =
      Module.End.eigenspace ((totalSpinHalfOp3 Λ).mulVecLin) := by
    funext M
    exact magnetizationSubspace_eq_eigenspace Λ M
  rw [heq]
  exact Module.End.eigenspaces_iSupIndep _

/-- The magnetization subspaces form an internal direct sum. -/
theorem magnetizationSubspace_isInternal :
    DirectSum.IsInternal (magnetizationSubspace Λ) :=
  (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr
    ⟨magnetizationSubspace_iSupIndep Λ,
     iSup_magnetizationSubspace_eq_top Λ⟩

/-! ## Membership of the ferromagnetic ground-state ladder iterates

Combining `totalSpinHalfOp3_mulVec_totalSpinHalfOp{Minus,Plus}_pow_basisVec_all_{up,down}`
(in `TotalSpin.lean`) with `mem_magnetizationSubspace_iff` shows that
the unnormalised iterates `(Ŝtot^∓)^k · |↑..↑⟩` and
`(Ŝtot^+)^k · |↓..↓⟩` of Tasaki §2.4 eq. (2.4.9) ground-state ladder
lie in the magnetisation sectors `H_{Smax - k}` and `H_{-Smax + k}`
respectively. -/

/-- The unnormalised iterate `(Ŝtot^-)^k · |↑..↑⟩` lies in the
magnetisation subspace `H_{|Λ|/2 - k}` (Tasaki §2.4 eq. (2.4.9), p. 33,
expressed in the `magnetizationSubspace` Submodule language). -/
theorem totalSpinHalfOpMinus_pow_basisVec_all_up_mem_magnetizationSubspace
    (k : ℕ) :
    ((totalSpinHalfOpMinus Λ) ^ k).mulVec
        (basisVec (fun _ : Λ => (0 : Fin 2))) ∈
      magnetizationSubspace Λ (((Fintype.card Λ : ℂ) / 2) - (k : ℂ)) :=
  totalSpinHalfOp3_mulVec_totalSpinHalfOpMinus_pow_basisVec_all_up Λ k

/-- The unnormalised iterate `(Ŝtot^+)^k · |↓..↓⟩` lies in the
magnetisation subspace `H_{-|Λ|/2 + k}` (Tasaki §2.4 eq. (2.4.9), p. 33,
parameterised from the lowest weight). -/
theorem totalSpinHalfOpPlus_pow_basisVec_all_down_mem_magnetizationSubspace
    (k : ℕ) :
    ((totalSpinHalfOpPlus Λ) ^ k).mulVec
        (basisVec (fun _ : Λ => (1 : Fin 2))) ∈
      magnetizationSubspace Λ ((-((Fintype.card Λ : ℂ) / 2)) + (k : ℂ)) :=
  totalSpinHalfOp3_mulVec_totalSpinHalfOpPlus_pow_basisVec_all_down Λ k

/-! ## Two-site Néel and singlet/triplet states in `H_0` (Tasaki §2.5/§A.3)

The two-site antiparallel basis states `|↑↓⟩ = basisVec upDown` and
`|↓↑⟩ = basisVec (basisSwap upDown 0 1)` both have total magnetisation
zero, hence lie in `magnetizationSubspace (Fin 2) 0`. Their sum and
difference are the standard SU(2) singlet (`m = 0`, `S = 0`) and
triplet-`m=0` (`S = 1`) states. -/

/-- The two-site Néel state `|↑↓⟩` lies in `H_0` (Tasaki §2.5
eq. (2.5.2), p. 37, two-site spin-1/2 instance). -/
theorem basisVec_upDown_mem_magnetizationSubspace_zero :
    (basisVec upDown : (Fin 2 → Fin 2) → ℂ) ∈
      magnetizationSubspace (Fin 2) 0 := by
  have h := basisVec_mem_magnetizationSubspace (Fin 2) upDown
  have hmag : magnetization (Fin 2) upDown = 0 := by
    unfold magnetization
    rw [Fin.sum_univ_two]
    simp [upDown_zero, upDown_one, spinSign]
  rw [hmag] at h
  simpa using h

/-- The swapped two-site state `|↓↑⟩` lies in `H_0`. -/
theorem basisVec_basisSwap_upDown_mem_magnetizationSubspace_zero :
    (basisVec (basisSwap upDown 0 1) : (Fin 2 → Fin 2) → ℂ) ∈
      magnetizationSubspace (Fin 2) 0 := by
  have h := basisVec_mem_magnetizationSubspace (Fin 2)
    (basisSwap upDown 0 1)
  have hmag : magnetization (Fin 2) (basisSwap upDown 0 1) = 0 := by
    unfold magnetization
    rw [Fin.sum_univ_two, basisSwap_upDown]
    simp [spinSign]
  rw [hmag] at h
  simpa using h

/-- The spin-singlet `|↑↓⟩ - |↓↑⟩` lies in `H_0`. -/
theorem singlet_mem_magnetizationSubspace_zero :
    (basisVec upDown - basisVec (basisSwap upDown 0 1) : (Fin 2 → Fin 2) → ℂ) ∈
      magnetizationSubspace (Fin 2) 0 :=
  Submodule.sub_mem _ basisVec_upDown_mem_magnetizationSubspace_zero
    basisVec_basisSwap_upDown_mem_magnetizationSubspace_zero

/-- The triplet `m = 0` state `|↑↓⟩ + |↓↑⟩` lies in `H_0`. -/
theorem triplet_zero_mem_magnetizationSubspace_zero :
    (basisVec upDown + basisVec (basisSwap upDown 0 1) : (Fin 2 → Fin 2) → ℂ) ∈
      magnetizationSubspace (Fin 2) 0 :=
  Submodule.add_mem _ basisVec_upDown_mem_magnetizationSubspace_zero
    basisVec_basisSwap_upDown_mem_magnetizationSubspace_zero

/-! ## Generic commuting-with-Ŝtot^(3) operator preserves the magnetisation sectors

Any operator `A` that commutes with `Ŝtot^(3)` maps each magnetisation
subspace `H_M` to itself. The Casimir `Ŝtot²` (commuting via
`totalSpinHalfSquared_commutator_totalSpinHalfOp3 = 0`) and the
Heisenberg Hamiltonian (PR #91) are both specialisations. -/

/-- An operator commuting with `Ŝtot^(3)` preserves every magnetisation
subspace `H_M`. -/
theorem mulVec_mem_magnetizationSubspace_of_commute_of_mem
    {A : ManyBodyOp Λ} (h : Commute A (totalSpinHalfOp3 Λ))
    {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    A.mulVec v ∈ magnetizationSubspace Λ M := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec, h.symm, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

/-- The Casimir `Ŝtot²` preserves every magnetisation subspace `H_M`
(consequence of `[Ŝtot², Ŝtot^(3)] = 0`). -/
theorem totalSpinHalfSquared_mulVec_mem_magnetizationSubspace_of_mem
    {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (totalSpinHalfSquared Λ).mulVec v ∈ magnetizationSubspace Λ M :=
  mulVec_mem_magnetizationSubspace_of_commute_of_mem Λ
    (sub_eq_zero.mp (totalSpinHalfSquared_commutator_totalSpinHalfOp3 Λ)) hv

/-! ## Heisenberg Hamiltonian preserves the magnetisation sectors

A direct consequence of SU(2) invariance
(`heisenbergHamiltonian_commutator_totalSpinHalfOp3 J = 0`): if
`v ∈ H_M`, then `H · v ∈ H_M`. This is the operator-level statement
that any Heisenberg Hamiltonian block-diagonalises against Tasaki
eq. (2.2.10) decomposition into magnetisation sectors. -/

/-- The Heisenberg Hamiltonian preserves the magnetisation-`M`
subspace `H_M`: if `v ∈ magnetizationSubspace M`, then
`H · v ∈ magnetizationSubspace M`. Equivalently, `H` block-diagonalises
against Tasaki §2.2 eq. (2.2.10), p. 22, decomposition into
magnetisation sectors. The invariance follows from the SU(2)
symmetry `[H, Ŝtot^(3)] = 0` (Tasaki §2.2 eq. (2.2.13), p. 23,
`heisenbergHamiltonian_commutator_totalSpinHalfOp3` in `SpinDot.lean`). -/
theorem heisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem
    (J : Λ → Λ → ℂ) {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (heisenbergHamiltonian J).mulVec v ∈ magnetizationSubspace Λ M := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  have hcomm : totalSpinHalfOp3 Λ * heisenbergHamiltonian J =
      heisenbergHamiltonian J * totalSpinHalfOp3 Λ :=
    (sub_eq_zero.mp (heisenbergHamiltonian_commutator_totalSpinHalfOp3 J)).symm
  rw [Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

/-! ## Ladder operators shift magnetisation `H_M → H_{M ± 1}`

The standard SU(2) ladder action: by the Cartan relations
`[Ŝtot^(3), Ŝtot^±] = ±Ŝtot^±` (already in `TotalSpin.lean`), the
raising operator `Ŝtot^+` increases the magnetisation eigenvalue by
one (`H_M → H_{M+1}`) and the lowering operator `Ŝtot^-` decreases
it by one (`H_M → H_{M-1}`). -/

/-- `Ŝ^-_tot` shifts magnetisation by `-1`: if `v ∈ H_M` then
`Ŝ^-_tot · v ∈ H_{M-1}`. -/
theorem totalSpinHalfOpMinus_mulVec_mem_magnetizationSubspace_of_mem
    {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (totalSpinHalfOpMinus Λ).mulVec v ∈ magnetizationSubspace Λ (M - 1) := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  -- [Ŝtot^(3), Ŝtot^-] = -Ŝtot^- ⟹ Ŝtot^(3) · Ŝtot^- = Ŝtot^- · Ŝtot^(3) - Ŝtot^-
  have h := totalSpinHalfOp3_commutator_totalSpinHalfOpMinus Λ
  have hcomm : totalSpinHalfOp3 Λ * totalSpinHalfOpMinus Λ =
      totalSpinHalfOpMinus Λ * totalSpinHalfOp3 Λ - totalSpinHalfOpMinus Λ := by
    have hadd : totalSpinHalfOp3 Λ * totalSpinHalfOpMinus Λ =
        (totalSpinHalfOp3 Λ * totalSpinHalfOpMinus Λ -
          totalSpinHalfOpMinus Λ * totalSpinHalfOp3 Λ) +
        totalSpinHalfOpMinus Λ * totalSpinHalfOp3 Λ := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, sub_smul, one_smul]

/-- `Ŝ^+_tot` shifts magnetisation by `+1`: if `v ∈ H_M` then
`Ŝ^+_tot · v ∈ H_{M+1}`. -/
theorem totalSpinHalfOpPlus_mulVec_mem_magnetizationSubspace_of_mem
    {M : ℂ} {v : (Λ → Fin 2) → ℂ}
    (hv : v ∈ magnetizationSubspace Λ M) :
    (totalSpinHalfOpPlus Λ).mulVec v ∈ magnetizationSubspace Λ (M + 1) := by
  rw [mem_magnetizationSubspace_iff] at hv ⊢
  -- [Ŝtot^(3), Ŝtot^+] = +Ŝtot^+ ⟹ Ŝtot^(3) · Ŝtot^+ = Ŝtot^+ · Ŝtot^(3) + Ŝtot^+
  have h := totalSpinHalfOp3_commutator_totalSpinHalfOpPlus Λ
  have hcomm : totalSpinHalfOp3 Λ * totalSpinHalfOpPlus Λ =
      totalSpinHalfOpPlus Λ * totalSpinHalfOp3 Λ + totalSpinHalfOpPlus Λ := by
    have hadd : totalSpinHalfOp3 Λ * totalSpinHalfOpPlus Λ =
        (totalSpinHalfOp3 Λ * totalSpinHalfOpPlus Λ -
          totalSpinHalfOpPlus Λ * totalSpinHalfOp3 Λ) +
        totalSpinHalfOpPlus Λ * totalSpinHalfOp3 Λ := by abel
    rw [hadd, h]; abel
  rw [Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul, add_smul, one_smul]

end LatticeSystem.Quantum
