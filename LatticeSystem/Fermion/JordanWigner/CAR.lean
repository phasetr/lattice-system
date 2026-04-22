/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Operators
import Mathlib.Tactic.NoncommRing

/-!
# Jordan–Wigner canonical anticommutation relations

The full CAR algebra for the JW-mapped multi-mode fermions:
- same-site `{c_i, c_i†} = 1` and `c_i² = (c_i†)² = 0`,
- number-operator commutativity,
- 2-site cross-site CAR (simplest nontrivial),
- JW string interior factorisation,
- general cross-site CAR `{c_i, c_j} = {c_i†, c_j†} = 0`,
  `{c_i, c_j†} = δ_ij` for any `i < j`.

(Refactor Phase 2 PR 12 — third step of the JordanWigner 5-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Number operator: commutativity and total -/

/-- Site-occupation number operators commute for any sites
`i, j : Fin (N + 1)`: they are simultaneously diagonal in the
occupation-number basis. -/
theorem fermionMultiNumber_commute (N : ℕ) (i j : Fin (N + 1)) :
    Commute (fermionMultiNumber N i) (fermionMultiNumber N j) := by
  rw [fermionMultiNumber_eq_onSite, fermionMultiNumber_eq_onSite]
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · exact onSite_mul_onSite_of_ne hij _ _

/-- The total particle-number operator on `Fin (N + 1)`:
`N̂ := Σ_i n_i`. -/
noncomputable def fermionTotalNumber (N : ℕ) : ManyBodyOp (Fin (N + 1)) :=
  ∑ i : Fin (N + 1), fermionMultiNumber N i

/-- The total particle-number operator is Hermitian (sum of
Hermitian summands). -/
theorem fermionTotalNumber_isHermitian (N : ℕ) :
    (fermionTotalNumber N).IsHermitian := by
  unfold fermionTotalNumber
  classical
  induction (Finset.univ : Finset (Fin (N + 1))) using Finset.induction_on with
  | empty => simp
  | @insert a t hat ih =>
    rw [Finset.sum_insert hat]
    exact (fermionMultiNumber_isHermitian N a).add ih

/-! ## Same-site canonical anticommutation -/

/-- The single-site identity `σ^+ · σ^- + σ^- · σ^+ = I`. This is the
spin-1/2 raising/lowering anticommutator, equal to the identity. -/
private lemma spinHalfOpPlus_anticomm_spinHalfOpMinus :
    spinHalfOpPlus * spinHalfOpMinus + spinHalfOpMinus * spinHalfOpPlus
      = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold spinHalfOpPlus spinHalfOpMinus
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The same-site canonical anticommutation relation:
`c_i · c_i† + c_i† · c_i = 1`. Combined with `c_i² = 0` and
`(c_i†)² = 0`, this constitutes the full single-site CAR algebra in
the multi-mode setting. -/
theorem fermionMultiAnticomm_self (N : ℕ) (i : Fin (N + 1)) :
    fermionMultiAnnihilation N i * fermionMultiCreation N i
      + fermionMultiCreation N i * fermionMultiAnnihilation N i = 1 := by
  unfold fermionMultiAnnihilation fermionMultiCreation
  have hcomm_plus : Commute (onSite i spinHalfOpPlus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpPlus).symm
  have hcomm_minus : Commute (onSite i spinHalfOpMinus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpMinus).symm
  have h1 : jwString N i * onSite i spinHalfOpPlus *
              (jwString N i * onSite i spinHalfOpMinus)
          = jwString N i * jwString N i *
              (onSite i spinHalfOpPlus * onSite i spinHalfOpMinus) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpPlus),
        hcomm_plus.eq, Matrix.mul_assoc, Matrix.mul_assoc]
  have h2 : jwString N i * onSite i spinHalfOpMinus *
              (jwString N i * onSite i spinHalfOpPlus)
          = jwString N i * jwString N i *
              (onSite i spinHalfOpMinus * onSite i spinHalfOpPlus) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (onSite i spinHalfOpMinus),
        hcomm_minus.eq, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h1, h2, jwString_sq, Matrix.one_mul, Matrix.one_mul,
    onSite_mul_onSite_same, onSite_mul_onSite_same, ← onSite_add,
    spinHalfOpPlus_anticomm_spinHalfOpMinus, onSite_one]

/-! ## Cross-site CAR on `Fin 2` (simplest nontrivial JW case)

For the 2-site lattice `Fin 2`, the Jordan-Wigner string at site 1 is
exactly `σ^z_0` (the single factor), so
`c_0 = σ^+_0` and `c_1 = σ^z_0 · σ^+_1`. Combining the Pauli identities
`σ^+ σ^z = -σ^+` and `σ^z σ^+ = σ^+` with the `onSite` algebra,
`{c_0, c_1} = 0`. -/

/-- Cross-site CAR on `Fin 2`: `c_0 · c_1 + c_1 · c_0 = 0`. The
simplest nontrivial Jordan-Wigner cross-site anticommutator. -/
theorem fermionMultiAnnihilation_anticomm_two_site_cross :
    fermionMultiAnnihilation 1 (0 : Fin 2) *
        fermionMultiAnnihilation 1 1 +
      fermionMultiAnnihilation 1 1 *
        fermionMultiAnnihilation 1 0 = 0 := by
  -- c_0 = σ^+_0 via jwString_zero.
  rw [fermionMultiAnnihilation_zero]
  -- c_1 = jwString 1 1 * σ^+_1. The JW string has one factor (site 0).
  have hjw : jwString 1 (1 : Fin 2) = onSite (0 : Fin 2) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin 2)).filter
        (fun j : Fin 2 => j.val < (1 : Fin 2).val) = ({0} : Finset (Fin 2)) := by
      ext k; fin_cases k <;> simp
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  change onSite (0 : Fin 2) spinHalfOpPlus *
        fermionMultiAnnihilation 1 1 +
      fermionMultiAnnihilation 1 1 *
        onSite (0 : Fin 2) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw]
  -- Goal: σ^+_0 · (σ^z_0 · σ^+_1) + (σ^z_0 · σ^+_1) · σ^+_0 = 0
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- Compute c_0 · c_1 = σ^+_0 · σ^z_0 · σ^+_1 = (σ^+ σ^z)_0 · σ^+_1 = -σ^+_0 · σ^+_1
  have hfirst : onSite (0 : Fin 2) spinHalfOpPlus *
      (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpPlus) =
        -(onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpPlus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    -- Goal: onSite 0 (-σ^+) * onSite 1 σ^+ = -(onSite 0 σ^+ * onSite 1 σ^+)
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- Compute c_1 · c_0 = σ^z_0 · σ^+_1 · σ^+_0 = σ^z_0 · σ^+_0 · σ^+_1 = σ^+_0 · σ^+_1
  have hsecond : (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpPlus) *
      onSite (0 : Fin 2) spinHalfOpPlus =
        onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpPlus := by
    -- Swap σ^+_1 past σ^+_0 (disjoint sites 0 and 1), then combine σ^z σ^+ = σ^+
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Cross-site CAR for the creation operators on `Fin 2`:
`c_0† · c_1† + c_1† · c_0† = 0`. Direct consequence of the
annihilation-operator version
(`fermionMultiAnnihilation_anticomm_two_site_cross`) by taking the
matrix `conjTranspose`. -/
theorem fermionMultiCreation_anticomm_two_site_cross :
    fermionMultiCreation 1 (0 : Fin 2) *
        fermionMultiCreation 1 1 +
      fermionMultiCreation 1 1 *
        fermionMultiCreation 1 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_two_site_cross
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  -- h2 : c_1† · c_0† + c_0† · c_1† = 0, goal: c_0† · c_1† + c_1† · c_0† = 0
  rw [show fermionMultiCreation 1 (0 : Fin 2) * fermionMultiCreation 1 1 +
        fermionMultiCreation 1 1 * fermionMultiCreation 1 (0 : Fin 2) =
      fermionMultiCreation 1 1 * fermionMultiCreation 1 (0 : Fin 2) +
        fermionMultiCreation 1 (0 : Fin 2) * fermionMultiCreation 1 1 from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR on `Fin 2`: `c_0 · c_1† + c_1† · c_0 = 0`.
Same proof structure as PR #108 with `σ^+_1` replaced by `σ^-_1` at
site 1 (the site-0 Pauli identities are unchanged). -/
theorem fermionMultiAnnihilation_creation_anticomm_two_site_cross :
    fermionMultiAnnihilation 1 (0 : Fin 2) *
        fermionMultiCreation 1 1 +
      fermionMultiCreation 1 1 *
        fermionMultiAnnihilation 1 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw : jwString 1 (1 : Fin 2) = onSite (0 : Fin 2) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin 2)).filter
        (fun j : Fin 2 => j.val < (1 : Fin 2).val) = ({0} : Finset (Fin 2)) := by
      ext k; fin_cases k <;> simp
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  change onSite (0 : Fin 2) spinHalfOpPlus *
        fermionMultiCreation 1 1 +
      fermionMultiCreation 1 1 *
        onSite (0 : Fin 2) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  -- c_0 · c_1† = σ^+_0 · σ^z_0 · σ^-_1 = -σ^+_0 · σ^-_1
  have hfirst : onSite (0 : Fin 2) spinHalfOpPlus *
      (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpMinus) =
        -(onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpMinus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- c_1† · c_0 = σ^z_0 · σ^-_1 · σ^+_0 = σ^z_0 · σ^+_0 · σ^-_1 = σ^+_0 · σ^-_1
  have hsecond : (onSite (0 : Fin 2) pauliZ * onSite (1 : Fin 2) spinHalfOpMinus) *
      onSite (0 : Fin 2) spinHalfOpPlus =
        onSite (0 : Fin 2) spinHalfOpPlus * onSite (1 : Fin 2) spinHalfOpMinus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Cross-site CAR for any chain length `N ≥ 1`:
`c_0 · c_1 + c_1 · c_0 = 0` on `Fin (N+1)`. Generalises the `Fin 2`
case to arbitrary `N`, since the JW string at site 1 only depends on
the filter `{j : j.val < 1} = {0}`, independent of `N`. -/
theorem fermionMultiAnnihilation_anticomm_zero_one
    (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
        (fun j : Fin (N + 1) => j.val < (⟨1, by omega⟩ : Fin (N + 1)).val) =
        ({(0 : Fin (N + 1))} : Finset (Fin (N + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · apply Fin.ext
        have : (k.val : ℕ) < 1 := h
        have : (k.val : ℕ) = 0 := by omega
        rw [this]; rfl
      · rw [h]; change (0 : ℕ) < 1; omega
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    have := Fin.val_eq_of_eq h
    simp at this
  -- c_0 · c_1 = σ^+_0 · σ^z_0 · σ^+_1 = -σ^+_0 · σ^+_1
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- c_1 · c_0 = σ^z_0 · σ^+_1 · σ^+_0 = σ^z_0 · σ^+_0 · σ^+_1 = σ^+_0 · σ^+_1
  have hsecond : (onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpPlus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Dual cross-site CAR for creation operators on `Fin (N+1)`, `N ≥ 1`:
`c_0† · c_1† + c_1† · c_0† = 0`. Obtained from PR #112 by taking
`conjTranspose`. -/
theorem fermionMultiCreation_anticomm_zero_one (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_one N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR on `Fin (N+1)`, `N ≥ 1`:
`c_0 · c_1† + c_1† · c_0 = 0`. Same template as PR #112 with
`σ^+_1` replaced by `σ^-_1` at site 1. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_one
    (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
        (fun j : Fin (N + 1) => j.val < (⟨1, by omega⟩ : Fin (N + 1)).val) =
        ({(0 : Fin (N + 1))} : Finset (Fin (N + 1))) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · apply Fin.ext
        have : (k.val : ℕ) < 1 := h
        have : (k.val : ℕ) = 0 := by omega
        rw [this]; rfl
      · rw [h]; change (0 : ℕ) < 1; omega
    unfold jwString
    rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
    exact Finset.noncommProd_singleton _ _
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiCreation N ⟨1, by omega⟩ +
      fermionMultiCreation N ⟨1, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    have := Fin.val_eq_of_eq h
    simp at this
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
    rw [← Matrix.mul_assoc, onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : (onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) spinHalfOpMinus := by
    rw [Matrix.mul_assoc, onSite_mul_onSite_of_ne h01.symm, ← Matrix.mul_assoc,
      onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Mixed cross-site CAR on `Fin (N+1)`, `N ≥ 1`:
`c_0† · c_1 + c_1 · c_0† = 0`. Obtained by `conjTranspose` of the
previous. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_one
    (N : ℕ) (hN : 1 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_one N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩ +
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiAnnihilation N ⟨1, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨1, by omega⟩
    from add_comm _ _]
  exact h2

/-- Cross-site CAR `{c_0, c_2} = 0` on `Fin 3`. First 3-site case,
using `jwString_succ_eq` to factor
`jwString 2 2 = onSite 0 pauliZ * onSite 1 pauliZ`. -/
theorem fermionMultiAnnihilation_anticomm_zero_two_fin_three :
    fermionMultiAnnihilation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        fermionMultiAnnihilation 2 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  -- jwString 2 2 via succ_eq: jwString 2 (1+1) = jwString 2 1 * onSite 1 pauliZ
  have hjw1 : jwString 2 (1 : Fin 3) = onSite (0 : Fin 3) pauliZ := by
    have := jwString_succ_eq 2 (0 : Fin 3) (by decide)
    simpa [jwString_zero] using this
  have hjw2 : jwString 2 (2 : Fin 3) =
      onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ := by
    have h := jwString_succ_eq 2 (1 : Fin 3) (by decide)
    -- h : jwString 2 ⟨2, _⟩ = jwString 2 1 * onSite 1 pauliZ
    rw [hjw1] at h
    -- h : jwString 2 ⟨2, _⟩ = onSite 0 pauliZ * onSite 1 pauliZ
    convert h using 2
  change onSite (0 : Fin 3) spinHalfOpPlus *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        onSite (0 : Fin 3) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw2]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  -- c_0 · c_2 = σ^+_0 · (σ^z_0 · σ^z_1) · σ^+_2
  --           = (σ^+_0 · σ^z_0) · σ^z_1 · σ^+_2 = -σ^+_0 · σ^z_1 · σ^+_2.
  have hfirst : onSite (0 : Fin 3) spinHalfOpPlus *
      (onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
        onSite (2 : Fin 3) spinHalfOpPlus) =
        -(onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus)) := by
    rw [show onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpPlus =
        onSite (0 : Fin 3) pauliZ *
            (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin 3) spinHalfOpPlus), onSite_mul_onSite_same,
      spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  -- c_2 · c_0 = (σ^z_0 · σ^z_1 · σ^+_2) · σ^+_0 = σ^+_0 · σ^z_1 · σ^+_2.
  have hsecond : onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
      onSite (2 : Fin 3) spinHalfOpPlus *
      onSite (0 : Fin 3) spinHalfOpPlus =
        onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
    have step1 : onSite (2 : Fin 3) spinHalfOpPlus *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (2 : Fin 3) spinHalfOpPlus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpPlus spinHalfOpPlus
    have step2 : onSite (1 : Fin 3) pauliZ *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (1 : Fin 3) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          onSite (2 : Fin 3) spinHalfOpPlus *
          onSite (0 : Fin 3) spinHalfOpPlus
        = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (2 : Fin 3) spinHalfOpPlus *
            onSite (0 : Fin 3) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpPlus) := by rw [step1]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ *
            (onSite (0 : Fin 3) spinHalfOpPlus *
              onSite (2 : Fin 3) spinHalfOpPlus)) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpPlus) := by rw [step2]
      _ = onSite (0 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) (pauliZ * spinHalfOpPlus) *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
          rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpPlus) := by
          rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Mixed cross-site CAR `{c_0, c_2†} = 0` on `Fin 3`. Same template
as PR #116 with `σ^+_2` replaced by `σ^-_2`. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_two_fin_three :
    fermionMultiAnnihilation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        fermionMultiAnnihilation 2 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw1 : jwString 2 (1 : Fin 3) = onSite (0 : Fin 3) pauliZ := by
    have := jwString_succ_eq 2 (0 : Fin 3) (by decide)
    simpa [jwString_zero] using this
  have hjw2 : jwString 2 (2 : Fin 3) =
      onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ := by
    have h := jwString_succ_eq 2 (1 : Fin 3) (by decide)
    rw [hjw1] at h
    convert h using 2
  change onSite (0 : Fin 3) spinHalfOpPlus *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        onSite (0 : Fin 3) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw2]
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have hfirst : onSite (0 : Fin 3) spinHalfOpPlus *
      (onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
        onSite (2 : Fin 3) spinHalfOpMinus) =
        -(onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus)) := by
    rw [show onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpMinus =
        onSite (0 : Fin 3) pauliZ *
            (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin 3) spinHalfOpPlus), onSite_mul_onSite_same,
      spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
      onSite (2 : Fin 3) spinHalfOpMinus *
      onSite (0 : Fin 3) spinHalfOpPlus =
        onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
    have step1 : onSite (2 : Fin 3) spinHalfOpMinus *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (2 : Fin 3) spinHalfOpMinus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpMinus spinHalfOpPlus
    have step2 : onSite (1 : Fin 3) pauliZ *
        onSite (0 : Fin 3) spinHalfOpPlus =
      onSite (0 : Fin 3) spinHalfOpPlus *
        onSite (1 : Fin 3) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          onSite (2 : Fin 3) spinHalfOpMinus *
          onSite (0 : Fin 3) spinHalfOpPlus
        = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (2 : Fin 3) spinHalfOpMinus *
            onSite (0 : Fin 3) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ * onSite (1 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpMinus) := by rw [step1]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ *
            (onSite (0 : Fin 3) spinHalfOpPlus *
              onSite (2 : Fin 3) spinHalfOpMinus)) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (1 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
            onSite (2 : Fin 3) spinHalfOpMinus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) pauliZ *
          (onSite (0 : Fin 3) spinHalfOpPlus * onSite (1 : Fin 3) pauliZ *
            onSite (2 : Fin 3) spinHalfOpMinus) := by rw [step2]
      _ = onSite (0 : Fin 3) pauliZ * onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin 3) (pauliZ * spinHalfOpPlus) *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
          rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin 3) spinHalfOpPlus *
          (onSite (1 : Fin 3) pauliZ * onSite (2 : Fin 3) spinHalfOpMinus) := by
          rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Cross-site CAR `{c_0, c_2} = 0` for any chain length `N ≥ 2`.
Generalises PR #116 (Fin 3) to arbitrary `Fin (N+1)` using the same
`jwString_succ_eq` factorisation. -/
theorem fermionMultiAnnihilation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  -- jwString at sites 1 and 2 via jwString_succ_eq
  have hjw1 : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (0 : Fin (N + 1))
      (show (0 : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    simpa [jwString_zero] using h
  have hjw2 : jwString N ⟨2, by omega⟩ =
      onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (⟨1, by omega⟩ : Fin (N + 1))
      (show (⟨1, _⟩ : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    rw [hjw1] at h
    convert h using 2
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiAnnihilation
  rw [hjw2]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨1, _⟩ : Fin (N + 1)).val
      simp)
  have h02 : (0 : Fin (N + 1)) ≠ ⟨2, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨2, _⟩ : Fin (N + 1)).val
      simp)
  -- Same as PR #116 structure
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus)) := by
    rw [show onSite (0 : Fin (N + 1)) pauliZ *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) pauliZ *
            (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin (N + 1)) spinHalfOpPlus),
      onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
      onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
    have step1 : onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpPlus spinHalfOpPlus
    have step2 : onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus
        = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by rw [step1]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus)) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by rw [step2]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) (pauliZ * spinHalfOpPlus) *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpPlus) := by
                rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Dual `{c_0†, c_2†} = 0` for any `N ≥ 2` via adjoint of PR #123. -/
theorem fermionMultiCreation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_two_general N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ from add_comm _ _]
  exact h2

/-- Mixed `{c_0, c_2†} = 0` for any `N ≥ 2`. Same template as PR #123
with `σ^+_2` replaced by `σ^-_2`. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hjw1 : jwString N ⟨1, by omega⟩ = onSite (0 : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (0 : Fin (N + 1))
      (show (0 : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    simpa [jwString_zero] using h
  have hjw2 : jwString N ⟨2, by omega⟩ =
      onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ := by
    have h := jwString_succ_eq N (⟨1, by omega⟩ : Fin (N + 1))
      (show (⟨1, _⟩ : Fin (N + 1)).val + 1 < N + 1 by simp; omega)
    rw [hjw1] at h
    convert h using 2
  change onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        fermionMultiCreation N ⟨2, by omega⟩ +
      fermionMultiCreation N ⟨2, by omega⟩ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
  unfold fermionMultiCreation
  rw [hjw2]
  have h01 : (0 : Fin (N + 1)) ≠ ⟨1, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨1, _⟩ : Fin (N + 1)).val
      simp)
  have h02 : (0 : Fin (N + 1)) ≠ ⟨2, by omega⟩ := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : Fin (N + 1)).val ≠ (⟨2, _⟩ : Fin (N + 1)).val
      simp)
  have hfirst : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
      (onSite (0 : Fin (N + 1)) pauliZ *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) =
        -(onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus)) := by
    rw [show onSite (0 : Fin (N + 1)) pauliZ *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus =
        onSite (0 : Fin (N + 1)) pauliZ *
            (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) from
          by rw [Matrix.mul_assoc]]
    rw [← Matrix.mul_assoc (onSite (0 : Fin (N + 1)) spinHalfOpPlus),
      onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ]
    rw [show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • spinHalfOpPlus
      from by rw [neg_one_smul], onSite_smul, Matrix.smul_mul, neg_one_smul]
  have hsecond : onSite (0 : Fin (N + 1)) pauliZ *
      onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
      onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
      onSite (0 : Fin (N + 1)) spinHalfOpPlus =
        onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
    have step1 : onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus :=
      onSite_mul_onSite_of_ne h02.symm spinHalfOpMinus spinHalfOpPlus
    have step2 : onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus =
      onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ :=
      onSite_mul_onSite_of_ne h01.symm pauliZ spinHalfOpPlus
    calc onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus
        = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus) := by rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by rw [step1]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
              onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus)) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          (onSite (0 : Fin (N + 1)) spinHalfOpPlus *
            onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by rw [step2]
      _ = onSite (0 : Fin (N + 1)) pauliZ *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = onSite (0 : Fin (N + 1)) (pauliZ * spinHalfOpPlus) *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [onSite_mul_onSite_same]
      _ = onSite (0 : Fin (N + 1)) spinHalfOpPlus *
          (onSite (⟨1, by omega⟩ : Fin (N + 1)) pauliZ *
            onSite (⟨2, by omega⟩ : Fin (N + 1)) spinHalfOpMinus) := by
                rw [pauliZ_mul_spinHalfOpPlus]
  rw [hfirst, hsecond, neg_add_cancel]

/-- Mixed dual `{c_0†, c_2} = 0` for any `N ≥ 2` via adjoint. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_two_general
    (N : ℕ) (hN : 2 ≤ N) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_two_general N hN
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ +
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiAnnihilation N ⟨2, by omega⟩ *
        fermionMultiCreation N (0 : Fin (N + 1)) +
      fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N ⟨2, by omega⟩ from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR `{c_0†, c_2} = 0` on `Fin 3` via adjoint of
PR #119. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_two_fin_three :
    fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        fermionMultiCreation 2 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_two_fin_three
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 +
      fermionMultiAnnihilation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) =
      fermionMultiAnnihilation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) +
      fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiAnnihilation 2 2 from add_comm _ _]
  exact h2

/-- Cross-site CAR `{c_0†, c_2†} = 0` on `Fin 3`. Direct consequence
of PR #116 via `conjTranspose`. -/
theorem fermionMultiCreation_anticomm_zero_two_fin_three :
    fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        fermionMultiCreation 2 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_two_fin_three
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 +
      fermionMultiCreation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) =
      fermionMultiCreation 2 2 *
        fermionMultiCreation 2 (0 : Fin 3) +
      fermionMultiCreation 2 (0 : Fin 3) *
        fermionMultiCreation 2 2 from add_comm _ _]
  exact h2

/-- Fourth off-diagonal CAR on `Fin 2`: `c_0† · c_1 + c_1 · c_0† = 0`.
Obtained from PR #110's mixed annihilation/creation version by taking
`conjTranspose`. Completes the 2-site off-diagonal CAR relations. -/
theorem fermionMultiCreation_annihilation_anticomm_two_site_cross :
    fermionMultiCreation 1 (0 : Fin 2) *
        fermionMultiAnnihilation 1 1 +
      fermionMultiAnnihilation 1 1 *
        fermionMultiCreation 1 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_two_site_cross
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  -- h2 : c_1 · c_0† + c_0† · c_1 = 0, goal: c_0† · c_1 + c_1 · c_0† = 0
  rw [show fermionMultiCreation 1 (0 : Fin 2) * fermionMultiAnnihilation 1 1 +
        fermionMultiAnnihilation 1 1 * fermionMultiCreation 1 (0 : Fin 2) =
      fermionMultiAnnihilation 1 1 * fermionMultiCreation 1 (0 : Fin 2) +
        fermionMultiCreation 1 (0 : Fin 2) * fermionMultiAnnihilation 1 1
    from add_comm _ _]
  exact h2

/-! ## JW string factorisation at an interior site (#210)

For any `i j : Fin (N + 1)` with `i.val < j.val`, the
Jordan-Wigner string at `j` contains a `σ^z_i` factor that we want
to extract. The remaining factors live at sites strictly less than
`j` *and* different from `i`, hence commute with any operator
acting at site `i`. This is the building block for the fully
general cross-site CAR `{c_i, c_j} = 0` (#210). -/

/-- The "site-`i` excluded" Jordan-Wigner string at `j`: the
non-commutative product of `σ^z_k` over all `k` with `k.val < j.val`
*and* `k ≠ i`. Together with `jwString_eq_onSite_mul_jwStringExceptAt`
this provides the canonical factorisation
`jwString N j = σ^z_i · jwStringExceptAt N j i` whenever
`i.val < j.val`. -/
private noncomputable def jwStringExceptAt
    (N : ℕ) (j i : Fin (N + 1)) : ManyBodyOp (Fin (N + 1)) :=
  ((Finset.univ : Finset (Fin (N + 1))).filter
    (fun k => k.val < j.val ∧ k ≠ i)).noncommProd
    (fun k => onSite k pauliZ)
    (fun _ _ _ _ hab => onSite_mul_onSite_of_ne hab pauliZ pauliZ)

/-- Factorisation of the Jordan-Wigner string at site `j` around an
interior site `i` with `i.val < j.val`:
`jwString N j = σ^z_i · jwStringExceptAt N j i`. -/
private lemma jwString_eq_onSite_mul_jwStringExceptAt
    (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    jwString N j = onSite i pauliZ * jwStringExceptAt N j i := by
  unfold jwString jwStringExceptAt
  have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
      (fun k => k.val < j.val) =
      insert i ((Finset.univ : Finset (Fin (N + 1))).filter
        (fun k => k.val < j.val ∧ k ≠ i)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro h
      by_cases hki : k = i
      · left; exact hki
      · right; exact ⟨h, hki⟩
    · rintro (h0 | ⟨hlt, _⟩)
      · rw [h0]; exact hij
      · exact hlt
  have hi_notmem : i ∉ ((Finset.univ : Finset (Fin (N + 1))).filter
      (fun k => k.val < j.val ∧ k ≠ i)) := by
    simp
  rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ hi_notmem

/-- The site-`i`-excluded JW string commutes with any single-site
operator at site `i`: every factor of `jwStringExceptAt N j i`
lives at a site `k ≠ i`, so `onSite_mul_onSite_of_ne` applies
factor-wise. -/
private lemma jwStringExceptAt_commute_onSite
    (N : ℕ) (j i : Fin (N + 1)) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (jwStringExceptAt N j i) (onSite i A) := by
  unfold jwStringExceptAt
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro k hk
  rw [Finset.mem_filter] at hk
  exact onSite_mul_onSite_of_ne hk.2.2.symm A pauliZ

/-- Operator-level anticommutator at an interior site: for every
`i j : Fin (N + 1)` with `i.val < j.val`,

  `σ^+_i · jwString N j + jwString N j · σ^+_i = 0`.

Generalises `jwString_anticomm_onSite_zero_spinHalfOpPlus`
(the `i = 0` special case used for the (0, k) cross-site CAR) to
arbitrary `i < j`. Building block for the fully general cross-site
CAR `{c_i, c_j} = 0` (#210). -/
theorem jwString_anticomm_onSite_pos_spinHalfOpPlus
    (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    onSite i spinHalfOpPlus * jwString N j +
      jwString N j * onSite i spinHalfOpPlus = 0 := by
  rw [jwString_eq_onSite_mul_jwStringExceptAt N i j hij]
  set A := onSite i spinHalfOpPlus
  set Z := onSite i pauliZ
  set M := jwStringExceptAt N j i
  have hcomm : A * M = M * A :=
    (jwStringExceptAt_commute_onSite N j i spinHalfOpPlus).symm
  have h_ZA : Z * A = A := by
    rw [onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  have h_AZ_eq_neg_A : A * Z = -A := by
    rw [onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ,
      show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) =
          0 - spinHalfOpPlus from (zero_sub _).symm,
      onSite_sub, onSite_zero, zero_sub]
  -- Goal: A * (Z * M) + Z * M * A = 0
  calc A * (Z * M) + Z * M * A
      = A * Z * M + Z * M * A := by rw [← Matrix.mul_assoc]
    _ = (-A) * M + Z * M * A := by rw [h_AZ_eq_neg_A]
    _ = (-A) * M + Z * (M * A) := by rw [Matrix.mul_assoc]
    _ = (-A) * M + Z * (A * M) := by rw [← hcomm]
    _ = (-A) * M + (Z * A) * M := by rw [← Matrix.mul_assoc]
    _ = (-A) * M + A * M := by rw [h_ZA]
    _ = (-A + A) * M := by rw [Matrix.add_mul]
    _ = 0 * M := by rw [neg_add_cancel]
    _ = 0 := Matrix.zero_mul _

/-- Companion anticommutator at an interior site with the lowering
operator: for every `i j : Fin (N + 1)` with `i.val < j.val`,

  `σ^-_i · jwString N j + jwString N j · σ^-_i = 0`.

Derived from the `σ^+_i` version
(`jwString_anticomm_onSite_pos_spinHalfOpPlus`) by matrix
`conjTranspose`, using `jwString_isHermitian` and
`spinHalfOpPlus_conjTranspose` (`(σ^+)† = σ^-`). -/
theorem jwString_anticomm_onSite_pos_spinHalfOpMinus
    (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    onSite i spinHalfOpMinus * jwString N j +
      jwString N j * onSite i spinHalfOpMinus = 0 := by
  have h := jwString_anticomm_onSite_pos_spinHalfOpPlus N i j hij
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_zero, (jwString_isHermitian N j).eq] at h2
  have hplus : (onSite i spinHalfOpPlus)ᴴ = onSite i spinHalfOpMinus := by
    rw [onSite_conjTranspose, spinHalfOpPlus_conjTranspose]
  rw [hplus] at h2
  -- h2 : JW_j · σ^-_i + σ^-_i · JW_j = 0; goal: σ^-_i · JW_j + JW_j · σ^-_i = 0
  exact (add_comm _ _).trans h2

/-! ## JW string commutativity (any two strings commute)

Every `jwString N i` is a product of `σ^z` operators at distinct
sites, each of which is self-inverse (`σ^z · σ^z = 1`) and pairwise
commuting (`onSite_mul_onSite_of_ne`). Consequently any two
Jordan-Wigner strings `jwString N i` and `jwString N j` commute —
a combinatorial fact used in the fully general cross-site CAR
(#210). -/

/-- Two Jordan-Wigner strings commute. Both are built as
`Finset.noncommProd` over subsets of `Fin (N + 1)` of the function
`k ↦ onSite k pauliZ`; every cross pair lies at distinct sites so
`onSite_mul_onSite_of_ne` applies term-wise. -/
theorem jwString_commute_jwString (N : ℕ) (i j : Fin (N + 1)) :
    Commute (jwString N i) (jwString N j) := by
  unfold jwString
  apply Finset.noncommProd_commute
  intro a ha
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro b hb
  by_cases hab : a = b
  · subst hab
    exact Commute.refl _
  · exact onSite_mul_onSite_of_ne hab pauliZ pauliZ

/-! ## General cross-site CAR at site zero (`{c_0, c_k} = 0`, `k ≥ 1`)

For every `k : Fin (N + 1)` with `0 < k.val`, the Jordan-Wigner
string at site `k` anticommutes with the single-site raising
operator at site `0`:

  `σ^+_0 · jwString N k + jwString N k · σ^+_0 = 0`.

The proof is by induction on the number of factors in the string.
At one factor (`k.val = 1`) the string is exactly `σ^z_0`, and the
single-site Pauli identity `σ^+ σ^z + σ^z σ^+ = 0` closes the base
case. The inductive step appends one more `σ^z_j` at a site
`j ≥ 1` which commutes with `σ^+_0` (different sites), so the
anticommutation propagates unchanged.

Combined with the fact that `σ^+_0` commutes with the site-`k`
raising operator `σ^+_k` for `k ≠ 0`, this yields the full
cross-site CAR

  `c_0 · c_k + c_k · c_0 = 0` for every `k : Fin (N + 1)`
  with `0 < k.val`,

generalising the already-established
`fermionMultiAnnihilation_anticomm_zero_{one,two_general}` special
cases. The three companion off-diagonal CAR relations
(`{c_0, c_k†}`, `{c_0†, c_k}`, `{c_0†, c_k†}`) follow by
replacing `σ^+` with `σ^-` in the same argument — or by taking
matrix `conjTranspose` of the annihilation/annihilation version. -/

/-- Inductive helper: for every `m : ℕ` with `m + 1 < N + 1`, the
Jordan-Wigner string `jwString N ⟨m + 1, _⟩` anticommutes with
`σ^+_0`. Proof by induction on `m`. -/
private lemma jwString_anticomm_onSite_zero_spinHalfOpPlus
    (N : ℕ) (m : ℕ) :
    ∀ (hm : m + 1 < N + 1),
      onSite (0 : Fin (N + 1)) spinHalfOpPlus * jwString N ⟨m + 1, hm⟩ +
        jwString N ⟨m + 1, hm⟩ *
          onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0 := by
  induction m with
  | zero =>
    intro hm
    have hjw : jwString N (⟨1, hm⟩ : Fin (N + 1)) =
        onSite (0 : Fin (N + 1)) pauliZ := by
      have hfilter : (Finset.univ : Finset (Fin (N + 1))).filter
          (fun j : Fin (N + 1) => j.val < (⟨1, hm⟩ : Fin (N + 1)).val) =
          ({(0 : Fin (N + 1))} : Finset (Fin (N + 1))) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · apply Fin.ext
          have : (k.val : ℕ) < 1 := h
          change k.val = 0
          omega
        · rw [h]; change (0 : ℕ) < 1; omega
      unfold jwString
      rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
      exact Finset.noncommProd_singleton _ _
    rw [hjw, onSite_mul_onSite_same, onSite_mul_onSite_same,
      ← onSite_add, spinHalfOpPlus_mul_pauliZ, pauliZ_mul_spinHalfOpPlus,
      neg_add_cancel, onSite_zero]
  | succ m' ih =>
    intro hm
    have hm' : m' + 1 < N + 1 := by omega
    have IH := ih hm'
    have hm'' : (⟨m' + 1, hm'⟩ : Fin (N + 1)).val + 1 < N + 1 := by
      change m' + 1 + 1 < N + 1; exact hm
    have hrec : jwString N (⟨m' + 1 + 1, hm⟩ : Fin (N + 1)) =
        jwString N (⟨m' + 1, hm'⟩ : Fin (N + 1)) *
          onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ := by
      have h := jwString_succ_eq N (⟨m' + 1, hm'⟩ : Fin (N + 1)) hm''
      convert h using 2
    have h_ne : (0 : Fin (N + 1)) ≠ ⟨m' + 1, hm'⟩ := by
      intro h
      exact absurd (congrArg Fin.val h) (by
        change (0 : ℕ) ≠ m' + 1
        omega)
    have hcomm : onSite (0 : Fin (N + 1)) spinHalfOpPlus *
        onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ =
      onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ *
        onSite (0 : Fin (N + 1)) spinHalfOpPlus :=
      onSite_mul_onSite_of_ne h_ne _ _
    rw [hrec]
    -- Goal: σ^+_0 * (JW_{m'+1} * σ^z_{m'+1}) + JW_{m'+1} * σ^z_{m'+1} * σ^+_0 = 0
    set A := onSite (0 : Fin (N + 1)) spinHalfOpPlus
    set B := jwString N (⟨m' + 1, hm'⟩ : Fin (N + 1))
    set Z := onSite (⟨m' + 1, hm'⟩ : Fin (N + 1)) pauliZ
    have hstep : A * (B * Z) + B * Z * A = (A * B + B * A) * Z := by
      calc A * (B * Z) + B * Z * A
          = A * B * Z + B * Z * A := by rw [← Matrix.mul_assoc]
        _ = A * B * Z + B * (Z * A) := by rw [Matrix.mul_assoc B]
        _ = A * B * Z + B * (A * Z) := by rw [← hcomm]
        _ = A * B * Z + B * A * Z := by rw [← Matrix.mul_assoc B]
        _ = (A * B + B * A) * Z := by rw [Matrix.add_mul]
    rw [hstep, IH, Matrix.zero_mul]

/-- General cross-site CAR at site zero: for every `N : ℕ` and every
`k : Fin (N + 1)` with `0 < k.val`,

  `c_0 · c_k + c_k · c_0 = 0`.

Generalises `fermionMultiAnnihilation_anticomm_zero_one` (the
`k.val = 1` special case) and
`fermionMultiAnnihilation_anticomm_zero_two_general` (the
`k.val = 2` special case). The proof reduces the cross-site
anticommutator of the fermion operators to the anticommutator
`{σ^+_0, jwString N k}`, which vanishes by
`jwString_anticomm_onSite_zero_spinHalfOpPlus`. -/
theorem fermionMultiAnnihilation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N k +
      fermionMultiAnnihilation N k *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  -- Reduce to σ^+_0 anticommuting with jwString_k, modulo commuting
  -- σ^+_0 past σ^+_k (different sites).
  have hm : k.val - 1 + 1 < N + 1 := by
    have := k.isLt; omega
  have hkeq : k = ⟨k.val - 1 + 1, hm⟩ := by
    apply Fin.ext
    change k.val = k.val - 1 + 1
    omega
  have h_ne : (0 : Fin (N + 1)) ≠ k := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : ℕ) ≠ k.val
      omega)
  have h_ne_sym : k ≠ (0 : Fin (N + 1)) := h_ne.symm
  -- c_k = jwString N k * onSite k σ^+
  unfold fermionMultiAnnihilation
  -- Goal: σ^+_0 * (JW_k * σ^+_k) + (JW_k * σ^+_k) * σ^+_0 = 0
  set A := onSite (0 : Fin (N + 1)) spinHalfOpPlus
  set B := jwString N k
  set P := onSite k spinHalfOpPlus
  have hcomm_AP : A * P = P * A :=
    onSite_mul_onSite_of_ne h_ne _ _
  have hanticomm : A * B + B * A = 0 := by
    change onSite (0 : Fin (N + 1)) spinHalfOpPlus * jwString N k +
      jwString N k * onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
    rw [hkeq]
    exact jwString_anticomm_onSite_zero_spinHalfOpPlus N (k.val - 1) hm
  -- Goal: A * (B * P) + B * P * A = 0
  calc A * (B * P) + B * P * A
      = A * B * P + B * P * A := by rw [← Matrix.mul_assoc]
    _ = A * B * P + B * (P * A) := by rw [Matrix.mul_assoc B]
    _ = A * B * P + B * (A * P) := by rw [← hcomm_AP]
    _ = A * B * P + B * A * P := by rw [← Matrix.mul_assoc B]
    _ = (A * B + B * A) * P := by rw [Matrix.add_mul]
    _ = 0 * P := by rw [hanticomm]
    _ = 0 := Matrix.zero_mul _

/-- Dual `{c_0†, c_k†} = 0` for any `k : Fin (N + 1)` with
`0 < k.val`, via `conjTranspose` of
`fermionMultiAnnihilation_anticomm_zero_pos`. -/
theorem fermionMultiCreation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiCreation N k +
      fermionMultiCreation N k *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_anticomm_zero_pos N k hk
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose, Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiCreation N k +
        fermionMultiCreation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiCreation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) +
        fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiCreation N k from add_comm _ _]
  exact h2

/-- Mixed cross-site CAR `{c_0, c_k†} = 0` for every `k : Fin (N + 1)`
with `0 < k.val`. Proof: identical structure to
`fermionMultiAnnihilation_anticomm_zero_pos`, since `c_k†` differs
from `c_k` only by the single-site factor at `k` (`σ^-_k` instead of
`σ^+_k`); the JW-string part is unchanged. Generalises
`fermionMultiAnnihilation_creation_anticomm_zero_one` and
`fermionMultiAnnihilation_creation_anticomm_zero_two_general`. -/
theorem fermionMultiAnnihilation_creation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiAnnihilation N (0 : Fin (N + 1)) *
        fermionMultiCreation N k +
      fermionMultiCreation N k *
        fermionMultiAnnihilation N 0 = 0 := by
  rw [fermionMultiAnnihilation_zero]
  have hm : k.val - 1 + 1 < N + 1 := by
    have := k.isLt; omega
  have hkeq : k = ⟨k.val - 1 + 1, hm⟩ := by
    apply Fin.ext
    change k.val = k.val - 1 + 1
    omega
  have h_ne : (0 : Fin (N + 1)) ≠ k := by
    intro h
    exact absurd (congrArg Fin.val h) (by
      change (0 : ℕ) ≠ k.val
      omega)
  unfold fermionMultiCreation
  set A := onSite (0 : Fin (N + 1)) spinHalfOpPlus
  set B := jwString N k
  set M := onSite k spinHalfOpMinus
  have hcomm_AM : A * M = M * A :=
    onSite_mul_onSite_of_ne h_ne _ _
  have hanticomm : A * B + B * A = 0 := by
    change onSite (0 : Fin (N + 1)) spinHalfOpPlus * jwString N k +
      jwString N k * onSite (0 : Fin (N + 1)) spinHalfOpPlus = 0
    rw [hkeq]
    exact jwString_anticomm_onSite_zero_spinHalfOpPlus N (k.val - 1) hm
  calc A * (B * M) + B * M * A
      = A * B * M + B * M * A := by rw [← Matrix.mul_assoc]
    _ = A * B * M + B * (M * A) := by rw [Matrix.mul_assoc B]
    _ = A * B * M + B * (A * M) := by rw [← hcomm_AM]
    _ = A * B * M + B * A * M := by rw [← Matrix.mul_assoc B]
    _ = (A * B + B * A) * M := by rw [Matrix.add_mul]
    _ = 0 * M := by rw [hanticomm]
    _ = 0 := Matrix.zero_mul _

/-- Mixed cross-site CAR `{c_0†, c_k} = 0` for every `k : Fin (N + 1)`
with `0 < k.val`, via `conjTranspose` of
`fermionMultiAnnihilation_creation_anticomm_zero_pos`. -/
theorem fermionMultiCreation_annihilation_anticomm_zero_pos
    (N : ℕ) (k : Fin (N + 1)) (hk : 0 < k.val) :
    fermionMultiCreation N (0 : Fin (N + 1)) *
        fermionMultiAnnihilation N k +
      fermionMultiAnnihilation N k *
        fermionMultiCreation N 0 = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_zero_pos N k hk
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  rw [show fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiAnnihilation N k +
        fermionMultiAnnihilation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) =
      fermionMultiAnnihilation N k *
          fermionMultiCreation N (0 : Fin (N + 1)) +
        fermionMultiCreation N (0 : Fin (N + 1)) *
          fermionMultiAnnihilation N k from add_comm _ _]
  exact h2

/-! ## Fully general cross-site CAR for arbitrary `i < j` (#210)

For every `i j : Fin (N + 1)` with `i.val < j.val`,

  `c_i · c_j + c_j · c_i = 0`   (and the three dual / mixed forms).

The (0, k) special case was #208, #211. This section closes the
general case via the interior-site JW string anticommutator
(`jwString_anticomm_onSite_pos_spinHalfOpPlus{,Minus}`) together
with the JW string commutativity lemma
(`jwString_commute_jwString`). -/

/-- Fully general cross-site CAR for annihilation operators:
`c_i · c_j + c_j · c_i = 0` for every `i j : Fin (N + 1)` with
`i.val < j.val`.

Proof: write `c_i = JW_i · σ^+_i`, `c_j = JW_j · σ^+_j`. Using
commutativity of `σ^+_i` with `JW_i` (`jwString_commute_onSite`)
and the anticommutator `{σ^+_i, JW_j} = 0` (for `i < j`),

  `c_i c_j = JW_i · σ^+_i · JW_j · σ^+_j = -JW_i · JW_j · σ^+_i · σ^+_j`,
  `c_j c_i = JW_j · σ^+_j · JW_i · σ^+_i =  JW_j · JW_i · σ^+_i · σ^+_j`,

and the two `JW_i · JW_j`, `JW_j · JW_i` agree by
`jwString_commute_jwString`, so the sum collapses. -/
theorem fermionMultiAnnihilation_anticomm_lt
    (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiAnnihilation N i * fermionMultiAnnihilation N j +
      fermionMultiAnnihilation N j * fermionMultiAnnihilation N i = 0 := by
  have h_ne : i ≠ j := by
    intro h
    exact absurd (congrArg Fin.val h) (by omega)
  have h_anticomm : onSite i spinHalfOpPlus * jwString N j +
      jwString N j * onSite i spinHalfOpPlus = 0 :=
    jwString_anticomm_onSite_pos_spinHalfOpPlus N i j hij
  have hcomm_JWi_JWj : Commute (jwString N i) (jwString N j) :=
    jwString_commute_jwString N i j
  have hcomm_plus_i_JWi : Commute (onSite i spinHalfOpPlus) (jwString N i) :=
    (jwString_commute_onSite N i spinHalfOpPlus).symm
  have hcomm_plus_j_JWi :
      Commute (onSite j spinHalfOpPlus) (jwString N i) := by
    unfold jwString
    apply Finset.noncommProd_commute
    intro k hk
    rw [Finset.mem_filter] at hk
    have hkj : k ≠ j := by
      intro h; rw [h] at hk; exact absurd hk.2 (lt_asymm hij)
    exact onSite_mul_onSite_of_ne hkj.symm spinHalfOpPlus pauliZ
  have hcomm_plus_i_plus_j : onSite i spinHalfOpPlus * onSite j spinHalfOpPlus
      = onSite j spinHalfOpPlus * onSite i spinHalfOpPlus :=
    onSite_mul_onSite_of_ne h_ne _ _
  unfold fermionMultiAnnihilation
  set A := onSite i spinHalfOpPlus
  set B := onSite j spinHalfOpPlus
  set JWi := jwString N i
  set JWj := jwString N j
  -- Goal: (JWi * A) * (JWj * B) + (JWj * B) * (JWi * A) = 0
  have hAJ : A * JWj = -(JWj * A) := by
    have := h_anticomm
    rw [add_eq_zero_iff_eq_neg] at this
    exact this
  have hBJ : B * JWi = JWi * B := hcomm_plus_j_JWi.eq
  have hAB : A * B = B * A := hcomm_plus_i_plus_j
  have hJJ : JWi * JWj = JWj * JWi := hcomm_JWi_JWj.eq
  have step_ci_cj : (JWi * A) * (JWj * B) =
      -(JWi * JWj * A * B) := by
    rw [show (JWi * A) * (JWj * B) = JWi * (A * JWj) * B by noncomm_ring]
    rw [hAJ]
    noncomm_ring
  have step_cj_ci : (JWj * B) * (JWi * A) =
      JWj * JWi * A * B := by
    rw [show (JWj * B) * (JWi * A) = JWj * (B * JWi) * A by noncomm_ring]
    rw [hBJ]
    rw [show JWj * (JWi * B) * A = JWj * JWi * (B * A) by noncomm_ring]
    rw [← hAB]
    noncomm_ring
  rw [step_ci_cj, step_cj_ci, hJJ]
  abel

/-- Companion: for every `i j` with `i.val < j.val`,

  `c_i† · c_j† + c_j† · c_i† = 0`.

Derived via matrix `conjTranspose` from
`fermionMultiAnnihilation_anticomm_lt`. -/
theorem fermionMultiCreation_anticomm_lt
    (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiCreation N i * fermionMultiCreation N j +
      fermionMultiCreation N j * fermionMultiCreation N i = 0 := by
  have h := fermionMultiAnnihilation_anticomm_lt N i j hij
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  -- h2 : c_j† c_i† + c_i† c_j† = 0; goal: c_i† c_j† + c_j† c_i† = 0
  exact (add_comm _ _).trans h2

/-- Mixed `{c_i, c_j†} = 0` for every `i j : Fin (N + 1)` with
`i.val < j.val`. Same proof structure as
`fermionMultiAnnihilation_anticomm_lt`: `σ^-_j` at site `j` is
replaced by `σ^-_j` (still commutes with `σ^+_i` since `i ≠ j`).
-/
theorem fermionMultiAnnihilation_creation_anticomm_lt
    (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiAnnihilation N i * fermionMultiCreation N j +
      fermionMultiCreation N j * fermionMultiAnnihilation N i = 0 := by
  have h_ne : i ≠ j := by
    intro h
    exact absurd (congrArg Fin.val h) (by omega)
  have h_anticomm : onSite i spinHalfOpPlus * jwString N j +
      jwString N j * onSite i spinHalfOpPlus = 0 :=
    jwString_anticomm_onSite_pos_spinHalfOpPlus N i j hij
  have hcomm_JWi_JWj : Commute (jwString N i) (jwString N j) :=
    jwString_commute_jwString N i j
  have hcomm_minus_j_JWi :
      Commute (onSite j spinHalfOpMinus) (jwString N i) := by
    unfold jwString
    apply Finset.noncommProd_commute
    intro k hk
    rw [Finset.mem_filter] at hk
    have hkj : k ≠ j := by
      intro h; rw [h] at hk; exact absurd hk.2 (lt_asymm hij)
    exact onSite_mul_onSite_of_ne hkj.symm spinHalfOpMinus pauliZ
  have hcomm_plus_i_minus_j :
      onSite i spinHalfOpPlus * onSite j spinHalfOpMinus
      = onSite j spinHalfOpMinus * onSite i spinHalfOpPlus :=
    onSite_mul_onSite_of_ne h_ne _ _
  unfold fermionMultiAnnihilation fermionMultiCreation
  set A := onSite i spinHalfOpPlus
  set B := onSite j spinHalfOpMinus
  set JWi := jwString N i
  set JWj := jwString N j
  have hAJ : A * JWj = -(JWj * A) := by
    have := h_anticomm
    rw [add_eq_zero_iff_eq_neg] at this
    exact this
  have hBJ : B * JWi = JWi * B := hcomm_minus_j_JWi.eq
  have hAB : A * B = B * A := hcomm_plus_i_minus_j
  have hJJ : JWi * JWj = JWj * JWi := hcomm_JWi_JWj.eq
  have step_ci_cjd : (JWi * A) * (JWj * B) = -(JWi * JWj * A * B) := by
    rw [show (JWi * A) * (JWj * B) = JWi * (A * JWj) * B by noncomm_ring]
    rw [hAJ]
    noncomm_ring
  have step_cjd_ci : (JWj * B) * (JWi * A) = JWj * JWi * A * B := by
    rw [show (JWj * B) * (JWi * A) = JWj * (B * JWi) * A by noncomm_ring]
    rw [hBJ]
    rw [show JWj * (JWi * B) * A = JWj * JWi * (B * A) by noncomm_ring]
    rw [← hAB]
    noncomm_ring
  rw [step_ci_cjd, step_cjd_ci, hJJ]
  abel

/-- Mixed dual `{c_i†, c_j} = 0` for every `i j : Fin (N + 1)` with
`i.val < j.val`. Derived via matrix `conjTranspose` from
`fermionMultiAnnihilation_creation_anticomm_lt`. -/
theorem fermionMultiCreation_annihilation_anticomm_lt
    (N : ℕ) (i j : Fin (N + 1)) (hij : i.val < j.val) :
    fermionMultiCreation N i * fermionMultiAnnihilation N j +
      fermionMultiAnnihilation N j * fermionMultiCreation N i = 0 := by
  have h := fermionMultiAnnihilation_creation_anticomm_lt N i j hij
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionMultiAnnihilation_conjTranspose,
    fermionMultiCreation_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  exact (add_comm _ _).trans h2


end LatticeSystem.Fermion
