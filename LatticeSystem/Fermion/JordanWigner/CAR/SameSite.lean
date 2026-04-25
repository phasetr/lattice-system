/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# CAR algebra — number operators, same-site relations, and small-N cross-site cases

Extracted from `JordanWigner/CAR.lean` (codex audit Item 10). This sub-file
contains the three lowest-level layers of the full CAR algebra:

1. **Number operators** — pairwise commutativity, total `N̂`, Hermiticity.
2. **Same-site CAR** — `{c_i, c_i†} = 1` (and the auxiliary `{σ^+, σ^-} = 1`).
3. **Small-N explicit cross-site cases** — `Fin 2`, `Fin (N+1)` at gaps 1 and 2
   (annihilation / creation / mixed variants), proved by direct Pauli computation
   without the general JW string factorisation machinery.

The general JW string factorisation and the fully general `i < j` CAR live in the
sibling sub-files `StringFactorization.lean` and `CrossSite.lean`.

(Codex audit Item 10, split of `JordanWigner/CAR.lean`, tracked in #390.)
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

end LatticeSystem.Fermion
