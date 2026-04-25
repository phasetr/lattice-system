/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.CAR.StringFactorization
import Mathlib.Tactic.NoncommRing

/-!
# CAR algebra — fully general cross-site relations for arbitrary `i < j`

Extracted from `JordanWigner/CAR.lean` (codex audit Item 10). This sub-file
contains the four fully general cross-site CAR relations for arbitrary pairs
`i j : Fin (N + 1)` with `i.val < j.val`:

- `{c_i, c_j} = 0` (`fermionMultiAnnihilation_anticomm_lt`)
- `{c_i†, c_j†} = 0` (`fermionMultiCreation_anticomm_lt`)
- `{c_i, c_j†} = 0` (`fermionMultiAnnihilation_creation_anticomm_lt`)
- `{c_i†, c_j} = 0` (`fermionMultiCreation_annihilation_anticomm_lt`)

The proofs use `jwString_anticomm_onSite_pos_spinHalfOpPlus{,Minus}` and
`jwString_commute_jwString` from the sibling `StringFactorization.lean`.

(Codex audit Item 10, split of `JordanWigner/CAR.lean`, tracked in #390.)
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

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
