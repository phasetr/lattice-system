import LatticeSystem.Fermion.JordanWigner.Operators
import LatticeSystem.Fermion.JordanWigner.CAR.SameSiteCore

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
