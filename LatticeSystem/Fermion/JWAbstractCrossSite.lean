import LatticeSystem.Fermion.JWAbstract

/-!
# Abstract Jordan–Wigner cross-site CAR relations

This module ports the four cross-site canonical anticommutation
relations (CAR) from the `Fin (N + 1)`-indexed "multi" operators
(`LatticeSystem.Fermion.JordanWigner.CAR.CrossSite` and
`…CAR.CrossSiteOfNe`) to the abstract operators
`fermionAnnihilationAbstract` / `fermionCreationAbstract` defined
in `JWAbstract.lean` for an arbitrary finite linearly-ordered
index type `Λ`.

For every `i j : Λ` with `i ≠ j` we prove the four anticommutators

- `{c_i, c_j} = 0`   (`fermionAnnihilationAbstract_anticomm_of_ne`)
- `{c_i†, c_j†} = 0` (`fermionCreationAbstract_anticomm_of_ne`)
- `{c_i, c_j†} = 0`  (`fermionAnnihilationAbstract_creation_anticomm_of_ne`)
- `{c_i†, c_j} = 0`  (`fermionCreationAbstract_annihilation_anticomm_of_ne`)

The `_lt` forms require `i < j` in the linear order; the `_of_ne`
forms follow by `lt_trichotomy` + `add_comm`, exactly mirroring
`CrossSiteOfNe.lean`.

These complete the cross-site CAR infrastructure for the abstract
operators, as a foundation for Tasaki Lemma 9.1 (Slater-determinant
overlap), tracked in #4593.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [LinearOrder Λ]

/-! ## JW string factorisation at an interior site

For any `i j : Λ` with `i < j`, the abstract Jordan-Wigner string
at `j` contains a `σ^z_i` factor. Extracting it leaves a product of
`σ^z_k` over `k < j` with `k ≠ i`, which commutes with any
single-site operator at `i`. This is the building block for the
abstract cross-site CAR. -/

/-- The "site-`i` excluded" abstract Jordan-Wigner string at `j`:
the non-commutative product of `σ^z_k` over all `k` with `k < j`
*and* `k ≠ i`. Together with
`jwStringAbstract_eq_onSite_mul_jwStringExceptAtAbstract` this gives
the factorisation `jwStringAbstract j = σ^z_i · jwStringExceptAtAbstract j i`
whenever `i < j`. -/
private noncomputable def jwStringExceptAtAbstract (j i : Λ) : ManyBodyOp Λ :=
  ((Finset.univ : Finset Λ).filter (fun k => k < j ∧ k ≠ i)).noncommProd
    (fun k => onSite k pauliZ)
    (fun _ _ _ _ hab => onSite_mul_onSite_of_ne hab pauliZ pauliZ)

/-- Factorisation of the abstract Jordan-Wigner string at site `j`
around an interior site `i` with `i < j`:
`jwStringAbstract j = σ^z_i · jwStringExceptAtAbstract j i`. -/
private lemma jwStringAbstract_eq_onSite_mul_jwStringExceptAtAbstract
    (i j : Λ) (hij : i < j) :
    jwStringAbstract j = onSite i pauliZ * jwStringExceptAtAbstract j i := by
  unfold jwStringAbstract jwStringExceptAtAbstract
  have hfilter : (Finset.univ : Finset Λ).filter (fun k => k < j) =
      insert i ((Finset.univ : Finset Λ).filter (fun k => k < j ∧ k ≠ i)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_cases hki : k = i
      · left; exact hki
      · right; exact ⟨h, hki⟩
    · rintro (h0 | ⟨hlt, _⟩)
      · rw [h0]; exact hij
      · exact hlt
  have hi_notmem : i ∉ ((Finset.univ : Finset Λ).filter
      (fun k => k < j ∧ k ≠ i)) := by simp
  rw [Finset.noncommProd_congr hfilter (fun _ _ => rfl)]
  exact Finset.noncommProd_insert_of_notMem _ _ _ _ hi_notmem

/-- The site-`i`-excluded abstract JW string commutes with any
single-site operator at site `i`: every factor lives at a site
`k ≠ i`, so `onSite_mul_onSite_of_ne` applies factor-wise. -/
private lemma jwStringExceptAtAbstract_commute_onSite
    (j i : Λ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Commute (jwStringExceptAtAbstract j i) (onSite i A) := by
  unfold jwStringExceptAtAbstract
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro k hk
  rw [Finset.mem_filter] at hk
  exact onSite_mul_onSite_of_ne hk.2.2.symm A pauliZ

/-- Operator-level anticommutator at an interior site: for every
`i j : Λ` with `i < j`,

  `σ^+_i · jwStringAbstract j + jwStringAbstract j · σ^+_i = 0`.

Abstract analogue of `jwString_anticomm_onSite_pos_spinHalfOpPlus`. -/
theorem jwStringAbstract_anticomm_onSite_pos_spinHalfOpPlus
    (i j : Λ) (hij : i < j) :
    onSite i spinHalfOpPlus * jwStringAbstract j +
      jwStringAbstract j * onSite i spinHalfOpPlus = 0 := by
  rw [jwStringAbstract_eq_onSite_mul_jwStringExceptAtAbstract i j hij]
  set A := onSite i spinHalfOpPlus
  set Z := onSite i pauliZ
  set M := jwStringExceptAtAbstract j i
  have hcomm : A * M = M * A :=
    (jwStringExceptAtAbstract_commute_onSite j i spinHalfOpPlus).symm
  have h_ZA : Z * A = A := by
    rw [onSite_mul_onSite_same, pauliZ_mul_spinHalfOpPlus]
  have h_AZ_eq_neg_A : A * Z = -A := by
    rw [onSite_mul_onSite_same, spinHalfOpPlus_mul_pauliZ,
      show (-spinHalfOpPlus : Matrix (Fin 2) (Fin 2) ℂ) =
          0 - spinHalfOpPlus from (zero_sub _).symm,
      onSite_sub, onSite_zero, zero_sub]
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
operator: for every `i j : Λ` with `i < j`,

  `σ^-_i · jwStringAbstract j + jwStringAbstract j · σ^-_i = 0`.

Derived from the `σ^+_i` version by matrix `conjTranspose`, using
`jwStringAbstract_isHermitian` and `(σ^+)† = σ^-`. -/
theorem jwStringAbstract_anticomm_onSite_pos_spinHalfOpMinus
    (i j : Λ) (hij : i < j) :
    onSite i spinHalfOpMinus * jwStringAbstract j +
      jwStringAbstract j * onSite i spinHalfOpMinus = 0 := by
  have h := jwStringAbstract_anticomm_onSite_pos_spinHalfOpPlus i j hij
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_zero, (jwStringAbstract_isHermitian j).eq] at h2
  have hplus : (onSite i spinHalfOpPlus)ᴴ = onSite i spinHalfOpMinus := by
    rw [onSite_conjTransposeAbstract, spinHalfOpPlus_conjTranspose]
  rw [hplus] at h2
  exact (add_comm _ _).trans h2

/-- Two abstract Jordan-Wigner strings commute. Both are built as
`Finset.noncommProd` over subsets of `Λ` of `k ↦ onSite k pauliZ`;
every cross pair lies at distinct sites so `onSite_mul_onSite_of_ne`
applies term-wise. -/
theorem jwStringAbstract_commute_jwStringAbstract (i j : Λ) :
    Commute (jwStringAbstract i) (jwStringAbstract j) := by
  unfold jwStringAbstract
  apply Finset.noncommProd_commute
  intro a _
  apply Commute.symm
  apply Finset.noncommProd_commute
  intro b _
  by_cases hab : a = b
  · subst hab
    exact Commute.refl _
  · exact onSite_mul_onSite_of_ne hab pauliZ pauliZ

/-! ## Cross-site CAR for `i < j` -/

/-- Cross-site CAR for abstract annihilation operators:
`c_i · c_j + c_j · c_i = 0` for `i j : Λ` with `i < j`.

Abstract analogue of `fermionMultiAnnihilation_anticomm_lt`. -/
theorem fermionAnnihilationAbstract_anticomm_lt (i j : Λ) (hij : i < j) :
    fermionAnnihilationAbstract i * fermionAnnihilationAbstract j +
      fermionAnnihilationAbstract j * fermionAnnihilationAbstract i = 0 := by
  have h_ne : i ≠ j := ne_of_lt hij
  have h_anticomm : onSite i spinHalfOpPlus * jwStringAbstract j +
      jwStringAbstract j * onSite i spinHalfOpPlus = 0 :=
    jwStringAbstract_anticomm_onSite_pos_spinHalfOpPlus i j hij
  have hcomm_JWi_JWj : Commute (jwStringAbstract i) (jwStringAbstract j) :=
    jwStringAbstract_commute_jwStringAbstract i j
  have hcomm_plus_j_JWi :
      Commute (onSite j spinHalfOpPlus) (jwStringAbstract i) := by
    unfold jwStringAbstract
    apply Finset.noncommProd_commute
    intro k hk
    rw [Finset.mem_filter] at hk
    have hkj : k ≠ j := by
      intro h; rw [h] at hk; exact absurd hk.2 (lt_asymm hij)
    exact onSite_mul_onSite_of_ne hkj.symm spinHalfOpPlus pauliZ
  have hcomm_plus_i_plus_j :
      onSite i spinHalfOpPlus * onSite j spinHalfOpPlus
      = onSite j spinHalfOpPlus * onSite i spinHalfOpPlus :=
    onSite_mul_onSite_of_ne h_ne _ _
  unfold fermionAnnihilationAbstract
  set A := onSite i spinHalfOpPlus
  set B := onSite j spinHalfOpPlus
  set JWi := jwStringAbstract i
  set JWj := jwStringAbstract j
  have hAJ : A * JWj = -(JWj * A) := by
    rw [add_eq_zero_iff_eq_neg] at h_anticomm; exact h_anticomm
  have hBJ : B * JWi = JWi * B := hcomm_plus_j_JWi.eq
  have hAB : A * B = B * A := hcomm_plus_i_plus_j
  have hJJ : JWi * JWj = JWj * JWi := hcomm_JWi_JWj.eq
  have step_ci_cj : (JWi * A) * (JWj * B) = -(JWi * JWj * A * B) := by
    rw [show (JWi * A) * (JWj * B) = JWi * (A * JWj) * B by noncomm_ring]
    rw [hAJ]
    noncomm_ring
  have step_cj_ci : (JWj * B) * (JWi * A) = JWj * JWi * A * B := by
    rw [show (JWj * B) * (JWi * A) = JWj * (B * JWi) * A by noncomm_ring]
    rw [hBJ]
    rw [show JWj * (JWi * B) * A = JWj * JWi * (B * A) by noncomm_ring]
    rw [← hAB]
    noncomm_ring
  rw [step_ci_cj, step_cj_ci, hJJ]
  abel

/-- Cross-site CAR for abstract creation operators:
`c_i† · c_j† + c_j† · c_i† = 0` for `i j : Λ` with `i < j`.

Derived via matrix `conjTranspose` from
`fermionAnnihilationAbstract_anticomm_lt`. -/
theorem fermionCreationAbstract_anticomm_lt (i j : Λ) (hij : i < j) :
    fermionCreationAbstract i * fermionCreationAbstract j +
      fermionCreationAbstract j * fermionCreationAbstract i = 0 := by
  have h := fermionAnnihilationAbstract_anticomm_lt i j hij
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionAnnihilationAbstract_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  exact (add_comm _ _).trans h2

/-- Mixed `{c_i, c_j†} = 0` for `i j : Λ` with `i < j`. Same
structure as `fermionAnnihilationAbstract_anticomm_lt` with `σ^+_j`
replaced by `σ^-_j` (still commutes with `σ^+_i` since `i ≠ j`). -/
theorem fermionAnnihilationAbstract_creation_anticomm_lt
    (i j : Λ) (hij : i < j) :
    fermionAnnihilationAbstract i * fermionCreationAbstract j +
      fermionCreationAbstract j * fermionAnnihilationAbstract i = 0 := by
  have h_ne : i ≠ j := ne_of_lt hij
  have h_anticomm : onSite i spinHalfOpPlus * jwStringAbstract j +
      jwStringAbstract j * onSite i spinHalfOpPlus = 0 :=
    jwStringAbstract_anticomm_onSite_pos_spinHalfOpPlus i j hij
  have hcomm_JWi_JWj : Commute (jwStringAbstract i) (jwStringAbstract j) :=
    jwStringAbstract_commute_jwStringAbstract i j
  have hcomm_minus_j_JWi :
      Commute (onSite j spinHalfOpMinus) (jwStringAbstract i) := by
    unfold jwStringAbstract
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
  unfold fermionAnnihilationAbstract fermionCreationAbstract
  set A := onSite i spinHalfOpPlus
  set B := onSite j spinHalfOpMinus
  set JWi := jwStringAbstract i
  set JWj := jwStringAbstract j
  have hAJ : A * JWj = -(JWj * A) := by
    rw [add_eq_zero_iff_eq_neg] at h_anticomm; exact h_anticomm
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

/-- Mixed dual `{c_i†, c_j} = 0` for `i j : Λ` with `i < j`.
Derived via matrix `conjTranspose` from
`fermionAnnihilationAbstract_creation_anticomm_lt`. -/
theorem fermionCreationAbstract_annihilation_anticomm_lt
    (i j : Λ) (hij : i < j) :
    fermionCreationAbstract i * fermionAnnihilationAbstract j +
      fermionAnnihilationAbstract j * fermionCreationAbstract i = 0 := by
  have h := fermionAnnihilationAbstract_creation_anticomm_lt i j hij
  have h2 := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    fermionAnnihilationAbstract_conjTranspose,
    fermionCreationAbstract_conjTranspose,
    Matrix.conjTranspose_zero] at h2
  exact (add_comm _ _).trans h2

/-! ## Symmetric `_of_ne` cross-site CAR identities -/

/-- `{c_i, c_j} = 0` for any `i ≠ j` (symmetric form of
`fermionAnnihilationAbstract_anticomm_lt`). -/
theorem fermionAnnihilationAbstract_anticomm_of_ne {i j : Λ} (hij : i ≠ j) :
    fermionAnnihilationAbstract i * fermionAnnihilationAbstract j +
      fermionAnnihilationAbstract j * fermionAnnihilationAbstract i = 0 := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact fermionAnnihilationAbstract_anticomm_lt i j hlt
  · exact absurd heq hij
  · have h := fermionAnnihilationAbstract_anticomm_lt j i hgt
    exact (add_comm _ _).trans h

/-- `{c_i†, c_j†} = 0` for any `i ≠ j`. -/
theorem fermionCreationAbstract_anticomm_of_ne {i j : Λ} (hij : i ≠ j) :
    fermionCreationAbstract i * fermionCreationAbstract j +
      fermionCreationAbstract j * fermionCreationAbstract i = 0 := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact fermionCreationAbstract_anticomm_lt i j hlt
  · exact absurd heq hij
  · have h := fermionCreationAbstract_anticomm_lt j i hgt
    exact (add_comm _ _).trans h

/-- `{c_i, c_j†} = 0` for any `i ≠ j`. -/
theorem fermionAnnihilationAbstract_creation_anticomm_of_ne
    {i j : Λ} (hij : i ≠ j) :
    fermionAnnihilationAbstract i * fermionCreationAbstract j +
      fermionCreationAbstract j * fermionAnnihilationAbstract i = 0 := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact fermionAnnihilationAbstract_creation_anticomm_lt i j hlt
  · exact absurd heq hij
  · have h := fermionCreationAbstract_annihilation_anticomm_lt j i hgt
    exact (add_comm _ _).trans h

/-- `{c_i†, c_j} = 0` for any `i ≠ j`. -/
theorem fermionCreationAbstract_annihilation_anticomm_of_ne
    {i j : Λ} (hij : i ≠ j) :
    fermionCreationAbstract i * fermionAnnihilationAbstract j +
      fermionAnnihilationAbstract j * fermionCreationAbstract i = 0 := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact fermionCreationAbstract_annihilation_anticomm_lt i j hlt
  · exact absurd heq hij
  · have h := fermionAnnihilationAbstract_creation_anticomm_lt j i hgt
    exact (add_comm _ _).trans h

end LatticeSystem.Fermion
