import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# Jordan–Wigner string factorisation and commutativity (foundation)

Foundational layer extracted from `StringFactorization.lean` for build speed (#210).
This file develops the Jordan–Wigner string factorisation at an interior site
(`jwStringExceptAt` and the factorisation `jwString = onSite · jwStringExceptAt`, with the
commutation of `jwStringExceptAt` with on-site operators) and the JW string commutativity
(`jwString_commute_jwString`: any two strings commute).

The general cross-site CAR at site zero (`{c_0, c_k} = 0`, `k ≥ 1`) and its consequences
are kept in the capstone module `StringFactorization.lean`.

Reference: Jordan–Wigner transformation; cross-site CAR thread (Issue #210).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

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

end LatticeSystem.Fermion
