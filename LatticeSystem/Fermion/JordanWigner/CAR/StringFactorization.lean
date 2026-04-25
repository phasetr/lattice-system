/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Fermion.JordanWigner.Operators

/-!
# CAR algebra — JW string factorisation, commutativity, and zero-site general CAR

Extracted from `JordanWigner/CAR.lean` (codex audit Item 10). This sub-file
contains the general JW string machinery needed to prove cross-site CAR for
arbitrary site pairs:

1. **JW string factorisation** — extracting an interior `σ^z_i` factor from
   `jwString N j` when `i.val < j.val`, via the private `jwStringExceptAt`
   helper.
2. **Anticommutation at interior sites** — `{σ^+_i, jwString N j} = 0` and
   `{σ^-_i, jwString N j} = 0` for `i.val < j.val`.
3. **JW string commutativity** — any two JW strings commute.
4. **Zero-indexed general cross-site CAR** — `{c_0, c_k} = 0` for all
   `k` with `0 < k.val`, and the three companion off-diagonal forms.

The fully general `i < j` cross-site CAR built on top of this lives in the
sibling sub-file `CrossSite.lean`.

(Codex audit Item 10, split of `JordanWigner/CAR.lean`, tracked in #390.)
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

end LatticeSystem.Fermion
