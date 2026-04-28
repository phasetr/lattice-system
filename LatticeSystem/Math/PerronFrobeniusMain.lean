/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Math.PerronFrobeniusPrimitive
import LatticeSystem.Math.CollatzWielandt
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs

/-!
# Perron-Frobenius: positive eigenvector via Collatz-Wielandt

Proves existence of a strictly positive eigenvector for primitive and irreducible
nonneg matrices using the Collatz-Wielandt maximizer argument.

## Main results

- `pos_of_nonneg_eigenvec`: nonneg eigenvector of irreducible matrix with `v ≠ 0` is positive
- `exists_positive_eigenvector_of_primitive`: primitive nonneg ⟹ positive eigenvector
- `exists_positive_eigenvector_of_irreducible`: irreducible nonneg ⟹ positive eigenvector

## Proof sketch (primitive case)

1. `exists_maximizer` gives `v ∈ stdSimplex` with `CW(v)` maximal; set `r₀ = CW(v)`.
2. `le_mulVec` gives `r₀ • v ≤ A *ᵥ v`; set `z = A *ᵥ v - r₀ • v ≥ 0`.
3. Suppose `z ≠ 0`. Primitivity gives `k` with `A^k > 0`. `A^k z > 0` ⟹ all ratios
   `(A^(k+1) v)_i / (A^k v)_i > r₀`. Normalising `A^k v` gives `CW > r₀` — contradiction.
4. Hence `A *ᵥ v = r₀ • v`. Then `v > 0` from irreducibility, `r₀ > 0` from `A^k v > 0`.

## References

- Seneta, *Non-negative Matrices and Markov Chains*, §1.2 (pp. 27–28).
- or4nge19/MCMC: `Primitive.lean`, `Irreducible.lean`.
-/

namespace LatticeSystem.Math.PerronFrobeniusMain

set_option linter.unusedDecidableInType false

open Matrix Finset LatticeSystem.Math.CollatzWielandt

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Positivity propagation -/

omit [Nonempty n] [DecidableEq n] in
/-- If `A` is irreducible nonneg, `Av = μ • v`, `v ≥ 0`, `v ≠ 0`, then `v > 0`.

Proof: `v_i = 0` forces all `v_j = 0` via the row equations and irreducibility. -/
theorem pos_of_nonneg_eigenvec [DecidableEq n]
    {A : Matrix n n ℝ} (hIrred : A.IsIrreducible)
    {μ : ℝ} {v : n → ℝ}
    (hAv : A *ᵥ v = μ • v) (hv_nonneg : ∀ i, 0 ≤ v i) (hv_ne : v ≠ 0) :
    ∀ i, 0 < v i := by
  intro i
  by_contra hi
  simp only [not_lt] at hi
  have hi0 : v i = 0 := le_antisymm hi (hv_nonneg i)
  have hApow : ∀ m, A ^ m *ᵥ v = μ ^ m • v := by
    intro m; induction m with
    | zero => simp
    | succ p ih =>
      calc A ^ (p + 1) *ᵥ v
          = A ^ p *ᵥ (A *ᵥ v) := by rw [pow_succ, ← mulVec_mulVec]
        _ = A ^ p *ᵥ (μ • v) := by rw [hAv]
        _ = μ • (A ^ p *ᵥ v) := by rw [mulVec_smul]
        _ = μ • μ ^ p • v := by rw [ih]
        _ = μ ^ (p + 1) • v := by rw [smul_smul]; congr 1; ring
  have hAll : ∀ j, v j = 0 := by
    intro j
    obtain ⟨k, _, hAk_pos⟩ :=
      (Matrix.isIrreducible_iff_exists_pow_pos hIrred.nonneg).mp hIrred i j
    have hsum0 : ∑ l : n, (A ^ k) i l * v l = 0 := by
      have hrow : (A ^ k *ᵥ v) i = ∑ l : n, (A ^ k) i l * v l := by
        simp [mulVec, dotProduct]
      have h := congr_fun (hApow k) i
      simp only [Pi.smul_apply, smul_eq_mul] at h
      rw [hi0, mul_zero] at h; linarith [hrow.symm ▸ h]
    have hAk_nn : ∀ l, 0 ≤ (A ^ k) i l :=
      fun l => Matrix.pow_apply_nonneg hIrred.nonneg k i l
    have hTermJ : (A ^ k) i j * v j = 0 :=
      le_antisymm
        (by have := single_le_sum (fun l _ => mul_nonneg (hAk_nn l) (hv_nonneg l)) (mem_univ j)
            linarith [hsum0])
        (mul_nonneg (hAk_nn j) (hv_nonneg j))
    rcases mul_eq_zero.mp hTermJ with h | h
    · linarith [hAk_pos]
    · exact h
  exact hv_ne (funext hAll)

/-! ## Maximizer is an eigenvector (primitive case) -/

/-- For a primitive nonneg matrix, the CW maximizer `v ∈ stdSimplex` satisfies
`A *ᵥ v = CW(v) • v`.

Proof by contradiction: if `z := A *ᵥ v - r₀ • v ≠ 0` (it is ≥ 0 by `le_mulVec`),
then `A^k z > 0`, so all ratios `(A^(k+1) v)_i / (A^k v)_i > r₀`, giving a normalised
simplex point with `CW > r₀` — contradicting maximality. -/
private theorem maximizer_is_eigenvector
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (hPrim : A.IsPrimitive)
    {v : n → ℝ} (hv_mem : v ∈ stdSimplex ℝ n)
    (hv_max : ∀ y ∈ stdSimplex ℝ n, collatzWielandtFn A y ≤ collatzWielandtFn A v) :
    A *ᵥ v = collatzWielandtFn A v • v := by
  set r₀ := collatzWielandtFn A v
  -- z = A *ᵥ v - r₀ • v ≥ 0 (by le_mulVec)
  have hz_nonneg : ∀ i, 0 ≤ (A *ᵥ v - r₀ • v) i := fun i => by
    have := (le_mulVec hA hv_mem.1) i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
  -- It suffices to show A *ᵥ v - r₀ • v = 0
  suffices h : A *ᵥ v - r₀ • v = 0 by
    have heq := funext_iff.mp h
    ext i; simp only [Pi.smul_apply, smul_eq_mul]
    have := heq i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this; linarith
  by_contra hz_ne
  obtain ⟨k, hk_pos, hk_all⟩ := hPrim.exists_pos_pow
  have hv_nonneg : ∀ i, 0 ≤ v i := hv_mem.1
  have hv_ne : v ≠ 0 := ne_zero_of_mem_stdSimplex hv_mem
  -- z has a positive entry (z ≥ 0, z ≠ 0)
  obtain ⟨j_z, hj_z⟩ : ∃ j, 0 < (A *ᵥ v - r₀ • v) j := by
    by_contra h; push Not at h
    exact hz_ne (funext fun i => le_antisymm (h i) (hz_nonneg i))
  -- v has a positive entry (v ≥ 0, v ≠ 0)
  obtain ⟨j_v, hj_v⟩ : ∃ j, 0 < v j := by
    by_contra h; push Not at h
    exact hv_ne (funext fun j => le_antisymm (h j) (hv_nonneg j))
  -- A^k *ᵥ (A *ᵥ v - r₀ • v) > 0 componentwise
  have hAkz_pos : ∀ i, 0 < (A ^ k *ᵥ (A *ᵥ v - r₀ • v)) i := fun i => by
    simp only [mulVec, dotProduct]
    exact sum_pos' (fun j _ => mul_nonneg (le_of_lt (hk_all i j)) (hz_nonneg j))
      ⟨j_z, mem_univ _, mul_pos (hk_all i j_z) hj_z⟩
  -- A^k *ᵥ v > 0 componentwise
  have hAkv_pos : ∀ i, 0 < (A ^ k *ᵥ v) i := fun i => by
    simp only [mulVec, dotProduct]
    exact sum_pos' (fun j _ => mul_nonneg (le_of_lt (hk_all i j)) (hv_nonneg j))
      ⟨j_v, mem_univ _, mul_pos (hk_all i j_v) hj_v⟩
  -- A^(k+1) v = r₀ • A^k v + A^k z
  have hdecomp : A ^ (k + 1) *ᵥ v =
      r₀ • (A ^ k *ᵥ v) + A ^ k *ᵥ (A *ᵥ v - r₀ • v) := by
    have h1 : A ^ (k + 1) *ᵥ v = A ^ k *ᵥ (A *ᵥ v) := by
      rw [pow_succ, ← mulVec_mulVec]
    have h2 : A ^ k *ᵥ (A *ᵥ v - r₀ • v) =
        A ^ k *ᵥ (A *ᵥ v) - A ^ k *ᵥ (r₀ • v) := mulVec_sub _ _ _
    have h3 : A ^ k *ᵥ (r₀ • v) = r₀ • (A ^ k *ᵥ v) := mulVec_smul _ _ _
    rw [h1, h2, h3]; abel
  -- All ratios of A^(k+1) v over A^k v exceed r₀
  have hall_ratios : ∀ i, r₀ < (A ^ (k + 1) *ᵥ v) i / (A ^ k *ᵥ v) i := fun i => by
    rw [lt_div_iff₀ (hAkv_pos i), hdecomp]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hAkz_pos i]
  -- CW(A^k v) > r₀ by lt_of_all_ratios_gt
  have hCW_Akv : r₀ < collatzWielandtFn A (A ^ k *ᵥ v) :=
    lt_of_all_ratios_gt hAkv_pos fun i => by
      have : A *ᵥ (A ^ k *ᵥ v) = A ^ (k + 1) *ᵥ v := by rw [pow_succ', ← mulVec_mulVec]
      rw [this]; exact hall_ratios i
  -- Normalise A^k v → w ∈ stdSimplex; CW(w) = CW(A^k v) > r₀
  have hAkv_sum_pos : 0 < ∑ i : n, (A ^ k *ᵥ v) i :=
    sum_pos (fun i _ => hAkv_pos i) ⟨Classical.arbitrary n, mem_univ _⟩
  set s := ∑ i : n, (A ^ k *ᵥ v) i
  set w : n → ℝ := fun i => (A ^ k *ᵥ v) i / s
  have hw_mem : w ∈ stdSimplex ℝ n := by
    constructor
    · exact fun i => div_nonneg (le_of_lt (hAkv_pos i)) (le_of_lt hAkv_sum_pos)
    · simp only [w, div_eq_mul_inv, ← Finset.sum_mul]
      exact mul_inv_cancel₀ (ne_of_gt hAkv_sum_pos)
  have hCW_w_gt : r₀ < collatzWielandtFn A w := by
    have hw_eq : w = (1 / s) • (A ^ k *ᵥ v) := by
      ext i; simp only [w, Pi.smul_apply, smul_eq_mul]; ring
    rw [hw_eq, smul_eq (by positivity) (fun i => le_of_lt (hAkv_pos i)) (fun h => by
      have := congr_fun h (Classical.arbitrary n)
      simp only [Pi.zero_apply] at this; linarith [hAkv_pos (Classical.arbitrary n)])]
    exact hCW_Akv
  linarith [hv_max w hw_mem]

/-! ## Main theorems -/

/-- For a primitive nonneg matrix, there exist `r > 0` and `v > 0` with `A *ᵥ v = r • v`.

Ref: Seneta §1.2 (pp. 27–28); MCMC `Primitive.lean`. -/
theorem exists_positive_eigenvector_of_primitive
    {A : Matrix n n ℝ} (hA : ∀ i j, 0 ≤ A i j) (hPrim : A.IsPrimitive) :
    ∃ (r : ℝ) (v : n → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  obtain ⟨v, hv_mem, hv_max⟩ := exists_maximizer A
  set r₀ := collatzWielandtFn A v
  have h_eig : A *ᵥ v = r₀ • v := maximizer_is_eigenvector hA hPrim hv_mem hv_max
  have hv_pos : ∀ i, 0 < v i :=
    pos_of_nonneg_eigenvec hPrim.isIrreducible h_eig hv_mem.1 (ne_zero_of_mem_stdSimplex hv_mem)
  obtain ⟨k, hk_pos, hk_all⟩ := hPrim.exists_pos_pow
  -- A^m *ᵥ v = r₀^m • v by induction
  have hApow : ∀ m, A ^ m *ᵥ v = r₀ ^ m • v := by
    intro m; induction m with
    | zero => simp
    | succ p ih =>
      calc A ^ (p + 1) *ᵥ v
          = A ^ p *ᵥ (A *ᵥ v) := by rw [pow_succ, ← mulVec_mulVec]
        _ = A ^ p *ᵥ (r₀ • v) := by rw [h_eig]
        _ = r₀ • (A ^ p *ᵥ v) := by rw [mulVec_smul]
        _ = r₀ • r₀ ^ p • v := by rw [ih]
        _ = r₀ ^ (p + 1) • v := by rw [smul_smul]; congr 1; ring
  -- (A^k v)_i₀ > 0
  have hAkv_pos : 0 < (A ^ k *ᵥ v) (Classical.arbitrary n) := by
    simp only [mulVec, dotProduct]
    exact sum_pos (fun j _ => mul_pos (hk_all (Classical.arbitrary n) j) (hv_pos j))
      ⟨Classical.arbitrary n, mem_univ _⟩
  -- r₀^k > 0 (from r₀^k * v_i₀ = (A^k v)_i₀ > 0 and v_i₀ > 0)
  have hrk_pos : 0 < r₀ ^ k := by
    rw [hApow k] at hAkv_pos
    simp only [Pi.smul_apply, smul_eq_mul] at hAkv_pos
    nlinarith [hv_pos (Classical.arbitrary n)]
  -- r₀ ≥ 0: from (A *ᵥ v)_i = r₀ * v_i ≥ 0
  have hr₀_nn : 0 ≤ r₀ := by
    have hAv_nn : 0 ≤ (A *ᵥ v) (Classical.arbitrary n) :=
      sum_nonneg fun j _ => mul_nonneg (hA _ j) (le_of_lt (hv_pos j))
    have heq : (A *ᵥ v) (Classical.arbitrary n) = r₀ * v (Classical.arbitrary n) := by
      have := congr_fun h_eig (Classical.arbitrary n)
      simp only [Pi.smul_apply, smul_eq_mul] at this; exact this
    rw [heq] at hAv_nn; nlinarith [hv_pos (Classical.arbitrary n)]
  -- r₀ > 0: r₀ = 0 would give r₀^k = 0
  have hr₀_pos : 0 < r₀ := by
    rcases hr₀_nn.eq_or_lt with h | h
    · simp [show r₀ = 0 from h.symm, zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)] at hrk_pos
    · exact h
  exact ⟨r₀, v, hr₀_pos, hv_pos, h_eig⟩

/-- For an irreducible nonneg matrix, there exist `r > 0` and `v > 0` with `A *ᵥ v = r • v`.

Proof: `B = I + A` is primitive (positive diagonal + irreducibility). Apply primitive theorem:
get `r_B`, `v > 0`, `B *ᵥ v = r_B • v`. Then `A *ᵥ v = (r_B - 1) • v`.
`r_B > 1`: `B ≥ I` forces `r_B ≥ 1`, and `r_B = 1` would give `A = 0`.

Ref: Seneta §1.2; MCMC `Irreducible.lean`. -/
theorem exists_positive_eigenvector_of_irreducible
    {A : Matrix n n ℝ} (hIrred : A.IsIrreducible) :
    ∃ (r : ℝ) (v : n → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ A *ᵥ v = r • v := by
  set B := 1 + A with hB_def
  -- B ≥ 0 with positive diagonal
  have hB_nonneg : ∀ i j, 0 ≤ B i j := fun i j => by
    change 0 ≤ (1 : Matrix n n ℝ) i j + A i j
    rw [one_apply]; split_ifs <;> linarith [hIrred.nonneg i j]
  have hB_diag : ∀ i, 0 < B i i := fun i => by
    change 0 < (1 : Matrix n n ℝ) i i + A i i
    rw [one_apply_eq]; linarith [hIrred.nonneg i i]
  -- B^k ≥ A^k componentwise (B ≥ A ≥ 0 by induction)
  have hBA_le : ∀ i j, A i j ≤ B i j := fun i j => by
    change A i j ≤ (1 : Matrix n n ℝ) i j + A i j
    rw [one_apply]; split_ifs <;> linarith [hIrred.nonneg i j]
  have hBpow_ge : ∀ m i j, (A ^ m) i j ≤ (B ^ m) i j := by
    intro m; induction m with
    | zero => intros; simp
    | succ p ih =>
      intro i j; rw [pow_succ, pow_succ, mul_apply, mul_apply]
      exact sum_le_sum fun l _ => mul_le_mul (ih i l) (hBA_le l j)
        (hIrred.nonneg l j) (Matrix.pow_apply_nonneg hB_nonneg p i l)
  -- B is irreducible (same paths as A, plus self-loops at i = j)
  have hB_irred : B.IsIrreducible := by
    rw [isIrreducible_iff_exists_pow_pos hB_nonneg]
    intro i j
    by_cases hij : i = j
    · refine ⟨1, one_pos, ?_⟩
      rw [pow_one]; rw [hij]; exact hB_diag j
    · obtain ⟨k, hk_pos, hAk_pos⟩ :=
        (isIrreducible_iff_exists_pow_pos hIrred.nonneg).mp hIrred i j
      exact ⟨k, hk_pos, lt_of_lt_of_le hAk_pos (hBpow_ge k i j)⟩
  -- B is primitive (irreducible + positive diagonal)
  have hB_prim : B.IsPrimitive :=
    Matrix.IsPrimitive.of_irreducible_pos_diagonal hB_nonneg hB_irred hB_diag
  -- Apply primitive theorem to B
  obtain ⟨r_B, v, hr_B_pos, hv_pos, hBv⟩ :=
    exists_positive_eigenvector_of_primitive hB_nonneg hB_prim
  -- v + A *ᵥ v = r_B • v
  have hBv_split : v + A *ᵥ v = r_B • v :=
    (show B *ᵥ v = v + A *ᵥ v by rw [hB_def, add_mulVec, one_mulVec]).symm.trans hBv
  -- A *ᵥ v = (r_B - 1) • v
  have hAv : A *ᵥ v = (r_B - 1) • v := by
    ext i; have := congr_fun hBv_split i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢; linarith
  -- r_B ≥ 1: (r_B - 1) * v_i = (A *ᵥ v)_i ≥ 0 and v_i > 0
  have hr_B_ge : 1 ≤ r_B := by
    have hAv_nn : 0 ≤ (A *ᵥ v) (Classical.arbitrary n) :=
      sum_nonneg fun j _ => mul_nonneg (hIrred.nonneg _ j) (le_of_lt (hv_pos j))
    have heq : (A *ᵥ v) (Classical.arbitrary n) = (r_B - 1) * v (Classical.arbitrary n) := by
      have := congr_fun hAv (Classical.arbitrary n)
      simp only [Pi.smul_apply, smul_eq_mul] at this; exact this
    rw [heq] at hAv_nn; nlinarith [hv_pos (Classical.arbitrary n)]
  -- r_B > 1: r_B = 1 ⟹ A *ᵥ v = 0 ⟹ A = 0 ⟹ not irreducible
  have hr_pos : 0 < r_B - 1 := by
    rcases hr_B_ge.eq_or_lt with h | h
    · exfalso
      have hAv0 : A *ᵥ v = 0 := by
        have hrB1 : r_B - 1 = 0 := by linarith
        rw [hAv, hrB1, zero_smul]
      have hA0 : A = 0 := by
        ext i j
        have hrow0 : ∑ l : n, A i l * v l = 0 := by
          have := congr_fun hAv0 i
          simp only [Pi.zero_apply, mulVec, dotProduct] at this; exact this
        have hnn : ∀ l, 0 ≤ A i l * v l :=
          fun l => mul_nonneg (hIrred.nonneg i l) (le_of_lt (hv_pos l))
        have hterm : A i j * v j = 0 :=
          le_antisymm
            (by have := single_le_sum (fun l _ => hnn l) (mem_univ j); linarith)
            (hnn j)
        exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt (hv_pos j))
      obtain ⟨k, hk_pos, hk⟩ :=
        (isIrreducible_iff_exists_pow_pos hIrred.nonneg).mp hIrred
          (Classical.arbitrary n) (Classical.arbitrary n)
      rw [hA0, zero_pow (Nat.pos_iff_ne_zero.mp hk_pos)] at hk
      simp at hk
    · linarith
  exact ⟨r_B - 1, v, hr_pos, hv_pos, hAv⟩

end LatticeSystem.Math.PerronFrobeniusMain
