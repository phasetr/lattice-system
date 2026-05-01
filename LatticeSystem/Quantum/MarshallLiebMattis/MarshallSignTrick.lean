import LatticeSystem.Quantum.MarshallLiebMattis.Realness

/-!
# The Marshall sign trick: non-positivity of off-diagonal dressed Heisenberg matrix elements
(Tasaki §2.5, p. 41, "Property (ii)" in the proof of Theorem 2.2)

This is the key step in Tasaki's Perron–Frobenius proof of the
Marshall–Lieb–Mattis theorem (Theorem 2.2, §2.5 p. 39).

**Statement.** For the spin-1/2 antiferromagnetic Heisenberg
Hamiltonian `H = Σ_{x,y} J(x,y) Ŝ_x · Ŝ_y` on a bipartite graph
`(Λ, A)` (sublattice indicator `A : Λ → Bool`, with bipartite
support `J(x,y) = 0` whenever `A x = A y`) and non-negative
real coupling `J ≥ 0`, the **dressed off-diagonal matrix elements**

  `Σ_τ |Ψ̃^σ⟩ τ · (H · |Ψ̃^σ'⟩) τ`

have non-positive **real part** for every `σ ≠ σ'` (Tasaki §2.5
p. 41, Property (ii)).

**Proof outline.**

1. The dressed pairing equals `marshallSignOf A σ · marshallSignOf A σ' · H σ σ'`
   (`dot_marshallDressed_marshallDressed_eq`, generalised from PR α-2).
2. The spin-1/2 Heisenberg matrix entry decomposes as
   `H σ σ' = Σ_{x,y} J(x,y) · (spinHalfDot x y) σ σ'`.
3. For each bond `(x, y)`, the contribution
   `S(σ) · S(σ') · J(x,y) · (spinHalfDot x y) σ σ'` to the dressed pairing
   has non-positive real part (this is the **Marshall sign trick**):
   - `(spinHalfDot x y) σ σ' = 0` unless `x ≠ y`, `σ' x ≠ σ' y` and
     `σ = basisSwap σ' x y`, in which case the value is `1/2`.
   - When non-zero, `σ` and `σ'` differ at exactly `{x, y}`.
   - For the bipartite case `A x ≠ A y`, exactly one of `x, y` lies in
     `A`, so the Marshall sign flips by exactly `(-1)`:
     `marshallSignOf A σ' = -marshallSignOf A σ`.
   - Combined with `J(x,y) ≥ 0` and the value `1/2`, the contribution
     is `-(1/2) · J(x,y) ≤ 0`.
   - For the same-sublattice case `A x = A y`, the bipartite support
     hypothesis `hJ_bipartite` forces `J(x,y) = 0`, so the
     contribution is `0`.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41 (Property (ii) in the proof of Theorem 2.2).
- W. Marshall (1955); E.H. Lieb, D. Mattis (1962).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Helper: matrix entry from `mulVec` -/

/-- `M.mulVec (basisVec σ') σ = M σ σ'`. The dotProduct collapses to
the unique non-zero summand at `τ = σ'`. -/
private theorem mulVec_basisVec_apply (M : ManyBodyOp Λ)
    (σ σ' : Λ → Fin 2) :
    M.mulVec (basisVec σ') σ = M σ σ' := by
  change dotProduct (fun j => M σ j) (basisVec σ') = M σ σ'
  unfold dotProduct
  rw [sum_mul_basisVec σ' (M σ)]

/-! ## Factorisation of the dressed bilinear pairing -/

/-- For any operator `M` and any pair of configurations `σ, σ'`,
the dressed bilinear pairing factorises:

  `Σ_τ |Ψ̃^σ⟩ τ · (M · |Ψ̃^σ'⟩) τ = marshallSignOf A σ · marshallSignOf A σ' · M σ σ'`.

This generalises the inner-product computation used in PR α-2 from
the Heisenberg Hamiltonian to arbitrary matrices. -/
theorem dot_marshallDressed_mulVec_marshallDressed_eq
    (A : Λ → Bool) (M : ManyBodyOp Λ) (σ σ' : Λ → Fin 2) :
    ∑ τ : Λ → Fin 2,
        marshallDressedBasis A σ τ *
          (M.mulVec (marshallDressedBasis A σ')) τ =
      marshallSignOf A σ * marshallSignOf A σ' * M σ σ' := by
  have hmul : M.mulVec (marshallDressedBasis A σ') =
      marshallSignOf A σ' • M.mulVec (basisVec σ') := by
    unfold marshallDressedBasis
    rw [Matrix.mulVec_smul]
  rw [hmul]
  rw [show ∑ τ : Λ → Fin 2,
        marshallDressedBasis A σ τ *
          (marshallSignOf A σ' • M.mulVec (basisVec σ')) τ =
      marshallSignOf A σ * marshallSignOf A σ' *
        ∑ τ : Λ → Fin 2,
          basisVec σ τ * (M.mulVec (basisVec σ')) τ from ?_]
  · rw [basisVec_sum_mul σ (M.mulVec (basisVec σ')),
        mulVec_basisVec_apply]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [marshallDressedBasis_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-! ## Marshall sign behaviour under `basisSwap` for bipartite antiparallel bonds -/

omit [Fintype Λ] [DecidableEq Λ] in
/-- A single `(-1) ^ (s : ℕ)` factor for `s : Fin 2` is `±1`,
in particular real, and squares to `1`. -/
private theorem neg_one_pow_fin2_sq (s : Fin 2) :
    ((-1 : ℂ) ^ (s : ℕ)) * ((-1 : ℂ) ^ (s : ℕ)) = 1 := by
  rcases s with ⟨k, hk⟩
  interval_cases k <;> norm_num

omit [Fintype Λ] [DecidableEq Λ] in
/-- For `s, t : Fin 2` with `s ≠ t`,
`(-1)^(s : ℕ) * (-1)^(t : ℕ) = -1`. -/
private theorem neg_one_pow_fin2_mul_of_ne {s t : Fin 2} (h : s ≠ t) :
    ((-1 : ℂ) ^ (s : ℕ)) * ((-1 : ℂ) ^ (t : ℕ)) = -1 := by
  fin_cases s <;> fin_cases t
  · exact absurd rfl h
  · norm_num
  · norm_num
  · exact absurd rfl h

omit [Fintype Λ] [DecidableEq Λ] in
/-- Auxiliary: for a configuration `σ : Λ → Fin 2` and a single
site `z`, the product `factor σ z · factor σ z = 1`,
where `factor σ z := if A z then (-1)^(σ z : ℕ) else 1`. -/
private theorem factor_sq_eq_one (A : Λ → Bool) (σ : Λ → Fin 2) (z : Λ) :
    (if A z then ((-1 : ℂ) ^ (σ z : ℕ)) else 1) *
        (if A z then ((-1 : ℂ) ^ (σ z : ℕ)) else 1) = 1 := by
  by_cases hA : A z = true
  · rw [if_pos hA]; exact neg_one_pow_fin2_sq (σ z)
  · rw [if_neg hA]; ring

/-- **Key Marshall sign relation.** When the bond `{x, y}` crosses
the bipartition (`A x ≠ A y`) and `σ` is antiparallel at `{x, y}`
(`σ x ≠ σ y`), the Marshall sign on `basisSwap σ x y` differs by
exactly `(-1)` from that on `σ`:

  `marshallSignOf A σ * marshallSignOf A (basisSwap σ x y) = -1`.

Proof: combine the two products factor-wise (`Finset.prod_mul_distrib`),
extract `x` and `y` via `Finset.mul_prod_erase`. Outside `{x, y}`,
each pairwise factor squares to `1`. At the unique site in
`A ∩ {x, y}`, the pair contributes `(-1)^(σ x + σ y) = -1` since
`σ x ≠ σ y` in `Fin 2`; the other site of `{x, y}` contributes `1`
because it lies outside `A`. -/
theorem marshallSignOf_mul_marshallSignOf_basisSwap_of_bipartite_antiparallel
    (A : Λ → Bool) {x y : Λ} (hxy : x ≠ y) (hA : A x ≠ A y)
    {σ : Λ → Fin 2} (h : σ x ≠ σ y) :
    marshallSignOf A σ * marshallSignOf A (basisSwap σ x y) = -1 := by
  -- basisSwap values at x, y, and elsewhere.
  have hbsx : basisSwap σ x y x = σ y := by
    unfold basisSwap; rw [Function.update_of_ne hxy, Function.update_self]
  have hbsy : basisSwap σ x y y = σ x := by
    unfold basisSwap; rw [Function.update_self]
  have hbselse : ∀ z, z ≠ x → z ≠ y → basisSwap σ x y z = σ z := by
    intro z hzx hzy
    unfold basisSwap
    rw [Function.update_of_ne hzy, Function.update_of_ne hzx]
  -- Combine the two marshallSignOf products.
  unfold marshallSignOf
  rw [← Finset.prod_mul_distrib]
  -- Extract x from Finset.univ.
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x)]
  -- Extract y from Finset.univ.erase x. Since y ≠ x, y ∈ univ.erase x.
  have hy_mem : y ∈ Finset.univ.erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
  rw [← Finset.mul_prod_erase _ _ hy_mem]
  -- Now: factor at x · (factor at y · ∏ z ∈ (univ.erase x).erase y, ...).
  -- The inner product is 1 (each pairwise factor is factor² = 1 since basisSwap = σ off {x, y}).
  rw [show
      (∏ z ∈ (Finset.univ.erase x).erase y,
          ((if A z then ((-1 : ℂ) ^ (σ z : ℕ)) else 1) *
           (if A z then ((-1 : ℂ) ^ ((basisSwap σ x y z : Fin 2) : ℕ)) else 1)))
        = 1 from ?_]
  · -- Now compute the outer factor at x times factor at y.
    rw [hbsx, hbsy, mul_one]
    -- Goal: (factor σ x · factor (swap) x) · (factor σ y · factor (swap) y) = -1
    -- After hbsx, hbsy substitution, the LHS becomes a product of four
    -- conditional `(-1)^σ_·` factors, depending on `A x` and `A y`.
    by_cases hAx : A x = true
    · have hAy : A y = false := by
        cases hb : A y with
        | true => exact absurd (hAx.trans hb.symm) hA
        | false => rfl
      rw [if_pos hAx, if_pos hAx, if_neg (by rw [hAy]; decide),
          if_neg (by rw [hAy]; decide)]
      rw [neg_one_pow_fin2_mul_of_ne h]
      ring
    · have hAxF : A x = false := by
        cases hb : A x with | true => exact absurd hb hAx | false => rfl
      have hAy : A y = true := by
        cases hb : A y with
        | true => rfl
        | false => exact absurd (hAxF.trans hb.symm) hA
      rw [if_neg (by rw [hAxF]; decide), if_neg (by rw [hAxF]; decide),
          if_pos hAy, if_pos hAy]
      rw [neg_one_pow_fin2_mul_of_ne h.symm]
      ring
  · -- ∏ z ∈ (univ.erase x).erase y, factor² σ z = 1.
    refine Finset.prod_eq_one fun z hz => ?_
    simp only [Finset.mem_erase, Finset.mem_univ] at hz
    obtain ⟨hzy, hzx, _⟩ := hz
    rw [hbselse z hzx hzy]
    exact factor_sq_eq_one A σ z

/-! ## Per-bond contribution -/

/-- **Per-bond Marshall sign trick.** For a fixed bond `(x, y)` and
configurations `σ ≠ σ'`, the contribution to the dressed off-diagonal
matrix element from `(x, y)`,

  `marshallSignOf A σ · marshallSignOf A σ' · J(x,y) · (spinHalfDot x y) σ σ'`,

has non-positive real part, given:
- `(J x y).im = 0` (real coupling),
- `0 ≤ (J x y).re` (non-negative coupling),
- `A x = A y → J x y = 0` (bipartite support).

Proof: case analysis on `(spinHalfDot x y) σ σ'`.

* If `x = y`, the matrix is `(3/4) • I`, so the entry is non-zero only
  for `σ = σ'`. Contradiction with `σ ≠ σ'`. Contribution `= 0`.
* If `x ≠ y` and `σ' x = σ' y` (parallel σ'), the action is
  `(1/4) • basisVec σ'` and the entry is `(1/4) [σ = σ']` — also `0`
  for `σ ≠ σ'`.
* If `x ≠ y` and `σ' x ≠ σ' y` (antiparallel σ'), the action is
  `(1/2) basisVec (basisSwap σ' x y) - (1/4) basisVec σ'`, and the
  entry is `(1/2) [σ = basisSwap σ' x y] - (1/4) [σ = σ']`.
  Since `σ ≠ σ'`, only the first term can survive. So either the
  contribution is `0` or `σ = basisSwap σ' x y` (and value `1/2`).
  - If furthermore `A x = A y`, then `J x y = 0` by hypothesis, so
    the contribution is `0`.
  - If `A x ≠ A y`, the Marshall sign relation gives
    `marshallSignOf A σ · marshallSignOf A σ' = -1`, so the
    contribution is `-(1/2) · (J x y).re ≤ 0`. -/
theorem bond_dressed_contribution_re_nonpos
    (A : Λ → Bool) (x y : Λ)
    {J : Λ → Λ → ℂ}
    (hJ_real : (J x y).im = 0)
    (hJ_nn : 0 ≤ (J x y).re)
    (hJ_bipartite : A x = A y → J x y = 0)
    {σ σ' : Λ → Fin 2} (hne : σ ≠ σ') :
    (marshallSignOf A σ * marshallSignOf A σ' *
        (J x y * (spinHalfDot x y) σ σ')).re ≤ 0 := by
  -- Replace (spinHalfDot x y) σ σ' via the column-σ' action.
  rw [show (spinHalfDot x y) σ σ' =
      ((spinHalfDot x y).mulVec (basisVec σ')) σ from
        (mulVec_basisVec_apply (spinHalfDot x y) σ σ').symm]
  by_cases hxy : x = y
  · -- spinHalfDot x x = (3/4) • 1, so the column-σ' action is (3/4) • basisVec σ'.
    -- Evaluation at σ ≠ σ' is 0.
    subst hxy
    rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.smul_apply, smul_eq_mul, basisVec_of_ne hne, mul_zero,
        mul_zero, mul_zero, Complex.zero_re]
  · by_cases hpar : σ' x = σ' y
    · -- (spinHalfDot x y).mulVec (basisVec σ') = (1/4) • basisVec σ'.
      -- Evaluation at σ ≠ σ' is 0.
      rw [spinHalfDot_mulVec_basisVec_parallel hxy σ' hpar,
          Pi.smul_apply, smul_eq_mul, basisVec_of_ne hne, mul_zero,
          mul_zero, mul_zero, Complex.zero_re]
    · -- (spinHalfDot x y).mulVec (basisVec σ') = (1/2) • basisVec (swap σ') - (1/4) • basisVec σ'.
      rw [spinHalfDot_mulVec_basisVec_antiparallel hxy σ' hpar]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      -- Evaluation at σ:
      -- = (1/2) * basisVec (swap σ') σ - (1/4) * basisVec σ' σ
      -- The second term is 0 (σ ≠ σ').
      rw [basisVec_of_ne hne, mul_zero, sub_zero]
      by_cases hsw : σ = basisSwap σ' x y
      · -- σ = swap σ': the (1/2) term contributes (1/2).
        subst hsw
        -- Show that σ' x ≠ σ' y is preserved through `basisSwap` (we need σ ≠ σ' already given).
        rw [show basisVec (basisSwap σ' x y) (basisSwap σ' x y) = (1 : ℂ) from
              basisVec_self _, mul_one]
        -- Contribution = marshallSignOf A (swap σ') * marshallSignOf A σ' * (J x y * (1/2)).
        by_cases hAxy : A x = A y
        · -- Bipartite hypothesis forces J x y = 0.
          rw [hJ_bipartite hAxy]
          simp
        · -- A x ≠ A y: Marshall sign trick gives sign factor = -1.
          have hsign : marshallSignOf A (basisSwap σ' x y) * marshallSignOf A σ' = -1 := by
            -- Use the basisSwap-invariance: (basisSwap σ' x y) basisSwap = σ', so
            -- the relation is symmetric.
            have h := marshallSignOf_mul_marshallSignOf_basisSwap_of_bipartite_antiparallel
              A hxy hAxy hpar
            -- h : marshallSignOf A σ' * marshallSignOf A (basisSwap σ' x y) = -1
            rw [mul_comm]
            exact h
          -- Now the dressed contribution = -1 · J x y · (1/2).
          rw [show marshallSignOf A (basisSwap σ' x y) * marshallSignOf A σ' *
                  (J x y * (1 / 2 : ℂ)) =
              (marshallSignOf A (basisSwap σ' x y) * marshallSignOf A σ') *
                ((1 / 2 : ℂ) * J x y) from by ring,
              hsign]
          -- Re of (-1 * (1/2) * J x y) = -(1/2) * J.re
          rw [show ((-1 : ℂ) * ((1 / 2 : ℂ) * J x y)) = -((1 / 2 : ℂ) * J x y) from by ring,
              Complex.neg_re, Complex.mul_re]
          have h12_re : ((1 / 2 : ℂ) : ℂ).re = 1 / 2 := by norm_num
          have h12_im : ((1 / 2 : ℂ) : ℂ).im = 0 := by norm_num
          rw [h12_re, h12_im, zero_mul, sub_zero]
          have : 0 ≤ (1 / 2 : ℝ) * (J x y).re := by
            apply mul_nonneg
            · norm_num
            · exact hJ_nn
          linarith
      · -- σ ≠ swap σ': the (1/2) term also vanishes.
        rw [basisVec_of_ne (Ne.symm fun h => hsw h.symm), mul_zero, mul_zero,
            mul_zero, Complex.zero_re]

/-! ## Main theorem -/

/-- **Property (ii) of the Marshall–Lieb–Mattis theorem** (Tasaki §2.5, p. 41).

For the spin-1/2 antiferromagnetic Heisenberg Hamiltonian on a bipartite
graph `(Λ, A)` with non-negative real coupling `J` supported on bipartite
bonds, every off-diagonal dressed matrix element has non-positive real
part:

  `Re Σ_τ |Ψ̃^σ⟩ τ · (H · |Ψ̃^σ'⟩) τ ≤ 0`  for all `σ ≠ σ'`.

Proof: by linearity, decompose the dressed pairing into bond contributions
and apply the per-bond non-positivity (`bond_dressed_contribution_re_nonpos`). -/
theorem dot_marshallDressed_heisenbergHamiltonian_marshallDressed_re_nonpos_of_ne
    (A : Λ → Bool)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    {σ σ' : Λ → Fin 2} (hne : σ ≠ σ') :
    (∑ τ : Λ → Fin 2,
        marshallDressedBasis A σ τ *
          ((heisenbergHamiltonian J).mulVec (marshallDressedBasis A σ')) τ).re
      ≤ 0 := by
  rw [dot_marshallDressed_mulVec_marshallDressed_eq A (heisenbergHamiltonian J) σ σ']
  -- Decompose H σ σ' = Σ_x Σ_y J(x,y) · (spinHalfDot x y) σ σ'.
  have hdecomp : (heisenbergHamiltonian J) σ σ' =
      ∑ x : Λ, ∑ y : Λ, J x y * (spinHalfDot x y) σ σ' := by
    unfold heisenbergHamiltonian
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [hdecomp]
  -- Distribute marshallSignOf σ * marshallSignOf σ' across the double sum.
  rw [Finset.mul_sum]
  -- Goal: (Σ_x marshallSignOf σ * marshallSignOf σ' * (Σ_y J x y * spinHalfDot x y σ σ')).re ≤ 0
  rw [show (∑ x : Λ, marshallSignOf A σ * marshallSignOf A σ' *
        ∑ y : Λ, J x y * (spinHalfDot x y) σ σ') =
      ∑ x : Λ, ∑ y : Λ,
        marshallSignOf A σ * marshallSignOf A σ' *
          (J x y * (spinHalfDot x y) σ σ') from ?_,
      Complex.re_sum]
  · refine Finset.sum_nonpos fun x _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_nonpos fun y _ => ?_
    exact bond_dressed_contribution_re_nonpos A x y
      (hJ_real x y) (hJ_nn x y) (hJ_bipartite x y) hne
  · refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]

end LatticeSystem.Quantum
