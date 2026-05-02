import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Spin-`S` Marshall sign on a bipartite sublattice
(Tasaki §2.5 Phase B-β β-4h)

For a vertex type `V`, a sublattice-`A` indicator `A : V → Bool`, and
a spin-`S` configuration `σ : V → Fin (N + 1)`, the Marshall sign is

  `marshallSignS A σ := ∏_{x ∈ A} (-1)^(σ x).val
                     = (-1)^(Σ_{x ∈ A} (σ x).val)`.

Generalises the spin-1/2 `marshallSignOf` (`Quantum/NeelState/MarshallSign.lean`).

For the spin-1/2 case `N = 1`, `(σ x).val ∈ {0, 1}` so
`Σ_{x ∈ A} (σ x).val = |{x ∈ A : σ x = 1}|`
recovers the standard "down-spin count on sublattice A" sign.

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] {N : ℕ}

/-- The spin-`S` Marshall sign on sublattice indicator `A`. -/
noncomputable def marshallSignS (A : V → Bool) (σ : V → Fin (N + 1)) : ℂ :=
  ∏ x : V, if A x then ((-1 : ℂ) ^ (σ x).val) else 1

/-- All-`s = 0` Marshall sign is `+1` on any sublattice. -/
theorem marshallSignS_const_zero (A : V → Bool) :
    marshallSignS A (fun _ : V => (0 : Fin (N + 1))) = 1 := by
  unfold marshallSignS
  apply Finset.prod_eq_one
  intro x _
  by_cases hAx : A x
  · simp [hAx]
  · simp [hAx]

/-- Marshall sign with the all-false sublattice indicator is `+1`:
no factor `(-1)^k` ever fires, so the product is `1`. -/
theorem marshallSignS_eq_one_of_A_false
    (σ : V → Fin (N + 1)) :
    marshallSignS (fun _ : V => false) σ = 1 := by
  unfold marshallSignS
  apply Finset.prod_eq_one
  intro x _
  rfl

/-- Marshall sign with the all-true sublattice indicator: each factor
fires, giving `(-1)^(magSumS σ)`. -/
theorem marshallSignS_eq_neg_one_pow_of_A_true (σ : V → Fin (N + 1)) :
    marshallSignS (fun _ : V => true) σ = (-1 : ℂ) ^ magSumS σ := by
  unfold marshallSignS magSumS
  simp only [if_true]
  rw [← Finset.prod_pow_eq_pow_sum]

/-- Marshall sign over an empty lattice is `1`. -/
theorem marshallSignS_of_isEmpty [IsEmpty V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ = 1 := by
  unfold marshallSignS
  rw [show (Finset.univ : Finset V) = ∅ from Finset.eq_empty_of_isEmpty _]
  exact Finset.prod_empty

/-- For `N = 0` (`S = 0`), the only configuration is the constant
zero, so the Marshall sign is always `1`. -/
theorem marshallSignS_N_zero (A : V → Bool) (σ : V → Fin 1) :
    marshallSignS A σ = 1 := by
  have : σ = (fun _ => (0 : Fin 1)) := by
    funext x; apply Fin.ext; have := (σ x).isLt; omega
  rw [this, marshallSignS_const_zero]

/-- The Marshall sign at `σ'` and `σ` are equal when σ' = σ. -/
theorem marshallSignS_eq_of_eq (A : V → Bool)
    {σ' σ : V → Fin (N + 1)} (h : σ' = σ) :
    marshallSignS A σ' = marshallSignS A σ := by rw [h]

/-- Symmetric form of the Marshall sign product:
`marshallSignS A σ' * marshallSignS A σ = marshallSignS A σ * marshallSignS A σ'`. -/
theorem marshallSignS_mul_swap (A : V → Bool) (σ σ' : V → Fin (N + 1)) :
    marshallSignS A σ * marshallSignS A σ' =
      marshallSignS A σ' * marshallSignS A σ :=
  mul_comm _ _


/-- For a constant configuration `σ ≡ s` and `s.val` even, the
Marshall sign is `+1`. (Each `(-1)^(s.val)` factor is `+1`.) -/
theorem marshallSignS_const_of_even
    (A : V → Bool) {s : Fin (N + 1)} (hs : Even s.val) :
    marshallSignS A (fun _ : V => s) = 1 := by
  unfold marshallSignS
  apply Finset.prod_eq_one
  intro x _
  by_cases hAx : A x
  · simp [hAx]
    exact Even.neg_one_pow hs
  · simp [hAx]


/-- The Marshall sign restricted to `A`-sites: factors away the
trivial `1` contributions from non-`A` sites. -/
theorem marshallSignS_eq_prod_A_filter
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ =
      ∏ x ∈ Finset.univ.filter (fun x : V => A x = true),
        ((-1 : ℂ) ^ (σ x).val) := by
  classical
  unfold marshallSignS
  rw [Finset.prod_filter]


/-- Definitional unfolding of `marshallSignS`. -/
theorem marshallSignS_def (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ =
      ∏ x : V, if A x then ((-1 : ℂ) ^ (σ x).val) else 1 := rfl


/-- Product of two Marshall signs at the same sublattice indicator
factors site-wise: each `A`-site contributes `(-1)^((σ x).val + (σ' x).val)`. -/
theorem marshallSignS_mul (A : V → Bool) (σ σ' : V → Fin (N + 1)) :
    marshallSignS A σ * marshallSignS A σ' =
      ∏ x : V, if A x then ((-1 : ℂ) ^ ((σ x).val + (σ' x).val)) else 1 := by
  unfold marshallSignS
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro x _
  by_cases hAx : A x
  · simp only [hAx, if_true]
    rw [← pow_add]
  · simp [hAx]

/-- The Marshall sign is non-zero. Each factor is either `(-1)^k = ±1`
or `1`, never zero, so the product is non-zero. -/
theorem marshallSignS_ne_zero (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ ≠ 0 := by
  unfold marshallSignS
  apply Finset.prod_ne_zero_iff.mpr
  intro x _
  by_cases hAx : A x
  · simp only [hAx, if_true]
    exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)
  · simp [hAx]

/-- The Marshall sign is `±1`: its square is `1`. -/
theorem marshallSignS_sq (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ * marshallSignS A σ = 1 := by
  unfold marshallSignS
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro x _
  by_cases hAx : A x
  · simp only [hAx, if_true]
    rw [← pow_add, ← two_mul, pow_mul]
    rw [show ((-1 : ℂ) ^ 2) = 1 from by norm_num]
    rw [one_pow]
  · simp [hAx]

/-- The Marshall sign is either `1` or `-1`: a corollary of
`marshallSignS_sq` in the field ℂ. -/
theorem marshallSignS_eq_one_or_neg_one
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ = 1 ∨ marshallSignS A σ = -1 := by
  have hsq := marshallSignS_sq A σ
  -- `x² = 1 ↔ (x - 1)(x + 1) = 0`, then field property.
  have h : (marshallSignS A σ - 1) * (marshallSignS A σ + 1) = 0 := by
    rw [show (marshallSignS A σ - 1) * (marshallSignS A σ + 1) =
        marshallSignS A σ * marshallSignS A σ - 1 from by ring]
    rw [hsq, sub_self]
  rcases mul_eq_zero.mp h with h1 | h2
  · left; exact sub_eq_zero.mp h1
  · right
    have := add_eq_zero_iff_eq_neg.mp h2
    rw [this]

/-- The norm of the Marshall sign is `1`. -/
theorem marshallSignS_norm (A : V → Bool) (σ : V → Fin (N + 1)) :
    ‖marshallSignS A σ‖ = 1 := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · rw [h, norm_one]
  · rw [h]; simp

/-- Even powers of the Marshall sign are `1`. -/
theorem marshallSignS_pow_two_mul (A : V → Bool) (σ : V → Fin (N + 1))
    (k : ℕ) :
    marshallSignS A σ ^ (2 * k) = 1 := by
  rw [pow_mul]
  rw [show marshallSignS A σ ^ 2 = 1 from by
    rw [pow_two]; exact marshallSignS_sq A σ]
  rw [one_pow]

/-- Cube of the Marshall sign equals itself: `(σ_M)^3 = σ_M`. -/
theorem marshallSignS_pow_three (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ ^ 3 = marshallSignS A σ := by
  rw [show (3 : ℕ) = 2 + 1 from rfl]
  rw [pow_succ, pow_two, marshallSignS_sq, one_mul]

/-- **Marshall sign factorization on two-site differences**: when
configurations `σ', σ` agree at every site except possibly `x` and
`y` (with `x ≠ y`), the product `marshallSignS A σ' * marshallSignS A σ`
factors into a product of per-site contributions at `x` and `y`,
since at every other site the agreement forces the contribution to
be `(-1)^(2 σ_z) = 1`. -/
theorem marshallSignS_mul_of_agree_off_two_site
    (A : V → Bool) {x y : V} (hxy : x ≠ y)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    marshallSignS A σ' * marshallSignS A σ =
      (if A x then ((-1 : ℂ) ^ ((σ' x).val + (σ x).val)) else 1) *
      (if A y then ((-1 : ℂ) ^ ((σ' y).val + (σ y).val)) else 1) := by
  classical
  rw [marshallSignS_mul]
  have hsplit :
      (Finset.univ : Finset V) = {x, y} ∪ (Finset.univ \ {x, y}) := by
    ext z
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.mem_sdiff, true_iff, true_and]
    by_cases hzx : z = x
    · left; left; exact hzx
    · by_cases hzy : z = y
      · left; right; exact hzy
      · right
        intro hz
        rcases hz with hz | hz
        · exact hzx hz
        · exact hzy hz
  rw [hsplit]
  rw [Finset.prod_union (by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext z; simp)]
  rw [Finset.prod_pair hxy]
  have hrest : ∏ z ∈ (Finset.univ \ {x, y} : Finset V),
      (if A z then ((-1 : ℂ) ^ ((σ' z).val + (σ z).val)) else 1) = 1 := by
    refine Finset.prod_eq_one (fun z hz => ?_)
    rw [Finset.mem_sdiff] at hz
    have hzxy : z ∉ ({x, y} : Finset V) := hz.2
    have hzx : z ≠ x := fun heq => hzxy (by simp [heq])
    have hzy : z ≠ y := fun heq => hzxy (by simp [heq])
    rw [h z hzx hzy]
    by_cases hAz : A z
    · simp [hAz, ← two_mul, pow_mul]
    · simp [hAz]
  rw [hrest, mul_one]

/-- **Marshall sign on a bipartite raising/lowering bond is `-1`**.
For `x ∈ A`, `y ∉ A`, and configurations `σ', σ` that agree off
`{x, y}` with `(σ' x).val + (σ x).val` odd and `(σ' y).val + (σ y).val`
even (or vice versa) — i.e., a single raising/lowering shift on
exactly one of `{x, y}` lying in `A` — the Marshall sign product is
`-1`. The general formula collapses since the `y` factor (with `A y`
false) is `1`, and the `x` factor with odd exponent is `-1`. -/
theorem marshallSignS_mul_of_agree_off_two_site_bipartite_x
    (A : V → Bool) {x y : V} (hxy : x ≠ y)
    (hAx : A x = true) (hAy : A y = false)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hxod : Odd ((σ' x).val + (σ x).val)) :
    marshallSignS A σ' * marshallSignS A σ = -1 := by
  rw [marshallSignS_mul_of_agree_off_two_site A hxy h]
  rw [if_pos hAx]
  simp [hAy, Odd.neg_one_pow hxod]

/-- Same as above but with `x ∉ A`, `y ∈ A`. -/
theorem marshallSignS_mul_of_agree_off_two_site_bipartite_y
    (A : V → Bool) {x y : V} (hxy : x ≠ y)
    (hAx : A x = false) (hAy : A y = true)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hyod : Odd ((σ' y).val + (σ y).val)) :
    marshallSignS A σ' * marshallSignS A σ = -1 := by
  rw [marshallSignS_mul_of_agree_off_two_site A hxy h]
  rw [if_neg (by simp [hAx])]
  simp [hAy, Odd.neg_one_pow hyod]

/-- The Marshall sign equals its inverse: `(marshallSignS A σ)⁻¹ = marshallSignS A σ`. -/
theorem marshallSignS_inv (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ)⁻¹ = marshallSignS A σ := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- `(marshallSignS A σ)⁻¹ * marshallSignS A σ = 1`. -/
theorem marshallSignS_inv_mul_self (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ)⁻¹ * marshallSignS A σ = 1 := by
  rw [marshallSignS_inv, marshallSignS_sq]

/-- `marshallSignS A σ * (marshallSignS A σ)⁻¹ = 1`. -/
theorem marshallSignS_mul_self_inv (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ * (marshallSignS A σ)⁻¹ = 1 := by
  rw [marshallSignS_inv, marshallSignS_sq]

/-- The Marshall sign is `±1` valued in `ℝ` (after embedding into ℂ). -/
theorem marshallSignS_re (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ).re = 1 ∨ (marshallSignS A σ).re = -1 := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · left; rw [h]; rfl
  · right; rw [h]; rfl

/-- Imaginary part of the Marshall sign is zero. -/
theorem marshallSignS_im (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ).im = 0 := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- `marshallSignS A σ = ((marshallSignS A σ).re : ℂ)`: the Marshall
sign is real-valued (always ±1, both real), so it equals its embedded
real part. -/
theorem marshallSignS_eq_ofReal_re (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ = ((marshallSignS A σ).re : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact marshallSignS_im A σ

/-- The real part of the Marshall sign is `±1`. -/
theorem marshallSignS_re_eq_one_or_neg_one (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ).re = 1 ∨ (marshallSignS A σ).re = -1 := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-- The absolute value of the Marshall sign's real part is exactly 1. -/
theorem marshallSignS_re_abs (A : V → Bool) (σ : V → Fin (N + 1)) :
    |(marshallSignS A σ).re| = 1 := by
  rcases marshallSignS_re_eq_one_or_neg_one A σ with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- The square of the Marshall sign's real part equals 1. -/
theorem marshallSignS_re_sq (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ).re * (marshallSignS A σ).re = 1 := by
  rcases marshallSignS_re_eq_one_or_neg_one A σ with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- Marshall sign multiplication is commutative (trivially in ℂ). -/
theorem marshallSignS_mul_comm (A : V → Bool) (σ σ' : V → Fin (N + 1)) :
    marshallSignS A σ * marshallSignS A σ' =
      marshallSignS A σ' * marshallSignS A σ :=
  mul_comm _ _

/-- Restated form: `marshallSignS A σ * marshallSignS A σ = 1`. -/
theorem marshallSignS_mul_self (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ * marshallSignS A σ = 1 :=
  marshallSignS_sq A σ

/-- The Marshall sign belongs to the set `{1, -1}`. -/
theorem marshallSignS_mem_pm_one
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallSignS A σ ∈ ({1, -1} : Set ℂ) := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · left; exact h
  · right; rw [Set.mem_singleton_iff]; exact h

/-- The Marshall sign is real: its complex conjugate is itself. Each
factor `(-1)^k` is real, so the star/conjugation acts as identity on
the product. -/
theorem marshallSignS_star (A : V → Bool) (σ : V → Fin (N + 1)) :
    star (marshallSignS A σ) = marshallSignS A σ := by
  unfold marshallSignS
  rw [star_prod]
  apply Finset.prod_congr rfl
  intro x _
  by_cases hAx : A x
  · simp only [hAx, if_true]
    rw [show ((-1 : ℂ) ^ (σ x).val) = ((-1 : ℂ)) ^ (σ x).val from rfl]
    rw [star_pow]
    rw [show star (-1 : ℂ) = -1 from by simp]
  · simp [hAx]

/-! ## Marshall-dressed basis -/

/-- The Marshall-dressed basis vector at `σ`:

  `marshallDressedBasisS A σ := marshallSignS A σ • basisVecS σ`.

This is the orthonormal basis used in the Marshall–Lieb–Mattis
machinery: by absorbing the Marshall sign into the basis vector, the
Heisenberg matrix elements become *real and non-positive*
off-diagonal in this rotated basis (Marshall sign trick), enabling
the Perron–Frobenius argument.

Generalises the spin-1/2 `marshallDressedBasis`
(`Quantum/MarshallDressedBasis.lean`) to arbitrary spin. -/
noncomputable def marshallDressedBasisS [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) : (V → Fin (N + 1)) → ℂ :=
  marshallSignS A σ • basisVecS σ

/-- Definitional unfolding of `marshallDressedBasisS`. -/
theorem marshallDressedBasisS_def [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ = marshallSignS A σ • basisVecS σ := rfl

/-- Component formula: `marshallDressedBasisS A σ τ` is
`marshallSignS A σ` if `τ = σ`, else `0`. -/
theorem marshallDressedBasisS_apply [DecidableEq V]
    (A : V → Bool) (σ τ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ τ =
      if τ = σ then marshallSignS A σ else 0 := by
  unfold marshallDressedBasisS basisVecS
  rw [Pi.smul_apply, smul_eq_mul]
  by_cases h : τ = σ
  · rw [if_pos h, if_pos h, mul_one]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Diagonal component: `marshallDressedBasisS A σ σ = marshallSignS A σ`. -/
@[simp]
theorem marshallDressedBasisS_self [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ σ = marshallSignS A σ := by
  rw [marshallDressedBasisS_apply, if_pos rfl]

/-- Off-diagonal component: zero for `τ ≠ σ`. -/
theorem marshallDressedBasisS_of_ne [DecidableEq V]
    (A : V → Bool) {σ τ : V → Fin (N + 1)} (hne : τ ≠ σ) :
    marshallDressedBasisS A σ τ = 0 := by
  rw [marshallDressedBasisS_apply, if_neg hne]

/-- All-`s = 0` Marshall-dressed basis vector equals the standard
basis vector at the all-zero config (since the Marshall sign is
`+1` there). -/
theorem marshallDressedBasisS_const_zero [DecidableEq V]
    (A : V → Bool) :
    marshallDressedBasisS A (fun _ : V => (0 : Fin (N + 1))) =
      basisVecS (fun _ : V => (0 : Fin (N + 1))) := by
  unfold marshallDressedBasisS
  rw [marshallSignS_const_zero, one_smul]

/-- For `N = 0` (`S = 0`), the Marshall-dressed basis vector equals
the plain basis vector. -/
theorem marshallDressedBasisS_N_zero [DecidableEq V]
    (A : V → Bool) (σ : V → Fin 1) :
    marshallDressedBasisS A σ = basisVecS σ := by
  unfold marshallDressedBasisS
  rw [marshallSignS_N_zero, one_smul]

/-- For an empty lattice, the Marshall-dressed basis vector equals
the plain basis vector (Marshall sign is `1`). -/
theorem marshallDressedBasisS_of_isEmpty [DecidableEq V] [IsEmpty V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ = basisVecS σ := by
  unfold marshallDressedBasisS
  rw [marshallSignS_of_isEmpty, one_smul]

/-- **Orthonormality of the Marshall-dressed basis**:

  `Σ_τ (marshallDressedBasisS A σ τ).star * marshallDressedBasisS A σ' τ
     = if σ = σ' then 1 else 0`. -/
theorem marshallDressedBasisS_inner_product [DecidableEq V]
    (A : V → Bool) (σ σ' : V → Fin (N + 1)) :
    (∑ τ : V → Fin (N + 1),
        star (marshallDressedBasisS A σ τ) *
          marshallDressedBasisS A σ' τ) =
      if σ = σ' then 1 else 0 := by
  by_cases hσ : σ = σ'
  · subst hσ
    rw [if_pos rfl]
    -- Only τ = σ contributes; that term is (marshallSignS).star * marshallSignS = 1.
    rw [Fintype.sum_eq_single σ (fun τ hτ => by
      rw [marshallDressedBasisS_of_ne A hτ, mul_zero])]
    rw [marshallDressedBasisS_self, marshallSignS_star,
        marshallSignS_sq]
  · rw [if_neg hσ]
    -- For σ ≠ σ', no τ can simultaneously equal σ and σ', so each term is 0.
    apply Finset.sum_eq_zero
    intro τ _
    by_cases hτσ : τ = σ
    · subst hτσ
      have hne : τ ≠ σ' := fun heq => hσ heq
      rw [marshallDressedBasisS_of_ne A hne, mul_zero]
    · rw [marshallDressedBasisS_of_ne A hτσ, star_zero, zero_mul]

/-- The Marshall-dressed basis vector lies in the magnetization
subspace of its underlying configuration: scaling by the Marshall
sign preserves the magnetization eigenvalue (linearity of the
subspace). -/
theorem marshallDressedBasisS_mem_magSubspaceS [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallDressedBasisS A σ : (V → Fin (N + 1)) → ℂ) ∈
      magSubspaceS V N (magEigenvalueS σ) := by
  unfold marshallDressedBasisS
  exact (magSubspaceS V N (magEigenvalueS σ)).smul_mem _
    (basisVecS_mem_magSubspaceS σ)

/-- **Inverse relation**: scaling the Marshall-dressed basis by the
(real) Marshall sign recovers the plain basis vector:

  `marshallSignS A σ • marshallDressedBasisS A σ = basisVecS σ`.

(Since the Marshall sign is real and squares to 1, multiplying by it
once more inverts the dressing.) -/
theorem marshallSignS_smul_marshallDressedBasisS [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ : ℂ) • marshallDressedBasisS A σ = basisVecS σ := by
  unfold marshallDressedBasisS
  rw [smul_smul, marshallSignS_sq, one_smul]

/-- The Marshall-dressed basis vector is non-zero: at its diagonal
component, `marshallDressedBasisS A σ σ = marshallSignS A σ ≠ 0`. -/
theorem marshallDressedBasisS_ne_zero [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ ≠ 0 := by
  intro h
  have h0 : marshallDressedBasisS A σ σ = 0 := by rw [h]; rfl
  rw [marshallDressedBasisS_self] at h0
  exact marshallSignS_ne_zero A σ h0

/-- The Marshall-dressed basis vector at its own configuration has
norm 1: `‖marshallDressedBasisS A σ σ‖ = 1`. -/
theorem marshallDressedBasisS_self_norm [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    ‖marshallDressedBasisS A σ σ‖ = 1 := by
  rw [marshallDressedBasisS_self, marshallSignS_norm]

/-- Component-wise norm of the Marshall-dressed basis equals the
component-wise norm of the plain basis (since dressing only changes
sign): `‖marshallDressedBasisS A σ τ‖ = ‖basisVecS σ τ‖`. -/
theorem marshallDressedBasisS_norm_eq_basisVecS [DecidableEq V]
    (A : V → Bool) (σ τ : V → Fin (N + 1)) :
    ‖marshallDressedBasisS A σ τ‖ = ‖(basisVecS σ τ : ℂ)‖ := by
  unfold marshallDressedBasisS
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [marshallSignS_norm, one_mul]

/-- The Marshall-dressed basis vector lies in the supremum of all
magnetization subspaces (since it lies in `magSubspaceS V N (magEigenvalueS σ)`
which is included in `⨆ M, magSubspaceS V N M`). -/
theorem marshallDressedBasisS_mem_iSup_magSubspaceS [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallDressedBasisS A σ : (V → Fin (N + 1)) → ℂ) ∈
      ⨆ M : ℂ, magSubspaceS V N M :=
  Submodule.mem_iSup_of_mem (magEigenvalueS σ)
    (marshallDressedBasisS_mem_magSubspaceS A σ)

/-- **Marshall-dressed basis is `±basisVecS`**: depending on whether
the Marshall sign is `+1` or `-1`, the dressed basis vector equals
`+basisVecS σ` or `-basisVecS σ`. -/
theorem marshallDressedBasisS_eq_or [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ = basisVecS σ ∨
      marshallDressedBasisS A σ = -basisVecS σ := by
  unfold marshallDressedBasisS
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · left; rw [h, one_smul]
  · right; rw [h, neg_smul, one_smul]

/-- **Inverse decomposition**: every plain basis vector is
`marshallSignS A σ` times the corresponding Marshall-dressed basis
vector. (This is `marshallSignS_smul_marshallDressedBasisS` restated
with sides swapped for use as a rewrite from `basisVecS` toward
`marshallDressedBasisS`.) -/
theorem basisVecS_eq_marshallSignS_smul_marshallDressedBasisS
    [DecidableEq V] (A : V → Bool) (σ : V → Fin (N + 1)) :
    (basisVecS σ : (V → Fin (N + 1)) → ℂ) =
      marshallSignS A σ • marshallDressedBasisS A σ :=
  (marshallSignS_smul_marshallDressedBasisS A σ).symm

/-- **Marshall-dressed basis decomposition** of any vector:
`v = Σ_σ (marshallSignS A σ * v(σ)) • marshallDressedBasisS A σ`.
Substituting `basisVecS σ = marshallSignS A σ • marshallDressedBasisS A σ`
into `fun_eq_sum_smul_basisVecS`. -/
theorem fun_eq_sum_smul_marshallDressedBasisS [DecidableEq V]
    (A : V → Bool) (v : (V → Fin (N + 1)) → ℂ) :
    v = ∑ σ : V → Fin (N + 1),
      (marshallSignS A σ * v σ) • marshallDressedBasisS A σ := by
  conv_lhs => rw [fun_eq_sum_smul_basisVecS v]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [basisVecS_eq_marshallSignS_smul_marshallDressedBasisS A σ]
  rw [smul_smul]
  rw [mul_comm (v σ) (marshallSignS A σ)]

end LatticeSystem.Quantum
