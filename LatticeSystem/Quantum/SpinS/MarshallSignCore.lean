import LatticeSystem.Quantum.SpinS.Magnetization
import LatticeSystem.Quantum.SpinS.TotalSpin

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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

/-- **Marshall sign factorization on a single-site difference**:
when configurations `σ'` and `σ` agree away from `x`, the product of
their Marshall signs only sees the possible change at `x`. -/
theorem marshallSignS_mul_of_agree_off_site
    (A : V → Bool) (x : V) {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → σ' k = σ k) :
    marshallSignS A σ' * marshallSignS A σ =
      if A x then ((-1 : ℂ) ^ ((σ' x).val + (σ x).val)) else 1 := by
  classical
  rw [marshallSignS_mul]
  have hsplit :
      (Finset.univ : Finset V) = {x} ∪ (Finset.univ \ {x}) := by
    ext z
    simp
  rw [hsplit]
  rw [Finset.prod_union (by
    rw [Finset.disjoint_iff_inter_eq_empty]
    ext z; simp)]
  rw [Finset.prod_singleton]
  have hrest : ∏ z ∈ (Finset.univ \ {x} : Finset V),
      (if A z then ((-1 : ℂ) ^ ((σ' z).val + (σ z).val)) else 1) = 1 := by
    refine Finset.prod_eq_one (fun z hz => ?_)
    rw [Finset.mem_sdiff] at hz
    have hzx : z ≠ x := fun heq => hz.2 (by simp [heq])
    rw [h z hzx]
    by_cases hAz : A z
    · simp [hAz, ← two_mul, pow_mul]
    · simp [hAz]
  rw [hrest, mul_one]

/-- **Single-site lowering predecessor sign on `A`**: if `σ'` is
obtained from `σ` by raising the index at the single `A`-site `x` by
one and agreeing off `x`, then the Marshall signs multiply to `-1`. -/
theorem marshallSignS_mul_of_agree_off_site_A_true_lower
    (A : V → Bool) {x : V} (hAx : A x = true)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) :
    marshallSignS A σ' * marshallSignS A σ = -1 := by
  rw [marshallSignS_mul_of_agree_off_site A x h]
  rw [if_pos hAx]
  have hxodd : Odd ((σ' x).val + (σ x).val) := by
    refine ⟨(σ x).val, ?_⟩
    omega
  exact Odd.neg_one_pow hxodd

/-- **Single-site lowering predecessor sign off `A`**: if `σ'` and
`σ` agree off a site `x ∉ A`, their Marshall signs multiply to `1`;
in particular this applies to single-site lowering predecessor pairs. -/
theorem marshallSignS_mul_of_agree_off_site_A_false_lower
    (A : V → Bool) {x : V} (hAx : A x = false)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → σ' k = σ k)
    (_hx : (σ x).val + 1 = (σ' x).val) :
    marshallSignS A σ' * marshallSignS A σ = 1 := by
  rw [marshallSignS_mul_of_agree_off_site A x h]
  rw [if_neg (by simp [hAx])]

/-- The Marshall sign equals its inverse: `(marshallSignS A σ)⁻¹ = marshallSignS A σ`. -/
theorem marshallSignS_inv (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ)⁻¹ = marshallSignS A σ := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- Imaginary part of the Marshall sign is zero. -/
theorem marshallSignS_im (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ).im = 0 := by
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · rw [h]; simp
  · rw [h]; simp

/-- Real-part form of
`marshallSignS_mul_of_agree_off_site_A_true_lower`. -/
theorem marshallSignS_re_mul_re_of_agree_off_site_A_true_lower
    (A : V → Bool) {x : V} (hAx : A x = true)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) :
    (marshallSignS A σ').re * (marshallSignS A σ).re = -1 := by
  have hmul :=
    marshallSignS_mul_of_agree_off_site_A_true_lower A hAx h hx
  have hre :
      (marshallSignS A σ' * marshallSignS A σ).re =
        (marshallSignS A σ').re * (marshallSignS A σ).re := by
    rw [Complex.mul_re, marshallSignS_im, marshallSignS_im]
    ring
  rw [hmul] at hre
  norm_num at hre
  exact hre.symm

/-- Real-part form of
`marshallSignS_mul_of_agree_off_site_A_false_lower`. -/
theorem marshallSignS_re_mul_re_of_agree_off_site_A_false_lower
    (A : V → Bool) {x : V} (hAx : A x = false)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) :
    (marshallSignS A σ').re * (marshallSignS A σ).re = 1 := by
  have hmul :=
    marshallSignS_mul_of_agree_off_site_A_false_lower A hAx h hx
  have hre :
      (marshallSignS A σ' * marshallSignS A σ).re =
        (marshallSignS A σ').re * (marshallSignS A σ).re := by
    rw [Complex.mul_re, marshallSignS_im, marshallSignS_im]
    ring
  rw [hmul] at hre
  norm_num at hre
  exact hre.symm

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

/-- The square of the Marshall sign's real part equals 1. -/
theorem marshallSignS_re_sq (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ).re * (marshallSignS A σ).re = 1 := by
  rcases marshallSignS_re_eq_one_or_neg_one A σ with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

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


end LatticeSystem.Quantum
