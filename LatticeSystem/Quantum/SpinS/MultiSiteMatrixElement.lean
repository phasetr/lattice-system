import LatticeSystem.Quantum.SpinS.MultiSite

/-!
# Two-site product matrix-element formulas
(build-speed companion to `MultiSite.lean`)

Hosts the trailing sections on two-site product matrix elements
of the on-site spin-`S` operator products
(`onSiteS x A * onSiteS y B`):

- Imaginary-part vanishing + real-cast forms.
- Off-`{x, y}`-agree / off-diag matrix-element formulas.
- The `(S^3 ⊗ S^3)`, `(S^+ ⊗ S^-)`, `(S^- ⊗ S^+)` matrix element
  formulas.
- `basisVecS_expectation_eq_diagonal` (the `<basisVec σ | A | basisVec σ>
  = A σ σ` diagonal-extraction lemma used by `NeelToyComplementExpectation`,
  `SingleClusterHamiltonian`, `SublatticeCasimirNeel`,
  `SublatticeCasimirNeelBasisVecS`).

Originally lines 761..993 of the parent `MultiSite.lean` file.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- For distinct sites `x ≠ y`, the product `S^3_x ⊗ S^3_y` matrix
element has zero imaginary part. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_im_zero
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    ((onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ).im = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  by_cases h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k
  · rw [if_pos h]
    rw [Complex.mul_im]
    rw [spinSOp3_apply_im_zero, spinSOp3_apply_im_zero]
    ring
  · rw [if_neg h]; simp

/-- For distinct sites `x ≠ y`, the product `onSiteS x (S^3) * onSiteS y (S^3)`
preserves real entries. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_eq_ofReal_re
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ =
      ((((onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact onSiteS_spinSOp3_mul_onSiteS_spinSOp3_im_zero hxy σ' σ

/-- For distinct sites `x ≠ y`, the product `S+_x ⊗ S-_y` matrix
element equals its real-part embedding. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_eq_ofReal_re
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ =
      ((((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_im_zero hxy σ' σ

/-- For distinct sites `x ≠ y`, the product `S-_x ⊗ S+_y` matrix
element equals its real-part embedding. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_eq_ofReal_re
    {x y : Λ} (hxy : x ≠ y) (σ' σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ =
      ((((onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ).re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp
  · rw [Complex.ofReal_im]
    exact onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_im_zero hxy σ' σ

/-- For distinct sites `x ≠ y`, when configurations agree at every
site other than `x` and `y`, the matrix element of `S^3_x S^3_y`
factors into the per-site `S^3` entries. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ =
      spinSOp3 N (σ' x) (σ x) * spinSOp3 N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- Same factor formula for `S^+_x ⊗ S^-_y`. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ =
      spinSOpPlus N (σ' x) (σ x) * spinSOpMinus N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- Same factor formula for `S^-_x ⊗ S^+_y`. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_of_off_two_site_agree
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ =
      spinSOpMinus N (σ' x) (σ x) * spinSOpPlus N (σ' y) (σ y) := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]

/-- For distinct sites `x ≠ y` and configurations differing on at
least one of `{x, y}^c`, the `S+_x ⊗ S-_y` matrix element vanishes. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_off_two_site_diff
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_neg h]

/-- Same for `S-_x ⊗ S+_y`. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_off_two_site_diff
    {x y : Λ} (hxy : x ≠ y) {σ' σ : Λ → Fin (N + 1)}
    (h : ¬ ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_neg h]

/-- Vanishing with witness difference site: if `z ∉ {x, y}` and
`σ' z ≠ σ z`, the product `onSiteS x A * onSiteS y B` vanishes at
`(σ', σ)`. -/
theorem onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    (A B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x A * onSiteS y B : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy]
  rw [if_neg]
  intro hagree
  exact hz (hagree z hzx hzy)

/-- Same for `S^3_x ⊗ S^3_y`. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ = 0 :=
  onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair hxy _ _ hzx hzy hz

/-- Same for `S+_x ⊗ S-_y`. -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ = 0 :=
  onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair hxy _ _ hzx hzy hz

/-- Same for `S-_x ⊗ S+_y`. -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_diff_outside_pair
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    {z : Λ} (hzx : z ≠ x) (hzy : z ≠ y) (hz : σ' z ≠ σ z) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ = 0 :=
  onSiteS_mul_onSiteS_apply_eq_zero_of_diff_outside_pair hxy _ _ hzx hzy hz

/-! ## `(S^3 ⊗ S^3)` matrix element formulas -/

/-- For `x ≠ y`, when `σ' = σ`, the `S^3_x ⊗ S^3_y` matrix element
factors into the per-site `S^3` diagonal entries:
`(N/2 - σ_x.val) * (N/2 - σ_y.val)`. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_diag
    {x y : Λ} (hxy : x ≠ y) (σ : Λ → Fin (N + 1)) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ σ =
      ((N : ℂ) / 2 - (σ x).val) * ((N : ℂ) / 2 - (σ y).val) := by
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree hxy
    (fun _ _ _ => rfl)]
  rw [spinSOp3_apply_diag, spinSOp3_apply_diag]

/-- For `x ≠ y` and `σ' σ` agreeing off `{x, y}` with `σ' x ≠ σ x`,
the `S^3_x ⊗ S^3_y` matrix element vanishes (`S^3` is diagonal). -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_x
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσx : σ' x ≠ σ x) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree hxy h]
  rw [show spinSOp3 N (σ' x) (σ x) = 0 from
    Matrix.diagonal_apply_ne _ hσx]
  ring

/-- Symmetric: vanishes if `σ' y ≠ σ y`. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_eq_zero_of_off_diag_at_y
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) (hσy : σ' y ≠ σ y) :
    (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_spinSOp3_mul_onSiteS_spinSOp3_apply_of_off_two_site_agree hxy h]
  rw [show spinSOp3 N (σ' y) (σ y) = 0 from
    Matrix.diagonal_apply_ne _ hσy]
  ring

/-- For `x ≠ y` and `σ', σ` agreeing off `{x, y}` with `σ_x = σ'_x + 1`
("S+ raises k=σ from σ' = σ - 1"), the `S-_x ⊗ S+_y` matrix element
vanishes (wrong direction at site `x`). -/
theorem onSiteS_spinSOpMinus_mul_onSiteS_spinSOpPlus_apply_eq_zero_of_raising_x
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val) :
    (onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
  rw [show spinSOpMinus N (σ' x) (σ x) = 0 from
    spinSOpMinus_apply_other N (by omega)]
  ring

/-- For `x ≠ y` and `σ', σ` agreeing off `{x, y}` with
`σ'_x = σ_x + 1` ("S- lowers k=σ to σ' = σ + 1"), the `S+_x ⊗ S-_y`
matrix element vanishes (wrong direction at site `x`). -/
theorem onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_lowering_x
    {x y : Λ} (hxy : x ≠ y)
    {σ' σ : Λ → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val) :
    (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N)
          : ManyBodyOpS Λ N) σ' σ = 0 := by
  rw [onSiteS_mul_onSiteS_apply_eq hxy, if_pos h]
  rw [show spinSOpPlus N (σ' x) (σ x) = 0 from
    spinSOpPlus_apply_other N (by omega)]
  ring

/-- For any matrix `M` and basis vector `|σ⟩ = basisVecS σ`:
`<σ | M | σ> = M σ σ`. The expectation value of a matrix on a basis vector
equals its diagonal element at that basis. -/
theorem basisVecS_expectation_eq_diagonal
    (σ : Λ → Fin (N + 1)) (M : ManyBodyOpS Λ N) :
    dotProduct (star (basisVecS σ : (Λ → Fin (N + 1)) → ℂ))
        (M.mulVec (basisVecS σ)) = M σ σ := by
  unfold dotProduct
  rw [Finset.sum_eq_single σ]
  · simp only [Pi.star_apply, basisVecS_self, star_one, one_mul]
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single σ]
    · rw [basisVecS_self, mul_one]
    · intros τ _ hτne
      rw [basisVecS_of_ne hτne]
      simp
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · intros τ _ hτne
    simp [basisVecS_of_ne hτne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end LatticeSystem.Quantum
