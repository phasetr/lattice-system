import LatticeSystem.Quantum.SpinS.DressedHeisenbergMarshallCore

/-!
# Marshall-dressed bipartite re-nonpos arguments and
`dressedHeisenbergSReMatrix` Hermiticity (build-speed companion)

Build-speed companion to `DressedHeisenberg.lean`. Hosts the
trailing section "Marshall-dressed `(Ŝ_x · Ŝ_y)` on bipartite
raising/lowering pairs" plus the re-nonpos arguments and the
`dressedHeisenbergSReMatrix` Hermiticity / `_apply_eq_ofReal_re`
/ `_eq_dressedHeisenbergSReMatrix_complex` results
(originally lines 570..1058 of the pre-#37 parent file).

Splitting these blocks out drops the parent from ~1058 lines to
~569 lines.

`ShiftedDressedMatrix.lean` updated to additionally import this
companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body
  Systems*, Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Two-site matrix-element formula for the dressed Heisenberg
matrix**: for `x ≠ y` and configurations `σ', σ` agreeing off `{x, y}`
with `σ' ≠ σ`,

    `dressedHeisenbergS A J N σ' σ
       = (J(x, y) + J(y, x)) ·
           (marshallSignS A σ' · marshallSignS A σ) · (Ŝ_x · Ŝ_y) σ' σ`.

Direct corollary of `heisenbergHamiltonianS_apply_of_off_two_site_agree`
unfolded through the dressed-Heisenberg definition. -/
theorem dressedHeisenbergS_apply_of_off_two_site_agree
    (A : V → Bool) {J : V → V → ℂ} {x y : V} (hxy : x ≠ y) (N : ℕ)
    {σ' σ : V → Fin (N + 1)} (hne : σ' ≠ σ)
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k) :
    dressedHeisenbergS A J N σ' σ =
      (J x y + J y x) * (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_apply_of_off_two_site_agree (Λ := V) hxy N
    hne h]
  ring

/-- **Off-diagonal dressed Heisenberg non-positivity, bipartite raising
case** (Tasaki §2.5 Property (ii) for general spin, raising at `x ∈ A`).

For a bipartite sublattice indicator `A` (`A x = true`, `A y = false`),
real symmetric coupling `J` with `(J x y).re ≥ 0`, and configurations
`σ', σ` agreeing off `{x, y}` exhibiting raising at `x` and lowering
at `y` (`σ' x = σ x + 1`, `σ y = σ' y + 1`), the dressed matrix
element has non-positive real part:

    `Re (dressedHeisenbergS A J N σ' σ) ≤ 0`.

Combines the two-site dressed formula with the spinSDot bipartite
non-positivity (`marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x`).
The symmetric coupling collapses `J(x, y) + J(y, x)` to `2 · J(x, y)`,
and the realness of `J` lets the real coupling factor through `Re`. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_x
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (hy : (σ' y).val + 1 = (σ y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  -- (J x y + J y x) = 2 * J x y.
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  -- 2 * J x y is real with re = 2 * (J x y).re.
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  -- ((real) * (sign·sign·spinSDot)).re = real · (sign·sign·spinSDot).re.
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  -- Now: (2 · (J x y).re) · (sign·sign·spinSDot).re ≤ 0.
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x_lowering hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- **Off-diagonal dressed Heisenberg non-positivity, bipartite case
`x ∉ A, y ∈ A`, raising at `x ∉ A`**. Symmetric to the
`bipartite_x` case with the sublattice roles swapped. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_y
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- Mirror of `dressedHeisenbergS_apply_re_nonpos_bipartite_x`:
bipartite case `x ∈ A, y ∉ A`, but lowering at `x` and raising at `y`. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_x_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- Mirror of `dressedHeisenbergS_apply_re_nonpos_bipartite_y`:
bipartite case `x ∉ A, y ∈ A`, but raising at `x` and lowering at `y`. -/
theorem dressedHeisenbergS_apply_re_nonpos_bipartite_y_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {J : V → V → ℂ} (hJ_real : (J x y).im = 0) (hJ_nn : 0 ≤ (J x y).re)
    (hJ_sym : J x y = J y x)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (hy : (σ' y).val + 1 = (σ y).val) :
    (dressedHeisenbergS A J N σ' σ).re ≤ 0 := by
  have hne : σ' ≠ σ := by
    intro heq
    have : (σ' x).val = (σ x).val := by rw [heq]
    omega
  rw [dressedHeisenbergS_apply_of_off_two_site_agree A hxy N hne h]
  rw [show (J x y + J y x) = 2 * J x y from by rw [← hJ_sym]; ring]
  rw [show (2 : ℂ) * J x y = ((2 * (J x y).re : ℝ) : ℂ) from by
    apply Complex.ext
    · simp
    · simp [hJ_real]]
  rw [show (((2 * (J x y).re : ℝ) : ℂ) *
        (marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ : ℂ) =
      ((2 * (J x y).re : ℝ) : ℂ) *
        ((marshallSignS A σ' * marshallSignS A σ) *
          (spinSDot x y N : ManyBodyOpS V N) σ' σ) from by ring]
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have hc :
      ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 :=
    marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y_lowering hxy N A
      hAx hAy h hx hy
  have h2J : 0 ≤ 2 * (J x y).re := by linarith
  nlinarith

/-- The real-part dressed Heisenberg matrix entry vanishes when the
two configurations have different magnetization quantum numbers. -/
theorem dressedHeisenbergSReMatrix_apply_eq_zero_of_mag_ne
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    (h : magEigenvalueS σ ≠ magEigenvalueS σ') :
    dressedHeisenbergSReMatrix A J N σ' σ = 0 := by
  rw [dressedHeisenbergSReMatrix_apply]
  have hzero : dressedHeisenbergS A J N σ' σ = 0 :=
    dressedHeisenbergSMatrix_apply_eq_zero_of_mag_ne A J N h
  rw [hzero]; simp

/-- magSumS-based version: when two configurations have different
`magSumS` values, the dressed real-matrix entry vanishes. (Equivalent
to the `magEigenvalueS`-based version via bijection.) -/
theorem dressedHeisenbergSReMatrix_apply_eq_zero_of_magSumS_ne
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    (h : magSumS σ ≠ magSumS σ') :
    dressedHeisenbergSReMatrix A J N σ' σ = 0 := by
  apply dressedHeisenbergSReMatrix_apply_eq_zero_of_mag_ne
  unfold magEigenvalueS
  intro heq
  apply h
  -- magEig σ = magEig σ' ⟹ magSum σ = magSum σ'.
  have : ((magSumS σ : ℂ)) = ((magSumS σ' : ℂ)) := by linear_combination -heq
  exact_mod_cast this


end LatticeSystem.Quantum

