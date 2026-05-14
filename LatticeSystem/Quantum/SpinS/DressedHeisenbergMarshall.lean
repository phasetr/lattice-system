import LatticeSystem.Quantum.SpinS.DressedHeisenberg

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

/-! ## Marshall-dressed `(Ŝ_x · Ŝ_y)` on bipartite raising/lowering pairs -/

/-- **Bipartite Marshall dressing makes the off-diagonal `Ŝ_x · Ŝ_y`
matrix element non-positive**: for `x ∈ A`, `y ∉ A`, configurations
`σ', σ` agreeing off `{x, y}` with the raising shift at `x`
(`σ_x = σ'_x + 1`) and lowering shift at `y` (`σ_y + 1 = σ'_y`), the
dressed spinSDot real part `(marshallSignS A σ' * marshallSignS A σ) *
(Ŝ_x · Ŝ_y) σ' σ` is non-positive.

The Marshall sign factor is `-1` (PR #772), the off-diagonal entry
is positive (PR #781), so the product is non-positive. This is the
key non-positivity needed for the Marshall sign trick (Tasaki Theorem 2.2). -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ' x).val + 1 = (σ x).val)
    (_hy : (σ y).val + 1 = (σ' y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  -- Marshall sign factor: bipartite raising at x with A x = true gives -1.
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy h
    -- Need: Odd ((σ' x).val + (σ x).val).
    rw [show (σ x).val = (σ' x).val + 1 from hx.symm]
    rw [show (σ' x).val + ((σ' x).val + 1) = 2 * (σ' x).val + 1 from by ring]
    exact ⟨(σ' x).val, rfl⟩
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_x hxy N h hx

/-- Symmetric: lowering at `x` direction. -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_x_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = true) (hAy : A y = false)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (_hy : (σ' y).val + 1 = (σ y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_x A hxy hAx hAy h
    rw [show (σ' x).val = (σ x).val + 1 from hx.symm]
    rw [show (σ x).val + 1 + (σ x).val = 2 * (σ x).val + 1 from by ring]
    exact ⟨(σ x).val, rfl⟩
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_y hxy N h hx

/-- The dressed Heisenberg matrix vanishes on one-site differences.
Direct corollary: dressed = sign × sign × H, and H vanishes there. -/
theorem dressedHeisenbergS_apply_eq_zero_of_one_site_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z : V} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_apply_eq_zero_of_one_site_diff
    (Λ := V) J N hagree hz]
  ring

/-- The dressed Heisenberg matrix (as a `ManyBodyOpS`) vanishes on
one-site differences. -/
theorem dressedHeisenbergSMatrix_apply_eq_zero_of_one_site_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z : V} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    dressedHeisenbergSMatrix A J N σ' σ = 0 :=
  dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N hagree hz

/-- The real-part dressed Heisenberg matrix vanishes on one-site
differences. -/
theorem dressedHeisenbergSReMatrix_apply_eq_zero_of_one_site_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z : V} (hagree : ∀ k, k ≠ z → σ' k = σ k) (hz : σ' z ≠ σ z) :
    dressedHeisenbergSReMatrix A J N σ' σ = 0 := by
  rw [dressedHeisenbergSReMatrix_apply,
    dressedHeisenbergS_apply_eq_zero_of_one_site_diff A J N hagree hz]
  simp

/-- Dressed Heisenberg matrix vanishes on three-site differences. -/
theorem dressedHeisenbergS_apply_eq_zero_of_three_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z₁ z₂ z₃ : V}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    dressedHeisenbergS A J N σ' σ = 0 := by
  unfold dressedHeisenbergS
  rw [heisenbergHamiltonianS_apply_eq_zero_of_three_diff (Λ := V) J N
    h12 h13 h23 hz1 hz2 hz3]
  ring

/-- Dressed Heisenberg `Matrix` vanishes on three-site differences. -/
theorem dressedHeisenbergSMatrix_apply_eq_zero_of_three_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z₁ z₂ z₃ : V}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    dressedHeisenbergSMatrix A J N σ' σ = 0 :=
  dressedHeisenbergS_apply_eq_zero_of_three_diff A J N h12 h13 h23 hz1 hz2 hz3

/-- Real-part dressed Heisenberg matrix vanishes on three-site differences. -/
theorem dressedHeisenbergSReMatrix_apply_eq_zero_of_three_diff
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    {σ' σ : V → Fin (N + 1)}
    {z₁ z₂ z₃ : V}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (hz1 : σ' z₁ ≠ σ z₁) (hz2 : σ' z₂ ≠ σ z₂) (hz3 : σ' z₃ ≠ σ z₃) :
    dressedHeisenbergSReMatrix A J N σ' σ = 0 := by
  rw [dressedHeisenbergSReMatrix_apply,
    dressedHeisenbergS_apply_eq_zero_of_three_diff A J N
      h12 h13 h23 hz1 hz2 hz3]
  simp

/-- Symmetric: bipartite case `x ∉ A, y ∈ A`, raising at `x`. -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (_hx : (σ' x).val + 1 = (σ x).val)
    (hy : (σ y).val + 1 = (σ' y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy h
    rw [show (σ' y).val = (σ y).val + 1 from hy.symm]
    rw [show (σ y).val + 1 + (σ y).val = 2 * (σ y).val + 1 from by ring]
    exact ⟨(σ y).val, rfl⟩
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_x hxy N h _hx

/-- Mirror of `marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y`:
bipartite case `x ∉ A, y ∈ A`, but lowering at `y` and raising at `x`. -/
theorem marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_y_lowering
    {x y : V} (hxy : x ≠ y) (N : ℕ)
    (A : V → Bool) (hAx : A x = false) (hAy : A y = true)
    {σ' σ : V → Fin (N + 1)}
    (h : ∀ k, k ≠ x → k ≠ y → σ' k = σ k)
    (hx : (σ x).val + 1 = (σ' x).val)
    (_hy : (σ' y).val + 1 = (σ y).val) :
    ((marshallSignS A σ' * marshallSignS A σ) *
        (spinSDot x y N : ManyBodyOpS V N) σ' σ).re ≤ 0 := by
  have hsign : marshallSignS A σ' * marshallSignS A σ = -1 := by
    apply marshallSignS_mul_of_agree_off_two_site_bipartite_y A hxy hAx hAy h
    rw [show (σ' y).val = (σ y).val - 1 from by omega]
    rw [show (σ y).val - 1 + (σ y).val = 2 * (σ y).val - 1 from by omega]
    -- Need: Odd (2 * (σ y).val - 1).
    rcases (σ y).val.eq_zero_or_pos with hzero | hpos
    · -- (σ y).val = 0 forces (σ' y).val + 1 = 0, impossible.
      exfalso
      rw [hzero] at _hy
      omega
    · refine ⟨(σ y).val - 1, ?_⟩
      omega
  rw [hsign]
  rw [show ((-1 : ℂ) * (spinSDot x y N : ManyBodyOpS V N) σ' σ).re =
        -((spinSDot x y N : ManyBodyOpS V N) σ' σ).re from by
    rw [Complex.mul_re]
    simp]
  rw [neg_nonpos]
  exact spinSDot_apply_re_nonneg_of_raising_lowering_y hxy N h hx

/-- The real-part dressed Heisenberg matrix is additive in the
coupling. -/
theorem dressedHeisenbergSReMatrix_add_J
    (A : V → Bool) (J J' : V → V → ℂ) (N : ℕ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A (fun x y => J x y + J' x y) N σ σ' =
      dressedHeisenbergSReMatrix A J N σ σ' +
        dressedHeisenbergSReMatrix A J' N σ σ' := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_add_J]
  simp [dressedHeisenbergSReMatrix_apply]

/-- The real-part dressed Heisenberg matrix negates with the
coupling. -/
theorem dressedHeisenbergSReMatrix_neg_J
    (A : V → Bool) (J : V → V → ℂ) (N : ℕ)
    (σ σ' : V → Fin (N + 1)) :
    dressedHeisenbergSReMatrix A (fun x y => -(J x y)) N σ σ' =
      -(dressedHeisenbergSReMatrix A J N σ σ') := by
  rw [dressedHeisenbergSReMatrix_apply, dressedHeisenbergS_neg_J]
  simp [dressedHeisenbergSReMatrix_apply]

/-- For real coupling, the real-part dressed Heisenberg matrix is
Hermitian (which for a real-valued matrix is equivalent to
symmetry). -/
theorem dressedHeisenbergSReMatrix_isHermitian
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (dressedHeisenbergSReMatrix A J N).IsHermitian := by
  ext σ σ'
  simp only [Matrix.conjTranspose_apply, star_trivial]
  have h := dressedHeisenbergSReMatrix_isSymm A N hreal
  exact congrFun (congrFun h σ) σ'

/-- Real-part dressed Heisenberg matrix Hermiticity for a graph-derived
coupling. -/
theorem dressedHeisenbergSReMatrix_couplingOf_isHermitian
    (A : V → Bool) (G : SimpleGraph V) [DecidableRel G.Adj]
    {J : ℂ} (hJ : star J = J) (N : ℕ) :
    (dressedHeisenbergSReMatrix A
        (LatticeSystem.Lattice.couplingOf G J) N).IsHermitian :=
  dressedHeisenbergSReMatrix_isHermitian A N
    (LatticeSystem.Lattice.couplingOf_real G hJ)

/-- Real-part dressed Heisenberg matrix on the open chain — Hermiticity. -/
theorem dressedHeisenbergSReMatrix_chain_isHermitian
    (M : ℕ) (A : Fin (M + 1) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSReMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.pathGraph (M + 1)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSReMatrix_couplingOf_isHermitian A _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

/-- Real-part dressed Heisenberg matrix on the periodic chain — Hermiticity. -/
theorem dressedHeisenbergSReMatrix_periodicChain_isHermitian
    (M : ℕ) (A : Fin (M + 2) → Bool) (J : ℝ) (N : ℕ) :
    (dressedHeisenbergSReMatrix A
        (LatticeSystem.Lattice.couplingOf
          (SimpleGraph.cycleGraph (M + 2)) (-(J : ℂ))) N).IsHermitian :=
  dressedHeisenbergSReMatrix_couplingOf_isHermitian A _
    (by simp : star (-(J : ℂ)) = -(J : ℂ)) N

/-- The complex dressed matrix entry equals the real-embedded
real-part: `dressed σ' σ = ((dressedRe σ' σ : ℝ) : ℂ)` for coupling
with real entries. -/
theorem dressedHeisenbergSMatrix_apply_eq_ofReal_re
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0)
    (σ' σ : V → Fin (N + 1)) :
    dressedHeisenbergSMatrix A J N σ' σ =
      ((dressedHeisenbergSReMatrix A J N σ' σ : ℝ) : ℂ) := by
  rw [dressedHeisenbergSReMatrix_apply]
  apply Complex.ext
  · rfl
  · rw [Complex.ofReal_im]
    exact dressedHeisenbergS_apply_im_zero A N hreal σ' σ

/-- Matrix-level equality: the complex dressed matrix equals the
ℂ-embedding of the real-valued dressed matrix entry-wise. -/
theorem dressedHeisenbergSMatrix_eq_dressedHeisenbergSReMatrix_complex
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ)
    (hreal : ∀ x y, (J x y).im = 0) :
    dressedHeisenbergSMatrix A J N =
      (dressedHeisenbergSReMatrix A J N).map (fun r : ℝ => (r : ℂ)) := by
  ext σ' σ
  rw [Matrix.map_apply, dressedHeisenbergSMatrix_apply_eq_ofReal_re A N hreal]

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

