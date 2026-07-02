import LatticeSystem.Quantum.SpinS.DressedHeisenberg

/-!
# Marshall-dressed Heisenberg: building-block lemmas (foundation)

Foundational layer extracted from `DressedHeisenbergMarshall.lean` for build speed.
This file collects the per-pair Marshall-dressed `(Ŝ_x · Ŝ_y)` sign lemmas
(`marshallSignS_mul_spinSDot_apply_re_nonpos_bipartite_{x,y}` raising/lowering), the
one-site/three-site vanishing lemmas across operator/complex-matrix/real-matrix forms,
the `dressedHeisenbergSReMatrix` additivity / Hermiticity (chain, periodic chain) lemmas,
and the real↔complex matrix conversions.

The assembled `dressedHeisenbergS_apply_re_nonpos_bipartite_*` sign results and the
magnetization-sector vanishing of `dressedHeisenbergSReMatrix` are kept in the capstone
module `DressedHeisenbergMarshall.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §2.5 (Marshall–Lieb–Mattis, Marshall sign transformation).
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

end LatticeSystem.Quantum
