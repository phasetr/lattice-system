import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall

/-!
# Eigenvalue uniqueness for the dressed / Heisenberg sector matrices
(build-speed companion)

Build-speed companion to `DressedMatrixOnMagSector.lean`. Hosts the
trailing section "Eigenvalue uniqueness (positive eigenvectors
share the same eigenvalue)" plus the downstream Marshall-positive
complex-eigenvector uniqueness theorems and the final full-MLM
statement on the Heisenberg sector (originally lines 867..1145 of
the parent file).

Splitting these blocks out drops the parent from ~1145 lines to
~865 lines. `MagSectorEmbedding.lean` (the sole external
consumer of the moved theorems) updated to additionally import
this companion.

References:
- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5 Theorem 2.2 (Marshall–Lieb–Mattis),
  pp. 39–43.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Eigenvalue uniqueness (positive eigenvectors share the same eigenvalue) -/

/-- The dressed Heisenberg sector matrix is symmetric (lifted from the
symmetry of the full dressed Heisenberg matrix via `IsSymm.submatrix`). -/
theorem dressedHeisenbergSReMatrixOnMagSector_isSymm
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (M : ℕ)
    (hreal : ∀ x y, star (J x y) = J x y) :
    (dressedHeisenbergSReMatrixOnMagSector A J N M).IsSymm :=
  (dressedHeisenbergSReMatrix_isSymm A N hreal).submatrix Subtype.val

/-- **Eigenvalue uniqueness for symmetric matrices on positive
eigenvectors**: for a real symmetric matrix `A` over `ℝ`, two strictly
positive eigenvectors with eigenvalues `μ` and `ν` must satisfy `μ = ν`.

Proof: by symmetry `⟨v, A w⟩ = ⟨A v, w⟩`, hence `μ ⟨v, w⟩ = ν ⟨v, w⟩`,
and `⟨v, w⟩ > 0` (positive componentwise sum), so `μ = ν`. -/
theorem pos_eigenvec_eigenvalue_unique_of_isSymm
    {n : Type*} [Fintype n] [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsSymm)
    {μ ν : ℝ} {v w : n → ℝ}
    (hv : A.mulVec v = μ • v) (hv_pos : ∀ i, 0 < v i)
    (hw : A.mulVec w = ν • w) (hw_pos : ∀ i, 0 < w i) :
    μ = ν := by
  have h_inner_pos : 0 < v ⬝ᵥ w := by
    refine Finset.sum_pos (fun i _ => mul_pos (hv_pos i) (hw_pos i))
      Finset.univ_nonempty
  -- ⟨v, A w⟩ = ν * (v ⬝ᵥ w).
  have h_right : v ⬝ᵥ A.mulVec w = ν * (v ⬝ᵥ w) := by
    rw [hw, dotProduct_smul, smul_eq_mul]
  -- ⟨v, A w⟩ = ⟨A v, w⟩ by symmetry, then = μ * (v ⬝ᵥ w).
  have hsym : Matrix.vecMul v A = A.mulVec v := by
    funext i
    change ∑ j, v j * A j i = ∑ j, A i j * v j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have hAji : A j i = A i j := by
      have hT : A.transpose = A := hA
      have h := congrFun (congrFun hT i) j
      change A j i = A i j at h
      exact h
    rw [hAji, mul_comm]
  have h_left : v ⬝ᵥ A.mulVec w = μ * (v ⬝ᵥ w) := by
    rw [Matrix.dotProduct_mulVec, hsym, hv, smul_dotProduct, smul_eq_mul]
  have h_eq : μ * (v ⬝ᵥ w) = ν * (v ⬝ᵥ w) := by
    rw [← h_left, h_right]
  exact mul_right_cancel₀ (ne_of_gt h_inner_pos) h_eq

/-- **Eigenvalue uniqueness for the dressed Heisenberg sector matrix**:
any two strictly positive eigenvectors with eigenvalues `μ₁, μ₂` must
satisfy `μ₁ = μ₂`. (The dressed sector matrix is symmetric and admits
positive eigenvectors only at the unique Perron eigenvalue.) -/
theorem pos_eigenvec_eigenvalue_unique_dressedHeisenbergSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, star (J x y) = J x y)
    {μ₁ μ₂ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec v = μ₁ • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec w = μ₂ • w)
    (hw_pos : ∀ σ, 0 < w σ) :
    μ₁ = μ₂ :=
  pos_eigenvec_eigenvalue_unique_of_isSymm
    (dressedHeisenbergSReMatrixOnMagSector_isSymm A N M hJ_real)
    hv hv_pos hw hw_pos

/-- **Upper bound from a positive Perron vector**: if a non-negative
symmetric real matrix has a strictly positive eigenvector at eigenvalue
`r`, then every real eigenvalue `s` is bounded above by `r`.

This is the elementary Collatz-Wielandt comparison used to turn the
positive Perron vector of the shifted dressed matrix into a lower bound
for the corresponding dressed/Heisenberg eigenvalues. -/
theorem eigenvalue_le_of_nonnegative_isSymm_of_positive_eigenvec
    {n : Type*} [Fintype n] [Nonempty n]
    {B : Matrix n n ℝ}
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hB_symm : B.IsSymm)
    {r s : ℝ} {v w : n → ℝ}
    (hv_pos : ∀ i, 0 < v i)
    (hv : B.mulVec v = r • v)
    (hw_ne : w ≠ 0)
    (hw : B.mulVec w = s • w) :
    s ≤ r := by
  classical
  have hr_nonneg : 0 ≤ r := by
    have hrow_nonneg : 0 ≤ B.mulVec v (Classical.arbitrary n) := by
      change 0 ≤ ∑ j, B (Classical.arbitrary n) j * v j
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hB_nonneg _ j) (le_of_lt (hv_pos j))
    have hrow := congrFun hv (Classical.arbitrary n)
    change B.mulVec v (Classical.arbitrary n) = r * v (Classical.arbitrary n) at hrow
    nlinarith [hv_pos (Classical.arbitrary n)]
  by_cases hs_nonpos : s ≤ 0
  · exact hs_nonpos.trans hr_nonneg
  have hs_pos : 0 < s := lt_of_not_ge hs_nonpos
  let y : n → ℝ := fun i => |w i|
  have hy_nonneg : ∀ i, 0 ≤ y i := fun i => abs_nonneg (w i)
  have hy_ne : y ≠ 0 := by
    intro hy_zero
    apply hw_ne
    funext i
    have hi := congrFun hy_zero i
    exact abs_eq_zero.mp hi
  have hy_pos_some : ∃ i, 0 < y i := by
    by_contra hnone
    simp only [not_exists, not_lt] at hnone
    exact hy_ne (funext fun i => le_antisymm (hnone i) (hy_nonneg i))
  have hBy_ge : ∀ i, s * y i ≤ B.mulVec y i := by
    intro i
    have hrow_abs : |B.mulVec w i| ≤ B.mulVec y i := by
      calc
        |B.mulVec w i| = |∑ j, B i j * w j| := by rfl
        _ ≤ ∑ j, |B i j * w j| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j, B i j * y j := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [abs_mul, abs_of_nonneg (hB_nonneg i j)]
        _ = B.mulVec y i := by rfl
    have hrow := congrFun hw i
    change B.mulVec w i = s * w i at hrow
    calc
      s * y i = |s * w i| := by
        rw [abs_mul, abs_of_pos hs_pos]
      _ = |B.mulVec w i| := by rw [hrow]
      _ ≤ B.mulVec y i := hrow_abs
  have hdot_pos : 0 < v ⬝ᵥ y := by
    refine Finset.sum_pos' (fun i _ => mul_nonneg (le_of_lt (hv_pos i)) (hy_nonneg i)) ?_
    obtain ⟨i, hi⟩ := hy_pos_some
    exact ⟨i, Finset.mem_univ i, mul_pos (hv_pos i) hi⟩
  have hweighted_le : s * (v ⬝ᵥ y) ≤ v ⬝ᵥ B.mulVec y := by
    calc
      s * (v ⬝ᵥ y) = ∑ i, v i * (s * y i) := by
        rw [dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
      _ ≤ ∑ i, v i * B.mulVec y i := by
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (hBy_ge i) (le_of_lt (hv_pos i))
      _ = v ⬝ᵥ B.mulVec y := by rfl
  have hsym_vec : Matrix.vecMul v B = B.mulVec v := by
    funext i
    change ∑ j, v j * B j i = ∑ j, B i j * v j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hB_symm.apply i j, mul_comm]
  have hweighted_eq : v ⬝ᵥ B.mulVec y = r * (v ⬝ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, hsym_vec, hv, smul_dotProduct, smul_eq_mul]
  nlinarith [hweighted_le, hweighted_eq, hdot_pos]

/-- **Shifted dressed-sector eigenvalue upper bound**: the positive
eigenvector of the shifted dressed matrix gives an upper bound on all
real shifted-sector eigenvalues. -/
theorem shiftedDressedSReMatrixOnMagSector_eigenvalue_le_of_positive_eigenvec
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {r s : ℝ} {v w : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ)
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v)
    (hw_ne : w ≠ 0)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = s • w) :
    s ≤ r := by
  have hB_nonneg :
      ∀ σ τ,
        0 ≤ shiftedDressedSReMatrixOnMagSector A J N c M σ τ :=
    shiftedDressedSReMatrixOnMagSector_nonneg A N c M hJ_real hJ_nn hJ_sym
      hJ_bipartite (fun σ => le_of_lt (hc_strict σ))
  have hB_symm :
      (shiftedDressedSReMatrixOnMagSector A J N c M).IsSymm := by
    rw [shiftedDressedSReMatrixOnMagSector_eq_smul_sub_dressed]
    exact ((Matrix.isSymm_one (n := magConfigS V N M)).smul c).sub
      (dressedHeisenbergSReMatrixOnMagSector_isSymm A N M hJ_real')
  exact eigenvalue_le_of_nonnegative_isSymm_of_positive_eigenvec
    hB_nonneg hB_symm hv_pos hv hw_ne hw

/-- **Real-sector spectral lower bound from a Marshall-positive sector
ground state**: if a sector contains a Marshall-positive real eigenvector
at energy `μ`, then every real eigenvalue in that sector is at least
`μ`.

The proof Marshall-conjugates to the dressed matrix, shifts by `c`, and
applies the positive-eigenvector upper bound to the non-negative shifted
dressed matrix. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ μ' : ℝ} {w φ : magConfigS V N M → ℝ}
    (hw : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w)
    (hw_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w σ)
    (hφ_ne : φ ≠ 0)
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ) :
    μ ≤ μ' := by
  let wD : magConfigS V N M → ℝ := fun σ => (marshallSignS A σ.1).re * w σ
  let φD : magConfigS V N M → ℝ := fun σ => (marshallSignS A σ.1).re * φ σ
  have hwD_pos : ∀ σ, 0 < wD σ := hw_marshall_pos
  have hwD_dressed :
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec wD = μ • wD := by
    exact dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
      A N hJ_real hw
  have hφD_ne : φD ≠ 0 := by
    intro hzero
    apply hφ_ne
    funext σ
    have hσ := congrFun hzero σ
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    dsimp [φD] at hσ
    calc
      φ σ = 1 * φ σ := by ring
      _ = ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * φ σ := by rw [hsq]
      _ = (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * φ σ) := by ring
      _ = 0 := by rw [hσ, mul_zero]
  have hφD_dressed :
      (dressedHeisenbergSReMatrixOnMagSector A J N M).mulVec φD = μ' • φD := by
    exact dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
      A N hJ_real hφ
  have hwD_shifted :
      (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec wD = (c - μ) • wD :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c hwD_dressed
  have hφD_shifted :
      (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec φD = (c - μ') • φD :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c hφD_dressed
  have hle : c - μ' ≤ c - μ :=
    shiftedDressedSReMatrixOnMagSector_eigenvalue_le_of_positive_eigenvec
      A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hwD_pos hwD_shifted hφD_ne hφD_shifted
  linarith

/-- **Eigenvalue uniqueness for the Heisenberg sector matrix on
Marshall-positive eigenvectors** (Tasaki §2.5 Theorem 2.2 strengthening):
any two real eigenvectors with strictly positive Marshall conjugates
must have the same eigenvalue.

Reduction: by inverse Marshall conjugation (PR #854), the conjugates
`sign · w_i` are positive eigenvectors of the dressed sector matrix
with the same eigenvalues as the heis sector eigenvectors. By dressed
sector eigenvalue uniqueness (this PR) the eigenvalues coincide. -/
theorem marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    {μ₁ μ₂ : ℝ} {w₁ w₂ : magConfigS V N M → ℝ}
    (hw₁ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₁ = μ₁ • w₁)
    (hw₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₁ σ)
    (hw₂ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w₂ = μ₂ • w₂)
    (hw₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * w₂ σ) :
    μ₁ = μ₂ := by
  -- Marshall-conjugate both: vᵢ := sign · wᵢ are dressed positive eigenvectors at μᵢ.
  have hv₁ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₁
  have hv₂ := dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec
    A N hJ_real hw₂
  exact pos_eigenvec_eigenvalue_unique_dressedHeisenbergSReMatrixOnMagSector
    A N hJ_real' hv₁ hw₁_marshall_pos hv₂ hw₂_marshall_pos

/-- **Tasaki §2.5 Theorem 2.2 ground-state existence on the complex
Heisenberg sector matrix**: the un-dressed complex Heisenberg
Hamiltonian, restricted to the magnetization-`M` sector, admits a
strictly Marshall-positive complex ground-state eigenvector

  `Φ σ := ((sign A σ.1).re * v σ : ℂ)`

(real-valued, equal to a positive function of `σ` times the Marshall
sign at `σ`) at some real eigenvalue `μ < c`.

Composition of:
- `exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`
  (PR #853, real-form existence).
- `heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal`
  (PR #858, real → complex eigenvector lift). -/
theorem exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) =
        (μ : ℂ) • (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨μ, v, hμ, hv_pos, hmul⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  exact ⟨μ, v, hμ, hv_pos,
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal N hJ_real hmul⟩

/-- **Real part extraction**: for real coupling, the real part of a
complex eigenvector of the complex Heisenberg sector matrix at a real
eigenvalue `μ` is a real eigenvector of the real-form sector matrix at
the same `μ`.

This is the inverse of `heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal`
(PR #858) and gives a complete real-↔-complex correspondence on the
sector for real coupling. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {W : magConfigS V N M → ℂ}
    (hW : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W =
      (μ : ℂ) • W) :
    (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
      (fun σ => (W σ).re) = μ • (fun σ => (W σ).re) := by
  funext σ
  have hσ := congrFun hW σ
  -- Take real parts of both sides of hσ.
  have hRe_eq : ((heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W σ).re =
      (((μ : ℂ) • W) σ).re := by rw [hσ]
  -- LHS: Re(∑τ heis_C σ τ * W τ) = ∑τ heis_re σ τ * (W τ).re.
  have hLHS : ((heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W σ).re =
      ∑ τ, heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ * (W τ).re := by
    change (∑ τ, heisenbergHamiltonianSMatrixOnMagSector J N M σ τ * W τ).re = _
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal _ _ hJ_real]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  -- RHS: Re(μ • W σ) = μ * (W σ).re.
  have hRHS : (((μ : ℂ) • W) σ).re = μ * (W σ).re := by
    change ((μ : ℂ) * W σ).re = _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hLHS, hRHS] at hRe_eq
  change (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
    (fun σ => (W σ).re) σ = μ * (W σ).re
  exact hRe_eq

/-- **Imaginary part extraction**: for real coupling, the imaginary part of
a complex eigenvector of the complex Heisenberg sector matrix at a real
eigenvalue `μ` is a real eigenvector of the real-form sector matrix at
the same `μ`.

Together with
`heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec`,
this reduces arbitrary complex sector eigenvectors to real sector
eigenvectors componentwise. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
    {J : V → V → ℂ} (N : ℕ) {M : ℕ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    {μ : ℝ} {W : magConfigS V N M → ℂ}
    (hW : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W =
      (μ : ℂ) • W) :
    (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
      (fun σ => (W σ).im) = μ • (fun σ => (W σ).im) := by
  funext σ
  have hσ := congrFun hW σ
  have hIm_eq : ((heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W σ).im =
      (((μ : ℂ) • W) σ).im := by rw [hσ]
  have hLHS : ((heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W σ).im =
      ∑ τ, heisenbergHamiltonianSReMatrixOnMagSector J N M σ τ * (W τ).im := by
    change (∑ τ, heisenbergHamiltonianSMatrixOnMagSector J N M σ τ * W τ).im = _
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    rw [heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal _ _ hJ_real]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hRHS : (((μ : ℂ) • W) σ).im = μ * (W σ).im := by
    change ((μ : ℂ) * W σ).im = _
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hLHS, hRHS] at hIm_eq
  change (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
    (fun σ => (W σ).im) σ = μ * (W σ).im
  exact hIm_eq

/-- **Complex-form uniqueness for Marshall-positive eigenvectors of the
real-coupling complex Heisenberg sector matrix at real eigenvalues**:
any two complex sector eigenvectors `W₁, W₂` with strictly positive
Marshall-conjugated real parts share the same eigenvalue (`μ₁ = μ₂`)
and their real parts are positive scalar multiples of each other.

Proof: extract real parts via PR #861 to reduce to the real-form
Marshall-positive uniqueness theorems (PRs #854, #856). -/
theorem marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ₁ μ₂ : ℝ} {W₁ W₂ : magConfigS V N M → ℂ}
    (hW₁ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W₁ =
      (μ₁ : ℂ) • W₁)
    (hW₁_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * (W₁ σ).re)
    (hW₂ : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W₂ =
      (μ₂ : ℂ) • W₂)
    (hW₂_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * (W₂ σ).re) :
    μ₁ = μ₂ ∧ ∃ r : ℝ, 0 < r ∧
      ∀ σ, (W₂ σ).re = r * (W₁ σ).re := by
  -- Extract real parts → real-form sector eigenvectors at μᵢ.
  have hW₁_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hW₁
  have hW₂_re :=
    heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
      N hJ_real hW₂
  -- Eigenvalue uniqueness for Marshall-positive heis_sec eigenvectors.
  have hμ_eq : μ₁ = μ₂ :=
    marshallPositive_eigenvec_eigenvalue_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N hJ_real hJ_real' hW₁_re hW₁_marshall_pos hW₂_re hW₂_marshall_pos
  refine ⟨hμ_eq, ?_⟩
  subst hμ_eq
  -- Same-eigenvalue eigenvector uniqueness on heis_sec.
  obtain ⟨r, hr_pos, hrel⟩ :=
    marshallPositive_eigenvec_unique_heisenbergHamiltonianSReMatrixOnMagSector
      A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate
      hW₁_re hW₁_marshall_pos hW₂_re hW₂_marshall_pos
  exact ⟨r, hr_pos, fun σ => congrFun hrel σ⟩

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis), strongest
ground-state form on the COMPLEX sector matrix**: bundles complex
existence (PR #860) with complex Marshall-positive uniqueness
(PR #862). The COMPLEX-Hilbert-space form of Tasaki §2.5 Theorem 2.2:
the ground state of the un-dressed quantum Heisenberg Hamiltonian
restricted to the magnetization sector is unique (up to a positive
real scalar in its real part) and has the Marshall sign structure
`Φ σ := ((sign A σ.1).re * v σ : ℂ)` with `v > 0`. -/
theorem marshallLiebMattis_spinS_heisenbergSector_complexGroundState_full
    (A : V → Bool)
    {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N) :
    ∃ (μ : ℝ) (v : magConfigS V N M → ℝ),
      μ < c ∧ (∀ σ, 0 < v σ) ∧
      (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) =
        (μ : ℂ) • (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) ∧
      (∀ {μ' : ℝ} {W : magConfigS V N M → ℂ},
        (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W = (μ' : ℂ) • W →
        (∀ σ, 0 < (marshallSignS A σ.1).re * (W σ).re) →
        μ' = μ ∧ ∃ r : ℝ, 0 < r ∧
          ∀ σ, (W σ).re = r * ((marshallSignS A σ.1).re * v σ)) := by
  obtain ⟨μ, v, hμ_lt, hv_pos, hmul⟩ :=
    exists_marshallSign_complexEigenvector_heisenbergHamiltonianSMatrixOnMagSector
      (M := M) A N c hJ_real hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate
  refine ⟨μ, v, hμ_lt, hv_pos, hmul, ?_⟩
  intro μ' W hW hW_marshall_pos
  have hΦ_marshall_pos : ∀ σ, 0 < (marshallSignS A σ.1).re *
      ((fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) σ).re := fun σ => by
    change 0 < (marshallSignS A σ.1).re *
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ).re
    rw [Complex.ofReal_re]
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    rw [← mul_assoc, hsq, one_mul]
    exact hv_pos σ
  obtain ⟨hμ_eq, r, hr_pos, hrel⟩ :=
    marshallPositive_complexEigenvec_re_unique_heisenbergHamiltonianSMatrixOnMagSector
      A N c hJ_real hJ_real' hJ_pos hJ_nn hJ_sym hJ_bipartite hc_strict
      h_intermediate hmul hΦ_marshall_pos hW hW_marshall_pos
  refine ⟨hμ_eq.symm, r, hr_pos, fun σ => ?_⟩
  have hΦ_re : (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ).re =
      (marshallSignS A σ.1).re * v σ := by rw [Complex.ofReal_re]
  rw [hrel σ, hΦ_re]

end LatticeSystem.Quantum
