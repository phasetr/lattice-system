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
