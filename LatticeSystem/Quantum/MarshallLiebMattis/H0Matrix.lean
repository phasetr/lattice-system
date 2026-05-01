import LatticeSystem.Quantum.MarshallLiebMattis.Connectivity

/-!
# Real-valued dressed Heisenberg matrix on `H_0` (Tasaki §2.5 setup)

This module assembles the **real-valued matrix** to which Tasaki's
Perron–Frobenius proof of the Marshall–Lieb–Mattis theorem
(Theorem 2.2, §2.5) applies.

For a bipartite `(Λ, A)` with real symmetric non-negative coupling
`J : Λ → Λ → ℂ` supported on bipartite bonds, define on the
**zero-magnetisation index type**

  `H₀Index Λ := {σ : Λ → Fin 2 // magnetization Λ σ = 0}`

the matrix

  `dressedHeisenbergMatrixH0 A J σ τ
     := Re (marshallSignOf A σ.val · marshallSignOf A τ.val ·
            (heisenbergHamiltonian J) σ.val τ.val)`.

This file proves the two structural Marshall–Lieb–Mattis-relevant
properties of this matrix that follow directly from the previous
PRs:

* `dressedHeisenbergMatrixH0_isSymm` — the matrix is **symmetric**:
  `M σ τ = M τ σ` (consequence of Hermiticity of the Heisenberg
  Hamiltonian + realness for real symmetric `J`).
* `dressedHeisenbergMatrixH0_offdiag_nonpos` — **off-diagonal
  entries are non-positive**: `σ ≠ τ ⇒ M σ τ ≤ 0` (the Marshall
  sign trick, PR α-3).

The remaining PR α-5b will:

* upgrade non-positivity into the non-negativity of `c · I − M` for
  large enough `c`,
* prove irreducibility of `c · I − M` from the swap-connectivity of
  PR α-4,
* apply Perron–Frobenius (`Math.PerronFrobenius`) to conclude that
  the antiferromagnetic Heisenberg ground state in `H_0` admits a
  unique expansion `Σ_σ c_σ |Ψ̃^σ⟩` with `c_σ > 0` (Tasaki (2.5.4)).

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41 (proof of Theorem 2.2).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Index type for the zero-magnetisation subspace `H_0` -/

/-- The zero-magnetisation index type: configurations
`σ : Λ → Fin 2` with total magnetization `0`. -/
def H₀Index (Λ : Type*) [Fintype Λ] : Type _ :=
  {σ : Λ → Fin 2 // magnetization Λ σ = 0}

instance : Fintype (H₀Index Λ) :=
  Subtype.fintype _

instance : DecidableEq (H₀Index Λ) :=
  fun _ _ => Subtype.instDecidableEq _ _

/-! ## The real dressed Heisenberg matrix on `H_0` -/

/-- The real-valued matrix entry indexed by zero-magnetisation
configurations:

  `M σ τ := Re (marshallSignOf A σ · marshallSignOf A τ · (H_J)_{σ,τ})`.

By PR α-2 (Property (i)), the complex value inside `Re` is real;
by PR α-3 (Property (ii)), for `σ ≠ τ` it is `≤ 0`. -/
noncomputable def dressedHeisenbergMatrixH0 (A : Λ → Bool)
    (J : Λ → Λ → ℂ) :
    Matrix (H₀Index Λ) (H₀Index Λ) ℝ :=
  fun σ τ =>
    (marshallSignOf A σ.val * marshallSignOf A τ.val *
      (heisenbergHamiltonian J) σ.val τ.val).re

/-! ## Symmetry -/

/-- Helper: for a real symmetric Hermitian matrix entry,
the entries are equal (no conjugation needed). -/
private theorem heisenberg_apply_symm_of_real_symm
    {J : Λ → Λ → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x)
    (σ τ : Λ → Fin 2) :
    (heisenbergHamiltonian J) σ τ = (heisenbergHamiltonian J) τ σ := by
  -- Hermiticity: (H τ σ).conj = H σ τ.
  have hJstar : ∀ x y, star (J x y) = J x y := by
    intro x y
    apply Complex.ext
    · rw [Complex.star_def, Complex.conj_re]
    · rw [Complex.star_def, Complex.conj_im, hJ_real x y, neg_zero]
  have hherm : (heisenbergHamiltonian J).IsHermitian :=
    heisenbergHamiltonian_isHermitian_of_real_symm hJstar hJ_symm
  -- IsHermitian: M.conjTranspose = M ⇒ M σ τ = star (M τ σ).
  have h1 : (heisenbergHamiltonian J) σ τ =
      star ((heisenbergHamiltonian J) τ σ) := by
    have := congrFun (congrFun hherm σ) τ
    -- this : M.conjTranspose σ τ = M σ τ
    -- M.conjTranspose σ τ = star (M τ σ)
    rw [Matrix.conjTranspose_apply] at this
    exact this.symm
  -- For real entries: star a = a when a.im = 0.
  have h2 : star ((heisenbergHamiltonian J) τ σ) =
      (heisenbergHamiltonian J) τ σ := by
    apply Complex.ext
    · rw [Complex.star_def, Complex.conj_re]
    · rw [Complex.star_def, Complex.conj_im,
          heisenbergHamiltonian_apply_im_eq_zero hJ_real, neg_zero]
  rw [h1, h2]

/-- The dressed Heisenberg matrix on `H_0` is **symmetric**:
`M σ τ = M τ σ` for any zero-magnetisation configurations
`σ, τ`.

Follows from Hermiticity of the Heisenberg Hamiltonian (proven for
real symmetric `J` in `heisenbergHamiltonian_isHermitian_of_real_symm`)
combined with the realness of matrix entries (PR α-2,
`heisenbergHamiltonian_apply_im_eq_zero`). The Marshall sign
factors commute and are themselves real, so the dressed product
preserves the symmetry. -/
theorem dressedHeisenbergMatrixH0_isSymm (A : Λ → Bool)
    {J : Λ → Λ → ℂ} (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_symm : ∀ x y, J x y = J y x) :
    (dressedHeisenbergMatrixH0 (Λ := Λ) A J).IsSymm := by
  ext σ τ
  unfold dressedHeisenbergMatrixH0
  rw [Matrix.transpose_apply,
      heisenberg_apply_symm_of_real_symm hJ_real hJ_symm σ.val τ.val]
  congr 1
  ring

/-! ## Off-diagonal non-positivity -/

/-- The dressed Heisenberg matrix on `H_0` has **non-positive
off-diagonal entries**: for `σ ≠ τ`, `M σ τ ≤ 0`.

Follows from the Marshall sign trick (PR α-3,
`bond_dressed_contribution_re_nonpos`) summed over bonds, and
unwrapped from the bilinear-pairing form to the matrix-entry form
via `dot_marshallDressed_mulVec_marshallDressed_eq`. -/
theorem dressedHeisenbergMatrixH0_offdiag_nonpos (A : Λ → Bool)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    {σ τ : H₀Index Λ} (hne : σ ≠ τ) :
    dressedHeisenbergMatrixH0 A J σ τ ≤ 0 := by
  unfold dressedHeisenbergMatrixH0
  -- Convert Subtype inequality to underlying inequality.
  have hne_val : σ.val ≠ τ.val := fun heq => hne (Subtype.ext heq)
  -- Use the bilinear pairing formula in PR α-3.
  -- Σ_τ' marshallDressedBasis A σ τ' * (H · marshallDressedBasis A τ) τ'
  --   = marshallSignOf A σ.val * marshallSignOf A τ.val * H σ.val τ.val.
  have hbilin :=
    dot_marshallDressed_heisenbergHamiltonian_marshallDressed_re_nonpos_of_ne
      A hJ_real hJ_nn hJ_bipartite hne_val
  -- The factorisation gives the same complex value as the matrix entry.
  rw [show
      (∑ ρ : Λ → Fin 2,
        marshallDressedBasis A σ.val ρ *
          ((heisenbergHamiltonian J).mulVec
            (marshallDressedBasis A τ.val)) ρ) =
      marshallSignOf A σ.val * marshallSignOf A τ.val *
        (heisenbergHamiltonian J) σ.val τ.val from
    dot_marshallDressed_mulVec_marshallDressed_eq A
      (heisenbergHamiltonian J) σ.val τ.val] at hbilin
  exact hbilin

/-! ## Diagonal entries are real (no further constraint) -/

/-- The dressed Heisenberg matrix on `H_0` has real diagonal
entries (always, by PR α-2 Property (i)). The actual value depends
on the operator and is computed in PR α-5b when needed. -/
theorem dressedHeisenbergMatrixH0_diag_eq_re (A : Λ → Bool)
    (J : Λ → Λ → ℂ) (σ : H₀Index Λ) :
    dressedHeisenbergMatrixH0 A J σ σ =
      (marshallSignOf A σ.val * marshallSignOf A σ.val *
        (heisenbergHamiltonian J) σ.val σ.val).re := rfl

end LatticeSystem.Quantum
