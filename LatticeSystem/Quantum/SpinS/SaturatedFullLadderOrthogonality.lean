import LatticeSystem.Quantum.SpinS.SaturatedFullLadderLI
import LatticeSystem.Quantum.SpinS.TotalSpin

/-!
# Pairwise orthogonality of the saturated-ferromagnet ladder iterates

For `[Nonempty V]`, distinct iterates `(Ŝ^-_{tot})^i · |σ_⊤⟩` and
`(Ŝ^-_{tot})^j · |σ_⊤⟩` (for `i ≠ j` in `Fin (|V|·N + 1)`) are
orthogonal in the standard inner product
`⟨v, w⟩ := Σ_σ conj(v σ) · w σ`.

The proof is the standard "Hermitian operator → distinct-eigenvalue
eigenvectors are orthogonal" argument applied to `Ŝ^z_{tot}` (which
is Hermitian, PR via `totalSpinSOp3_isHermitian`):

  `(α : ℂ) · ⟨v, w⟩ = ⟨Ŝ^z v, w⟩ = ⟨v, Ŝ^z w⟩ = β · ⟨v, w⟩`,

where `α = m_max − i` and `β = m_max − j` are the eigenvalues, both
real (being differences of natural-number casts in ℂ). Hence
`(α − β) · ⟨v, w⟩ = 0`, and `α ≠ β` (PR #896) forces `⟨v, w⟩ = 0`.

This strengthens PR #896 (linear independence) to orthogonality —
the iterates form an orthogonal basis of the saturated-ferromagnet
ground-state ladder.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Generic helper: Hermitian + distinct real eigenvalues → orthogonal -/

/-- For a Hermitian matrix `M`, two eigenvectors at distinct **real**
eigenvalues are orthogonal in the dot product `star v ⬝ᵥ w`.

The realness assumption is supplied as `star α = α` and `star β = β`. -/
theorem Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne
    {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} (hM : M.IsHermitian)
    {α β : ℂ} (hα : star α = α) (hβ : star β = β)
    {v w : n → ℂ}
    (hv : M.mulVec v = α • v) (hw : M.mulVec w = β • w)
    (hαβ : α ≠ β) :
    star v ⬝ᵥ w = 0 := by
  -- Compute `star v ⬝ᵥ M *ᵥ w` in two ways.
  -- Way 1: substitute hw.
  have h1 : star v ⬝ᵥ M.mulVec w = β * (star v ⬝ᵥ w) := by
    rw [hw, dotProduct_smul, smul_eq_mul]
  -- Way 2: shift M to the left side (using Hermiticity).
  have hHerm : Matrix.conjTranspose M = M := hM
  have h_left : Matrix.vecMul (star v) M = α • star v := by
    have h1 : Matrix.vecMul (star v) M =
        Matrix.vecMul (star v) (Matrix.conjTranspose M) := by rw [hHerm]
    rw [h1, ← Matrix.star_mulVec, hv, star_smul, hα]
  have h2 : dotProduct (star v) (M.mulVec w) = α * dotProduct (star v) w := by
    rw [Matrix.dotProduct_mulVec, h_left, smul_dotProduct, smul_eq_mul]
  -- α * ⟨v,w⟩ = β * ⟨v,w⟩ ⇒ (α - β) * ⟨v,w⟩ = 0 ⇒ ⟨v,w⟩ = 0 since α ≠ β.
  have hαβ_ne : α - β ≠ 0 := sub_ne_zero.mpr hαβ
  have heq : α * (star v ⬝ᵥ w) = β * (star v ⬝ᵥ w) := h2.symm.trans h1
  have hsub : (α - β) * (star v ⬝ᵥ w) = 0 := by
    rw [sub_mul, heq, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left hαβ_ne

/-! ## Pairwise orthogonality of the ladder iterates -/

/-- The ladder eigenvalue `m_max − k` is real, i.e., its complex
conjugate equals itself. -/
theorem ladderEigenvalueUp_star_eq (k : Fin (Fintype.card V * N + 1)) :
    star (ladderEigenvalueUp V N k) = ladderEigenvalueUp V N k := by
  unfold ladderEigenvalueUp
  simp [Complex.star_def, Complex.conj_ofReal, Complex.conj_natCast]

/-- **Pairwise orthogonality of the saturated-ferromagnet ladder
iterates**: for `[Nonempty V]` and any two distinct indices
`i ≠ j` in `Fin (|V|·N + 1)`, the iterates
`ladderIterateUp V N i` and `ladderIterateUp V N j` are orthogonal:

  `star (ladderIterateUp V N i) ⬝ᵥ ladderIterateUp V N j = 0`.

Proof: apply the generic Hermitian distinct-eigenvalue orthogonality
lemma to `Ŝ^z_{tot}` (Hermitian via `totalSpinSOp3_isHermitian`),
with the real eigenvalues `m_max − i`, `m_max − j` (distinct by
`ladderEigenvalueUp_injective`). -/
theorem ladderIterateUp_orthogonal [Nonempty V]
    {i j : Fin (Fintype.card V * N + 1)} (hij : i ≠ j) :
    star (ladderIterateUp V N i) ⬝ᵥ ladderIterateUp V N j = 0 := by
  have hi := (ladderIterateUp_hasEigenvector i).left
  have hj := (ladderIterateUp_hasEigenvector j).left
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hi hj
  have hαβ : ladderEigenvalueUp V N i ≠ ladderEigenvalueUp V N j := by
    intro h
    exact hij (ladderEigenvalueUp_injective h)
  exact Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne
    (totalSpinSOp3_isHermitian (Λ := V) (N := N))
    (ladderEigenvalueUp_star_eq i) (ladderEigenvalueUp_star_eq j)
    hi hj hαβ

end LatticeSystem.Quantum
