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

end LatticeSystem.Quantum
