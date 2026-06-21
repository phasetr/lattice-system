import LatticeSystem.Quantum.SpinS.MarshallSignCore

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-!
# Spin-S Marshall-dressed basis (capstone)

Continues MarshallSignCore with the Marshall-dressed basis. Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] {N : ℕ}

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

/-- Definitional unfolding of `marshallDressedBasisS`. -/
theorem marshallDressedBasisS_def [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ = marshallSignS A σ • basisVecS σ := rfl

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

/-- For `N = 0` (`S = 0`), the Marshall-dressed basis vector equals
the plain basis vector. -/
theorem marshallDressedBasisS_N_zero [DecidableEq V]
    (A : V → Bool) (σ : V → Fin 1) :
    marshallDressedBasisS A σ = basisVecS σ := by
  unfold marshallDressedBasisS
  rw [marshallSignS_N_zero, one_smul]

/-- For an empty lattice, the Marshall-dressed basis vector equals
the plain basis vector (Marshall sign is `1`). -/
theorem marshallDressedBasisS_of_isEmpty [DecidableEq V] [IsEmpty V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ = basisVecS σ := by
  unfold marshallDressedBasisS
  rw [marshallSignS_of_isEmpty, one_smul]

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

/-- **Inverse relation**: scaling the Marshall-dressed basis by the
(real) Marshall sign recovers the plain basis vector:

  `marshallSignS A σ • marshallDressedBasisS A σ = basisVecS σ`.

(Since the Marshall sign is real and squares to 1, multiplying by it
once more inverts the dressing.) -/
theorem marshallSignS_smul_marshallDressedBasisS [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallSignS A σ : ℂ) • marshallDressedBasisS A σ = basisVecS σ := by
  unfold marshallDressedBasisS
  rw [smul_smul, marshallSignS_sq, one_smul]

/-- The Marshall-dressed basis vector is non-zero: at its diagonal
component, `marshallDressedBasisS A σ σ = marshallSignS A σ ≠ 0`. -/
theorem marshallDressedBasisS_ne_zero [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ ≠ 0 := by
  intro h
  have h0 : marshallDressedBasisS A σ σ = 0 := by rw [h]; rfl
  rw [marshallDressedBasisS_self] at h0
  exact marshallSignS_ne_zero A σ h0

/-- The Marshall-dressed basis vector at its own configuration has
norm 1: `‖marshallDressedBasisS A σ σ‖ = 1`. -/
theorem marshallDressedBasisS_self_norm [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    ‖marshallDressedBasisS A σ σ‖ = 1 := by
  rw [marshallDressedBasisS_self, marshallSignS_norm]

/-- Component-wise norm of the Marshall-dressed basis equals the
component-wise norm of the plain basis (since dressing only changes
sign): `‖marshallDressedBasisS A σ τ‖ = ‖basisVecS σ τ‖`. -/
theorem marshallDressedBasisS_norm_eq_basisVecS [DecidableEq V]
    (A : V → Bool) (σ τ : V → Fin (N + 1)) :
    ‖marshallDressedBasisS A σ τ‖ = ‖(basisVecS σ τ : ℂ)‖ := by
  unfold marshallDressedBasisS
  rw [Pi.smul_apply, smul_eq_mul, norm_mul]
  rw [marshallSignS_norm, one_mul]

/-- The Marshall-dressed basis vector lies in the supremum of all
magnetization subspaces (since it lies in `magSubspaceS V N (magEigenvalueS σ)`
which is included in `⨆ M, magSubspaceS V N M`). -/
theorem marshallDressedBasisS_mem_iSup_magSubspaceS [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    (marshallDressedBasisS A σ : (V → Fin (N + 1)) → ℂ) ∈
      ⨆ M : ℂ, magSubspaceS V N M :=
  Submodule.mem_iSup_of_mem (magEigenvalueS σ)
    (marshallDressedBasisS_mem_magSubspaceS A σ)

/-- **Marshall-dressed basis is `±basisVecS`**: depending on whether
the Marshall sign is `+1` or `-1`, the dressed basis vector equals
`+basisVecS σ` or `-basisVecS σ`. -/
theorem marshallDressedBasisS_eq_or [DecidableEq V]
    (A : V → Bool) (σ : V → Fin (N + 1)) :
    marshallDressedBasisS A σ = basisVecS σ ∨
      marshallDressedBasisS A σ = -basisVecS σ := by
  unfold marshallDressedBasisS
  rcases marshallSignS_eq_one_or_neg_one A σ with h | h
  · left; rw [h, one_smul]
  · right; rw [h, neg_smul, one_smul]

/-- **Inverse decomposition**: every plain basis vector is
`marshallSignS A σ` times the corresponding Marshall-dressed basis
vector. (This is `marshallSignS_smul_marshallDressedBasisS` restated
with sides swapped for use as a rewrite from `basisVecS` toward
`marshallDressedBasisS`.) -/
theorem basisVecS_eq_marshallSignS_smul_marshallDressedBasisS
    [DecidableEq V] (A : V → Bool) (σ : V → Fin (N + 1)) :
    (basisVecS σ : (V → Fin (N + 1)) → ℂ) =
      marshallSignS A σ • marshallDressedBasisS A σ :=
  (marshallSignS_smul_marshallDressedBasisS A σ).symm

/-- **Marshall-dressed basis decomposition** of any vector:
`v = Σ_σ (marshallSignS A σ * v(σ)) • marshallDressedBasisS A σ`.
Substituting `basisVecS σ = marshallSignS A σ • marshallDressedBasisS A σ`
into `fun_eq_sum_smul_basisVecS`. -/
theorem fun_eq_sum_smul_marshallDressedBasisS [DecidableEq V]
    (A : V → Bool) (v : (V → Fin (N + 1)) → ℂ) :
    v = ∑ σ : V → Fin (N + 1),
      (marshallSignS A σ * v σ) • marshallDressedBasisS A σ := by
  conv_lhs => rw [fun_eq_sum_smul_basisVecS v]
  refine Finset.sum_congr rfl ?_
  intro σ _
  rw [basisVecS_eq_marshallSignS_smul_marshallDressedBasisS A σ]
  rw [smul_smul]
  rw [mul_comm (v σ) (marshallSignS A σ)]

end LatticeSystem.Quantum
