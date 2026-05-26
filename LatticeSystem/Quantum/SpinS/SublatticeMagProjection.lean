import LatticeSystem.Quantum.SpinS.SublatticeMagSpectrum

/-!
# Sublattice magnetization projection and decomposition

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

The pointwise sublattice projector `sublatticeMagProjFn A M v` keeps `v σ` exactly
where the sublattice magnetization eigenvalue `sublatticeMagEigenvalueS A σ` equals
`M`.  It lands in `sublatticeMagSubspaceS A M`, is linear, and the projectors over
the finite spectrum `M = s_A − k` (`k = 0..|A|·N`) sum to the identity, so any
vector decomposes into its sublattice-weight components.

This is the sublattice analogue of `magProjFn` / `sum_magProjFn_eq`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The sublattice magnetization "sum": `∑_{x ∈ A} σ_x` (a natural number).  The
sublattice magnetization eigenvalue is `s_A − sublatticeMagSumS A σ`. -/
def sublatticeMagSumS (A : Λ → Bool) (σ : Λ → Fin (N + 1)) : ℕ :=
  ∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true), (σ x).val

omit [DecidableEq Λ] in
/-- `sublatticeMagSumS A σ ≤ |A|·N`. -/
theorem sublatticeMagSumS_le (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    sublatticeMagSumS A σ ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card * N := by
  unfold sublatticeMagSumS
  calc
    ∑ x ∈ Finset.univ.filter (fun x : Λ => A x = true), (σ x).val
        ≤ ∑ _x ∈ Finset.univ.filter (fun x : Λ => A x = true), N :=
          Finset.sum_le_sum (fun x _ => by have := (σ x).2; omega)
    _ = (Finset.univ.filter (fun x : Λ => A x = true)).card * N := by
          rw [Finset.sum_const, smul_eq_mul]

omit [DecidableEq Λ] in
/-- `sublatticeMagEigenvalueS A σ = |A|·N/2 − sublatticeMagSumS A σ`. -/
theorem sublatticeMagEigenvalueS_eq_sub (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    sublatticeMagEigenvalueS A σ =
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
        (sublatticeMagSumS A σ : ℂ) := by
  rw [sublatticeMagEigenvalueS_def, sublatticeMagSumS]
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- Pointwise sublattice magnetization projector: keeps `v σ` when
`sublatticeMagEigenvalueS A σ = M` and zeros it out otherwise. -/
noncomputable def sublatticeMagProjFn (A : Λ → Bool) (M : ℂ)
    (v : (Λ → Fin (N + 1)) → ℂ) : (Λ → Fin (N + 1)) → ℂ :=
  fun σ => if sublatticeMagEigenvalueS A σ = M then v σ else 0

omit [DecidableEq Λ] in
/-- `sublatticeMagProjFn` is additive in its vector argument. -/
theorem sublatticeMagProjFn_add (A : Λ → Bool) (M : ℂ)
    (v w : (Λ → Fin (N + 1)) → ℂ) :
    sublatticeMagProjFn A M (v + w) =
      sublatticeMagProjFn A M v + sublatticeMagProjFn A M w := by
  funext σ
  unfold sublatticeMagProjFn
  by_cases h : sublatticeMagEigenvalueS A σ = M <;> simp [h]

omit [DecidableEq Λ] in
/-- `sublatticeMagProjFn` is homogeneous in its vector argument. -/
theorem sublatticeMagProjFn_smul (A : Λ → Bool) (M c : ℂ)
    (v : (Λ → Fin (N + 1)) → ℂ) :
    sublatticeMagProjFn A M (c • v) = c • sublatticeMagProjFn A M v := by
  funext σ
  unfold sublatticeMagProjFn
  by_cases h : sublatticeMagEigenvalueS A σ = M <;> simp [h]

/-- **Support property of `sublatticeMagSubspaceS A M`**: a vector in
`sublatticeMagSubspaceS A M` vanishes at every configuration whose sublattice
magnetization eigenvalue differs from `M`. -/
theorem sublatticeMagSubspaceS_apply_eq_zero_of_sublatticeMagEigenvalueS_ne
    (A : Λ → Bool) {M : ℂ} {w : (Λ → Fin (N + 1)) → ℂ}
    (hw : w ∈ sublatticeMagSubspaceS A M) {σ : Λ → Fin (N + 1)}
    (hσ : sublatticeMagEigenvalueS A σ ≠ M) : w σ = 0 := by
  rw [mem_sublatticeMagSubspaceS_iff] at hw
  have hτ_lhs : (sublatticeSpinSOp3 N A).mulVec w σ =
      sublatticeMagEigenvalueS A σ * w σ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single σ]
    · rw [sublatticeSpinSOp3_apply_diag]
    · intros τ _ hτσ
      rw [sublatticeSpinSOp3_apply_off_diag A (Ne.symm hτσ), zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hτ_rhs : (M • w) σ = M * w σ := by simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq : sublatticeMagEigenvalueS A σ * w σ = M * w σ := by
    rw [← hτ_lhs, hw, hτ_rhs]
  have hsub : (sublatticeMagEigenvalueS A σ - M) * w σ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hσ)

/-- The pointwise sublattice projector lands in `sublatticeMagSubspaceS A M`. -/
theorem sublatticeMagProjFn_mem_sublatticeMagSubspaceS (A : Λ → Bool) (M : ℂ)
    (v : (Λ → Fin (N + 1)) → ℂ) :
    sublatticeMagProjFn A M v ∈ sublatticeMagSubspaceS A M := by
  rw [mem_sublatticeMagSubspaceS_iff]
  funext σ
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single σ]
  · rw [sublatticeSpinSOp3_apply_diag, Pi.smul_apply, smul_eq_mul]
    unfold sublatticeMagProjFn
    by_cases h : sublatticeMagEigenvalueS A σ = M
    · rw [if_pos h, h]
    · rw [if_neg h]; simp
  · intros τ _ hτσ
    rw [sublatticeSpinSOp3_apply_off_diag A (Ne.symm hτσ), zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

omit [DecidableEq Λ] in
/-- **Pointwise sublattice magnetization decomposition**:
`v = ∑_{k : Fin (|A|·N + 1)} sublatticeMagProjFn A (s_A − k) v`.

Every configuration `σ` has `sublatticeMagEigenvalueS A σ = s_A − sublatticeMagSumS A σ`
with `sublatticeMagSumS A σ ∈ {0, …, |A|·N}`, so exactly one index selects `v σ`. -/
theorem sum_sublatticeMagProjFn_eq (A : Λ → Bool) (v : (Λ → Fin (N + 1)) → ℂ) :
    (∑ k : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1),
      sublatticeMagProjFn A
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
          (k.val : ℂ)) v) = v := by
  funext σ
  rw [Finset.sum_apply]
  let k₀ : Fin ((Finset.univ.filter (fun x : Λ => A x = true)).card * N + 1) :=
    ⟨sublatticeMagSumS A σ, Nat.lt_succ_of_le (sublatticeMagSumS_le A σ)⟩
  rw [Finset.sum_eq_single k₀]
  · unfold sublatticeMagProjFn
    have hmag : sublatticeMagEigenvalueS A σ =
        ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
          (k₀.val : ℂ) := by
      rw [sublatticeMagEigenvalueS_eq_sub]
    rw [if_pos hmag]
  · intros k _ hkne
    unfold sublatticeMagProjFn
    rw [if_neg]
    intro hmag
    rw [sublatticeMagEigenvalueS_eq_sub] at hmag
    have hsum : (sublatticeMagSumS A σ : ℂ) = (k.val : ℂ) := sub_right_inj.mp hmag
    have hnat : k.val = sublatticeMagSumS A σ := by exact_mod_cast hsum.symm
    exact hkne (Fin.ext hnat)
  · intro h
    exact (h (Finset.mem_univ _)).elim

end LatticeSystem.Quantum
