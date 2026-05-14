import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishing
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum

/-!
# Boundary annihilation of the saturated-ferromagnet ladder

For `[Nonempty V]`, the iterate
`(Ŝ^-_{tot})^{|V|·N + 1} · |σ_⊤⟩ = 0`. This is one step beyond the
maximal non-zero iterate `k = |V|·N` of PR #895.

Argument: by PR #887 the iterate at `k = |V|·N + 1` is an
`Ŝ^z_{tot}`-eigenvector at `m_max − (|V|·N + 1) = −m_max − 1`,
which lies outside the spectrum of `Ŝ^z_{tot}` (every basis state
`basisVecS σ` has eigenvalue `magEigenvalueS σ ∈ [−m_max, m_max]`).
Hence the magnetization subspace at `−m_max − 1` is `⊥`, forcing
the iterate to vanish.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Magnetization subspace is trivial outside the spectrum -/

/-- For any `M : ℂ` not in the spectrum of `Ŝ^z_{tot}` (i.e., not
equal to `magEigenvalueS σ` for any `σ : V → Fin (N + 1)`), the
magnetization subspace `magSubspaceS V N M` is `⊥`.

Proof: `Ŝ^z_{tot}` is diagonal in the `basisVecS` basis, with
diagonal entries `magEigenvalueS σ`. For `v ∈ magSubspaceS V N M`,
evaluating `Ŝ^z_{tot} v = M • v` at each configuration `τ` yields
`(magEigenvalueS τ − M) · v(τ) = 0`. By hypothesis,
`magEigenvalueS τ ≠ M`, so `v(τ) = 0` for every `τ`, hence `v = 0`. -/
theorem magSubspaceS_eq_bot_of_not_in_spectrum {M : ℂ}
    (hM : ∀ σ : V → Fin (N + 1), magEigenvalueS σ ≠ M) :
    magSubspaceS V N M = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [mem_magSubspaceS_iff] at hv
  funext τ
  -- hv : (Ŝ^z_tot).mulVec v = M • v.
  -- Evaluating both sides at τ.
  have hτ_lhs : (totalSpinSOp3 V N).mulVec v τ =
      magEigenvalueS τ * v τ := by
    -- Diagonal computation using totalSpinSOp3_apply_{diag,off_diag}.
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single τ]
    · rw [totalSpinSOp3_apply_diag]
    · intros σ _ hστ
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hστ), zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hτ_rhs : (M • v) τ = M * v τ := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq : magEigenvalueS τ * v τ = M * v τ := by
    rw [← hτ_lhs, hv, hτ_rhs]
  have hsub : (magEigenvalueS τ - M) * v τ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  have hne : magEigenvalueS τ - M ≠ 0 := sub_ne_zero.mpr (hM τ)
  exact (mul_eq_zero.mp hsub).resolve_left hne

/-! ## Eigenvalue −m_max − 1 is outside the spectrum -/

omit [DecidableEq V] in
/-- The eigenvalue `−m_max − 1 = −|V|·N/2 − 1` is below the lowest
eigenvalue `−m_max` of `Ŝ^z_{tot}` on `basisVecS`-basis states,
hence not equal to `magEigenvalueS σ` for any `σ`. -/
theorem magEigenvalueS_ne_neg_mMax_sub_one (σ : V → Fin (N + 1)) :
    magEigenvalueS σ ≠
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((Fintype.card V * N : ℕ) + 1 : ℕ) := by
  unfold magEigenvalueS
  intro h
  -- h : (|V|·N : ℂ)/2 − magSumS σ = (|V|·N : ℂ)/2 − ((|V|·N : ℕ) + 1).
  have hSumS : (magSumS σ : ℂ) = ((Fintype.card V * N : ℕ) + 1 : ℕ) := by
    have := h
    linear_combination -h
  have hNat : magSumS σ = Fintype.card V * N + 1 := by
    exact_mod_cast hSumS
  have hLe := magSumS_le σ
  omega

/-! ## Boundary annihilation -/

/-- **Boundary annihilation**: for `[Nonempty V]`, the iterate at
`k = |V|·N + 1` (one step past the maximal non-zero iterate)
is the zero vector:

  `(Ŝ^-_{tot})^{|V|·N + 1} · |σ_⊤⟩ = 0`.

Proof: PR #887 gives the iterate as an `Ŝ^z_{tot}`-eigenvector
at `m_max − (|V|·N + 1) = −m_max − 1`. The magnetization subspace
at this eigenvalue is `⊥` (no configuration matches), so the
iterate must be `0`. -/
theorem totalSpinSOpMinus_pow_succ_card_mul_N_allAlignedStateS_zero
    [Nonempty V] :
    ((totalSpinSOpMinus V N) ^ (Fintype.card V * N + 1)).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) = 0 := by
  -- Set v_k for k = |V|·N + 1.
  set v := ((totalSpinSOpMinus V N) ^ (Fintype.card V * N + 1)).mulVec
    (allAlignedStateS V N (0 : Fin (N + 1)))
  -- Apply PR #887: v is an Ŝ^z_tot eigenvector at m_max − (|V|·N + 1).
  have h_eigen : (totalSpinSOp3 V N).mulVec v =
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) -
        ((Fintype.card V * N : ℕ) + 1 : ℕ)) • v := by
    have h := totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
      (V := V) (N := N) (Fintype.card V * N + 1)
    convert h using 2
  -- v ∈ magSubspaceS at the off-spectrum eigenvalue.
  have hv_mem : v ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) -
        ((Fintype.card V * N : ℕ) + 1 : ℕ)) := by
    rw [mem_magSubspaceS_iff]
    exact h_eigen
  -- The magSubspaceS at this eigenvalue is ⊥.
  have h_bot := magSubspaceS_eq_bot_of_not_in_spectrum
    (V := V) (N := N) magEigenvalueS_ne_neg_mMax_sub_one
  rw [h_bot, Submodule.mem_bot] at hv_mem
  exact hv_mem

/-! ## Symmetric boundary annihilation (raising side) -/

omit [DecidableEq V] in
/-- The eigenvalue `m_max + 1 = |V|·N/2 + 1` is above the highest
eigenvalue `m_max` of `Ŝ^z_{tot}` on `basisVecS`-basis states,
hence not equal to `magEigenvalueS σ` for any `σ`. -/
theorem magEigenvalueS_ne_mMax_add_one (σ : V → Fin (N + 1)) :
    magEigenvalueS σ ≠
      ((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1 := by
  unfold magEigenvalueS
  intro h
  -- h : (|V|·N : ℂ)/2 − magSumS σ = (|V|·N : ℂ)/2 + 1.
  have hSumS : (magSumS σ : ℂ) = (-1 : ℂ) := by linear_combination -h
  -- Cast to Nat: magSumS σ has positive Nat value, can't equal -1 in ℂ.
  have hReal : ((magSumS σ : ℝ) : ℂ) = ((-1 : ℝ) : ℂ) := by
    push_cast; exact_mod_cast hSumS
  have hReal' : (magSumS σ : ℝ) = -1 := by exact_mod_cast hReal
  have hNonneg : (0 : ℝ) ≤ (magSumS σ : ℝ) := by positivity
  linarith

/-- **Symmetric boundary annihilation** (raising side): for
`[Nonempty V]`, the iterate
`(Ŝ^+_{tot})^{|V|·N + 1} · |σ_⊥⟩ = 0`.

PR #887 (raising side) gives the iterate as an `Ŝ^z_{tot}`-eigenvector
at `−m_max + (|V|·N + 1) = m_max + 1`, outside the spectrum. -/
theorem totalSpinSOpPlus_pow_succ_card_mul_N_allAlignedStateS_last
    [Nonempty V] :
    ((totalSpinSOpPlus V N) ^ (Fintype.card V * N + 1)).mulVec
        (allAlignedStateS V N (Fin.last N)) = 0 := by
  set v := ((totalSpinSOpPlus V N) ^ (Fintype.card V * N + 1)).mulVec
    (allAlignedStateS V N (Fin.last N))
  have h_eigen : (totalSpinSOp3 V N).mulVec v =
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1) • v := by
    have h := totalSpinSOp3_mulVec_totalSpinSOpPlus_pow_allAlignedStateS_last
      (V := V) (N := N) (Fintype.card V * N + 1)
    convert h using 2
    push_cast
    ring
  have hv_mem : v ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) + 1) := by
    rw [mem_magSubspaceS_iff]
    exact h_eigen
  have h_bot := magSubspaceS_eq_bot_of_not_in_spectrum
    (V := V) (N := N) magEigenvalueS_ne_mMax_add_one
  rw [h_bot, Submodule.mem_bot] at hv_mem
  exact hv_mem

end LatticeSystem.Quantum
