import LatticeSystem.Quantum.SpinS.CasimirSpectralBound

/-!
# Total-Casimir magnetization lower bound `(Ŝ_tot)² ≥ m(m+1)`

First analytic ingredient for Issue #3674 (the abstract variational lower bound
completing the toy-ground-state predicted-Casimir witness, Issue #3658 / #3542):
a `(Ŝ_tot)²`-eigenvector in a magnetization sector with magnetization `m ≥ 0` has
Casimir eigenvalue at least `m(m+1)`.

The total spin dominates its `z`-projection: raising with `Ŝ⁺_tot` only *increases*
the magnetization, so the highest weight `M'` reached satisfies `M' ≥ m`; for a
highest-weight vector `(Ŝ_tot)² = M'(M'+1) ≥ m(m+1)`.  This is the lower-bound
companion of `totalSpinSSquared_eigenvalue_re_le_sMax`, reusing the same
highest-weight machinery while tracking that the magnetization never decreases.

In the extremal magnetization sector `m = s_A − s_B` it pins the toy ground
state's total Casimir to the predicted value `m(m+1)` (combined with the upper
bound), bypassing the Clebsch–Gordan triangle inequality.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

omit [DecidableEq V] in
/-- The real part of the magnetization value `s_max − k`. -/
theorem sMax_sub_natCast_re (k : ℕ) :
    (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)).re =
      (Fintype.card V : ℝ) * (N : ℝ) / 2 - (k : ℝ) := by
  simp [Complex.sub_re, Complex.mul_re]

/-- **Existence of a highest-weight eigenvector, magnetization-tracking**: from a
non-zero `(Ŝ_tot)²`-eigenvector at `γ` in `magSubspaceS V N (s_max − k)`, raising
with `Ŝ⁺_tot` produces a non-zero highest-weight eigenvector at the same `γ` whose
magnetization `M` satisfies `M.re ≥ s_max − k` (the magnetization never decreases). -/
theorem exists_highestWeight_eigenvector_ge (k : ℕ) :
    ∀ {γ : ℂ} {w : (V → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      w ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)) →
      (totalSpinSSquared V N).mulVec w = γ • w →
      ∃ (M : ℂ) (w' : (V → Fin (N + 1)) → ℂ),
        w' ≠ 0 ∧ w' ∈ magSubspaceS V N M ∧
        (totalSpinSOpPlus V N).mulVec w' = 0 ∧
        (totalSpinSSquared V N).mulVec w' = γ • w' ∧
        (Fintype.card V : ℝ) * (N : ℝ) / 2 - (k : ℝ) ≤ M.re := by
  induction k with
  | zero =>
    intro γ w hw_ne hw_mem hcas
    refine ⟨_, w, hw_ne, hw_mem, ?_, hcas, ?_⟩
    · have hmem1 := totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem hw_mem
      have hbot : magSubspaceS V N
          ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((0 : ℕ) : ℂ)) + 1) = ⊥ := by
        apply magSubspaceS_eq_bot_of_not_in_spectrum
        intro σ
        have h := magEigenvalueS_ne_mMax_add_one (V := V) (N := N) σ
        push_cast
        simpa using h
      exact (Submodule.eq_bot_iff _).mp hbot _ hmem1
    · rw [sMax_sub_natCast_re]
  | succ k ih =>
    intro γ w hw_ne hw_mem hcas
    by_cases hker : (totalSpinSOpPlus V N).mulVec w = 0
    · refine ⟨_, w, hw_ne, hw_mem, hker, hcas, ?_⟩
      rw [sMax_sub_natCast_re]
    · have hmem1 := totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem hw_mem
      have hidx : (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((k + 1 : ℕ) : ℂ)) + 1 =
          ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((k : ℕ) : ℂ) := by
        push_cast; ring
      rw [hidx] at hmem1
      have hcas1 : (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec w) =
          γ • (totalSpinSOpPlus V N).mulVec w :=
        mulVec_preserves_eigenvalue_of_commuteS totalSpinSSquared_commute_totalSpinSOpPlus hcas
      obtain ⟨M, w', hw'_ne, hw'_mem, hw'_ker, hw'_cas, hM_ge⟩ := ih hker hmem1 hcas1
      refine ⟨M, w', hw'_ne, hw'_mem, hw'_ker, hw'_cas, ?_⟩
      push_cast at hM_ge ⊢
      linarith

/-- **Total-Casimir magnetization lower bound**: a non-zero `(Ŝ_tot)²`-eigenvector
at `γ` lying in `magSubspaceS V N M` with `0 ≤ M.re` satisfies
`M.re·(M.re+1) ≤ γ.re`. -/
theorem totalSpinSSquared_eigenvalue_re_ge_of_mem_magSubspaceS
    {γ M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hv_mem : v ∈ magSubspaceS V N M)
    (hM_nn : 0 ≤ M.re)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    M.re * (M.re + 1) ≤ γ.re := by
  -- `M` is an attained magnetization eigenvalue, so `M = s_max − k` for some `k`.
  have hMspec : ∃ σ : V → Fin (N + 1), magEigenvalueS σ = M := by
    by_contra h
    exact hv ((Submodule.eq_bot_iff _).mp
      (magSubspaceS_eq_bot_of_not_in_spectrum (not_exists.mp h)) v hv_mem)
  obtain ⟨σ, hσ⟩ := hMspec
  have hMeq : M = ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((magSumS σ : ℕ) : ℂ) := by
    rw [← hσ, magEigenvalueS_def]
  have hv_mem' : v ∈ magSubspaceS V N
      (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((magSumS σ : ℕ) : ℂ)) := by
    rwa [← hMeq]
  obtain ⟨M', w', hw'_ne, hw'_mem, hw'_ker, hw'_cas, hM'_ge⟩ :=
    exists_highestWeight_eigenvector_ge (magSumS σ) hv hv_mem' hcas
  -- γ = M' (M' + 1).
  have hhw := tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpPlus_eq_zero_of_mem_magSubspaceS
    hw'_mem hw'_ker
  have hsmul : γ • w' = (M' * (M' + 1)) • w' := hw'_cas.symm.trans hhw
  have hγ : γ = M' * (M' + 1) := by
    have := sub_eq_zero.mpr hsmul
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw'_ne
  -- M'.im = 0, and M.re ≤ M'.re.
  have hM'im : M'.im = 0 := by
    -- M' is an attained eigenvalue too (w' ≠ 0 in magSubspaceS M').
    have : ∃ τ : V → Fin (N + 1), magEigenvalueS τ = M' := by
      by_contra h
      exact hw'_ne ((Submodule.eq_bot_iff _).mp
        (magSubspaceS_eq_bot_of_not_in_spectrum (not_exists.mp h)) w' hw'_mem)
    obtain ⟨τ, hτ⟩ := this
    rw [← hτ]; simp [magEigenvalueS_def]
  have hMre_le : M.re ≤ M'.re := by
    have hMre : M.re = (Fintype.card V : ℝ) * (N : ℝ) / 2 - (magSumS σ : ℝ) := by
      rw [hMeq, sMax_sub_natCast_re]
    rw [hMre]; exact hM'_ge
  -- γ.re = M'.re (M'.re + 1).
  have hre : γ.re = M'.re * (M'.re + 1) := by
    rw [hγ]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, hM'im]
    ring
  rw [hre]
  nlinarith [hMre_le, hM_nn]

end LatticeSystem.Quantum
