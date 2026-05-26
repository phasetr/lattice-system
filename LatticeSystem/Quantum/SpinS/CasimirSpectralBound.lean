import LatticeSystem.Quantum.SpinS.CasimirWeightComponent
import LatticeSystem.Quantum.SpinS.MagEigenvalueBound
import LatticeSystem.Quantum.SpinS.LadderBoundaryAnnihilation
import LatticeSystem.Quantum.SpinS.AllAlignedState
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.Theorem23Casimir

/-!
# Total-Casimir spectral max bound `(Ŝ_tot)² ≤ s_max(s_max+1)`

Final analytic ingredient for Issue #3658 (the witness construction completing
the sound Tasaki §2.5 Theorem 2.3 route, #3542): every eigenvalue of the total
Casimir `(Ŝ_tot)²` is at most `s_max(s_max+1)` with `s_max = |V|·N/2`.

Highest-weight argument: a non-zero eigenvector has a non-zero magnetization-weight
component (`CasimirWeightComponent`); raising it with `Ŝ⁺_tot` terminates (the
magnetization is bounded above by `s_max`, magSubspaces above are trivial), producing
a highest-weight vector annihilated by `Ŝ⁺_tot`, for which `(Ŝ_tot)² = M(M+1)` with
`|M| ≤ s_max`, hence the eigenvalue is `M(M+1) ≤ s_max(s_max+1)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Highest-weight Casimir bound**: a non-zero highest-weight `(Ŝ_tot)²`-eigenvector
(`Ŝ⁺_tot w = 0`) at `γ`, lying in `magSubspaceS V N M`, has `γ.re ≤ s_max(s_max+1)`.
Its Casimir value is `M(M+1)`, and `M` is an achievable magnetization, so
`|M| ≤ s_max`. -/
theorem totalSpinSSquared_highestWeight_eigenvalue_re_le
    {γ M : ℂ} {w : (V → Fin (N + 1)) → ℂ}
    (hw_ne : w ≠ 0)
    (hw_mem : w ∈ magSubspaceS V N M)
    (hker : (totalSpinSOpPlus V N).mulVec w = 0)
    (hcas : (totalSpinSSquared V N).mulVec w = γ • w) :
    γ.re ≤ ((Fintype.card V : ℝ) * (N : ℝ) / 2) * (((Fintype.card V : ℝ) * (N : ℝ) / 2) + 1) := by
  -- γ = M (M + 1).
  have hhw := tasaki23_totalSpinSSquared_mulVec_of_totalSpinSOpPlus_eq_zero_of_mem_magSubspaceS
    hw_mem hker
  have hsmul : γ • w = (M * (M + 1)) • w := hcas.symm.trans hhw
  have hγ : γ = M * (M + 1) := by
    have := sub_eq_zero.mpr hsmul
    rw [← sub_smul] at this
    rcases smul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hw_ne
  -- M is an achievable magnetization, so M = magEigenvalueS σ for some σ.
  have hMspec : ∃ σ : V → Fin (N + 1), magEigenvalueS σ = M := by
    by_contra h
    exact hw_ne ((Submodule.eq_bot_iff _).mp
      (magSubspaceS_eq_bot_of_not_in_spectrum (not_exists.mp h)) w hw_mem)
  obtain ⟨σ, hσ⟩ := hMspec
  -- Bounds |M.re| ≤ s_max, M.im = 0.
  subst hγ
  have hMre_ub : M.re ≤ (Fintype.card V : ℝ) * (N : ℝ) / 2 := by
    rw [← hσ]; exact magEigenvalueS_re_le_sMax σ
  have hMre_lb : -((Fintype.card V : ℝ) * (N : ℝ) / 2) ≤ M.re := by
    rw [← hσ]; exact neg_sMax_le_magEigenvalueS_re σ
  have hMim : M.im = 0 := by
    rw [← hσ]; simp [magEigenvalueS_def]
  -- (M*(M+1)).re = M.re*(M.re+1) − M.im*(M.im) ... = M.re(M.re+1) since M.im = 0.
  have hre : (M * (M + 1)).re = M.re * (M.re + 1) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.one_re,
      Complex.one_im, hMim]
    ring
  rw [hre]
  have hsmax_nn : (0 : ℝ) ≤ (Fintype.card V : ℝ) * (N : ℝ) / 2 := by positivity
  nlinarith [hMre_ub, hMre_lb, hsmax_nn]

/-- **Existence of a highest-weight eigenvector**: from a non-zero `(Ŝ_tot)²`-
eigenvector `w` at `γ` lying in `magSubspaceS V N (s_max − k)`, repeatedly raising
with `Ŝ⁺_tot` (which terminates once the magnetization exceeds `s_max`) produces a
non-zero highest-weight `(Ŝ_tot)²`-eigenvector at the same `γ`. -/
theorem exists_highestWeight_eigenvector (k : ℕ) :
    ∀ {γ : ℂ} {w : (V → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      w ∈ magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ)) →
      (totalSpinSSquared V N).mulVec w = γ • w →
      ∃ (M : ℂ) (w' : (V → Fin (N + 1)) → ℂ),
        w' ≠ 0 ∧ w' ∈ magSubspaceS V N M ∧
        (totalSpinSOpPlus V N).mulVec w' = 0 ∧
        (totalSpinSSquared V N).mulVec w' = γ • w' := by
  induction k with
  | zero =>
    intro γ w hw_ne hw_mem hcas
    refine ⟨_, w, hw_ne, hw_mem, ?_, hcas⟩
    -- Ŝ⁺ w ∈ magSubspace((s_max - 0) + 1) = magSubspace(s_max + 1) = ⊥.
    have hmem1 := totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem hw_mem
    have hbot : magSubspaceS V N
        ((((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((0 : ℕ) : ℂ)) + 1) = ⊥ := by
      apply magSubspaceS_eq_bot_of_not_in_spectrum
      intro σ
      have h := magEigenvalueS_ne_mMax_add_one (V := V) (N := N) σ
      push_cast
      simpa using h
    exact (Submodule.eq_bot_iff _).mp hbot _ hmem1
  | succ k ih =>
    intro γ w hw_ne hw_mem hcas
    by_cases hker : (totalSpinSOpPlus V N).mulVec w = 0
    · exact ⟨_, w, hw_ne, hw_mem, hker, hcas⟩
    · -- raise once and recurse
      have hmem1 := totalSpinSOpPlus_mulVec_mem_magSubspaceS_of_mem hw_mem
      have hidx : (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((k + 1 : ℕ) : ℂ)) + 1 =
          ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((k : ℕ) : ℂ) := by
        push_cast; ring
      rw [hidx] at hmem1
      have hcas1 : (totalSpinSSquared V N).mulVec ((totalSpinSOpPlus V N).mulVec w) =
          γ • (totalSpinSOpPlus V N).mulVec w :=
        mulVec_preserves_eigenvalue_of_commuteS totalSpinSSquared_commute_totalSpinSOpPlus hcas
      exact ih hker hmem1 hcas1

/-- **Total-Casimir spectral max bound**: every eigenvalue `γ` of `(Ŝ_tot)²`
(with a non-zero eigenvector) satisfies `γ.re ≤ s_max(s_max+1)`, `s_max = |V|·N/2`. -/
theorem totalSpinSSquared_eigenvalue_re_le_sMax
    {γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v) :
    γ.re ≤ ((Fintype.card V : ℝ) * (N : ℝ) / 2) * (((Fintype.card V : ℝ) * (N : ℝ) / 2) + 1) := by
  obtain ⟨k, hk_ne, hk_cas, hk_mem⟩ :=
    totalSpinSSquared_eigenvec_exists_weight_component hv hcas
  obtain ⟨M, w', hw'_ne, hw'_mem, hw'_ker, hw'_cas⟩ :=
    exists_highestWeight_eigenvector k.val hk_ne hk_mem hk_cas
  exact totalSpinSSquared_highestWeight_eigenvalue_re_le hw'_ne hw'_mem hw'_ker hw'_cas

end LatticeSystem.Quantum
