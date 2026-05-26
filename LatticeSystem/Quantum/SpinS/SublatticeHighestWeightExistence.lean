import LatticeSystem.Quantum.SpinS.SublatticeMagWeightComponent
import LatticeSystem.Quantum.SpinS.SublatticeMagShift
import LatticeSystem.Quantum.SpinS.SublatticeSpinLadder

/-!
# Existence of a sublattice highest-weight eigenvector

Scaffold for the sublattice Casimir spectral max bound (Issue #3658, the final
obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

From a non-zero `(Ŝ_A)²`-eigenvector in a sublattice magnetization subspace,
repeatedly raising with `Ŝ_A^+` terminates (the sublattice magnetization is bounded
above by `s_A = |A|·N/2`, so the subspace one step above the top is `⊥`),
producing a non-zero highest-weight `(Ŝ_A)²`-eigenvector at the same eigenvalue.

This is the sublattice analogue of `exists_highestWeight_eigenvector`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

omit [DecidableEq Λ] in
/-- The eigenvalue `s_A + 1 = |A|·N/2 + 1` is above the highest sublattice
magnetization eigenvalue `s_A`, hence not equal to `sublatticeMagEigenvalueS A σ`
for any `σ`. -/
theorem sublatticeMagEigenvalueS_ne_sMax_add_one (A : Λ → Bool) (σ : Λ → Fin (N + 1)) :
    sublatticeMagEigenvalueS A σ ≠
      ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 + 1 := by
  rw [sublatticeMagEigenvalueS_eq_sub]
  intro h
  have hSumS : (sublatticeMagSumS A σ : ℂ) = (-1 : ℂ) := by linear_combination -h
  have hReal' : (sublatticeMagSumS A σ : ℝ) = -1 := by exact_mod_cast hSumS
  have hNonneg : (0 : ℝ) ≤ (sublatticeMagSumS A σ : ℝ) := by positivity
  linarith

/-- **Existence of a sublattice highest-weight eigenvector**: from a non-zero
`(Ŝ_A)²`-eigenvector `w` at `γ` in `sublatticeMagSubspaceS A (s_A − k)`, repeatedly
raising with `Ŝ_A^+` (which terminates once the sublattice magnetization exceeds
`s_A`) produces a non-zero highest-weight `(Ŝ_A)²`-eigenvector at the same `γ`. -/
theorem sublatticeExists_highestWeight_eigenvector (A : Λ → Bool) (k : ℕ) :
    ∀ {γ : ℂ} {w : (Λ → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      w ∈ sublatticeMagSubspaceS A
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
          (k : ℂ)) →
      (sublatticeSpinSquaredS N A).mulVec w = γ • w →
      ∃ (M : ℂ) (w' : (Λ → Fin (N + 1)) → ℂ),
        w' ≠ 0 ∧ w' ∈ sublatticeMagSubspaceS A M ∧
        (sublatticeSpinSOpPlus N A).mulVec w' = 0 ∧
        (sublatticeSpinSquaredS N A).mulVec w' = γ • w' := by
  induction k with
  | zero =>
    intro γ w hw_ne hw_mem hcas
    refine ⟨_, w, hw_ne, hw_mem, ?_, hcas⟩
    have hmem1 := sublatticeSpinSOpPlus_mulVec_mem_sublatticeMagSubspaceS_of_mem A hw_mem
    have hbot : sublatticeMagSubspaceS (N := N) A
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
          ((0 : ℕ) : ℂ)) + 1) = ⊥ := by
      apply sublatticeMagSubspaceS_eq_bot_of_not_in_spectrum
      intro σ
      have h := sublatticeMagEigenvalueS_ne_sMax_add_one (Λ := Λ) (N := N) A σ
      push_cast
      simpa using h
    exact (Submodule.eq_bot_iff _).mp hbot _ hmem1
  | succ k ih =>
    intro γ w hw_ne hw_mem hcas
    by_cases hker : (sublatticeSpinSOpPlus N A).mulVec w = 0
    · exact ⟨_, w, hw_ne, hw_mem, hker, hcas⟩
    · have hmem1 := sublatticeSpinSOpPlus_mulVec_mem_sublatticeMagSubspaceS_of_mem A hw_mem
      have hidx :
          ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
            ((k + 1 : ℕ) : ℂ)) + 1) =
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * (N : ℂ) / 2 -
              ((k : ℕ) : ℂ) := by
        push_cast; ring
      rw [hidx] at hmem1
      have hcas1 : (sublatticeSpinSquaredS N A).mulVec
          ((sublatticeSpinSOpPlus N A).mulVec w) =
          γ • (sublatticeSpinSOpPlus N A).mulVec w :=
        mulVec_preserves_eigenvalue_of_commuteS_ladder (N := N)
          (sublatticeSpinSquaredS_commute_sublatticeSpinSOpPlus N A) hcas
      exact ih hker hmem1 hcas1

end LatticeSystem.Quantum
