import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import LatticeSystem.Quantum.SpinS.BipartiteToyGSLadderInvariant

/-!
# Existence of a total lowest weight with joint Casimir eigenvalues

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a),
Route 5 brick 3b-engine (see `.self-local/tex/3717-coupled-total-spin-lower-bound.tex`).

A non-zero simultaneous eigenvector of `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` generates, by
repeatedly lowering with `Ŝ⁻_tot`, a non-zero **total lowest-weight** vector
(`Ŝ⁻_tot w' = 0`) at the *same* three eigenvalues (the sublattice Casimirs are
preserved because `Ŝ⁻_tot` commutes with them, #3714).  This is the reduction needed to
prove the coupled total-spin lower bound by examining the lowest weight.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Total lowest-weight existence (joint Casimir)**: lowering with `Ŝ⁻_tot` from a
joint eigenvector reaches, after at most `k` steps (here `k` indexes the magnetization
level `M = k − |V|·N/2` measured from the bottom), a non-zero `Ŝ⁻_tot`-killed vector at
the same `(Ŝ_tot)²`, `(Ŝ_A)²`, `(Ŝ_¬A)²` eigenvalues. -/
theorem exists_total_lowestWeight_joint (A : V → Bool) (k : ℕ) :
    ∀ {γ α β : ℂ} {w : (V → Fin (N + 1)) → ℂ},
      w ≠ 0 →
      w ∈ magSubspaceS V N ((k : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2)) →
      (totalSpinSSquared V N).mulVec w = γ • w →
      (sublatticeSpinSquaredS N A).mulVec w = α • w →
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w = β • w →
      ∃ (M : ℂ) (w' : (V → Fin (N + 1)) → ℂ),
        w' ≠ 0 ∧ w' ∈ magSubspaceS V N M ∧
        (totalSpinSOpMinus V N).mulVec w' = 0 ∧
        (totalSpinSSquared V N).mulVec w' = γ • w' ∧
        (sublatticeSpinSquaredS N A).mulVec w' = α • w' ∧
        (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w' = β • w' := by
  induction k with
  | zero =>
    intro γ α β w hw_ne hw_mem hγ hα hβ
    refine ⟨_, w, hw_ne, hw_mem, ?_, hγ, hα, hβ⟩
    -- At the bottom level `−|V|·N/2`, lowering lands in the empty level below.
    have hmem1 := totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem hw_mem
    have hbot : magSubspaceS V N
        (((0 : ℕ) : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2) - 1) = ⊥ := by
      apply magSubspaceS_eq_bot_of_not_in_spectrum
      intro σ hcontra
      exact magEigenvalueS_ne_neg_mMax_sub_one (V := V) (N := N) σ
        (hcontra.trans (by push_cast; ring))
    exact (Submodule.eq_bot_iff _).mp hbot _ hmem1
  | succ k ih =>
    intro γ α β w hw_ne hw_mem hγ hα hβ
    by_cases hker : (totalSpinSOpMinus V N).mulVec w = 0
    · exact ⟨_, w, hw_ne, hw_mem, hker, hγ, hα, hβ⟩
    · have hmem1 := totalSpinSOpMinus_mulVec_mem_magSubspaceS_of_mem hw_mem
      have hidx : (((k + 1 : ℕ) : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2)) - 1 =
          ((k : ℕ) : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2) := by
        push_cast; ring
      rw [hidx] at hmem1
      have hγ1 : (totalSpinSSquared V N).mulVec ((totalSpinSOpMinus V N).mulVec w) =
          γ • (totalSpinSOpMinus V N).mulVec w :=
        mulVec_preserves_eigenvalue_of_commuteS totalSpinSSquared_commute_totalSpinSOpMinus hγ
      have hα1 : (sublatticeSpinSquaredS N A).mulVec ((totalSpinSOpMinus V N).mulVec w) =
          α • (totalSpinSOpMinus V N).mulVec w :=
        mulVec_preserves_eigenvalue_of_commuteS
          (sublatticeSpinSquaredS_commute_totalSpinSOpMinus A) hα
      have hβ1 : (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec
            ((totalSpinSOpMinus V N).mulVec w) =
          β • (totalSpinSOpMinus V N).mulVec w :=
        mulVec_preserves_eigenvalue_of_commuteS
          (sublatticeSpinSquaredS_commute_totalSpinSOpMinus (fun x => ! A x)) hβ
      exact ih hker hmem1 hγ1 hα1 hβ1

end LatticeSystem.Quantum
