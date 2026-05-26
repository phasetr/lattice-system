import LatticeSystem.Quantum.SpinS.JointDiagonalKernel
import LatticeSystem.Quantum.SpinS.JointLadderIterateMag
import LatticeSystem.Quantum.SpinS.Theorem23ExtremalHighestWeight
import LatticeSystem.Quantum.SpinS.PredictedGSFinrankLtJointCasimirFinrank

/-!
# The minimal-total-spin joint predicted-Casimir eigenvector

Issue #3687 / #3674 (the final obligation of the sound Tasaki §2.5 Theorem 2.3
route, #3542).

Assembling the rank–nullity kernel (#3707) with the structural facts: the
`Ŝ⁺_tot`-killed extremal-sector vector `w*` produced by #3707 lies in the joint
maximal-sublattice-Casimir eigenspace `W` (each diagonal member does, #3698) and in
the extremal total-magnetization sector (#3699), so by the extremal highest-weight
relation (#3683) it is a `(Ŝ_tot)²`-eigenvector at the predicted value.  Hence
(for `|¬A| ≤ |A|`) there is a **non-zero joint eigenvector** of
`(Ŝ_tot)², (Ŝ_A)², (Ŝ_¬A)²` at `(predicted, s_A(s_A+1), s_B(s_B+1))` — the
minimal-total-spin state, the witness the toy-ground-state route needs.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Each diagonal member lies in the joint maximal-sublattice-Casimir eigenspace. -/
theorem jointDiagonalIterate_mem_jointSublatticeCasimirEigenspace (A : Λ → Bool)
    (kA : Fin ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N + 1)) :
    jointDiagonalIterate A N kA ∈ jointSublatticeCasimirEigenspace (Λ := Λ) A N := by
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact sublatticeSpinSquaredS_mulVec_jointLadderIterateDownS A kA.val _
  · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact sublatticeSpinSquaredS_complement_mulVec_jointLadderIterateDownS A kA.val _

/-- Each diagonal member lies in the extremal total-magnetization sector
`|V|·N/2 − |¬A|·N`. -/
theorem jointDiagonalIterate_mem_magSubspaceS (A : Λ → Bool)
    (kA : Fin ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N + 1)) :
    jointDiagonalIterate A N kA ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) := by
  have h := jointLadderIterateDownS_mem_magSubspaceS (Λ := Λ) (N := N) A kA.val
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N - kA.val)
  have hsum : kA.val + ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N - kA.val) =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N := by
    have : kA.val ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N :=
      Nat.lt_succ_iff.mp kA.isLt
    omega
  rw [hsum] at h
  exact h

/-- **The minimal-total-spin joint predicted-Casimir eigenvector exists** (for
`|¬A| ≤ |A|`): a non-zero vector in the extremal total-magnetization sector that is
a simultaneous eigenvector of `(Ŝ_tot)²` (at the predicted value), `(Ŝ_A)²` (at
`s_A(s_A+1)`) and `(Ŝ_¬A)²` (at `s_B(s_B+1)`). -/
theorem exists_jointPredictedCasimir_eigenvector (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ∃ w : (Λ → Fin (N + 1)) → ℂ, w ≠ 0 ∧
      (totalSpinSSquared Λ N).mulVec w =
        ((tasaki23PredictedCasimirValue (V := Λ) A N : ℝ) : ℂ) • w ∧
      (sublatticeSpinSquaredS N A).mulVec w =
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) • w ∧
      (sublatticeSpinSquaredS N (fun x => ! A x)).mulVec w =
        (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) *
          (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) * ((N : ℂ) / 2) + 1)) • w := by
  obtain ⟨w, hw_ne, hw_span, hw_ker⟩ := exists_jointDiagonal_totalSpinSOpPlus_kernel A horient
  -- w lies in the joint Casimir eigenspace W (span ⊆ W).
  have hw_W : w ∈ jointSublatticeCasimirEigenspace (Λ := Λ) A N :=
    (Submodule.span_le.mpr
      (Set.range_subset_iff.mpr (jointDiagonalIterate_mem_jointSublatticeCasimirEigenspace A))) hw_span
  obtain ⟨hw_A, hw_B⟩ := hw_W
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hw_A
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hw_B
  -- w lies in the extremal magnetization sector (span ⊆ magSubspaceS).
  have hw_mag : w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      (((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) :=
    (Submodule.span_le.mpr
      (Set.range_subset_iff.mpr (jointDiagonalIterate_mem_magSubspaceS A))) hw_span
  -- The extremal sector value matches `min(|A|, |¬A|)·N`.
  have hmin : min (Finset.univ.filter (fun x : Λ => A x = true)).card
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := min_eq_right horient
  have hw_mag' : w ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ) / 2) -
      ((min (Finset.univ.filter (fun x : Λ => A x = true)).card
          (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N : ℕ) : ℂ)) := by
    rw [hmin]; exact hw_mag
  -- (Ŝ_tot)² w = predicted, by the extremal highest-weight relation.
  have hw_tot := tasaki23_extremal_highestWeight_totalCasimir_eq_predicted (V := Λ) (N := N) A
    hw_mag' hw_ker
  exact ⟨w, hw_ne, hw_tot, hw_A, hw_B⟩

end LatticeSystem.Quantum
