import LatticeSystem.Quantum.SpinS.JointDiagonalRaiseImage

/-!
# A non-trivial `Ŝ⁺_tot`-kernel in the diagonal span

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

Rank–nullity: the `M+1` linearly-independent diagonal iterates (`M = |¬A|·N`,
#3704) span an `(M+1)`-dimensional space, while `Ŝ⁺_tot` maps them into the
`≤ M`-dimensional lower-index span (#3706).  Hence the `M+1` images are linearly
dependent, giving a non-trivial combination `w* = ∑ c_{k_A} · jointDiagonalIterate`
with `Ŝ⁺_tot w* = 0` and `w* ≠ 0` (by diagonal LI).  This `w*` is the
minimal-total-spin highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Non-trivial `Ŝ⁺_tot`-kernel in the diagonal span** (for `|¬A| ≤ |A|`): there is
a non-zero vector in the span of the diagonal family annihilated by `Ŝ⁺_tot`. -/
theorem exists_jointDiagonal_totalSpinSOpPlus_kernel (A : Λ → Bool)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ∃ w : (Λ → Fin (N + 1)) → ℂ, w ≠ 0 ∧
      w ∈ Submodule.span ℂ (Set.range (jointDiagonalIterate A N)) ∧
      (totalSpinSOpPlus Λ N).mulVec w = 0 := by
  classical
  set M := (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N with hM
  set E := Submodule.span ℂ (Set.range (jointLowerDiagonalIterate A N)) with hE
  -- finrank E ≤ M.
  have hE_le : finrank ℂ E ≤ M := by
    refine le_trans (finrank_span_le_card (Set.range (jointLowerDiagonalIterate A N))) ?_
    rw [Set.toFinset_range]
    refine le_trans (Finset.card_image_le) (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_fin]
  -- the lifted image family gbar : Fin (M+1) → E.
  let gbar : Fin (M + 1) → E := fun kA =>
    ⟨(totalSpinSOpPlus Λ N).mulVec (jointDiagonalIterate A N kA),
      totalSpinSOpPlus_mulVec_jointDiagonalIterate_mem_span A kA⟩
  -- gbar is linearly dependent (M+1 vectors in finrank-≤M space).
  have hnotLI : ¬ LinearIndependent ℂ gbar := by
    intro hLI
    have hcard := hLI.fintype_card_le_finrank
    rw [Fintype.card_fin] at hcard
    omega
  rw [Fintype.not_linearIndependent_iff] at hnotLI
  obtain ⟨c, hsum, i0, hi0⟩ := hnotLI
  refine ⟨∑ kA, c kA • jointDiagonalIterate A N kA, ?_, ?_, ?_⟩
  · -- w ≠ 0, by linear independence of the diagonal family.
    intro hw0
    have hLI_d := jointDiagonalIterate_linearIndependent (Λ := Λ) (N := N) A horient
    have := (Fintype.linearIndependent_iff.mp hLI_d) c hw0
    exact hi0 (this i0)
  · -- w ∈ span (range jointDiagonalIterate).
    exact Submodule.sum_mem _ (fun kA _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨kA, rfl⟩))
  · -- Ŝ⁺_tot · w = 0.
    rw [Matrix.mulVec_sum]
    simp_rw [Matrix.mulVec_smul]
    have hcoe := congrArg (Subtype.val) hsum
    simpa [gbar, Submodule.coe_sum, Submodule.coe_smul] using hcoe

end LatticeSystem.Quantum
