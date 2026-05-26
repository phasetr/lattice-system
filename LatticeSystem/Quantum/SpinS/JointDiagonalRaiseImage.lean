import LatticeSystem.Quantum.SpinS.JointDiagonalLI
import LatticeSystem.Quantum.SpinS.JointLadderRaiseBoundary

/-!
# `Ŝ⁺_tot` maps the diagonal family into the lower-index span

Scaffold for the minimal-total-spin joint eigenstate (Issue #3687 / #3674, the
final obligation of the sound Tasaki §2.5 Theorem 2.3 route, #3542).

Writing `M := |¬A|·N`, the diagonal family `jointDiagonalIterate A N` (`M+1`
members at total magnetization `s_A − s_B`) is mapped by `Ŝ⁺_tot = Ŝ_A^+ + Ŝ_¬A^+`
into the span of the **lower-index** family `jointLowerDiagonalIterate A N`
(`M` members at total magnetization `s_A − s_B + 1`): `Ŝ_A^+` lowers the `A`-index
(#3701, or annihilates at `0`, #3705) and `Ŝ_¬A^+` lowers the `¬A`-index (#3702, or
annihilates at `0`, #3705).  Since `M+1` vectors land in an `≤ M`-dimensional span,
the rank–nullity argument produces a non-trivial kernel of `Ŝ⁺_tot` on the diagonal
span — the minimal-total-spin highest-weight state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The lower-index diagonal family at total magnetization `s_A − s_B + 1`:
`j ↦ jointLadderIterateDownS A N j (|¬A|·N − 1 − j)`, `j = 0, …, |¬A|·N − 1`. -/
noncomputable def jointLowerDiagonalIterate (A : Λ → Bool) (N : ℕ)
    (j : Fin ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N)) :
    (Λ → Fin (N + 1)) → ℂ :=
  jointLadderIterateDownS A N j.val
    ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N - 1 - j.val)

/-- **`Ŝ⁺_tot` maps the diagonal family into the lower-index span**:
`Ŝ⁺_tot · jointDiagonalIterate A N kA ∈ span (range (jointLowerDiagonalIterate A N))`. -/
theorem totalSpinSOpPlus_mulVec_jointDiagonalIterate_mem_span (A : Λ → Bool)
    (kA : Fin ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N + 1)) :
    (totalSpinSOpPlus Λ N).mulVec (jointDiagonalIterate A N kA) ∈
      Submodule.span ℂ (Set.range (jointLowerDiagonalIterate A N)) := by
  obtain ⟨kAv, hkAv⟩ := kA
  set M := (Finset.univ.filter (fun x : Λ => (! A x) = true)).card * N with hM
  have hkA_le : kAv ≤ M := Nat.lt_succ_iff.mp hkAv
  have hdiag : jointDiagonalIterate A N ⟨kAv, hkAv⟩ =
      jointLadderIterateDownS A N kAv (M - kAv) := rfl
  rw [hdiag, totalSpinSOpPlus_eq_sublattice_sum (N := N) A, Matrix.add_mulVec]
  refine Submodule.add_mem _ ?_ ?_
  · -- Ŝ_A^+ term: lowers the A-index (or annihilates at kA = 0).
    rcases Nat.eq_zero_or_pos kAv with hk0 | hkpos
    · rw [hk0, sublatticeSpinSOpPlus_mulVec_jointLadderIterateDownS_zeroA]
      exact Submodule.zero_mem _
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
      rw [hk, sublatticeSpinSOpPlus_mulVec_jointLadderIterateDownS_succA]
      apply Submodule.smul_mem
      have hk_lt : k < M := by omega
      have heq : M - (k + 1) = M - 1 - k := by omega
      rw [heq]
      exact Submodule.subset_span ⟨⟨k, hk_lt⟩, rfl⟩
  · -- Ŝ_¬A^+ term: lowers the ¬A-index (or annihilates at kB = 0).
    rcases Nat.eq_zero_or_pos (M - kAv) with hk0 | hkpos
    · rw [hk0, sublatticeSpinSOpPlus_complement_mulVec_jointLadderIterateDownS_zeroB]
      exact Submodule.zero_mem _
    · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hkpos.ne'
      rw [hk, sublatticeSpinSOpPlus_complement_mulVec_jointLadderIterateDownS_succB]
      apply Submodule.smul_mem
      have hkA_lt : kAv < M := by omega
      have heq : k = M - 1 - kAv := by omega
      rw [heq]
      exact Submodule.subset_span ⟨⟨kAv, hkA_lt⟩, rfl⟩

end LatticeSystem.Quantum
