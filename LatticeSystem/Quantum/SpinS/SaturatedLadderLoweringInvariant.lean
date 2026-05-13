import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import LatticeSystem.Quantum.SpinS.LadderBoundaryAnnihilation

/-!
# Invariance of the saturated-ferromagnet joint eigenspace under `Ŝ^-_tot`

For `[Nonempty V]`, the saturated-ferromagnet joint
`(H, (Ŝ_{tot})²)`-eigenspace is invariant under the lowering
operator `Ŝ^-_{tot}`. This is the operational SU(2)-irrep statement
at the lowering level: the `(2m_max + 1)`-dimensional joint
eigenspace identified in Tasaki §2.4 Theorem 2.1 (PR #2768) carries
a representation of the lowering side of `su(2)`.

Pointwise: on each ladder iterate `ladderIterateUp V N k`,

  `Ŝ^-_{tot} · ladderIterateUp V N k =
      ladderIterateUp V N ⟨k.val + 1, _⟩`  if  `k.val + 1 < |V|·N + 1`,
  `Ŝ^-_{tot} · ladderIterateUp V N (Fin.last _) = 0`  (boundary annihilation).

These per-iterate identities follow definitionally from
`ladderIterateUp V N k = (Ŝ^-_{tot})^{k.val} · |σ_⊤⟩` and `pow_succ'`
combined with PR #905's boundary annihilation. They lift via
`Submodule.map_span` and `Submodule.span_le` to invariance of the
full joint eigenspace `joint = span(ladderIterateUp)` (PR #2768).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Lowering on a non-last ladder iterate**: for `k.val + 1` still
in range, `Ŝ^-_{tot}` shifts the iterate to the next one. -/
theorem totalSpinSOpMinus_mulVec_ladderIterateUp_interior
    (k : Fin (Fintype.card V * N + 1))
    (hk : k.val + 1 < Fintype.card V * N + 1) :
    (totalSpinSOpMinus V N).mulVec (ladderIterateUp V N k) =
      ladderIterateUp V N ⟨k.val + 1, hk⟩ := by
  unfold ladderIterateUp
  rw [Matrix.mulVec_mulVec, ← pow_succ']

/-- **Boundary annihilation for the last ladder iterate**: applying
`Ŝ^-_{tot}` to `ladderIterateUp V N (Fin.last _)` gives `0`. -/
theorem totalSpinSOpMinus_mulVec_ladderIterateUp_last [Nonempty V] :
    (totalSpinSOpMinus V N).mulVec
        (ladderIterateUp V N (Fin.last (Fintype.card V * N))) = 0 := by
  unfold ladderIterateUp
  rw [Fin.val_last, Matrix.mulVec_mulVec, ← pow_succ']
  exact totalSpinSOpMinus_pow_succ_card_mul_N_allAlignedStateS_zero

/-- **`Ŝ^-_{tot}` invariance of the saturated-ferromagnet joint
eigenspace**: for `[Nonempty V]`,

  `Ŝ^-_{tot} (joint J N) ⊆ joint J N`.

Combining `joint = span(ladderIterateUp)` (PR #2768) with the
per-iterate action above: each ladderIterateUp under `Ŝ^-_{tot}` is
either the next iterate (still in `span`) or `0` (trivially in any
submodule). `Submodule.map_span` + `Submodule.span_le` packages this. -/
theorem saturatedFerromagnetJointEigenspace_totalSpinSOpMinus_invariant
    [Nonempty V] (J : V → V → ℂ) :
    Submodule.map (totalSpinSOpMinus V N).mulVecLin
        (saturatedFerromagnetJointEigenspace (V := V) J N) ≤
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  rw [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp J,
      Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro w ⟨_, ⟨k, rfl⟩, rfl⟩
  by_cases hk : k.val + 1 < Fintype.card V * N + 1
  · rw [Matrix.mulVecLin_apply,
        totalSpinSOpMinus_mulVec_ladderIterateUp_interior k hk]
    exact Submodule.subset_span ⟨⟨k.val + 1, hk⟩, rfl⟩
  · have hk_eq : k = Fin.last (Fintype.card V * N) := by
      push Not at hk
      have hk1 := k.isLt
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [Matrix.mulVecLin_apply, hk_eq,
        totalSpinSOpMinus_mulVec_ladderIterateUp_last]
    exact Submodule.zero_mem _

end LatticeSystem.Quantum
