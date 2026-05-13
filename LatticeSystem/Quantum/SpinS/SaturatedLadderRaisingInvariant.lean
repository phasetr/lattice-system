import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishing

/-!
# Invariance of the saturated-ferromagnet joint eigenspace under `Ŝ^+_tot`

For `[Nonempty V]`, the saturated-ferromagnet joint
`(H, (Ŝ_{tot})²)`-eigenspace is invariant under the raising
operator `Ŝ^+_{tot}`. Together with the lowering-side counterpart
(PR #2770), this completes the operational SU(2)-irrep statement
for the joint eigenspace identified in Tasaki §2.4 Theorem 2.1
(PR #2768).

Pointwise: on each ladder iterate `ladderIterateUp V N k`,

  `Ŝ^+_{tot} · ladderIterateUp V N ⟨0, _⟩ = 0`
        (top-weight annihilation, PR #877),
  `Ŝ^+_{tot} · ladderIterateUp V N ⟨j+1, _⟩
      = ((j+1) · (|V|·N − j)) • ladderIterateUp V N ⟨j, _⟩`
        (Casimir-rearrangement scalar from PR #882 + PR #887 + PR #894).

These per-iterate identities lift via `Submodule.map_span` and
`Submodule.span_le` to invariance of the full joint eigenspace
`joint = span(ladderIterateUp)` (PR #2768).

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Top-weight annihilation on the first ladder iterate**: since
`ladderIterateUp V N ⟨0, _⟩ = |σ_⊤⟩`, applying `Ŝ^+_{tot}` gives `0`
by PR #877's top-weight identity. -/
theorem totalSpinSOpPlus_mulVec_ladderIterateUp_zero
    (h : 0 < Fintype.card V * N + 1 := Nat.succ_pos _) :
    (totalSpinSOpPlus V N).mulVec
        (ladderIterateUp V N ⟨0, h⟩) = 0 := by
  unfold ladderIterateUp
  simp only [pow_zero, Matrix.one_mulVec]
  exact totalSpinSOpPlus_mulVec_allAlignedStateS_zero

/-- **Raising on a non-first ladder iterate**: for `j` with
`j + 1 < |V|·N + 1` (i.e., the iterate has a predecessor in range),

  `Ŝ^+_{tot} · ladderIterateUp V N ⟨j + 1, h⟩
      = ((j + 1) · (|V|·N − j)) • ladderIterateUp V N ⟨j, h'⟩`

via the Casimir-rearrangement scalar identity of PR #894 (composed
with PR #882 / PR #887 / PR #909) packaged as
`totalSpinSOpPlus_mulVec_totalSpinSOpMinus_pow_succ_allAlignedStateS_zero`. -/
theorem totalSpinSOpPlus_mulVec_ladderIterateUp_succ
    [Nonempty V] (j : ℕ) (h : j + 1 < Fintype.card V * N + 1) :
    (totalSpinSOpPlus V N).mulVec
        (ladderIterateUp V N ⟨j + 1, h⟩) =
      (((j + 1 : ℕ) : ℂ) *
          ((Fintype.card V : ℂ) * (N : ℂ) - (j : ℂ))) •
        ladderIterateUp V N ⟨j, Nat.lt_of_succ_lt h⟩ := by
  unfold ladderIterateUp
  simp only []
  exact totalSpinSOpPlus_mulVec_totalSpinSOpMinus_pow_succ_allAlignedStateS_zero j

/-- **`Ŝ^+_{tot}` invariance of the saturated-ferromagnet joint
eigenspace**: for `[Nonempty V]`,

  `Ŝ^+_{tot} (joint J N) ⊆ joint J N`.

Combining `joint = span(ladderIterateUp)` (PR #2768) with the
per-iterate action above: each ladderIterateUp under `Ŝ^+_{tot}`
is either `0` (k.val = 0, top annihilation) or a scalar multiple of
the previous iterate (k.val = j + 1 > 0, Casimir-rearrangement
shift). Both stay in `span`. `Submodule.map_span` +
`Submodule.span_le` packages this. -/
theorem saturatedFerromagnetJointEigenspace_totalSpinSOpPlus_invariant
    [Nonempty V] (J : V → V → ℂ) :
    Submodule.map (totalSpinSOpPlus V N).mulVecLin
        (saturatedFerromagnetJointEigenspace (V := V) J N) ≤
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  rw [saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp J,
      Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro w ⟨_, ⟨k, rfl⟩, rfl⟩
  rcases Nat.eq_zero_or_pos k.val with hk0 | hkpos
  · -- k.val = 0: top annihilation, image = 0.
    have hk_eq : k = ⟨0, Nat.succ_pos _⟩ := Fin.ext hk0
    rw [Matrix.mulVecLin_apply, hk_eq,
        totalSpinSOpPlus_mulVec_ladderIterateUp_zero]
    exact Submodule.zero_mem _
  · -- k.val = j + 1 > 0: image is a scalar multiple of iterate j.
    obtain ⟨j, hj_eq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hkpos)
    have hj_eq' : k.val = j + 1 := hj_eq
    have hj_lt : j + 1 < Fintype.card V * N + 1 := by
      rw [← hj_eq']; exact k.isLt
    have hk_eq : k = ⟨j + 1, hj_lt⟩ := Fin.ext hj_eq'
    rw [Matrix.mulVecLin_apply, hk_eq,
        totalSpinSOpPlus_mulVec_ladderIterateUp_succ j hj_lt]
    refine Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨⟨j, Nat.lt_of_succ_lt hj_lt⟩, rfl⟩

end LatticeSystem.Quantum
