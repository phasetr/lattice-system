import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace
import LatticeSystem.Quantum.SpinS.MagSubspaceExtremalDim
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit
import LatticeSystem.Quantum.SpinS.CasimirRearrangement
import LatticeSystem.Quantum.SpinS.LadderBoundaryAnnihilation

/-!
# The saturated-ferromagnet ladder lies in the joint
`(H, (Ŝ_{tot})²)` eigenspace

Refines PRs #899 and #900: every iterate
`(Ŝ^-_{tot})^k · |σ_⊤⟩` lies in the **joint** eigenspace
`H-eigenspace at c_J` ∩ `(Ŝ_{tot})²-eigenspace at m_max(m_max+1)`.

The joint eigenspace contains the LI ladder family, hence has
`Module.finrank ℂ ≥ 2m_max + 1`. This is the cleanest dimension
lower bound on the saturated-ferromagnet ground-state sector
satisfying both Heisenberg and Casimir eigenvalue constraints.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The joint (H, `(Ŝ_{tot})²`)-eigenspace at the saturated-ferromagnet
eigenvalues `(c_J, m_max(m_max+1))`. -/
noncomputable def saturatedFerromagnetJointEigenspace
    (J : V → V → ℂ) (N : ℕ) :
    Submodule ℂ ((V → Fin (N + 1)) → ℂ) :=
  Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
      (saturatedFerromagnetEigenvalueS (V := V) J N) ⊓
  Module.End.eigenspace ((totalSpinSSquared V N).mulVecLin)
      (saturatedFerromagnetCasimirEigenvalueS V N)

/-- Each ladder iterate lies in the joint
`(H, (Ŝ_{tot})²)`-eigenspace. -/
theorem ladderIterateUp_mem_saturatedFerromagnetJointEigenspace
    [Nonempty V] (J : V → V → ℂ)
    (k : Fin (Fintype.card V * N + 1)) :
    ladderIterateUp V N k ∈
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  refine ⟨ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace J k, ?_⟩
  exact ladderIterateUp_mem_totalSpinSSquared_eigenspace k

/-- **Joint eigenspace dimension lower bound**: for `[Nonempty V]`,
`saturatedFerromagnetJointEigenspace J N` has
`Module.finrank ℂ ≥ |V|·N + 1 = 2m_max + 1`.

Proof: restrict the LI ladder family to the joint eigenspace,
apply `LinearIndependent.fintype_card_le_finrank`. -/
theorem saturatedFerromagnetJointEigenspace_finrank_ge_succ_card_mul_N
    [Nonempty V] (J : V → V → ℂ) :
    Fintype.card V * N + 1 ≤
      Module.finrank ℂ
        (saturatedFerromagnetJointEigenspace (V := V) J N) := by
  let E := saturatedFerromagnetJointEigenspace (V := V) J N
  let f : Fin (Fintype.card V * N + 1) → E :=
    fun k => ⟨ladderIterateUp V N k,
      ladderIterateUp_mem_saturatedFerromagnetJointEigenspace J k⟩
  have hLI : LinearIndependent ℂ f := by
    have h := ladderIterateUp_linearIndependent (V := V) (N := N)
    exact (LinearIndependent.of_comp E.subtype) (by
      simpa [f] using h)
  have := hLI.fintype_card_le_finrank
  simpa using this

/-- **Highest-weight magnetization sector ∩ joint eigenspace is the
line through `|σ_⊤⟩`.**

In the highest magnetization sector `M = m_max = |V|·N/2`, every
vector is a scalar multiple of `|σ_⊤⟩` (by
`magSubspaceS_mMax_eq_span_allAlignedStateS_zero`, PR #908). Since
`|σ_⊤⟩ = ladderIterateUp V N 0 ∈ saturatedFerromagnetJointEigenspace`,
the intersection equals `Submodule.span ℂ {|σ_⊤⟩}`.

This is the first concrete sector contribution to the upper bound
`finrank(joint) ≤ 2m_max + 1` that closes Tasaki §2.4 Theorem 2.1
(saturated-ferromagnet ground-state subspace is the
`(2m_max + 1)`-dimensional irreducible SU(2) representation). -/
theorem magSubspaceS_mMax_inf_saturatedFerromagnetJointEigenspace
    [Nonempty V] (J : V → V → ℂ) :
    magSubspaceS V N ((Fintype.card V : ℂ) * (N : ℂ) / 2)
      ⊓ saturatedFerromagnetJointEigenspace (V := V) J N =
    Submodule.span ℂ {(allAlignedStateS V N (0 : Fin (N + 1)) :
      (V → Fin (N + 1)) → ℂ)} := by
  rw [magSubspaceS_mMax_eq_span_allAlignedStateS_zero]
  apply le_antisymm
  · exact inf_le_left
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Submodule.mem_inf]
    refine ⟨Submodule.subset_span (Set.mem_singleton _), ?_⟩
    have h0 : ladderIterateUp V N (0 : Fin (Fintype.card V * N + 1)) =
        allAlignedStateS V N (0 : Fin (N + 1)) := by
      unfold ladderIterateUp
      simp
    rw [← h0]
    exact ladderIterateUp_mem_saturatedFerromagnetJointEigenspace J
      (0 : Fin (Fintype.card V * N + 1))

/-- **Lowest-weight magnetization sector ∩ joint eigenspace is the line
through `|σ_⊥⟩`.**

Symmetric statement to the `M = m_max` case: in the lowest magnetization
sector `M = -m_max`, every vector is a scalar multiple of `|σ_⊥⟩`. Uses
`magSubspaceS_neg_mMax_eq_span_allAlignedStateS_last` (PR #908) and
the fact that `|σ_⊥⟩` is both an H-eigenvector and a Casimir
eigenvector at the saturated values. -/
theorem magSubspaceS_neg_mMax_inf_saturatedFerromagnetJointEigenspace
    [Nonempty V] (J : V → V → ℂ) :
    magSubspaceS V N (-((Fintype.card V : ℂ) * (N : ℂ) / 2))
      ⊓ saturatedFerromagnetJointEigenspace (V := V) J N =
    Submodule.span ℂ {(allAlignedStateS V N (Fin.last N) :
      (V → Fin (N + 1)) → ℂ)} := by
  rw [magSubspaceS_neg_mMax_eq_span_allAlignedStateS_last]
  apply le_antisymm
  · exact inf_le_left
  · rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      Submodule.mem_inf]
    refine ⟨Submodule.subset_span (Set.mem_singleton _), ?_⟩
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff,
        Matrix.mulVecLin_apply, saturatedFerromagnetEigenvalueS_explicit,
        heisenbergHamiltonianS_mulVec_allAlignedStateS_last_eigenvalue]
    · rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      simp [totalSpinSSquared_mulVec_allAlignedStateS_last_eigenvalue,
        saturatedFerromagnetCasimirEigenvalueS]

/-- Spin-`S` analogue of `mulVec_preserves_eigenvalue_of_commute`:
generic eigenvalue preservation under commuting operators. If
`Commute A B` and `A.mulVec v = λ • v`, then `A.mulVec (B.mulVec v)
= λ • B.mulVec v`. -/
theorem mulVec_preserves_eigenvalue_of_commuteS
    {A B : ManyBodyOpS V N} (h : Commute A B)
    {lam : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : A.mulVec v = lam • v) :
    A.mulVec (B.mulVec v) = lam • B.mulVec v := by
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_smul]

/-- **`Ŝ^+_tot` maps `joint ⊓ H_M` into `joint ⊓ H_{M+1}`**: for any
`v ∈ saturatedFerromagnetJointEigenspace J N ⊓ magSubspaceS V N M`,
the vector `Ŝ^+_tot · v` lies in the next-higher magnetisation sector
of the joint eigenspace.

This is the inductive step in the chain
`dim(joint ⊓ H_M) ≤ dim(joint ⊓ H_{M+1})` for `M < m_max` (via
injectivity of `Ŝ^+_tot` on the joint eigenspace away from the
highest-weight sector), which propagates the `dim = 1` bound from
`H_{m_max}` (PR #2759) down to every sector. -/
theorem totalSpinSOpPlus_mulVec_mem_saturatedFerromagnetJointEigenspace_inf_magSubspaceS
    {J : V → V → ℂ} {M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N M) :
    (totalSpinSOpPlus V N).mulVec v ∈
      saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N (M + 1) := by
  rw [Submodule.mem_inf] at hv
  obtain ⟨hjoint, hM⟩ := hv
  unfold saturatedFerromagnetJointEigenspace at hjoint
  rw [Submodule.mem_inf] at hjoint
  obtain ⟨hH, hCas⟩ := hjoint
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hH hCas
  rw [mem_magSubspaceS_iff] at hM
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · unfold saturatedFerromagnetJointEigenspace
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact mulVec_preserves_eigenvalue_of_commuteS
        (heisenbergHamiltonianS_commute_totalSpinSOpPlus J) hH
    · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact mulVec_preserves_eigenvalue_of_commuteS
        totalSpinSSquared_commute_totalSpinSOpPlus hCas
  · rw [mem_magSubspaceS_iff]
    exact totalSpinSOp3_mulVec_totalSpinSOpPlus_mulVec_eigenvec hM

/-- **Injectivity of `Ŝ^+_tot` on `joint ⊓ H_M` away from the highest
weight**: for any `v ∈ saturatedFerromagnetJointEigenspace J N ⊓
magSubspaceS V N M` with `M ≠ m_max = |V|·N/2`, if
`Ŝ^+_tot · v = 0` then `v = 0`.

Argument via the MinusPlus Casimir rearrangement
`Ŝ^-_tot · Ŝ^+_tot = (Ŝ_tot)² − (Ŝ^z_tot)² − Ŝ^z_tot` (PR #894):
applying both sides to `v` gives
`Ŝ^-_tot · Ŝ^+_tot · v = (m_max(m_max+1) − M² − M) · v
                         = (m_max − M)(m_max + M + 1) · v`.
If `Ŝ^+_tot · v = 0`, the LHS is `0`, so the scalar factor must
annihilate `v`. The case `M = -m_max - 1` is ruled out because
`magSubspaceS V N (-m_max - 1) = ⊥` (PR #905), and `M ≠ m_max`
is the hypothesis; together they force `v = 0`.

This is the kernel-trivial step for the chain
`dim(joint ⊓ H_M) ≤ dim(joint ⊓ H_{M+1})` toward Tasaki §2.4
Theorem 2.1. -/
theorem totalSpinSOpPlus_mulVec_eq_zero_imp_eq_zero_of_mem_saturatedFerromagnetJointEigenspace_inf_magSubspaceS
    [Nonempty V]
    {J : V → V → ℂ} {M : ℂ}
    (hMne : M ≠ (Fintype.card V : ℂ) * (N : ℂ) / 2)
    {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N M)
    (h_ker : (totalSpinSOpPlus V N).mulVec v = 0) :
    v = 0 := by
  rw [Submodule.mem_inf] at hv
  obtain ⟨hjoint, hMmem⟩ := hv
  unfold saturatedFerromagnetJointEigenspace at hjoint
  rw [Submodule.mem_inf] at hjoint
  obtain ⟨_hH, hCas⟩ := hjoint
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hCas
  have hM := (mem_magSubspaceS_iff (Λ := V) (N := N) M v).mp hMmem
  -- `Ŝ^-_tot · Ŝ^+_tot · v = ((Ŝ_tot)² − (Ŝ^z_tot)² − Ŝ^z_tot) · v`.
  have hRearr := totalSpinSOpMinus_mul_totalSpinSOpPlus_eq_casimir_minus_z_sq_sub_z
    (V := V) (N := N)
  -- Apply both sides to v.
  have hLHS : ((totalSpinSOpMinus V N) * (totalSpinSOpPlus V N)).mulVec v
      = 0 := by
    rw [← Matrix.mulVec_mulVec, h_ker, Matrix.mulVec_zero]
  have hRHS : ((totalSpinSSquared V N - totalSpinSOp3 V N * totalSpinSOp3 V N -
        totalSpinSOp3 V N) : ManyBodyOpS V N).mulVec v =
        (saturatedFerromagnetCasimirEigenvalueS V N - M * M - M) • v := by
    rw [show (totalSpinSSquared V N - totalSpinSOp3 V N * totalSpinSOp3 V N -
      totalSpinSOp3 V N : ManyBodyOpS V N) =
      totalSpinSSquared V N - (totalSpinSOp3 V N * totalSpinSOp3 V N +
        totalSpinSOp3 V N) from by abel]
    rw [Matrix.sub_mulVec, hCas, Matrix.add_mulVec]
    have h_sq : (totalSpinSOp3 V N * totalSpinSOp3 V N).mulVec v =
        (M * M) • v := by
      rw [← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul, hM, smul_smul]
    rw [h_sq, hM, ← sub_sub, ← sub_smul, ← sub_smul]
  have hzero : (saturatedFerromagnetCasimirEigenvalueS V N - M * M - M) • v = 0 := by
    rw [← hRHS, ← hRearr]
    exact hLHS
  -- Factor: saturatedFerromagnetCasimirEigenvalueS - M² - M = (m_max - M)(m_max + M + 1).
  unfold saturatedFerromagnetCasimirEigenvalueS at hzero
  set mmax : ℂ := (Fintype.card V : ℂ) * (N : ℂ) / 2 with hmmax_def
  have hfactor : mmax * (mmax + 1) - M * M - M = (mmax - M) * (mmax + M + 1) := by
    ring
  rw [hfactor] at hzero
  rcases smul_eq_zero.mp hzero with h | h
  · -- (mmax - M)(mmax + M + 1) = 0. Two cases.
    rcases mul_eq_zero.mp h with h1 | h2
    · -- mmax - M = 0, contradicting hMne.
      exact (hMne (sub_eq_zero.mp h1).symm).elim
    · -- mmax + M + 1 = 0, i.e., M = -mmax - 1. magSubspaceS V N M = ⊥.
      have hMeq : M = -mmax - 1 := by linear_combination h2
      -- Show magSubspaceS V N (-mmax - 1) = ⊥.
      have hbot : magSubspaceS V N M = ⊥ := by
        rw [hMeq]
        apply magSubspaceS_eq_bot_of_not_in_spectrum
        intro σ
        have := magEigenvalueS_ne_neg_mMax_sub_one (V := V) (N := N) σ
        -- this : magEigenvalueS σ ≠ (|V|·N : ℂ)/2 - ((|V|·N : ℕ) + 1 : ℕ)
        -- We need : magEigenvalueS σ ≠ -mmax - 1
        -- mmax = (|V|·N : ℂ)/2, so -mmax - 1 = -(|V|·N : ℂ)/2 - 1
        -- = (|V|·N : ℂ)/2 - (|V|·N : ℂ) - 1 = (|V|·N : ℂ)/2 - ((|V|·N : ℕ) + 1 : ℕ)
        -- (after push_cast).
        intro heq
        apply this
        rw [heq]
        push_cast
        ring
      rw [hbot] at hMmem
      exact (Submodule.mem_bot _).mp hMmem
  · exact h

end LatticeSystem.Quantum
