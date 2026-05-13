import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace
import LatticeSystem.Quantum.SpinS.MagSubspaceExtremalDim
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit

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

end LatticeSystem.Quantum
