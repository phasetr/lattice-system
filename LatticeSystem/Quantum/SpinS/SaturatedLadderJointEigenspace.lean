import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace
import LatticeSystem.Quantum.SpinS.MagSubspaceExtremalDim
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit
import LatticeSystem.Quantum.SpinS.CasimirRearrangement
import LatticeSystem.Quantum.SpinS.LadderBoundaryAnnihilation
import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum
import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishing

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

/-- The raising operator `Ŝ^+_tot` as a linear map from
`joint ⊓ H_M` into `joint ⊓ H_{M+1}`, packaged via
`totalSpinSOpPlus_mulVec_mem_saturatedFerromagnetJointEigenspace_inf_magSubspaceS`. -/
noncomputable def totalSpinSOpPlusJointMagShift
    (J : V → V → ℂ) (M : ℂ) :
    (saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N M : Submodule ℂ ((V → Fin (N + 1)) → ℂ))
      →ₗ[ℂ]
    (saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N (M + 1) : Submodule ℂ ((V → Fin (N + 1)) → ℂ)) where
  toFun v := ⟨(totalSpinSOpPlus V N).mulVec v.val,
    totalSpinSOpPlus_mulVec_mem_saturatedFerromagnetJointEigenspace_inf_magSubspaceS
      v.property⟩
  map_add' a b := by
    ext
    simp [Matrix.mulVec_add]
  map_smul' c v := by
    ext
    simp [Matrix.mulVec_smul]

/-- **`Ŝ^+_tot` is injective on `joint ⊓ H_M` away from the highest
weight, as a linear map between the joint-magnetisation sectors**.

Direct consequence of the kernel-trivial result
`totalSpinSOpPlus_mulVec_eq_zero_imp_eq_zero_of_mem_saturatedFerromagnetJointEigenspace_inf_magSubspaceS`. -/
theorem totalSpinSOpPlusJointMagShift_injective [Nonempty V]
    (J : V → V → ℂ) {M : ℂ}
    (hMne : M ≠ (Fintype.card V : ℂ) * (N : ℂ) / 2) :
    Function.Injective (totalSpinSOpPlusJointMagShift (V := V) (N := N) J M) := by
  intro a b hab
  apply Subtype.ext
  have hsub :
      (totalSpinSOpPlus V N).mulVec (a.val - b.val) = 0 := by
    rw [Matrix.mulVec_sub]
    have := Subtype.ext_iff.mp hab
    simp [totalSpinSOpPlusJointMagShift] at this
    rw [this]
    simp
  have hmem : a.val - b.val ∈
      saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N M := by
    exact Submodule.sub_mem _ a.property b.property
  have h0 :=
    totalSpinSOpPlus_mulVec_eq_zero_imp_eq_zero_of_mem_saturatedFerromagnetJointEigenspace_inf_magSubspaceS
      hMne hmem hsub
  exact sub_eq_zero.mp h0

/-- **`dim(joint ⊓ H_M) ≤ dim(joint ⊓ H_{M+1})` for `M ≠ m_max`**.
The chain inequality propagating the 1-dim bound from `H_{m_max}`
(PR #2759) up the magnetisation ladder (toward Tasaki §2.4
Theorem 2.1). -/
theorem saturatedFerromagnetJointEigenspace_inf_magSubspaceS_finrank_le_succ
    [Nonempty V] (J : V → V → ℂ) {M : ℂ}
    (hMne : M ≠ (Fintype.card V : ℂ) * (N : ℂ) / 2) :
    Module.finrank ℂ
      (saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N M : Submodule ℂ ((V → Fin (N + 1)) → ℂ)) ≤
    Module.finrank ℂ
      (saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N (M + 1) : Submodule ℂ ((V → Fin (N + 1)) → ℂ)) :=
  LinearMap.finrank_le_finrank_of_injective
    (totalSpinSOpPlusJointMagShift_injective J hMne)

/-- **`dim(joint ⊓ H_{m_max - k}) ≤ 1` for every `k : ℕ`**.

Per-sector bound on the joint eigenspace dimension, parameterised by
the integer offset `k` from the highest-weight magnetisation
`m_max = |V|·N/2`. Proved by induction on `k`:
- `k = 0`: `joint ⊓ H_{m_max} = span {|σ_⊤⟩}` is 1-dim (PR #2759).
- `k → k + 1`: at `M = m_max - (k + 1)` we have `M ≠ m_max`, so the
  finrank chain (`saturatedFerromagnetJointEigenspace_inf_magSubspaceS_finrank_le_succ`)
  gives `finrank(joint ⊓ H_M) ≤ finrank(joint ⊓ H_{M + 1})
                                = finrank(joint ⊓ H_{m_max - k}) ≤ 1` by IH.

This is the iterated form of the chain. Summing over the
`2m_max + 1` values of `k ∈ {0, 1, ..., 2m_max}` corresponding to
the spectrum of `Ŝ^z_tot` yields `dim(joint) ≤ 2m_max + 1`, the
final ingredient for Tasaki §2.4 Theorem 2.1. -/
theorem saturatedFerromagnetJointEigenspace_inf_magSubspaceS_finrank_le_one
    [Nonempty V] (J : V → V → ℂ) (k : ℕ) :
    Module.finrank ℂ
      (saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k : ℂ))
        : Submodule ℂ ((V → Fin (N + 1)) → ℂ)) ≤ 1 := by
  induction k with
  | zero =>
    -- Base: M = m_max - 0 = m_max. Use PR #2759.
    have h_eq : ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((0 : ℕ) : ℂ) =
        (Fintype.card V : ℂ) * (N : ℂ) / 2 := by
      push_cast
      ring
    rw [h_eq, inf_comm,
      magSubspaceS_mMax_inf_saturatedFerromagnetJointEigenspace J]
    -- finrank (span {|σ_⊤⟩}) = 1.
    rw [finrank_span_singleton]
    · exact allAlignedStateS_ne_zero (0 : Fin (N + 1))
  | succ n ih =>
    -- Step: M = m_max - (n+1). Apply chain to get ≤ finrank at m_max - n ≤ 1 by IH.
    have hMne : ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((n + 1 : ℕ) : ℂ) ≠
        (Fintype.card V : ℂ) * (N : ℂ) / 2 := by
      intro h
      have : ((n + 1 : ℕ) : ℂ) = 0 := by linear_combination -h
      have hh : (n + 1 : ℝ) = 0 := by exact_mod_cast this
      linarith
    have h_chain := saturatedFerromagnetJointEigenspace_inf_magSubspaceS_finrank_le_succ
      (V := V) (N := N) J hMne
    have h_succ_eq : (((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((n + 1 : ℕ) : ℂ)) + 1 =
        ((Fintype.card V : ℂ) * (N : ℂ) / 2) - ((n : ℕ) : ℂ) := by
      push_cast
      ring
    rw [h_succ_eq] at h_chain
    exact le_trans h_chain ih

/-- **Per-sector identification**: for `k ∈ Fin (|V|·N + 1)`,
`joint ⊓ H_{m_max − k} = span {ladderIterateUp V N k}`.

The 1-dim subspace `joint ⊓ H_{m_max − k}` (from PR #2763) is
spanned by the non-zero ladder iterate
`ladderIterateUp V N k = (Ŝ^-_tot)^k · |σ_⊤⟩` (non-zero from
PR #895). Since `ladderIterateUp V N k` lies in the subspace
(as a member of joint by `ladderIterateUp_mem_saturatedFerromagnetJointEigenspace`,
and of `H_{m_max − k}` by `totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS`),
the singleton-span and the subspace coincide.

The 2m_max + 1 spectrum values `k ∈ {0, ..., 2m_max}` together with
the magnetization direct-sum decomposition (PR #889) will identify
`joint = span(ladderIterateUp)` (subsequent PR) and complete
Tasaki §2.4 Theorem 2.1. -/
theorem saturatedFerromagnetJointEigenspace_inf_magSubspaceS_eq_span_ladderIterateUp
    [Nonempty V] (J : V → V → ℂ) (k : Fin (Fintype.card V * N + 1)) :
    saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N
          (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) =
    Submodule.span ℂ {ladderIterateUp V N k} := by
  apply le_antisymm
  · -- LHS ⊆ span {ladderIterateUp V N k}.
    -- The subspace is ≤ 1-dim and contains a non-zero ladder iterate.
    have h_le_one := saturatedFerromagnetJointEigenspace_inf_magSubspaceS_finrank_le_one
      (V := V) (N := N) J k.val
    have h_mem : ladderIterateUp V N k ∈
        saturatedFerromagnetJointEigenspace (V := V) J N
          ⊓ magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) := by
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · exact ladderIterateUp_mem_saturatedFerromagnetJointEigenspace J k
      · -- ladderIterateUp V N k ∈ magSubspaceS V N (m_max - k.val).
        unfold ladderIterateUp
        exact totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS k.val
    have h_ne : ladderIterateUp V N k ≠ 0 := by
      unfold ladderIterateUp
      have hk_le : k.val ≤ Fintype.card V * N := by
        have := k.isLt
        omega
      exact totalSpinSOpMinus_pow_allAlignedStateS_zero_ne_zero hk_le
    have h_span_le :
        Submodule.span ℂ {ladderIterateUp V N k} ≤
        saturatedFerromagnetJointEigenspace (V := V) J N
          ⊓ magSubspaceS V N
            (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact h_mem
    -- finrank of `Submodule.span ℂ {ladderIterateUp V N k}` is 1.
    have h_span_finrank :
        Module.finrank ℂ
          (Submodule.span ℂ {ladderIterateUp V N k} :
            Submodule ℂ ((V → Fin (N + 1)) → ℂ)) = 1 :=
      finrank_span_singleton h_ne
    -- finrank ≥ 1 from the containment; finrank ≤ 1 from h_le_one.
    -- Hence finrank = 1 and span = LHS.
    have h_finrank_le : Module.finrank ℂ
          (saturatedFerromagnetJointEigenspace (V := V) J N
            ⊓ magSubspaceS V N
              (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) :
            Submodule ℂ ((V → Fin (N + 1)) → ℂ)) ≤ 1 := h_le_one
    -- Apply Submodule.eq_of_le_of_finrank_le: span ≤ LHS and finrank LHS ≤ finrank span give span = LHS.
    refine le_of_eq (Submodule.eq_of_le_of_finrank_le h_span_le ?_).symm
    rw [h_span_finrank]
    exact h_finrank_le
  · -- span {ladderIterateUp V N k} ⊆ LHS.
    rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · exact ladderIterateUp_mem_saturatedFerromagnetJointEigenspace J k
    · unfold ladderIterateUp
      exact totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS k.val

/-! ## Magnetisation projection (pointwise)

Concrete projector `magProjFn M v` mapping each component of `v`
through the magnetisation filter. Used to decompose elements of
`joint` into the per-sector pieces identified by PR #2764. -/

/-- Pointwise magnetisation projector: keeps `v σ` when
`magEigenvalueS σ = M` and zeros it out otherwise. -/
noncomputable def magProjFn (M : ℂ) (v : (V → Fin (N + 1)) → ℂ) :
    (V → Fin (N + 1)) → ℂ :=
  fun σ => if magEigenvalueS σ = M then v σ else 0

/-- The pointwise magnetisation projector lands in
`magSubspaceS V N M`. -/
theorem magProjFn_mem_magSubspaceS (M : ℂ) (v : (V → Fin (N + 1)) → ℂ) :
    magProjFn (V := V) (N := N) M v ∈ magSubspaceS V N M := by
  rw [mem_magSubspaceS_iff]
  funext σ
  -- Compute (Ŝ^z_tot · magProjFn M v) σ at the diagonal.
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single σ]
  · rw [totalSpinSOp3_apply_diag]
    by_cases hmag : magEigenvalueS σ = M
    · -- magProjFn M v σ = v σ; product gives magEigenvalueS σ · v σ = M · v σ.
      simp [magProjFn, hmag]
    · -- magProjFn M v σ = 0; both sides 0.
      simp [magProjFn, hmag]
  · intros τ _ hτσ
    rw [totalSpinSOp3_apply_off_diag (Ne.symm hτσ), zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end LatticeSystem.Quantum
