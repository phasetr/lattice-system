import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace
import LatticeSystem.Quantum.SpinS.MagSubspaceExtremalDim
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit
import LatticeSystem.Quantum.SpinS.CasimirRearrangement
import LatticeSystem.Quantum.SpinS.LadderBoundaryAnnihilation
import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum
import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishing
import LatticeSystem.Quantum.SpinS.ToyHamiltonianCasimir
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspaceCore

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
/-! ## Magnetisation projection (pointwise)

Concrete projector `magProjFn M v` mapping each component of `v`
through the magnetisation filter. Used to decompose elements of
`joint` into the per-sector pieces identified by PR #2764. -/

/-- Pointwise magnetisation projector: keeps `v σ` when
`magEigenvalueS σ = M` and zeros it out otherwise. -/
noncomputable def magProjFn (M : ℂ) (v : (V → Fin (N + 1)) → ℂ) :
    (V → Fin (N + 1)) → ℂ :=
  fun σ => if magEigenvalueS σ = M then v σ else 0

/-- **Support property of `magSubspaceS V N M`**: a vector in
`magSubspaceS V N M` vanishes at every configuration whose
magnetisation eigenvalue differs from `M`.

Direct consequence of the eigenvalue equation
`(Ŝ^z_tot · w) σ = magEigenvalueS σ · w σ` evaluated at `σ`. -/
theorem magSubspaceS_apply_eq_zero_of_magEigenvalueS_ne
    {M : ℂ} {w : (V → Fin (N + 1)) → ℂ}
    (hw : w ∈ magSubspaceS V N M) {σ : V → Fin (N + 1)}
    (hσ : magEigenvalueS σ ≠ M) : w σ = 0 := by
  rw [mem_magSubspaceS_iff] at hw
  have hτ_lhs : (totalSpinSOp3 V N).mulVec w σ = magEigenvalueS σ * w σ := by
    rw [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single σ]
    · rw [totalSpinSOp3_apply_diag]
    · intros τ _ hτσ
      rw [totalSpinSOp3_apply_off_diag (Ne.symm hτσ), zero_mul]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  have hτ_rhs : (M • w) σ = M * w σ := by
    simp [Pi.smul_apply, smul_eq_mul]
  have hτ_eq : magEigenvalueS σ * w σ = M * w σ := by
    rw [← hτ_lhs, hw, hτ_rhs]
  have hsub : (magEigenvalueS σ - M) * w σ = 0 := by
    rw [sub_mul, hτ_eq, sub_self]
  have hne : magEigenvalueS σ - M ≠ 0 := sub_ne_zero.mpr hσ
  exact (mul_eq_zero.mp hsub).resolve_left hne

omit [DecidableEq V] in
/-- `magProjFn` is additive in its vector argument. -/
theorem magProjFn_add (M : ℂ) (v w : (V → Fin (N + 1)) → ℂ) :
    magProjFn (V := V) (N := N) M (v + w) =
      magProjFn (V := V) (N := N) M v +
      magProjFn (V := V) (N := N) M w := by
  funext σ
  unfold magProjFn
  by_cases h : magEigenvalueS σ = M
  · simp [h]
  · simp [h]

omit [DecidableEq V] in
/-- `magProjFn` is homogeneous in its vector argument. -/
theorem magProjFn_smul (M : ℂ) (c : ℂ) (v : (V → Fin (N + 1)) → ℂ) :
    magProjFn (V := V) (N := N) M (c • v) =
      c • magProjFn (V := V) (N := N) M v := by
  funext σ
  unfold magProjFn
  by_cases h : magEigenvalueS σ = M
  · simp [h]
  · simp [h]

/-- **Matrix-element vanishing for magnetisation-preserving operators**:
if a matrix `A` sends every `basisVecS τ` into
`magSubspaceS V N (magEigenvalueS τ)`, then its off-magnetisation matrix
entries vanish: `A σ τ = 0` whenever `magEigenvalueS σ ≠ magEigenvalueS τ`. -/
theorem matrix_entry_eq_zero_of_mulVec_basisVecS_mem_magSubspaceS
    {A : ManyBodyOpS V N} {σ τ : V → Fin (N + 1)}
    (hA : A.mulVec (basisVecS τ) ∈ magSubspaceS V N (magEigenvalueS τ))
    (hne : magEigenvalueS σ ≠ magEigenvalueS τ) :
    A σ τ = 0 := by
  -- (A · basisVecS τ) σ = A σ τ.
  have happ : A.mulVec (basisVecS τ) σ = A σ τ := by
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single τ]
    · rw [basisVecS_self, mul_one]
    · intros ρ _ hρτ
      rw [basisVecS_of_ne hρτ, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [← happ]
  exact magSubspaceS_apply_eq_zero_of_magEigenvalueS_ne hA hne

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

/-- **Commutation `H · magProjFn M v = magProjFn M (H · v)`**.

The Heisenberg Hamiltonian commutes with the pointwise magnetisation
projector. Argument via the matrix-entry vanishing property: for
any `σ` and `τ` with `magEigenvalueS σ ≠ magEigenvalueS τ`, the
matrix entry `(heisenbergHamiltonianS J N) σ τ = 0` (since
`H · basisVecS τ ∈ magSubspaceS V N (magEigenvalueS τ)` by
PR #1078 / `heisenbergHamiltonianS_mulVec_basisVecS_mem_magSubspaceS`,
and applying the support property). -/
theorem heisenbergHamiltonianS_mulVec_magProjFn_eq
    (J : V → V → ℂ) (M : ℂ) (v : (V → Fin (N + 1)) → ℂ) :
    (heisenbergHamiltonianS J N).mulVec (magProjFn (V := V) (N := N) M v) =
      magProjFn (V := V) (N := N) M
        ((heisenbergHamiltonianS J N).mulVec v) := by
  funext σ
  -- LHS σ = Σ_τ H_{στ} · magProjFn M v τ.
  -- magProjFn M v τ = v τ if magEigenvalueS τ = M, else 0.
  -- So LHS σ = Σ_{τ : magEigenvalueS τ = M} H_{στ} · v τ.
  by_cases hσM : magEigenvalueS σ = M
  · -- magProjFn M (H · v) σ = (H · v) σ.
    -- Need: Σ_{τ : magEigenvalueS τ = M} H_{στ} · v τ = Σ_τ H_{στ} · v τ.
    -- For τ with magEigenvalueS τ ≠ M: magEigenvalueS σ = M ≠ magEigenvalueS τ,
    -- so H_{στ} = 0 by matrix-entry vanishing.
    have hRHS : magProjFn M ((heisenbergHamiltonianS J N).mulVec v) σ =
        (heisenbergHamiltonianS J N).mulVec v σ := by
      unfold magProjFn
      simp [hσM]
    rw [hRHS]
    rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hτM : magEigenvalueS τ = M
    · -- magProjFn M v τ = v τ.
      change heisenbergHamiltonianS J N σ τ * magProjFn M v τ =
        heisenbergHamiltonianS J N σ τ * v τ
      unfold magProjFn
      rw [if_pos hτM]
    · -- magProjFn M v τ = 0; need to show H_{στ} · 0 = H_{στ} · v τ via H_{στ} = 0.
      change heisenbergHamiltonianS J N σ τ * magProjFn M v τ =
        heisenbergHamiltonianS J N σ τ * v τ
      have h_basis_mem : (heisenbergHamiltonianS J N).mulVec (basisVecS τ) ∈
          magSubspaceS V N (magEigenvalueS τ) :=
        heisenbergHamiltonianS_mulVec_basisVecS_mem_magSubspaceS J N τ
      have hne : magEigenvalueS σ ≠ magEigenvalueS τ := by
        rw [hσM]
        exact Ne.symm hτM
      rw [matrix_entry_eq_zero_of_mulVec_basisVecS_mem_magSubspaceS h_basis_mem hne]
      ring
  · -- magProjFn M (H · v) σ = 0.
    -- Need: Σ_{τ : magEigenvalueS τ = M} H_{στ} · v τ = 0.
    -- For τ with magEigenvalueS τ = M: magEigenvalueS σ ≠ M = magEigenvalueS τ,
    -- so H_{στ} = 0.
    have hRHS : magProjFn M ((heisenbergHamiltonianS J N).mulVec v) σ = 0 := by
      unfold magProjFn
      simp [hσM]
    rw [hRHS]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro τ _
    by_cases hτM : magEigenvalueS τ = M
    · -- magProjFn M v τ = v τ, but H_{στ} = 0.
      have h_basis_mem : (heisenbergHamiltonianS J N).mulVec (basisVecS τ) ∈
          magSubspaceS V N (magEigenvalueS τ) :=
        heisenbergHamiltonianS_mulVec_basisVecS_mem_magSubspaceS J N τ
      have hne : magEigenvalueS σ ≠ magEigenvalueS τ := by
        rw [hτM]; exact hσM
      change heisenbergHamiltonianS J N σ τ * magProjFn M v τ = 0
      rw [matrix_entry_eq_zero_of_mulVec_basisVecS_mem_magSubspaceS h_basis_mem hne,
        zero_mul]
    · -- magProjFn M v τ = 0.
      change heisenbergHamiltonianS J N σ τ * magProjFn M v τ = 0
      unfold magProjFn
      rw [if_neg hτM, mul_zero]

/-- **Commutation `(Ŝ_tot)² · magProjFn M v = magProjFn M ((Ŝ_tot)² · v)`**.

Same matrix-entry-vanishing argument as the Heisenberg case
(PR #2766), now applied to `(Ŝ_tot)² · basisVecS τ`
(`totalSpinSSquared_mulVec_mem_magSubspaceS` from PR #1078). -/
theorem totalSpinSSquared_mulVec_magProjFn_eq
    (M : ℂ) (v : (V → Fin (N + 1)) → ℂ) :
    (totalSpinSSquared V N).mulVec (magProjFn (V := V) (N := N) M v) =
      magProjFn (V := V) (N := N) M
        ((totalSpinSSquared V N).mulVec v) := by
  funext σ
  by_cases hσM : magEigenvalueS σ = M
  · have hRHS : magProjFn M ((totalSpinSSquared V N).mulVec v) σ =
        (totalSpinSSquared V N).mulVec v σ := by
      unfold magProjFn
      simp [hσM]
    rw [hRHS]
    rw [Matrix.mulVec, dotProduct, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro τ _
    by_cases hτM : magEigenvalueS τ = M
    · change totalSpinSSquared V N σ τ * magProjFn M v τ =
        totalSpinSSquared V N σ τ * v τ
      unfold magProjFn
      rw [if_pos hτM]
    · change totalSpinSSquared V N σ τ * magProjFn M v τ =
        totalSpinSSquared V N σ τ * v τ
      have h_basis_mem : (totalSpinSSquared V N).mulVec (basisVecS τ) ∈
          magSubspaceS V N (magEigenvalueS τ) :=
        totalSpinSSquared_mulVec_mem_magSubspaceS (Λ := V) N
          (magEigenvalueS τ) (basisVecS_mem_magSubspaceS τ)
      have hne : magEigenvalueS σ ≠ magEigenvalueS τ := by
        rw [hσM]; exact Ne.symm hτM
      rw [matrix_entry_eq_zero_of_mulVec_basisVecS_mem_magSubspaceS
        h_basis_mem hne]
      ring
  · have hRHS : magProjFn M ((totalSpinSSquared V N).mulVec v) σ = 0 := by
      unfold magProjFn
      simp [hσM]
    rw [hRHS]
    rw [Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro τ _
    by_cases hτM : magEigenvalueS τ = M
    · have h_basis_mem : (totalSpinSSquared V N).mulVec (basisVecS τ) ∈
          magSubspaceS V N (magEigenvalueS τ) :=
        totalSpinSSquared_mulVec_mem_magSubspaceS (Λ := V) N
          (magEigenvalueS τ) (basisVecS_mem_magSubspaceS τ)
      have hne : magEigenvalueS σ ≠ magEigenvalueS τ := by
        rw [hτM]; exact hσM
      change totalSpinSSquared V N σ τ * magProjFn M v τ = 0
      rw [matrix_entry_eq_zero_of_mulVec_basisVecS_mem_magSubspaceS
        h_basis_mem hne, zero_mul]
    · change totalSpinSSquared V N σ τ * magProjFn M v τ = 0
      unfold magProjFn
      rw [if_neg hτM, mul_zero]

/-- **`magProjFn M v ∈ joint` for `v ∈ joint`**: the pointwise
magnetisation projector preserves the saturated-ferromagnet joint
eigenspace.

Direct from the H and Casimir commutations
(`heisenbergHamiltonianS_mulVec_magProjFn_eq`,
`totalSpinSSquared_mulVec_magProjFn_eq`) plus the linearity
`magProjFn_smul`. -/
theorem magProjFn_mem_saturatedFerromagnetJointEigenspace
    {J : V → V → ℂ} {M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ saturatedFerromagnetJointEigenspace (V := V) J N) :
    magProjFn (V := V) (N := N) M v ∈
      saturatedFerromagnetJointEigenspace (V := V) J N := by
  unfold saturatedFerromagnetJointEigenspace at hv ⊢
  rw [Submodule.mem_inf] at hv
  obtain ⟨hH, hCas⟩ := hv
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hH hCas
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    rw [heisenbergHamiltonianS_mulVec_magProjFn_eq, hH, magProjFn_smul]
  · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    rw [totalSpinSSquared_mulVec_magProjFn_eq, hCas, magProjFn_smul]

omit [DecidableEq V] in
/-- **Pointwise magnetisation decomposition of any vector**:
`v = ∑_{k : Fin (Fintype.card V * N + 1)} magProjFn (m_max - k.val) v`.

Every configuration `σ` has `magEigenvalueS σ = m_max - magSumS σ`
with `magSumS σ ∈ {0, ..., Fintype.card V * N}`, so exactly one
index `k = magSumS σ` in `Fin (Fintype.card V * N + 1)` selects
`v σ` (and the other indices contribute zero). -/
theorem sum_magProjFn_eq (v : (V → Fin (N + 1)) → ℂ) :
    (∑ k : Fin (Fintype.card V * N + 1),
      magProjFn (V := V) (N := N)
        (((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)) v) = v := by
  funext σ
  rw [Finset.sum_apply]
  -- Identify the unique index `k₀ = magSumS σ`.
  let k₀ : Fin (Fintype.card V * N + 1) :=
    ⟨magSumS σ, Nat.lt_succ_of_le (magSumS_le σ)⟩
  rw [Finset.sum_eq_single k₀]
  · -- At `k = k₀`, magEigenvalueS σ = m_max - k₀.val.
    unfold magProjFn
    have hmag : magEigenvalueS σ =
        (Fintype.card V : ℂ) * (N : ℂ) / 2 - (k₀.val : ℂ) := by
      unfold magEigenvalueS
      simp [k₀]
    rw [if_pos hmag]
  · -- For `k ≠ k₀`, magEigenvalueS σ ≠ m_max - k.val.
    intros k _ hkne
    unfold magProjFn
    rw [if_neg]
    intro hmag
    -- From `magEigenvalueS σ = m_max - k.val` derive `k.val = magSumS σ`.
    have hsum : (magSumS σ : ℂ) = (k.val : ℂ) := by
      unfold magEigenvalueS at hmag
      exact sub_right_inj.mp hmag
    have hnat : k.val = magSumS σ := by
      have : (k.val : ℂ) = (magSumS σ : ℂ) := hsum.symm
      exact_mod_cast this
    have : k = k₀ := Fin.ext hnat
    exact hkne this
  · intro h; exact (h (Finset.mem_univ _)).elim

/-- **Sector ladder singleton span into full ladder span**: the span of one
`ladderIterateUp` vector is contained in the span of the full ladder range. -/
theorem ladderIterateUp_singleton_span_le_span_range (N : ℕ)
    (k : Fin (Fintype.card V * N + 1)) :
    Submodule.span ℂ {ladderIterateUp V N k} ≤
      Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self k))

/-- **`joint ⊆ span (Set.range ladderIterateUp)`** — the joint
eigenspace decomposes into the linear span of the ladder iterates.

For any `v ∈ joint`, the magnetisation decomposition
`v = ∑_k magProjFn (m_max - k.val) v` (PR #2768) lifts each
component into `joint ⊓ H_{m_max - k.val} = span {ladderIterateUp V N k}`
(PR #2764). Summing across the `2m_max + 1` sectors yields
`v ∈ span (Set.range ladderIterateUp)`. -/
theorem saturatedFerromagnetJointEigenspace_le_span_ladderIterateUp
    [Nonempty V] (J : V → V → ℂ) :
    saturatedFerromagnetJointEigenspace (V := V) J N ≤
      Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  intro v hv
  -- Decompose v as the sum of its magnetisation components.
  rw [← sum_magProjFn_eq (V := V) (N := N) v]
  -- Each component lies in `joint ⊓ H_{m_max - k.val} = span {ladderIterateUp V N k}`.
  refine Submodule.sum_mem _ ?_
  intro k _
  have h_in_joint : magProjFn (V := V) (N := N)
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) v ∈
      saturatedFerromagnetJointEigenspace (V := V) J N :=
    magProjFn_mem_saturatedFerromagnetJointEigenspace hv
  have h_in_mag : magProjFn (V := V) (N := N)
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) v ∈
      magSubspaceS V N
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) :=
    magProjFn_mem_magSubspaceS _ v
  have h_in_inter : magProjFn (V := V) (N := N)
      ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) v ∈
      saturatedFerromagnetJointEigenspace (V := V) J N
        ⊓ magSubspaceS V N
          ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) :=
    Submodule.mem_inf.mpr ⟨h_in_joint, h_in_mag⟩
  rw [saturatedFerromagnetJointEigenspace_inf_magSubspaceS_eq_span_ladderIterateUp
    J k] at h_in_inter
  -- Now `h_in_inter : magProjFn ... v ∈ span {ladderIterateUp V N k}`.
  -- Embed into the larger `span (Set.range (ladderIterateUp V N))`.
  exact (ladderIterateUp_singleton_span_le_span_range (V := V) N k) h_in_inter

/-- **Tasaki §2.4 Theorem 2.1**:
`saturatedFerromagnetJointEigenspace J N = span (Set.range (ladderIterateUp V N))`.

The joint `(H, (Ŝ_tot)²)`-eigenspace at the saturated-ferromagnet
eigenvalues coincides with the `(2m_max + 1)`-dimensional linear
span of the ladder iterates. Combined with the linear independence
(PR #896) and dimension (PR #904), this identifies the joint
eigenspace as the `J_tot = m_max` irreducible SU(2) representation. -/
theorem saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp
    [Nonempty V] (J : V → V → ℂ) :
    saturatedFerromagnetJointEigenspace (V := V) J N =
      Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  apply le_antisymm
  · exact saturatedFerromagnetJointEigenspace_le_span_ladderIterateUp J
  · -- Reverse inclusion: span ⊆ joint (PR #904).
    rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    exact ladderIterateUp_mem_saturatedFerromagnetJointEigenspace J k

end LatticeSystem.Quantum
