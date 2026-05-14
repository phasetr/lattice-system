import LatticeSystem.Quantum.SpinS.IterateInductiveNonvanishing
import LatticeSystem.Quantum.SpinS.AllAlignedStateMagShift
import LatticeSystem.Quantum.SpinS.SaturatedPairLinearIndependent

/-!
# Full saturated-ferromagnet ladder linear independence

For `[Nonempty V]`, the family
`{(Ŝ^-_{tot})^k · |σ_⊤⟩ : k = 0, 1, …, |V|·N}` (parameterised by
`Fin (|V|·N + 1)`, which has cardinality `2m_max + 1`) is
`LinearIndependent ℂ`.

This is the spin-`S` saturated-ferromagnet ground-state ladder
basis: each iterate is a non-zero `Ŝ^z_{tot}`-eigenvector at a
distinct eigenvalue `m_max − k`, hence the family is linearly
independent by `Module.End.eigenvectors_linearIndependent'`.

Combines:
- PR #875: `Ŝ^z_{tot} · |σ_⊤⟩ = m_max · |σ_⊤⟩`.
- PR #887: `Ŝ^z_{tot} · ((Ŝ^-_{tot})^k · |σ_⊤⟩) = (m_max − k) · ...`.
- PR #889: `magSubspaceS_eq_eigenspace` bridge to `Module.End.eigenspace`.
- PR #895: inductive non-vanishing for `k ≤ |V|·N`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## The full ladder family and its eigenvalues -/

/-- The `k`-th unnormalised iterate `(Ŝ^-_{tot})^k · |σ_⊤⟩` for
`k : Fin (|V|·N + 1)`. -/
noncomputable def ladderIterateUp (V : Type*) (N : ℕ)
    [Fintype V] [DecidableEq V]
    (k : Fin (Fintype.card V * N + 1)) :
    (V → Fin (N + 1)) → ℂ :=
  ((totalSpinSOpMinus V N) ^ k.val).mulVec
    (allAlignedStateS V N (0 : Fin (N + 1)))

/-- The `Ŝ^z_{tot}`-eigenvalue of the `k`-th iterate: `m_max − k`. -/
noncomputable def ladderEigenvalueUp (V : Type*) (N : ℕ) [Fintype V]
    (k : Fin (Fintype.card V * N + 1)) : ℂ :=
  ((Fintype.card V : ℂ) * (N : ℂ) / 2) - (k.val : ℂ)

omit [DecidableEq V] in
/-- The eigenvalue function is injective. -/
theorem ladderEigenvalueUp_injective :
    Function.Injective (ladderEigenvalueUp V N) := by
  intros i j hij
  unfold ladderEigenvalueUp at hij
  -- (m_max - i.val : ℂ) = (m_max - j.val : ℂ) ⇒ (i.val : ℂ) = (j.val : ℂ).
  have hval : (i.val : ℂ) = (j.val : ℂ) := by linear_combination -hij
  have hnat : i.val = j.val := by exact_mod_cast hval
  exact Fin.ext hnat

/-! ## Each iterate is a HasEigenvector -/

/-- The `k`-th iterate lies in the `Ŝ^z_{tot}`-eigenspace at
`m_max − k`. Spin-`S` extension of #889's bridge plus PR #887's
iterated magnetic-quantum-number labelling. -/
theorem ladderIterateUp_mem_eigenspace
    (k : Fin (Fintype.card V * N + 1)) :
    ladderIterateUp V N k ∈
      Module.End.eigenspace ((totalSpinSOp3 V N).mulVecLin)
        (ladderEigenvalueUp V N k) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  unfold ladderIterateUp ladderEigenvalueUp
  exact totalSpinSOp3_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero k.val

/-- Each iterate is a non-zero `Ŝ^z_{tot}`-eigenvector. -/
theorem ladderIterateUp_hasEigenvector [Nonempty V]
    (k : Fin (Fintype.card V * N + 1)) :
    Module.End.HasEigenvector ((totalSpinSOp3 V N).mulVecLin)
      (ladderEigenvalueUp V N k) (ladderIterateUp V N k) := by
  refine ⟨ladderIterateUp_mem_eigenspace k, ?_⟩
  unfold ladderIterateUp
  exact totalSpinSOpMinus_pow_allAlignedStateS_zero_ne_zero
    (Nat.lt_succ_iff.mp k.isLt)

/-! ## Linear independence of the full ladder family -/

/-- **Full saturated-ferromagnet ladder LI**: for `[Nonempty V]`, the
family `ladderIterateUp V N : Fin (|V|·N + 1) → ((V → Fin (N+1)) → ℂ)`
is `LinearIndependent ℂ`.

Proof: `Module.End.eigenvectors_linearIndependent'` applied to the
`Ŝ^z_{tot}.mulVecLin` endomorphism with the eigenvalue function
`ladderEigenvalueUp` (injective) and the per-`k` `HasEigenvector`
witnesses. -/
theorem ladderIterateUp_linearIndependent [Nonempty V] :
    LinearIndependent ℂ (ladderIterateUp V N) := by
  let f : Module.End ℂ ((V → Fin (N + 1)) → ℂ) :=
    (totalSpinSOp3 V N).mulVecLin
  exact Module.End.eigenvectors_linearIndependent' f
    (ladderEigenvalueUp V N) ladderEigenvalueUp_injective
    (ladderIterateUp V N) ladderIterateUp_hasEigenvector

end LatticeSystem.Quantum
