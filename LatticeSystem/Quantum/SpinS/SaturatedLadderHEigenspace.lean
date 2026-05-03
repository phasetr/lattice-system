import LatticeSystem.Quantum.SpinS.SaturatedFullLadderLI

/-!
# The saturated-ferromagnet ladder lies in a single Heisenberg
eigenspace

For any spin-`S` Heisenberg coupling `J : V → V → ℂ` and
`[Nonempty V]`, every iterate of the form
`(Ŝ^-_{tot})^k · |σ_⊤⟩` (the saturated-ferromagnet ladder) is a
`heisenbergHamiltonianS J N`-eigenvector at the **single shared
eigenvalue** `c_J := H(σ_⊤, σ_⊤)` (the diagonal element of `H` at
the all-up configuration).

This packages PR #881 (`heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero`)
in the `Module.End.eigenspace`-membership form, ready to combine
with PR #896 (the family is `LinearIndependent ℂ`) into the
statement "the H-eigenspace at `c_J` has dimension at least
`2m_max + 1`".

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The saturated-ferromagnet eigenvalue of `heisenbergHamiltonianS J N`:
the diagonal value at the all-up configuration. -/
noncomputable def saturatedFerromagnetEigenvalueS
    (J : V → V → ℂ) (N : ℕ) : ℂ :=
  (heisenbergHamiltonianS J N)
    (allAlignedConfigS V N 0) (allAlignedConfigS V N 0)

/-- Each ladder iterate `(Ŝ^-_{tot})^k · |σ_⊤⟩` lies in the
`heisenbergHamiltonianS J N`-eigenspace at
`saturatedFerromagnetEigenvalueS J N`. Bridges PR #881
(`mulVec` form) to `Module.End.eigenspace` membership. -/
theorem ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace
    (J : V → V → ℂ) (k : Fin (Fintype.card V * N + 1)) :
    ladderIterateUp V N k ∈
      Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  unfold ladderIterateUp saturatedFerromagnetEigenvalueS
  exact heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero
    J k.val

/-- Each iterate is a non-zero `heisenbergHamiltonianS`-eigenvector
at `saturatedFerromagnetEigenvalueS`. -/
theorem ladderIterateUp_heisenbergHamiltonianS_hasEigenvector
    [Nonempty V] (J : V → V → ℂ)
    (k : Fin (Fintype.card V * N + 1)) :
    Module.End.HasEigenvector ((heisenbergHamiltonianS J N).mulVecLin)
      (saturatedFerromagnetEigenvalueS (V := V) J N)
      (ladderIterateUp V N k) :=
  ⟨ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace J k,
    (ladderIterateUp_hasEigenvector k).right⟩

/-- **Heisenberg eigenspace dimension lower bound**: for
`[Nonempty V]`, the dimension of the
`heisenbergHamiltonianS J N`-eigenspace at the saturated-
ferromagnet eigenvalue is at least `|V|·N + 1 = 2m_max + 1`.

Proof: the ladder family `ladderIterateUp` is `LinearIndependent`
(PR #896) and lives in this eigenspace. Apply
`LinearIndependent.fintype_card_le_finrank` after restricting the
family to the eigenspace via `Submodule.injOn_subtype`. -/
theorem heisenbergHamiltonianS_eigenspace_finrank_ge_succ_card_mul_N
    [Nonempty V] (J : V → V → ℂ) :
    Fintype.card V * N + 1 ≤
      Module.finrank ℂ
        (Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
          (saturatedFerromagnetEigenvalueS (V := V) J N)) := by
  -- Restrict the ladder family to the eigenspace.
  let E := Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
    (saturatedFerromagnetEigenvalueS (V := V) J N)
  let f : Fin (Fintype.card V * N + 1) → E :=
    fun k => ⟨ladderIterateUp V N k,
      ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace J k⟩
  have hLI : LinearIndependent ℂ f := by
    have h := ladderIterateUp_linearIndependent (V := V) (N := N)
    exact (LinearIndependent.of_comp E.subtype) (by
      simpa [f] using h)
  have := hLI.fintype_card_le_finrank
  simpa using this

end LatticeSystem.Quantum
