import LatticeSystem.Quantum.SpinS.SaturatedFullLadderLI

/-!
# The saturated-ferromagnet ladder lies in a single Casimir eigenspace

For `[Nonempty V]`, every iterate `(Ŝ^-_{tot})^k · |σ_⊤⟩` of the
saturated-ferromagnet ladder is a `(Ŝ_{tot})²`-eigenvector at the
**single shared Casimir eigenvalue**
`m_max(m_max + 1) = (|V|·N/2) · (|V|·N/2 + 1)`,
identifying the ladder span as a subspace of the
`J_{tot} = m_max` irreducible SU(2) representation.

This packages PR #882
(`totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero`)
in the `Module.End.eigenspace`-membership form, and combines with
PR #896 (the family is `LinearIndependent ℂ`) into the dimension
lower bound: the Casimir eigenspace at `m_max(m_max + 1)` has
`Module.finrank ℂ ≥ 2m_max + 1`.

Mirror of PR #899 (Heisenberg eigenspace bound) for the Casimir
operator `Ŝ_{tot}²`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- The saturated-ferromagnet Casimir eigenvalue
`m_max(m_max + 1) = (|V|·N/2) · (|V|·N/2 + 1)`. -/
noncomputable def saturatedFerromagnetCasimirEigenvalueS
    (V : Type*) [Fintype V] (N : ℕ) : ℂ :=
  ((Fintype.card V : ℂ) * (N : ℂ) / 2) *
    ((Fintype.card V : ℂ) * (N : ℂ) / 2 + 1)

/-- Each ladder iterate `(Ŝ^-_{tot})^k · |σ_⊤⟩` lies in the
`(Ŝ_{tot})²`-eigenspace at the saturated-ferromagnet Casimir
eigenvalue. Bridges PR #882 (`mulVec` form) to
`Module.End.eigenspace` membership. -/
theorem ladderIterateUp_mem_totalSpinSSquared_eigenspace
    [Nonempty V] (k : Fin (Fintype.card V * N + 1)) :
    ladderIterateUp V N k ∈
      Module.End.eigenspace ((totalSpinSSquared V N).mulVecLin)
        (saturatedFerromagnetCasimirEigenvalueS V N) := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
  unfold ladderIterateUp saturatedFerromagnetCasimirEigenvalueS
  exact totalSpinSSquared_mulVec_totalSpinSOpMinus_pow_allAlignedStateS_zero k.val

/-- Each iterate is a non-zero `(Ŝ_{tot})²`-eigenvector at the
saturated-ferromagnet Casimir eigenvalue. -/
theorem ladderIterateUp_totalSpinSSquared_hasEigenvector
    [Nonempty V] (k : Fin (Fintype.card V * N + 1)) :
    Module.End.HasEigenvector ((totalSpinSSquared V N).mulVecLin)
      (saturatedFerromagnetCasimirEigenvalueS V N)
      (ladderIterateUp V N k) :=
  ⟨ladderIterateUp_mem_totalSpinSSquared_eigenspace k,
    (ladderIterateUp_hasEigenvector k).right⟩

/-- **Casimir eigenspace dimension lower bound**: for
`[Nonempty V]`, the dimension of the `(Ŝ_{tot})²`-eigenspace at
`m_max(m_max + 1)` is at least `|V|·N + 1 = 2m_max + 1`.

Proof: the LI ladder family (PR #896) restricted to this eigenspace
gives a `(2m_max + 1)`-element linearly-independent family. Mirror
of PR #899 for the Heisenberg Hamiltonian. -/
theorem totalSpinSSquared_eigenspace_finrank_ge_succ_card_mul_N
    [Nonempty V] :
    Fintype.card V * N + 1 ≤
      Module.finrank ℂ
        (Module.End.eigenspace ((totalSpinSSquared V N).mulVecLin)
          (saturatedFerromagnetCasimirEigenvalueS V N)) := by
  let E := Module.End.eigenspace ((totalSpinSSquared V N).mulVecLin)
    (saturatedFerromagnetCasimirEigenvalueS V N)
  let f : Fin (Fintype.card V * N + 1) → E :=
    fun k => ⟨ladderIterateUp V N k,
      ladderIterateUp_mem_totalSpinSSquared_eigenspace k⟩
  have hLI : LinearIndependent ℂ f := by
    have h := ladderIterateUp_linearIndependent (V := V) (N := N)
    exact (LinearIndependent.of_comp E.subtype) (by
      simpa [f] using h)
  have := hLI.fintype_card_le_finrank
  simpa using this

end LatticeSystem.Quantum
