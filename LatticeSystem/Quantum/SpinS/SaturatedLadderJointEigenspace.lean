import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace

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

end LatticeSystem.Quantum
