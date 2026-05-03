import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedLadderCasimirEigenspace

/-!
# Saturated-ferromagnet ladder iterate is a simultaneous
`(H, Ŝ_{tot}², Ŝ^z_{tot})` eigenvector

Bundles PRs #881, #882, #887, #895 into the structural statement
identifying each ladder iterate
`(Ŝ^-_{tot})^k · |σ_⊤⟩` as a non-zero simultaneous eigenvector
of three commuting operators with explicit eigenvalues:

- Heisenberg `H = heisenbergHamiltonianS J N`: eigenvalue
  `c_J = saturatedFerromagnetEigenvalueS J N` (PR #881, #899).
- Casimir `(Ŝ_{tot})²`: eigenvalue
  `m_max(m_max + 1) = saturatedFerromagnetCasimirEigenvalueS V N`
  (PR #882, #900).
- Total `Ŝ^z_{tot}`: eigenvalue
  `m_max − k = ladderEigenvalueUp V N k` (PR #887, #896).

This is the operator-level form of Tasaki §2.4 (2.4.10): the
unnormalised iterates `|Φ_M⟩ := (Ŝ^-_{tot})^{m_max - M} · |σ_⊤⟩`
satisfy
`H |Φ_M⟩ = c_J |Φ_M⟩`, `Ŝ_{tot}² |Φ_M⟩ = m_max(m_max+1) |Φ_M⟩`,
`Ŝ^z_{tot} |Φ_M⟩ = M |Φ_M⟩`.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Simultaneous eigenvector bundle for the saturated-ferromagnet
ladder**: each iterate `(Ŝ^-_{tot})^k · |σ_⊤⟩` is a non-zero
simultaneous eigenvector of `H`, `(Ŝ_{tot})²`, and `Ŝ^z_{tot}`
with the eigenvalues `(c_J, m_max(m_max+1), m_max − k)`. -/
theorem ladderIterateUp_simultaneous_eigenvector
    [Nonempty V] (J : V → V → ℂ) (k : Fin (Fintype.card V * N + 1)) :
    Module.End.HasEigenvector ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
        (ladderIterateUp V N k) ∧
    Module.End.HasEigenvector ((totalSpinSSquared V N).mulVecLin)
        (saturatedFerromagnetCasimirEigenvalueS V N)
        (ladderIterateUp V N k) ∧
    Module.End.HasEigenvector ((totalSpinSOp3 V N).mulVecLin)
        (ladderEigenvalueUp V N k)
        (ladderIterateUp V N k) :=
  ⟨ladderIterateUp_heisenbergHamiltonianS_hasEigenvector J k,
   ladderIterateUp_totalSpinSSquared_hasEigenvector k,
   ladderIterateUp_hasEigenvector k⟩

end LatticeSystem.Quantum
