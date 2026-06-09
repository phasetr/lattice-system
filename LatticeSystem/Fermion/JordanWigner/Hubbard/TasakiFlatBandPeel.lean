import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandOccBasis
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandDualAnnihilation

/-!
# Tasaki §11.3.1: the dual-annihilator peel on occupation monomials (`BKernel ⊆ AlphaFock`)

The dual β-annihilator `d_{u,σ}` anticommutes (to `0`) with every rotated mode creation
`Ĉ†_τ(basis j)` except `b̂†_{u,σ}` (the mode `(inr u, σ)`), with which it gives the Kronecker `1`.
Hence `d_{u,σ}` peels the β-mode `(inr u, σ)` off an occupation monomial (removing it, up to a
nonzero sign) when present, and annihilates the monomial when absent.  This is the engine that
forces a
`b̂`-kernel vector to have no β-occupation, i.e. to lie in the α-Fock subspace.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **`{d_{u,σ}, Ĉ†_τ(basis j)} = 0`** for every rotated mode `(j, τ) ≠ (inr u, σ)`: the dual
annihilator passes every creation except its own `b̂†_{u,σ}` (`{d,â†}=0`, and `{d,b̂†_{w,τ}}=0`
unless `(w,τ)=(u,σ)`). -/
theorem flatBandDualBAnnihilation_basisCreation_anticomm (u : Fin (K + 1)) (σ τ : Fin 2)
    (j : Fin (K + 1) ⊕ Fin (K + 1)) (hj : (j, τ) ≠ (Sum.inr u, σ)) :
    flatBandDualBAnnihilation K ν u σ * flatBandModeCreation K τ (flatBandBasis K ν j)
      + flatBandModeCreation K τ (flatBandBasis K ν j) * flatBandDualBAnnihilation K ν u σ = 0 := by
  rw [flatBandModeCreation_basis]
  rcases j with p | w
  · rw [Sum.elim_inl]
    exact flatBandDualBAnnihilation_ACreation_anticomm K ν u p σ τ
  · rw [Sum.elim_inr, flatBandDualBAnnihilation_BCreation_anticomm]
    rw [if_neg (fun h => hj (by rw [h.1, h.2])), zero_smul]

/-- **`{d_{u,σ}, b̂†_{u,σ}} = 1`** (the matching β-mode). -/
theorem flatBandDualBAnnihilation_BCreation_self (u : Fin (K + 1)) (σ : Fin 2) :
    flatBandDualBAnnihilation K ν u σ * flatBandBCreation K ν u σ
      + flatBandBCreation K ν u σ * flatBandDualBAnnihilation K ν u σ = 1 := by
  rw [flatBandDualBAnnihilation_BCreation_anticomm, if_pos ⟨rfl, rfl⟩, one_smul]

end LatticeSystem.Fermion
