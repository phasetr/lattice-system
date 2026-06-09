import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandUniqueness
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandMultiplet
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandTheorem11_11

/-!
# Tasaki §11.3.1: discharging the Theorem 11.11 classification axiom (dimension route)

The half-filled zero-energy ground subspace of the flat-band Hubbard model equals the ferromagnetic
maximal-spin multiplet.  Following the §11.5 Theorem 11.26 dimension method (not symmetric-tensor
representation theory): the multiplet (dimension `K+2`) is contained in the ground subspace (the
existence half), and the ground subspace has dimension `≤ K+2` (amplitude invariance), so they
coincide — discharging `flatBand_zeroEnergy_halfFilled_mem_ferromagneticMultipletSpan`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1, Theorem 11.11; method as in §11.5.3, Theorem 11.26.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **The ferromagnetic multiplet has dimension `K+2 = 2 S_max + 1`** — its `K+2` lowered states
`(Ŝ⁻_tot)^k |Φα,all↑⟩` are linearly independent (`flatBand_ferromagnetic_multiplet`). -/
theorem flatBandFerromagneticMultipletSubmodule_finrank (K : ℕ) (ν : ℝ) :
    finrank ℂ (flatBandFerromagneticMultipletSubmodule K ν) = K + 2 := by
  rw [flatBandFerromagneticMultipletSubmodule,
    finrank_span_eq_card (flatBand_ferromagnetic_multiplet K ν).1, Fintype.card_fin]

end LatticeSystem.Fermion
