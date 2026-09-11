import LatticeSystem.Quantum.SpinDot.Hamiltonian

/-!
# Two-spin singlet and `M = 0` triplet states

The normalised two-spin states `|Φ_{0,0}⟩` and `|Φ_{1,0}⟩` of Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, Appendix A.3.3, eqs. (A.3.23) and (A.3.22), p. 474, as vectors on the
two-site configuration space `Fin 2 → Fin 2`. Site 1 of the book is `(0 : Fin 2)`, site 2 is
`(1 : Fin 2)`, and spin-up is `0`, so `|↑⟩₁|↓⟩₂` is `basisVec upDown` and `|↓⟩₁|↑⟩₂` is
`basisVec (basisSwap upDown 0 1)`.
-/

namespace LatticeSystem.Quantum

/-- The two-spin singlet `|Φ_{0,0}⟩ = (1/√2)(|↑⟩₁|↓⟩₂ − |↓⟩₁|↑⟩₂)` on `Fin 2`: Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, Appendix A.3.3, eq. (A.3.23), p. 474. -/
noncomputable def twoSiteSinglet : (Fin 2 → Fin 2) → ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (basisVec upDown - basisVec (basisSwap upDown (0 : Fin 2) 1))

/-- The two-spin `M = 0` triplet `|Φ_{1,0}⟩ = (1/√2)(|↑⟩₁|↓⟩₂ + |↓⟩₁|↑⟩₂)` on `Fin 2`: Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, Appendix A.3.3, eq. (A.3.22), p. 474. -/
noncomputable def twoSiteTripletZero : (Fin 2 → Fin 2) → ℂ :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (basisVec upDown + basisVec (basisSwap upDown (0 : Fin 2) 1))

end LatticeSystem.Quantum
