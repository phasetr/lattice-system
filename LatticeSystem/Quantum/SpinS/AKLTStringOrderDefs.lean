import LatticeSystem.Quantum.SpinS.SiteComponent
import LatticeSystem.Quantum.SpinS.MPSTheorem75Defs
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Tasaki §7.2.1: finite AKLT string-order definitions

The spin-one periodic AKLT state is represented by the frozen bond-dimension
two matrices from Tasaki equations (7.2.12)–(7.2.14). The finite string
correlations use the strict interval between two sites and the single leading
minus in corrected equation (7.2.6).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed., Springer, 2020, §7.2.1, corrected eqs.
(7.2.6)–(7.2.8), pp. 193–194, and §7.2.2, eqs. (7.2.12)–(7.2.14),
pp. 195–196.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {L : ℕ}

/-- The bond-dimension-two spin-one AKLT matrices, with physical labels
`0, 1, 2` corresponding to magnetic values `+1, 0, -1`. -/
noncomputable def akltVBSMatrices : MPSMatrices 2 2 :=
  ![
    !![(0 : ℂ), 0; -((Real.sqrt 2 : ℂ)⁻¹), 0],
    !![(1 / 2 : ℂ), 0; 0, -(1 / 2 : ℂ)],
    !![(0 : ℂ), (Real.sqrt 2 : ℂ)⁻¹; 0, 0]
  ]

/-- The unnormalized periodic trace-product AKLT coefficient built from
`akltVBSMatrices`. -/
noncomputable def akltVBSState (L : ℕ) : (Fin L → Fin 3) → ℂ :=
  fun σ => Matrix.trace (orderedProd akltVBSMatrices (List.ofFn σ))

/-- The spin-one single-site string phase
`exp(iπ Ŝ^{(3)}) = diag(-1, 1, -1)`. -/
noncomputable def spinSStringPhaseS1 : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun k => (-1 : ℂ) ^ (k.val + 1)

/-- The strict-window axis-three string operator on a spin-one ring. Its
diagonal coefficient is the product of `spinSStringPhaseS1` entries at the
sites strictly between `x` and `y`. -/
noncomputable def stringOperatorS
    (x y : Fin L) : ManyBodyOpS (Fin L) 2 :=
  Matrix.diagonal fun σ : Fin L → Fin 3 =>
    ∏ z ∈ Finset.univ.filter (fun z : Fin L =>
      x.val < z.val ∧ z.val < y.val),
      spinSStringPhaseS1 (σ z) (σ z)

/-- The axis-three den Nijs--Rommelse finite string correlation with the
single leading minus and the unnormalized-state Rayleigh denominator. -/
noncomputable def stringCorrelationS
    (x y : Fin L) (Φ : (Fin L → Fin 3) → ℂ) : ℝ :=
  -expectationRatioRe
    (spinSSiteOp3 x 2 * stringOperatorS x y * spinSSiteOp3 y 2) Φ

/-- The strict-window string exponential for the spin-one component selected
by `α`. -/
noncomputable def stringOperatorAxisS
    (α : Fin 3) (x y : Fin L) : ManyBodyOpS (Fin L) 2 :=
  NormedSpace.exp
    ((Complex.I * (Real.pi : ℂ)) •
      ∑ z ∈ Finset.univ.filter (fun z : Fin L =>
        x.val < z.val ∧ z.val < y.val), spinSSiteComponentS α z)

/-- The axis-indexed den Nijs--Rommelse finite string correlation with the
single leading minus and the unnormalized-state Rayleigh denominator. -/
noncomputable def stringCorrelationAxisS
    (α : Fin 3) (x y : Fin L) (Φ : (Fin L → Fin 3) → ℂ) : ℝ :=
  -expectationRatioRe
    (spinSSiteComponentS α x * stringOperatorAxisS α x y *
      spinSSiteComponentS α y) Φ

end LatticeSystem.Quantum
