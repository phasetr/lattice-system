import LatticeSystem.Quantum.SpinS.Problem25dBalancedSectorWitnessCore
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel

/-!
# Tasaki Problem 2.5.d: balanced-sector ladder witness

This module removes the explicit strict ladder-entry hypothesis from the
sector-supported Problem 2.5.d wrapper at the balanced sector
`M0 = |A| * N`.  For every cross-sublattice pair `A x ≠ A y`, the complement
Néel configuration gives a two-configuration witness inside this sector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution pp. 498--499, equations
(S.22)--(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Balanced-sector dot-product wrapper -/

/-- Balanced-sector Problem 2.5.d ground-state phase wrapper: at
`M0 = |A| * N`, the strict ladder-entry input is supplied by the explicit
balanced-sector witness, so the sector-supported eigenspace-phase wrapper no
longer needs `hentry_pos` as an assumption. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_balanced_sector_cross_eigenphase
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N)
    (J : V → V → ℂ) (μ : ℂ)
    (c : magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) → ℝ)
    (hc_pos : ∀ σ, 0 < c σ)
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne :
      (magSectorEmbedding (fun σ :
          magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
        marshallSignS A σ.1 * (c σ : ℂ))) ≠ 0)
    (hΦnorm :
      dotProduct
        (star (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (c σ : ℂ))))
        (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (c σ : ℂ))) = 1)
    (hΦeig :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun σ :
              magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
            marshallSignS A σ.1 * (c σ : ℂ))) =
        μ • (magSectorEmbedding (fun σ :
              magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
            marshallSignS A σ.1 * (c σ : ℂ)))) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_eigenphase
    A hxy hAxy J μ c hc_pos
    (exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_bipartite_ne_balanced_sector
      A hxy hAxy hN)
    huniq hΦ_ne hΦnorm hΦeig

end LatticeSystem.Quantum
