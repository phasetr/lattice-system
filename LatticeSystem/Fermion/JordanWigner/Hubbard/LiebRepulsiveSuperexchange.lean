import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchangeCollapse

/-!
# The superexchange capstone for Theorem 10.4 (Tasaki §10.1, eq. (10.1.10), PR-8b)

Ninth installment of the Theorem 10.4 discharge arc (issue #5320); second and final file of the
two-PR split of the original PR-8 (PR-8a / PR-8b). PR-8a supplied the whole-Fock-space hop-pair
collapse `liebPerturbationV_sq_apply_eq_of_singly_occupied`, reducing `V̂ · V̂`'s matrix elements on
the singly-occupied sector to a sum of `fermionHopReturn` terms with coefficient `t_{yx} · t_{xy}`
(the asymmetric product, not yet the endpoint-graph indicator). This file completes the
superexchange identity — Tasaki's eq. (10.1.10), p. 345 — by

1. defining the endpoint bipartite graph `liebEndpointGraph`;
2. reducing the coefficient `t_{yx} · t_{xy}` to the endpoint-graph indicator via the symmetry
   hypothesis `hT` (necessary, not decoration — see the design-round note reproduced below);
3. collapsing the diagonal (number-operator) part of `fermionHopReturn_eq`'s right-hand side on the
   half-filled hard-core sector, where `n̂_y` and `n̂_x n̂_y` act with eigenvalue `1`;
4. lifting the whole-Fock-space collapse to the compressed sector via
   `configSectorCompress_mul_of_preserves` (`HubbardImpossibilityLowUVariationalCore.lean`), whose
   hypothesis is exactly PR-6's `liebPerturbationV_preserves_liebHalfFillingPred`
   (`LiebRepulsiveSuperexchangeReducedInverse.lean`);
5. assembling the capstone `P̂₀ · V̂|_K · V̂|_K · P̂₀ = 2 • (P̂₀ · compress (tJExchange
   (liebEndpointGraph A)) · P̂₀)`;
6. and the PR-9/PR-10-facing corollary that composes this with PR-6's
   `secondOrderEffectiveHamiltonian_liebPerturbation_eq`.

## `hT` is a necessary hypothesis, not decoration

The coefficient reaching the capstone from PR-8a is `t_{yx} · t_{xy}`, not `t_{xy}²`. Under `hbip`
alone, `|liebEndpointHopping A T 1 y x| = |liebEndpointHopping A T 1 x y|`, but the *signs* can
differ: `liebEndpointHopping` (`LiebRepulsiveHomotopyContinuity.lean`) carries `sign(T x y)` on the
original support, so an asymmetric `T` with `T x y > 0 > T y x` gives `t_{yx} t_{xy} = −1` while the
endpoint-graph indicator is `+1`. Hence this file's capstone carries `(hT : ∀ x y, T x y = T y x)`
alongside `hbip`, exactly as `liebPerturbationVCompressed_isHermitian`
(`LiebRepulsivePerturbationSetup.lean`) already does. Only with `hT` is `t_{yx} t_{xy} =
t_{xy}² =` the endpoint-graph indicator.

## Endpoint-graph provenance (arc-wide documented deviation, restated)

`liebEndpointGraph A` is the *complete bipartite* graph on `(A, Aᶜ)` (`Adj x y := x ∈ A ↔ y ∉ A`),
**not** the book's bond set `B = {{x, y} | t_{x,y} ≠ 0}` (p. 345). This is the same intentional
complete-bipartite endpoint substitution documented for the whole arc since PR-4
(`LiebRepulsiveHomotopyContinuity.lean`); the Heisenberg model this capstone produces is therefore
on the complete bipartite graph, not on the original hopping graph's bond set.

## Debt

Nothing yet consumes this file's capstone or its corollary; both are staged for PR-9 (Fermion-Spin
bridge) and PR-10 (endpoint Heisenberg Casimir) per the fixed PR order (issue #5320).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1, eq. (10.1.10), p. 345.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math SimpleGraph
open scoped ComplexOrder

variable {N : ℕ}

/-! ## The endpoint bipartite graph -/

/-- **The endpoint bipartite graph** on the bipartition `(A, Aᶜ)`: `x` and `y` are adjacent iff
they lie in different parts. This is the complete bipartite graph on `(A, Aᶜ)`, an intentional
strengthening of the book's literal bond set `{{x, y} | t_{x,y} ≠ 0}` (p. 345), matching the
arc-wide endpoint-graph deviation documented since PR-4. Symmetric (`x ∈ A ↔ y ∉ A` swaps to
`y ∈ A ↔ x ∉ A` by elementary propositional reasoning on the two membership propositions) and
irreflexive (`x ∈ A ↔ x ∉ A` is `False`). -/
noncomputable def liebEndpointGraph {N : ℕ} (A : Finset (Fin (N + 1))) :
    SimpleGraph (Fin (N + 1)) where
  Adj x y := x ∈ A ↔ y ∉ A
  symm x y h := by tauto
  loopless := ⟨fun x h => by tauto⟩

/-- A genuine (non-`Classical.dec`) `DecidableRel` instance for `liebEndpointGraph`'s adjacency,
inherited directly from the decidability of `Finset` membership and of `Iff` between decidable
propositions — needed so `tJExchange (liebEndpointGraph A)` does not hit an instance mismatch
against a classical instance elsewhere in the sum. -/
instance liebEndpointGraph_decidableRel {N : ℕ} (A : Finset (Fin (N + 1))) :
    DecidableRel (liebEndpointGraph A).Adj :=
  fun x y => inferInstanceAs (Decidable (x ∈ A ↔ y ∉ A))

/-! ## The coefficient reduction: `t_{yx} · t_{xy}` to the endpoint-graph indicator -/

/-- **The endpoint hopping squared is the endpoint-graph indicator.** Under bipartite respect
alone: `(liebEndpointHopping A T 1 x y)² = if (liebEndpointGraph A).Adj x y then 1 else 0`. -/
theorem liebEndpointHopping_sq_eq_indicator {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (x y : Fin (N + 1)) :
    (liebEndpointHopping A T 1 x y) ^ 2 = if (liebEndpointGraph A).Adj x y then 1 else 0 := by
  sorry

/-- **The `hT` reduction of the asymmetric product to the endpoint-graph indicator.** Under
`hbip` *and* the symmetry `hT : ∀ x y, T x y = T y x`, the asymmetric coefficient surviving PR-8a's
collapse coincides with the square (hence with the endpoint-graph indicator via
`liebEndpointHopping_sq_eq_indicator`). `hT` is genuinely necessary here (see the module docstring):
without it an asymmetric `T` with `T x y > 0 > T y x` makes `t_{yx} t_{xy} = −1` while the indicator
is `+1`. -/
theorem liebEndpointHopping_mul_symm_eq_indicator {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (hT : ∀ x y, T x y = T y x) (x y : Fin (N + 1)) :
    liebEndpointHopping A T 1 y x * liebEndpointHopping A T 1 x y
      = if (liebEndpointGraph A).Adj x y then 1 else 0 := by
  sorry

/-! ## Half-filling diagonal collapse of `fermionHopReturn` -/

/-- **Half-filling diagonal collapse** (step 3 of the PR-8b design round). For `x ≠ y` and `c`
singly occupied at every site, `fermionHopReturn_eq`'s number-operator remainder
`n̂_y − ½ n̂_x n̂_y` collapses to `½ n̂_x n̂_y` (both `n̂_x` and `n̂_y` act with eigenvalue `1` on
`c`, `fermionSiteNumber_mulVec_basisVec`, `TJDiagonalMatrixElement.lean`), turning the identity
into `2 ((1/4) n̂_x n̂_y − Ŝ_x·Ŝ_y)` entrywise against an arbitrary bra `e`. This is where
half-filling is indispensable: with an empty site, `n̂_x n̂_y` would not agree with `n̂_y` there.
Only the `c`-side occupancy hypothesis is needed (no hypothesis on `e`). -/
theorem fermionHopReturn_apply_eq_of_singly_occupied {N : ℕ} {x y : Fin (N + 1)} (hxy : x ≠ y)
    {c : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1)
    (e : Fin (2 * N + 2) → Fin 2) :
    (fermionHopReturn N x y) e c
      = (2 : ℂ) * (((1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y)
          - fermionSpinDot N x y) e c) := by
  sorry

/-! ## Sector lift of `V̂ · V̂` -/

/-- **Sector lift** (step 4 of the PR-8b design round). The compressed product `V̂|_K · V̂|_K`
equals the compression of the whole-Fock-space product `V̂ · V̂`, via
`configSectorCompress_mul_of_preserves` (`HubbardImpossibilityLowUVariationalCore.lean`) applied to
PR-6's sector-preservation lemma `liebPerturbationV_preserves_liebHalfFillingPred`
(`LiebRepulsiveSuperexchangeReducedInverse.lean`) — finally clearing that reference-0 debt. -/
theorem liebPerturbationVCompressed_sq_eq_configSectorCompress (N nUp : ℕ)
    (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
      = configSectorCompress N (liebHalfFillingPred N nUp)
          (liebPerturbationV N A T * liebPerturbationV N A T) := by
  sorry

/-! ## The PR-8b capstone -/

/-- **PR-8b capstone: the superexchange identity** (Tasaki eq. (10.1.10), p. 345). On the
compressed half-filled fixed-`Ŝ³` sector, sandwiching `V̂|_K · V̂|_K` between the hard-core
projections `P̂₀` equals twice the sandwich of the exchange operator on the endpoint bipartite
graph. Assembled from PR-8a's whole-Fock-space collapse
(`liebPerturbationV_sq_apply_eq_of_singly_occupied`), the coefficient reduction
(`liebEndpointHopping_mul_symm_eq_indicator`, needs `hT`), the half-filling diagonal collapse
(`fermionHopReturn_apply_eq_of_singly_occupied`), and the sector lift
(`liebPerturbationVCompressed_sq_eq_configSectorCompress`). -/
theorem kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection (N nUp : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
        * liebPerturbationVCompressed N nUp A T * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
      = (2 : ℂ) • (LatticeSystem.Math.kernelProjectionMatrix
            (liebPerturbationH0Compressed N nUp)
          * configSectorCompress N (liebHalfFillingPred N nUp)
              (tJExchange N (liebEndpointGraph A))
          * LatticeSystem.Math.kernelProjectionMatrix
              (liebPerturbationH0Compressed N nUp)) := by
  sorry

/-- **Corollary for PR-9/PR-10**: composing the PR-8b capstone with PR-6's
`secondOrderEffectiveHamiltonian_liebPerturbation_eq`
(`LiebRepulsiveSuperexchangeReducedInverse.lean`), the compressed second-order effective
Hamiltonian is `−2 • (P̂₀ · compress (tJExchange (liebEndpointGraph A)) · P̂₀)`, i.e. Tasaki's
`Ĥspin = Σ_{x,y} (|t_{x,y}|²/U_x) · 2 (Ŝ_x·Ŝ_y − ¼) P̂₀` at this arc's `U = 1` normalisation and on
the complete-bipartite endpoint graph. -/
theorem secondOrderEffectiveHamiltonian_liebPerturbation_eq_tJExchange (N nUp : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) (hT : ∀ x y, T x y = T y x) :
    LatticeSystem.Math.secondOrderEffectiveHamiltonian (liebPerturbationH0Compressed N nUp)
        (liebPerturbationVCompressed N nUp A T) (liebPerturbationH0InvCompressed N nUp)
      = -((2 : ℂ) • (LatticeSystem.Math.kernelProjectionMatrix
              (liebPerturbationH0Compressed N nUp)
            * configSectorCompress N (liebHalfFillingPred N nUp)
                (tJExchange N (liebEndpointGraph A))
            * LatticeSystem.Math.kernelProjectionMatrix
                (liebPerturbationH0Compressed N nUp))) := by
  sorry

end LatticeSystem.Fermion
