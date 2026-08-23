import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSuperexchangeCollapse
import LatticeSystem.Quantum.MarshallLiebMattis.BipartiteGraph

/-!
# The superexchange capstone for Theorem 10.4 (Tasaki §10.1, eq. (10.1.10), PR-8b)

Ninth installment of the Theorem 10.4 discharge arc (issue #5320); second and final file of the
two-PR split of the original PR-8 (PR-8a / PR-8b). PR-8a supplied the whole-Fock-space hop-pair
collapse `liebPerturbationV_sq_apply_eq_of_singly_occupied`, reducing `V̂ · V̂`'s matrix elements on
the singly-occupied sector to a sum of `fermionHopReturn` terms with coefficient `t_{yx} · t_{xy}`
(the asymmetric product, not yet the endpoint-graph indicator). This file completes the
superexchange identity — Tasaki's eq. (10.1.10), p. 345 — by

1. defining the endpoint bipartite graph `liebEndpointGraph` as the `Finset` specialisation of the
   sublattice-indicator graph `bipartiteGraphFromA`
   (`Quantum/MarshallLiebMattis/BipartiteGraph.lean`);
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

`liebEndpointGraph A` is the *complete bipartite* graph on `(A, Aᶜ)` (adjacency `x ∈ A ↔ y ∉ A`,
`liebEndpointGraph_adj`), **not** the book's bond set `B = { {x, y} | t_{x,y} ≠ 0 }` (p. 345). This
is the same intentional complete-bipartite endpoint substitution documented for the whole arc since
PR-4 (`LiebRepulsiveHomotopyContinuity.lean`); the Heisenberg model this capstone produces is
therefore on the complete bipartite graph, not on the original hopping graph's bond set.

## Debt

None. The capstone `kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection` is
consumed here by the corollary `secondOrderEffectiveHamiltonian_liebPerturbation_eq_tJExchange`;
the four feeder lemmas, `liebEndpointGraph`, its adjacency lemma and its `DecidableRel` instance
all feed that same chain inside this file. Both the capstone and the corollary are consumed by
PR-9a's reindexing capstones (`LiebRepulsiveFermionSpinBridge.lean`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1, eq. (10.1.10), p. 345.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math SimpleGraph
open scoped ComplexOrder

variable {N : ℕ}

/-! ## The endpoint bipartite graph -/

/-- **The endpoint bipartite graph** on the bipartition `(A, Aᶜ)`: `x` and `y` are adjacent iff
they lie in different parts. Rather than a fresh `SimpleGraph` structure, this is the
sublattice-indicator complete bipartite graph `bipartiteGraphFromA`
(`Quantum/MarshallLiebMattis/BipartiteGraph.lean`) specialised at `Λ := Fin (N + 1)` and the
indicator `fun x => decide (x ∈ A)`, so symmetry and irreflexivity are inherited rather than
reproved; the `Finset` form of the adjacency used throughout this file is `liebEndpointGraph_adj`.
It is an intentional strengthening of the book's literal bond set `{ {x, y} | t_{x,y} ≠ 0 }`
(p. 345), matching the arc-wide endpoint-graph deviation documented since PR-4. -/
def liebEndpointGraph {N : ℕ} (A : Finset (Fin (N + 1))) : SimpleGraph (Fin (N + 1)) :=
  bipartiteGraphFromA fun x => decide (x ∈ A)

/-- **The endpoint graph's adjacency in `Finset` form**: `x` and `y` are adjacent iff exactly one
of them lies in `A`, which is what the `Bool`-indicator adjacency `decide (x ∈ A) ≠ decide (y ∈ A)`
of `bipartiteGraphFromA` says. -/
@[simp] theorem liebEndpointGraph_adj {N : ℕ} (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) :
    (liebEndpointGraph A).Adj x y ↔ (x ∈ A ↔ y ∉ A) := by
  simp only [liebEndpointGraph, bipartiteGraphFromA_adj, ne_eq, decide_eq_decide]
  tauto

/-- A genuine (non-`Classical.dec`) `DecidableRel` instance for `liebEndpointGraph`'s adjacency,
inherited directly from the decidability of `Finset` membership and of `Bool` disequality — needed
so `tJExchange (liebEndpointGraph A)` does not hit an instance mismatch against a classical
instance elsewhere in the sum. -/
instance liebEndpointGraph_decidableRel {N : ℕ} (A : Finset (Fin (N + 1))) :
    DecidableRel (liebEndpointGraph A).Adj :=
  fun x y => inferInstanceAs (Decidable (decide (x ∈ A) ≠ decide (y ∈ A)))

/-! ## The coefficient reduction: `t_{yx} · t_{xy}` to the endpoint-graph indicator -/

/-- **The endpoint hopping squared is the endpoint-graph indicator.** Under bipartite respect
alone: `(liebEndpointHopping A T 1 x y)² = if (liebEndpointGraph A).Adj x y then 1 else 0`. -/
theorem liebEndpointHopping_sq_eq_indicator {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (x y : Fin (N + 1)) :
    (liebEndpointHopping A T 1 x y) ^ 2 = if (liebEndpointGraph A).Adj x y then 1 else 0 := by
  by_cases hAB : x ∈ A ↔ y ∉ A
  · rw [if_pos ((liebEndpointGraph_adj A x y).mpr hAB)]
    by_cases hT0 : T x y = 0
    · rw [show liebEndpointHopping A T 1 x y = 1 by simp [liebEndpointHopping, hT0, hAB], one_pow]
    · rw [show liebEndpointHopping A T 1 x y = if 0 < T x y then 1 else -1 by
        simp [liebEndpointHopping, hT0]]
      split_ifs <;> norm_num
  · rw [if_neg (mt (liebEndpointGraph_adj A x y).mp hAB)]
    have hT0 : T x y = 0 := by
      by_contra h
      exact hAB (hbip h)
    rw [show liebEndpointHopping A T 1 x y = 0 by simp [liebEndpointHopping, hT0, hAB]]
    norm_num

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
  have hend : liebEndpointHopping A T 1 y x = liebEndpointHopping A T 1 x y := by
    have hiff : (y ∈ A ↔ x ∉ A) ↔ (x ∈ A ↔ y ∉ A) := by tauto
    simp only [liebEndpointHopping, hT y x, hiff]
  rw [hend, ← pow_two]
  exact liebEndpointHopping_sq_eq_indicator hbip x y

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
  have hx : ((c (spinfulIndex N x 0)).val : ℂ) + ((c (spinfulIndex N x 1)).val : ℂ) = 1 := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) (hc x)
  have hnum : (fermionSiteNumber N x * fermionSiteNumber N y) e c
      = (fermionSiteNumber N y) e c := by
    rw [← mulVec_basisVec_apply (fermionSiteNumber N x * fermionSiteNumber N y) e c,
      ← mulVec_basisVec_apply (fermionSiteNumber N y) e c, ← Matrix.mulVec_mulVec,
      fermionSiteNumber_mulVec_basisVec, Matrix.mulVec_smul,
      fermionSiteNumber_mulVec_basisVec, smul_smul, hx, mul_one]
  rw [fermionHopReturn_eq N x y hxy]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  rw [← hnum]
  ring

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
  rw [liebPerturbationVCompressed]
  exact configSectorCompress_mul_of_preserves (liebHalfFillingPred N nUp)
    (liebPerturbationV N A T)
    fun c c' hc hc' => liebPerturbationV_preserves_liebHalfFillingPred N nUp A T hc hc'

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
  have hentry : ∀ c e : Fin (2 * N + 2) → Fin 2,
      (∀ z : Fin (N + 1), (c (spinfulIndex N z 0)).val + (c (spinfulIndex N z 1)).val = 1) →
      (∀ z : Fin (N + 1), (e (spinfulIndex N z 0)).val + (e (spinfulIndex N z 1)).val = 1) →
      (liebPerturbationV N A T * liebPerturbationV N A T) e c
        = (2 : ℂ) * (tJExchange N (liebEndpointGraph A)) e c := by
    intro c e hc he
    rw [liebPerturbationV_sq_apply_eq_of_singly_occupied hbip hc he]
    simp only [tJExchange, Matrix.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [liebEndpointHopping_mul_symm_eq_indicator hbip hT u v]
    by_cases hadj : (liebEndpointGraph A).Adj u v
    · rw [if_pos hadj, if_pos hadj,
        fermionHopReturn_apply_eq_of_singly_occupied hadj.ne hc e, Complex.ofReal_one, one_mul]
    · rw [if_neg hadj, if_neg hadj, Complex.ofReal_zero, zero_mul, Matrix.zero_apply, mul_zero]
  rw [Matrix.mul_assoc (LatticeSystem.Math.kernelProjectionMatrix
        (liebPerturbationH0Compressed N nUp)) (liebPerturbationVCompressed N nUp A T)
      (liebPerturbationVCompressed N nUp A T),
    liebPerturbationVCompressed_sq_eq_configSectorCompress,
    kernelProjectionMatrix_liebPerturbationH0Compressed_eq_diagonal]
  ext s s'
  simp only [Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  by_cases hs : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val = 0
  · by_cases hs' : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s'.val = 0
    · rw [if_pos hs, if_pos hs']
      simp only [one_mul, mul_one]
      rw [configSectorCompress_apply, configSectorCompress_apply]
      exact hentry s'.val s.val (liebHalfFilling_site_occupation N nUp s'.property hs')
        (liebHalfFilling_site_occupation N nUp s.property hs)
    · rw [if_neg hs']
      ring
  · rw [if_neg hs]
    ring

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
  rw [secondOrderEffectiveHamiltonian_liebPerturbation_eq N nUp hbip,
    kernelProjection_mul_liebPerturbationVCompressed_sq_mul_kernelProjection N nUp hbip hT]

end LatticeSystem.Fermion
