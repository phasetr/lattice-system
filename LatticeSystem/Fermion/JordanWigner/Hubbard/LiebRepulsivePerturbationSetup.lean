import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveHomotopyContinuity

/-!
# Perturbation setup for Theorem 10.4 (Tasaki §10.2.2, PR-5)

Fifth installment of the Theorem 10.4 discharge arc (issue #5320). PR-4 built the homotopy
`H_s` and showed the occupied Casimir sector is constant across `s ∈ [0, 1]`; the remaining step
of Tasaki's argument is to pin that constant value at the endpoint `s = 1` by taking `λ → 0`
(p. 353), which is a **degenerate-perturbation-theory** computation in the sense of Tasaki
Lemma 10.1 (`Math/MatrixAnalysis/DegeneratePerturbation.lean`, discharged independently in
issue #5313). This file sets up the perturbation family `Ĥ(λ) = Ĥ₀ + λ V̂` at the homotopy
endpoint `s = 1` and the pieces of the Lemma 10.1 contract that are concrete for this model:

* `liebPerturbationH0` / `liebPerturbationV`: the `λ`-independent on-site interaction `Ĥ₀` and the
  unit-coupling hopping operator `V̂`, related to `H_s` at `s = 1` by
  `homotopyHamiltonian_one_eq_perturbedHamiltonian`.
* `liebPerturbationH0_posSemidef`: `Ĥ₀ ≥ 0` (a sum of positive-semidefinite same-site
  double-occupancy operators).
* `liebPerturbationH0_mulVec_basisVec` / `mem_matrixKernel_liebPerturbationH0_iff`: `Ĥ₀` is
  diagonal in the computational basis with eigenvalue the interaction weight
  (`hubbardConfigInteractionWeight`, `LiebAttractiveCoeffAction.lean`), and its kernel is exactly
  the hard-core subspace (`hubbardHardcoreSubspace`, `HardcoreSubspace.lean`).
* `kernelProjectionMatrix_liebPerturbationH0_eq_hardcoreProjection`: the orthogonal projection
  onto `ker Ĥ₀` (`kernelProjectionMatrix`) coincides with the explicit hard-core indicator
  projection `hubbardHardcoreProjection` (`HardcoreProjection.lean`).
* `liebPerturbationH0Inv` / `liebPerturbationH0_isReducedInverse`: the explicit diagonal reduced
  (Moore–Penrose) inverse of `Ĥ₀` — `0` on hard-core configurations, the reciprocal interaction
  weight elsewhere — discharging `IsReducedInverse Ĥ₀ Ĥ₀Inv`.
* `hubbardHardcoreProjection_mul_liebPerturbationV_mul_hubbardHardcoreProjection`: the
  first-order vanishing condition `P̂₀ V̂ P̂₀ = 0` at half filling, needed for the second-order
  effective Hamiltonian `Ĥeff = −P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀` (eq. (10.1.20)) to be the whole `λ²` term.

The constant-energy-shift lemma this setup also needs (normalising the hard-core ground energy to
`0` before comparing with `Ĥeff`) is `LatticeSystem.Math.minEnergyOn_add_const_smul_one`
(`Math/MatrixAnalysis/MinEnergyOnSubspace.lean`), added alongside PR-2's `minEnergyOn` API.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.1 (Lemma 10.1, eq. (10.1.20)) and §10.2.2 (p. 353).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped ComplexOrder

variable {N : ℕ}

/-! ## `Ĥ₀` and `V̂`: the `λ`-family at the homotopy endpoint `s = 1` -/

/-- The **unperturbed Hamiltonian** `Ĥ₀ = Σ_x n̂_{x↑} n̂_{x↓}` of Tasaki's `λ → 0` deformation
(§10.2.2, p. 353): the on-site interaction at the endpoint on-site coupling `U = 1`
(`homotopyOnSite U 1 = 1` for every original `U`), the piece of `H_s` at `s = 1` that does not
depend on `λ`. -/
noncomputable def liebPerturbationH0 (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardOnSiteInteractionSite N (fun _ => (1 : ℂ))

/-- The **perturbing hopping operator** `V̂` at unit coupling `λ = 1`: the kinetic operator on the
complete-bipartite `±1` endpoint hopping matrix `liebEndpointHopping A T 1`
(`LiebRepulsiveHomotopyContinuity.lean`). Since `liebEndpointHopping A T lam` is linear in `lam`,
`Ĥ_{s=1}(λ) = Ĥ₀ + λ V̂`. -/
noncomputable def liebPerturbationV (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) : ManyBodyOp (Fin (2 * N + 2)) :=
  hubbardKinetic N (fun x y => (liebEndpointHopping A T 1 x y : ℂ))

/-- **The `s = 1` homotopy endpoint is the perturbed Hamiltonian `Ĥ₀ + λ V̂`.** Since
`liebEndpointHopping A T lam` is linear in `lam` and `homotopyOnSite U 1 = 1`, the homotopy at
`s = 1` is exactly Tasaki's `λ`-family preceding eq. (10.1.6), specialized to this concrete
model — the bridge to `LatticeSystem.Math.perturbedHamiltonian`
(`Math/MatrixAnalysis/DegeneratePerturbation.lean`), the abstract object the rest of the
Lemma 10.1 infrastructure (`IsReducedInverse`, `secondOrderEffectiveHamiltonian`,
`DegeneratePerturbationConvergence.lean`) is stated for. -/
theorem homotopyHamiltonian_one_eq_perturbedHamiltonian (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U lam : ℝ) :
    homotopyHamiltonian N A T U lam 1
      = LatticeSystem.Math.perturbedHamiltonian (liebPerturbationH0 N) (liebPerturbationV N A T)
          lam := by
  sorry

/-! ## `Ĥ₀` is diagonal, positive-semidefinite, with the hard-core subspace as kernel -/

/-- **`Ĥ₀ ≥ 0`**: the unperturbed on-site interaction is positive-semidefinite, being a sum of the
positive-semidefinite same-site double-occupancy operators (`hubbardDoubleOccupancy_posSemidef`,
`TasakiFlatBandPosSemidef.lean`). -/
theorem liebPerturbationH0_posSemidef (N : ℕ) : (liebPerturbationH0 N).PosSemidef := by
  sorry

/-- **`Ĥ₀` is diagonal in the computational basis**, with eigenvalue the interaction weight
`hubbardConfigInteractionWeight N (fun _ => 1) c` (the number of doubly-occupied sites of `c`,
`LiebAttractiveCoeffAction.lean`). -/
theorem liebPerturbationH0_mulVec_basisVec (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    (liebPerturbationH0 N).mulVec (basisVec c)
      = hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c • basisVec c := by
  sorry

/-- **The kernel of `Ĥ₀` is the hard-core subspace**: a vector lies in `ker Ĥ₀` exactly when it
is (as a Fock-space vector) a member of `hubbardHardcoreSubspace N`, since the interaction weight
(a sum of `0`/`1` terms) vanishes at `c` exactly when no site of `c` is doubly occupied. -/
theorem mem_matrixKernel_liebPerturbationH0_iff (N : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    v ∈ LatticeSystem.Math.matrixKernel (liebPerturbationH0 N)
      ↔ WithLp.ofLp v ∈ hubbardHardcoreSubspace N := by
  sorry

/-- **`Ĥ₀`'s kernel projection is the hard-core projection**: the orthogonal projection onto
`ker Ĥ₀`, expressed as a matrix (`kernelProjectionMatrix`, `DegeneratePerturbation.lean`),
coincides with the explicit hard-core indicator projection
`hubbardHardcoreProjection N = ∏ᵢ (1 - n̂_{i↑} n̂_{i↓})` (`HardcoreProjection.lean`). -/
theorem kernelProjectionMatrix_liebPerturbationH0_eq_hardcoreProjection (N : ℕ) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0 N)
      = hubbardHardcoreProjection N := by
  sorry

/-! ## The explicit reduced inverse of `Ĥ₀` -/

/-- **The explicit reduced (Moore–Penrose) inverse of `Ĥ₀`**: diagonal in the computational
basis, `0` on hard-core configurations (`ker Ĥ₀`) and the reciprocal interaction weight on every
other configuration. At the single-double-occupancy configurations of Tasaki's leading-order
picture (§10.1) this is the `1/U` rescaling (here `U = 1`); away from that sector it is the
honest reciprocal of the (generically higher) interaction weight, so the construction is exact
for `Ĥ₀`, not merely a leading-order approximation. -/
noncomputable def liebPerturbationH0Inv (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  Matrix.diagonal fun c : Fin (2 * N + 2) → Fin 2 =>
    let w := hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c
    if w = 0 then 0 else w⁻¹

/-- **`Ĥ₀Inv` is the reduced inverse of `Ĥ₀`**: it inverts `Ĥ₀` on `(ker Ĥ₀)ᗮ` and vanishes on
`ker Ĥ₀`, discharging the `IsReducedInverse` contract of `DegeneratePerturbation.lean` for the
explicit diagonal construction above. -/
theorem liebPerturbationH0_isReducedInverse (N : ℕ) :
    LatticeSystem.Math.IsReducedInverse (liebPerturbationH0 N) (liebPerturbationH0Inv N) := by
  sorry

/-! ## `P̂₀ V̂ P̂₀ = 0` at half filling -/

/-- **The hopping term vanishes to first order on the hard-core, half-filled sector**:
`P̂₀ V̂ P̂₀ = 0`, where `P̂₀ = hubbardHardcoreProjection N` and `V̂ = liebPerturbationV N A T` is
the unit-coupling hopping operator on the sites `Fin (N + 1)` (half filling: `N + 1` electrons on
`N + 1` sites, so every hard-core configuration has exactly one electron per site). Every hopping
term `c†_{x,σ} c_{y,σ}` (`x ≠ y`) then either empties a singly-occupied site or doubly occupies
one, landing outside the hard-core subspace; `P̂₀` on the right annihilates it. -/
theorem hubbardHardcoreProjection_mul_liebPerturbationV_mul_hubbardHardcoreProjection
    (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    hubbardHardcoreProjection N * liebPerturbationV N A T * hubbardHardcoreProjection N = 0 := by
  sorry

end LatticeSystem.Fermion
