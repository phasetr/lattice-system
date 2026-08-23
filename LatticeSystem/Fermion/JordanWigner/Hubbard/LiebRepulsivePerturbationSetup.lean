import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveHomotopyContinuity
import LatticeSystem.Fermion.JordanWigner.Hubbard.HubbardImpossibilityLowUVariationalCore
import LatticeSystem.Math.MatrixAnalysis.BlockTransport

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
* `liebHalfFillingPred` / `liebPerturbationH0Compressed` / `liebPerturbationVCompressed`: the
  half-filled fixed-`Ŝ³` configuration sector and the compressions of `Ĥ₀`, `V̂` to it
  (`configSectorCompress`, `HubbardImpossibilityLowUVariationalCore.lean`), together with the
  preservation of positive semidefiniteness and Hermiticity under the compression.
* `kernelProjection_mul_liebPerturbationVCompressed_mul_kernelProjection`: the first-order
  vanishing condition `P̂₀ V̂ P̂₀ = 0` **inside that sector**, needed for the second-order effective
  Hamiltonian `Ĥeff = −P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀` (eq. (10.1.20)) to be the whole `λ²` term. The condition
  is genuinely a sector statement: on the whole Fock space it is false, because a hard-core
  configuration with an empty site can absorb a hopping electron and stay hard-core.

The energy-origin normalisation this setup needs (comparing the hard-core ground energy with that
of `Ĥeff` only up to an additive constant) is carried out by the arc's assembly at the level of
`IsUniqueGroundStateOn`, not of `minEnergyOn`: PR-11a's capstone
`isUniqueGroundStateOn_liebPerturbationH0Compressed_kernel_iff_heisenberg`
(`LiebRepulsiveSectorAssembly.lean`) states the Heisenberg side with the shift
`−|A| (N + 1 − |A|) • 1` already folded into the matrix, and the generic transport of a real
constant shift across that predicate is `LatticeSystem.Math.isUniqueGroundStateOn_sub_smul_one_iff`
(`Math/MatrixAnalysis/SubmatrixGroundState.lean`), itself unconsumed and staged for PR-11b.

Of the whole-Fock-space layer the compressed statements *in this file* consume only the
diagonality of `Ĥ₀` (`liebPerturbationH0_mulVec_basisVec`, transported to the sector basis by
`configSectorCompress_apply`, which is what turns `P̂₀|_K` into an explicit indicator), the
positive semidefiniteness of `Ĥ₀`, and the entries of `V̂` between singly-occupied configurations.
Downstream, the superexchange layer additionally consumes the bridge `Ĥ_{s=1}(λ) = Ĥ₀ + λ V̂` and
the *definition* `Ĥ₀Inv`, whose compression is the compressed reduced inverse; it does not consume
the *statement* `liebPerturbationH0_isReducedInverse`, re-deriving the compressed contract from the
diagonal form instead. The kernel description `ker Ĥ₀ = hard-core subspace` and the hard-core
projection identity built from it feed nothing, here or downstream.

The compressed counterparts of this setup live in `LiebRepulsiveSuperexchangeReducedInverse.lean`:
the compressed `IsReducedInverse` (whose matrix is the compression of `Ĥ₀Inv` from here), the
compressed bridge `Ĥ_{s=1}(λ)|_K = Ĥ₀|_K + λ V̂|_K` to `LatticeSystem.Math.perturbedHamiltonian`
(which consumes the whole-space bridge from here), and the nonemptiness of the compressed sector.

Every declaration introduced with this setup that no proof consumes is carried as debt, not as
settled API: on the whole Fock space the kernel criterion `mem_matrixKernel_liebPerturbationH0_iff`
with the hard-core projection identity that consumes it, and the whole-space `IsReducedInverse`
statement for `Ĥ₀Inv` (the definition itself is consumed downstream, the statement is not); on the
sector `Ĥ₀|_K ≥ 0` (which is the sole consumer of the whole-space `Ĥ₀ ≥ 0`), the
Hermiticity of `V̂|_K`, and the `P̂₀ V̂ P̂₀ = 0` capstone itself. All of them are staged for the
application of Lemma 10.1 and the assembly of the arc (PR-11 to PR-13); whatever that assembly
does not consume is to be deleted, not kept.

The helpers `liebHalfFilling_site_occupation`, `liebEndpointHopping_diag_eq_zero`,
`liebPerturbationH0Compressed_eq_diagonal` and `hubbardConfigInteractionWeight_one_star` are public
rather than `private` because the downstream superexchange layers (from
`LiebRepulsiveSuperexchangeReducedInverse.lean` on) consume them directly instead of duplicating
them.

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
  have hend : ∀ x y : Fin (N + 1),
      liebEndpointHopping A T lam x y = lam * liebEndpointHopping A T 1 x y := by
    intro x y
    simp only [liebEndpointHopping]
    split_ifs <;> ring
  have hkin : hubbardKinetic N (fun x y => ((liebEndpointHopping A T lam x y : ℝ) : ℂ))
      = (lam : ℂ) • hubbardKinetic N (fun x y => ((liebEndpointHopping A T 1 x y : ℝ) : ℂ)) := by
    simp only [hubbardKinetic, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, ← Complex.ofReal_mul, ← hend i j]
  have hhop : homotopyHopping T (liebEndpointHopping A T lam) 1 = liebEndpointHopping A T lam := by
    simp [homotopyHopping]
  have hons : homotopyOnSite U 1 = 1 := by simp [homotopyOnSite]
  simp only [homotopyHamiltonian, hhop, hons, repulsiveHubbardHamiltonian,
    LatticeSystem.Math.perturbedHamiltonian, liebPerturbationH0, liebPerturbationV,
    Complex.ofReal_one, hkin]
  exact add_comm _ _

/-! ## `Ĥ₀` is diagonal, positive-semidefinite, with the hard-core subspace as kernel -/

/-- **`Ĥ₀ ≥ 0`**: the unperturbed on-site interaction is positive-semidefinite, being a sum of the
positive-semidefinite same-site double-occupancy operators (`hubbardDoubleOccupancy_posSemidef`,
`TasakiFlatBandPosSemidef.lean`). -/
theorem liebPerturbationH0_posSemidef (N : ℕ) : (liebPerturbationH0 N).PosSemidef := by
  have hsum : liebPerturbationH0 N = ∑ x : Fin (N + 1), hubbardDoubleOccupancy N x := by
    simp only [liebPerturbationH0, hubbardOnSiteInteractionSite, one_smul, hubbardDoubleOccupancy]
  rw [hsum]
  exact Matrix.posSemidef_sum _ fun x _ => hubbardDoubleOccupancy_posSemidef N x

/-- **`Ĥ₀` is diagonal in the computational basis**, with eigenvalue the interaction weight
`hubbardConfigInteractionWeight N (fun _ => 1) c` (the number of doubly-occupied sites of `c`,
`LiebAttractiveCoeffAction.lean`). -/
theorem liebPerturbationH0_mulVec_basisVec (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    (liebPerturbationH0 N).mulVec (basisVec c)
      = hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c • basisVec c :=
  hubbardOnSiteInteractionSite_mulVec_basisVec N (fun _ => (1 : ℂ)) c

/-- The interaction weight of `Ĥ₀` counts, as a natural number, the doubly occupied sites of the
configuration `c`; the occupation values are `0`/`1`, so the sum has no cancellation. -/
private theorem hubbardConfigInteractionWeight_one_eq_natCast (N : ℕ)
    (c : Fin (2 * N + 2) → Fin 2) :
    hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c
      = ((∑ x : Fin (N + 1),
          (c (spinfulIndex N x 0)).val * (c (spinfulIndex N x 1)).val : ℕ) : ℂ) := by
  simp only [hubbardConfigInteractionWeight, Nat.cast_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  ring

/-- The interaction weight of `Ĥ₀` is real (it is a natural number), so the diagonal `Ĥ₀` and its
reciprocal-weight inverse are Hermitian. -/
theorem hubbardConfigInteractionWeight_one_star (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    star (hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c)
      = hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c := by
  rw [hubbardConfigInteractionWeight_one_eq_natCast]
  simp

/-- The interaction weight of `Ĥ₀` vanishes exactly on hard-core configurations: a sum of
`0`/`1`-valued double-occupancy terms is zero exactly when every term is. -/
private theorem hubbardConfigInteractionWeight_one_eq_zero_iff (N : ℕ)
    (c : Fin (2 * N + 2) → Fin 2) :
    hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0
      ↔ ∀ x : Fin (N + 1),
          ((c (spinfulIndex N x 0)).val : ℂ) * ((c (spinfulIndex N x 1)).val : ℂ) = 0 := by
  rw [hubbardConfigInteractionWeight_one_eq_natCast, Nat.cast_eq_zero, Finset.sum_eq_zero_iff]
  constructor
  · intro h x
    exact_mod_cast h x (Finset.mem_univ x)
  · intro h x _
    exact_mod_cast h x

/-- Matrix form of the diagonality of `Ĥ₀`: it is the diagonal matrix of interaction weights. -/
private theorem liebPerturbationH0_eq_diagonal (N : ℕ) :
    liebPerturbationH0 N
      = Matrix.diagonal (hubbardConfigInteractionWeight N (fun _ => (1 : ℂ))) := by
  ext c' c
  rw [← mulVec_basisVec_apply (liebPerturbationH0 N) c' c, liebPerturbationH0_mulVec_basisVec,
    Pi.smul_apply, smul_eq_mul, Matrix.diagonal_apply, basisVec_apply]
  by_cases h : c' = c
  · rw [if_pos h, if_pos h, mul_one, h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- **The kernel of `Ĥ₀` is the hard-core subspace**: a vector lies in `ker Ĥ₀` exactly when it
is (as a Fock-space vector) a member of `hubbardHardcoreSubspace N`, since the interaction weight
(a sum of `0`/`1` terms) vanishes at `c` exactly when no site of `c` is doubly occupied. -/
theorem mem_matrixKernel_liebPerturbationH0_iff (N : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :
    v ∈ LatticeSystem.Math.matrixKernel (liebPerturbationH0 N)
      ↔ WithLp.ofLp v ∈ hubbardHardcoreSubspace N := by
  have hofLp : WithLp.ofLp (Matrix.toEuclideanLin (liebPerturbationH0 N) v)
      = (liebPerturbationH0 N).mulVec (WithLp.ofLp v) := rfl
  have hbridge : v ∈ LatticeSystem.Math.matrixKernel (liebPerturbationH0 N)
      ↔ (liebPerturbationH0 N).mulVec (WithLp.ofLp v) = 0 := by
    rw [LatticeSystem.Math.matrixKernel, LinearMap.mem_ker]
    constructor
    · intro h
      rw [← hofLp, h]
      rfl
    · intro h
      apply WithLp.ofLp_injective 2
      rw [hofLp, h]
      rfl
  rw [hbridge, mem_hubbardHardcoreSubspace_iff]
  constructor
  · intro h i
    funext c
    rw [hubbardDoubleOccupancy_mulVec_apply, Pi.zero_apply]
    rcases eq_or_ne (WithLp.ofLp v c) 0 with hc | hc
    · rw [hc, mul_zero]
    · have hzero := congrFun h c
      simp only [liebPerturbationH0, hubbardOnSiteInteractionSite_mulVec_apply,
        Pi.zero_apply] at hzero
      rw [(hubbardConfigInteractionWeight_one_eq_zero_iff N c).mp
        ((mul_eq_zero.mp hzero).resolve_right hc) i, zero_mul]
  · intro h
    funext c
    simp only [liebPerturbationH0, hubbardOnSiteInteractionSite_mulVec_apply, Pi.zero_apply,
      hubbardConfigInteractionWeight]
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hx := congrFun (h x) c
    rw [hubbardDoubleOccupancy_mulVec_apply, Pi.zero_apply] at hx
    rw [one_mul]
    exact hx

/-- Uniqueness of the kernel projection of `Ĥ₀`: a Hermitian matrix `P` that maps into `ker Ĥ₀`
(`Ĥ₀ P = 0`) and fixes every hard-core vector *is* the orthogonal projection onto `ker Ĥ₀`, since
`ker Ĥ₀` is the hard-core subspace (`mem_matrixKernel_liebPerturbationH0_iff`) and the two
conditions are exactly the defining properties `P w ∈ ker Ĥ₀` and `w - P w ⊥ ker Ĥ₀`. Used to
identify `P̂₀` with the operator-product projection `∏ᵢ (1 - n̂↑n̂↓)`. -/
private theorem kernelProjectionMatrix_liebPerturbationH0_eq_of_fixes_hardcore (N : ℕ)
    {P : ManyBodyOp (Fin (2 * N + 2))} (hHerm : P.IsHermitian)
    (hmul : liebPerturbationH0 N * P = 0)
    (hfix : ∀ ψ ∈ hubbardHardcoreSubspace N, P.mulVec ψ = ψ) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0 N) = P :=
  LatticeSystem.Math.kernelProjectionMatrix_eq_of_fixes_kernel hHerm hmul fun u hu => by
    apply WithLp.ofLp_injective 2
    exact hfix _ ((mem_matrixKernel_liebPerturbationH0_iff N u).mp hu)

/-- **`Ĥ₀`'s kernel projection is the hard-core projection**: the orthogonal projection onto
`ker Ĥ₀`, expressed as a matrix (`kernelProjectionMatrix`, `DegeneratePerturbation.lean`),
coincides with the explicit hard-core indicator projection
`hubbardHardcoreProjection N = ∏ᵢ (1 - n̂_{i↑} n̂_{i↓})` (`HardcoreProjection.lean`). -/
theorem kernelProjectionMatrix_liebPerturbationH0_eq_hardcoreProjection (N : ℕ) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0 N)
      = hubbardHardcoreProjection N := by
  refine kernelProjectionMatrix_liebPerturbationH0_eq_of_fixes_hardcore N
    (hubbardHardcoreProjection_isHermitian N) ?_
    (fun ψ hψ => hubbardHardcoreProjection_mulVec_eq_self_of_mem N hψ)
  simp only [liebPerturbationH0, hubbardOnSiteInteractionSite, Finset.sum_mul, one_smul]
  exact Finset.sum_eq_zero fun x _ => hubbardDoubleOccupancy_mul_hardcoreProjection N x

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
  have hInv : liebPerturbationH0Inv N
      = Matrix.diagonal (fun c : Fin (2 * N + 2) → Fin 2 =>
          if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 then 0
          else (hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c)⁻¹) := rfl
  rw [liebPerturbationH0_eq_diagonal, hInv]
  exact LatticeSystem.Math.isReducedInverse_diagonal (hubbardConfigInteractionWeight_one_star N)

/-! ## The half-filled fixed-`Ŝ³` sector and the compressed `Ĥ₀`, `V̂` -/

/-- **The half-filled fixed-`Ŝ³` configuration predicate**: a Fock configuration carries `N + 1`
electrons on the `N + 1` sites (half filling, `N̂ = N + 1`), exactly `nUp` of them spin-up
(equivalently `Ŝ³ = (2 nUp − (N + 1)) / 2`). This is the configuration-basis description of the
joint sector `K = {N̂ = N + 1} ⊓ {Ŝ³ = m₀}` of `LiebRepulsiveCasimirSector.lean`; the perturbative
step of §10.2.2 takes place inside `K`, not on the whole Fock space. -/
abbrev liebHalfFillingPred (N nUp : ℕ) : (Fin (2 * N + 2) → Fin 2) → Prop :=
  fun c => (∑ j : Fin (2 * N + 2), (c j).val) = N + 1 ∧
    (∑ x : Fin (N + 1), (c (spinfulIndex N x 0)).val) = nUp

/-- **The compressed unperturbed Hamiltonian** `Ĥ₀|_K`: the matrix of `Ĥ₀` in the orthonormal
configuration basis of the half-filled fixed-`Ŝ³` sector (`configSectorCompress`,
`HubbardImpossibilityLowUVariationalCore.lean`). -/
noncomputable def liebPerturbationH0Compressed (N nUp : ℕ) :
    Matrix (configSector N (liebHalfFillingPred N nUp))
      (configSector N (liebHalfFillingPred N nUp)) ℂ :=
  configSectorCompress N (liebHalfFillingPred N nUp) (liebPerturbationH0 N)

/-- **The compressed perturbation** `V̂|_K`: the matrix of the unit-coupling endpoint hopping
operator in the configuration basis of the half-filled fixed-`Ŝ³` sector. -/
noncomputable def liebPerturbationVCompressed (N nUp : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) :
    Matrix (configSector N (liebHalfFillingPred N nUp))
      (configSector N (liebHalfFillingPred N nUp)) ℂ :=
  configSectorCompress N (liebHalfFillingPred N nUp) (liebPerturbationV N A T)

/-- **`Ĥ₀|_K ≥ 0`**: positive semidefiniteness survives the sector compression, since the latter is
the congruence `A ↦ Tᴴ A T` by the isometric sector embedding. -/
theorem liebPerturbationH0Compressed_posSemidef (N nUp : ℕ) :
    (liebPerturbationH0Compressed N nUp).PosSemidef := by
  rw [liebPerturbationH0Compressed, configSectorCompress]
  exact (liebPerturbationH0_posSemidef N).conjTranspose_mul_mul_same _

/-- **`V̂|_K` is Hermitian** whenever the original hopping matrix is symmetric: the endpoint
hopping matrix is then symmetric too (`homotopyHopping_symm` at `s = 1`), so `V̂` is Hermitian, and
Hermiticity survives the compression (`configSectorCompress_isHermitian`). -/
theorem liebPerturbationVCompressed_isHermitian (N nUp : ℕ) (A : Finset (Fin (N + 1)))
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hT : ∀ x y, T x y = T y x) :
    (liebPerturbationVCompressed N nUp A T).IsHermitian := by
  refine configSectorCompress_isHermitian _ (hubbardKinetic_isHermitian N fun i j => ?_)
  have hend : homotopyHopping T (liebEndpointHopping A T 1) 1 = liebEndpointHopping A T 1 := by
    simp [homotopyHopping]
  have hsymm := homotopyHopping_symm A T hT 1 1 j i
  rw [hend] at hsymm
  rw [hsymm]
  simp

/-- The compressed `Ĥ₀` stays diagonal, with the interaction weight of the sector configuration as
its eigenvalue: the sector basis is a subfamily of the computational basis, which already
diagonalizes `Ĥ₀`. -/
theorem liebPerturbationH0Compressed_eq_diagonal (N nUp : ℕ) :
    liebPerturbationH0Compressed N nUp
      = Matrix.diagonal (fun s : configSector N (liebHalfFillingPred N nUp) =>
          hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val) := by
  ext s s'
  rw [liebPerturbationH0Compressed, configSectorCompress_apply, liebPerturbationH0_eq_diagonal,
    Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : s = s'
  · rw [if_pos h, if_pos (congrArg Subtype.val h)]
  · rw [if_neg h, if_neg (fun hv => h (Subtype.ext hv))]

/-- **The hard-core predicate on the half-filled fixed-`Ŝ³` sector.** A sector configuration `s`
is hard-core (no doubly occupied site) exactly when its Fock-space interaction weight vanishes. -/
abbrev liebHalfFillingHardcorePred (N nUp : ℕ) :
    configSector N (liebHalfFillingPred N nUp) → Prop :=
  fun s => hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val = 0

/-- **`ker (Ĥ₀|_K)` is the coordinate span of the hard-core sector configurations.** Bridges the
diagonal form of the compressed unperturbed Hamiltonian (`liebPerturbationH0Compressed_eq_diagonal`)
to the generic coordinate-span kernel identification
(`LatticeSystem.Math.matrixKernel_diagonal_eq_coordinateSpan`,
`Math/MatrixAnalysis/BlockTransport.lean`); this is the sector-level analogue of
`mem_matrixKernel_liebPerturbationH0_iff` needed to apply Lemma 10.1's block transport to
`Ĥ₀|_K`. -/
theorem matrixKernel_liebPerturbationH0Compressed_eq_coordinateSpan (N nUp : ℕ) :
    LatticeSystem.Math.matrixKernel (liebPerturbationH0Compressed N nUp)
      = LatticeSystem.Math.coordinateSpan (liebHalfFillingHardcorePred N nUp) := by
  rw [liebPerturbationH0Compressed_eq_diagonal]
  exact LatticeSystem.Math.matrixKernel_diagonal_eq_coordinateSpan _ _ fun _ => Iff.rfl

/-- **`P̂₀` inside the sector is the hard-core indicator.** The orthogonal projection onto
`ker (Ĥ₀|_K)` is the diagonal indicator of the sector configurations without a doubly occupied
site. -/
theorem kernelProjectionMatrix_liebPerturbationH0Compressed_eq_diagonal (N nUp : ℕ) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
      = Matrix.diagonal (fun s : configSector N (liebHalfFillingPred N nUp) =>
          if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val = 0 then 1 else 0) := by
  rw [liebPerturbationH0Compressed_eq_diagonal,
    LatticeSystem.Math.kernelProjectionMatrix_diagonal]

/-! ## `P̂₀ V̂ P̂₀ = 0` on the half-filled sector -/

/-- On a site carrying exactly one electron, the spin orbital other than the occupied one is
empty. -/
private theorem spinfulSite_other_val_eq_zero {N : ℕ} {c : Fin (2 * N + 2) → Fin 2}
    {x : Fin (N + 1)} (hx : (c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val = 1)
    {σ τ : Fin 2} (hστ : τ ≠ σ) (hσ : c (spinfulIndex N x σ) = 1) :
    (c (spinfulIndex N x τ)).val = 0 := by
  have hsum : ∑ r : Fin 2, (c (spinfulIndex N x r)).val = 1 := by
    rw [Fin.sum_univ_two]
    exact hx
  have hσv : (c (spinfulIndex N x σ)).val = 1 := by rw [hσ]; rfl
  have hsplit : (c (spinfulIndex N x σ)).val
      + ∑ r ∈ Finset.univ.erase σ, (c (spinfulIndex N x r)).val
      = ∑ r : Fin 2, (c (spinfulIndex N x r)).val :=
    Finset.add_sum_erase Finset.univ (fun r : Fin 2 => (c (spinfulIndex N x r)).val)
      (Finset.mem_univ σ)
  have hrest : ∑ r ∈ Finset.univ.erase σ, (c (spinfulIndex N x r)).val = 0 := by omega
  exact Finset.sum_eq_zero_iff.mp hrest τ (Finset.mem_erase.mpr ⟨hστ, Finset.mem_univ τ⟩)

/-- **Half filling plus the hard-core condition means one electron per site.** A configuration of
the sector carries `N + 1` electrons on `N + 1` sites; if no site is doubly occupied, then no site
can be empty either, so every site carries exactly one electron. -/
theorem liebHalfFilling_site_occupation (N nUp : ℕ) {c : Fin (2 * N + 2) → Fin 2}
    (hc : liebHalfFillingPred N nUp c)
    (hhard : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0) (x : Fin (N + 1)) :
    (c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val = 1 := by
  have hle : ∀ y : Fin (N + 1),
      (c (spinfulIndex N y 0)).val + (c (spinfulIndex N y 1)).val ≤ 1 := by
    intro y
    have hz := (hubbardConfigInteractionWeight_one_eq_zero_iff N c).mp hhard y
    have h0 := (c (spinfulIndex N y 0)).isLt
    have h1 := (c (spinfulIndex N y 1)).isLt
    rcases mul_eq_zero.mp hz with h | h
    · have hv : (c (spinfulIndex N y 0)).val = 0 := by exact_mod_cast h
      omega
    · have hv : (c (spinfulIndex N y 1)).val = 0 := by exact_mod_cast h
      omega
  have hsum : ∑ y : Fin (N + 1),
      ((c (spinfulIndex N y 0)).val + (c (spinfulIndex N y 1)).val) = N + 1 := by
    rw [← sum_spinful_split N (fun j => (c j).val)]
    exact hc.1
  have heq : ∑ y : Fin (N + 1),
      ((c (spinfulIndex N y 0)).val + (c (spinfulIndex N y 1)).val)
        = ∑ _y : Fin (N + 1), 1 := by
    rw [hsum]
    simp
  exact (Finset.sum_eq_sum_iff_of_le fun y _ => hle y).mp heq x (Finset.mem_univ x)

/-- The endpoint hopping matrix has no diagonal entry: a bipartite hopping matrix vanishes on
`(x, x)` (a site is not in the sublattice opposite to its own), and the endpoint construction adds
an edge only between sites of *different* sublattices. -/
theorem liebEndpointHopping_diag_eq_zero {N : ℕ} {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (x : Fin (N + 1)) : liebEndpointHopping A T 1 x x = 0 := by
  have hT0 : T x x = 0 := by
    by_contra h
    have hiff := hbip h
    tauto
  simp [liebEndpointHopping, hT0]

/-- **`V̂` has no matrix element between two singly-occupied configurations.** With one electron
per site, a hopping term `c†_{x,σ} c_{y,σ}` with `x ≠ y` empties site `y`, so the resulting
configuration differs from every singly-occupied one; the terms with `x = y` are number operators,
whose coefficient is the vanishing diagonal entry of the bipartite endpoint hopping matrix. -/
private theorem liebPerturbationV_apply_eq_zero_of_singly_occupied {N : ℕ}
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) {c c' : Fin (2 * N + 2) → Fin 2}
    (hc : ∀ x, (c (spinfulIndex N x 0)).val + (c (spinfulIndex N x 1)).val = 1)
    (hc' : ∀ x, (c' (spinfulIndex N x 0)).val + (c' (spinfulIndex N x 1)).val = 1) :
    liebPerturbationV N A T c' c = 0 := by
  have hterm : ∀ (σ : Fin 2) (i j : Fin (N + 1)),
      (((liebEndpointHopping A T 1 i j : ℝ) : ℂ) •
        (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
          fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))) c' c = 0 := by
    intro σ i j
    rw [Matrix.smul_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      rw [liebEndpointHopping_diag_eq_zero hbip i, Complex.ofReal_zero, zero_mul]
    · refine mul_eq_zero_of_right _ ?_
      rw [← mulVec_basisVec_apply (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
          fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)) c' c,
        fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
      by_cases hcond : c (spinfulIndex N j σ) = 1 ∧
          (Function.update c (spinfulIndex N j σ) 0) (spinfulIndex N i σ) = 0
      · rw [if_pos hcond, Pi.smul_apply, smul_eq_mul]
        have hpq : spinfulIndex N i σ ≠ spinfulIndex N j σ :=
          fun h => hij ((spinfulIndex_eq_iff N i j σ σ).mp h).1
        have hall : ∀ r : Fin 2,
            ((Function.update (Function.update c (spinfulIndex N j σ) 0)
              (spinfulIndex N i σ) 1) (spinfulIndex N j r)).val = 0 := by
          intro r
          by_cases hr : r = σ
          · subst hr
            rw [Function.update_of_ne hpq.symm, Function.update_self]
            rfl
          · have h1 : spinfulIndex N j r ≠ spinfulIndex N j σ :=
              fun h => hr ((spinfulIndex_eq_iff N j j r σ).mp h).2
            have h2 : spinfulIndex N j r ≠ spinfulIndex N i σ :=
              fun h => hij ((spinfulIndex_eq_iff N j i r σ).mp h).1.symm
            rw [Function.update_of_ne h2, Function.update_of_ne h1]
            exact spinfulSite_other_val_eq_zero (hc j) hr hcond.1
        have hne : c' ≠ Function.update (Function.update c (spinfulIndex N j σ) 0)
            (spinfulIndex N i σ) 1 := by
          intro heq
          have hj := hc' j
          rw [heq, hall 0, hall 1] at hj
          omega
        rw [basisVec_apply, if_neg hne, mul_zero]
      · rw [if_neg hcond, Pi.zero_apply]
  rw [liebPerturbationV, hubbardKinetic]
  simp only [Matrix.sum_apply]
  exact Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun i _ =>
    Finset.sum_eq_zero fun j _ => hterm σ i j

/-- **First-order vanishing on the half-filled sector**: `P̂₀ V̂ P̂₀ = 0` for the compressed
family `Ĥ(λ)|_K = Ĥ₀|_K + λ V̂|_K`, with `P̂₀` the projection onto `ker (Ĥ₀|_K)`. This is the
hypothesis that makes the second-order effective Hamiltonian `Ĥeff = −P̂₀ V̂ Ĥ₀⁻¹ V̂ P̂₀`
(eq. (10.1.20)) carry the whole `λ²` term of Tasaki's `λ → 0` deformation (§10.2.2, p. 353).

The half-filling restriction is essential, not cosmetic: on the whole Fock space `P̂₀ V̂ P̂₀` does
not vanish (any hard-core configuration with an empty site can receive a hopping electron and stay
hard-core), which is why the statement lives on the compressed sector. Of the hopping matrix the
proof uses only the vanishing of the endpoint diagonal (`liebEndpointHopping_diag_eq_zero`), which
is what removes the on-site (number-operator) part of `V̂`; bipartiteness is a sufficient condition
for that, not a necessary one — a non-bipartite hopping matrix with vanishing diagonal has the same
first-order vanishing on the half-filled sector. -/
theorem kernelProjection_mul_liebPerturbationVCompressed_mul_kernelProjection (N nUp : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hbip : HoppingRespectsBipartition A T) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp)
        * liebPerturbationVCompressed N nUp A T
        * LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0Compressed N nUp) = 0 := by
  rw [kernelProjectionMatrix_liebPerturbationH0Compressed_eq_diagonal]
  ext s s'
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.zero_apply]
  by_cases hs : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s.val = 0
  · by_cases hs' : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) s'.val = 0
    · rw [liebPerturbationVCompressed, configSectorCompress_apply,
        liebPerturbationV_apply_eq_zero_of_singly_occupied hbip
          (liebHalfFilling_site_occupation N nUp s'.property hs')
          (liebHalfFilling_site_occupation N nUp s.property hs)]
      rw [mul_zero, zero_mul]
    · rw [if_neg hs', mul_zero]
  · rw [if_neg hs, zero_mul, zero_mul]

end LatticeSystem.Fermion
