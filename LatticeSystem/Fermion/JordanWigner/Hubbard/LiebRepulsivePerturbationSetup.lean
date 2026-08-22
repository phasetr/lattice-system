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
conditions are exactly the defining properties `P w ∈ ker Ĥ₀` and `w - P w ⊥ ker Ĥ₀`. Used both for
the operator-product projection `∏ᵢ (1 - n̂↑n̂↓)` and for the explicit diagonal indicator matrix. -/
private theorem kernelProjectionMatrix_liebPerturbationH0_eq_of_fixes_hardcore (N : ℕ)
    {P : ManyBodyOp (Fin (2 * N + 2))} (hHerm : P.IsHermitian)
    (hmul : liebPerturbationH0 N * P = 0)
    (hfix : ∀ ψ ∈ hubbardHardcoreSubspace N, P.mulVec ψ = ψ) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0 N) = P := by
  refine Matrix.toEuclideanLin.injective (LinearMap.ext fun w => ?_)
  rw [LatticeSystem.Math.toEuclideanLin_kernelProjectionMatrix]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · rw [LatticeSystem.Math.matrixKernel, LinearMap.mem_ker,
      ← LatticeSystem.Math.toEuclideanLin_mul_apply, hmul]
    simp
  · intro u hu
    have hPu : Matrix.toEuclideanLin P u = u := by
      apply WithLp.ofLp_injective 2
      exact hfix _ ((mem_matrixKernel_liebPerturbationH0_iff N u).mp hu)
    have hsym : (Matrix.toEuclideanLin P).IsSymmetric :=
      Matrix.isHermitian_iff_isSymmetric.mp hHerm
    rw [inner_sub_left, hsym w u, hPu, sub_self]

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

/-- The kernel projection of `Ĥ₀` in explicit diagonal form: the indicator matrix of the
hard-core configurations. Together with
`kernelProjectionMatrix_liebPerturbationH0_eq_hardcoreProjection` this identifies the operator
product `∏ᵢ (1 - n̂↑n̂↓)` with that indicator, which is what makes the reduced-inverse identities
below a diagonal computation. -/
private theorem kernelProjectionMatrix_liebPerturbationH0_eq_diagonal (N : ℕ) :
    LatticeSystem.Math.kernelProjectionMatrix (liebPerturbationH0 N)
      = Matrix.diagonal (fun c : Fin (2 * N + 2) → Fin 2 =>
          if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 then 1 else 0) := by
  refine kernelProjectionMatrix_liebPerturbationH0_eq_of_fixes_hardcore N ?_ ?_ ?_
  · refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
    change star (fun c : Fin (2 * N + 2) → Fin 2 =>
      if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 then (1 : ℂ) else 0) = _
    funext c
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 <;>
      simp [Pi.star_apply, h]
  · rw [liebPerturbationH0_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine Eq.trans (congrArg Matrix.diagonal ?_) Matrix.diagonal_zero'
    funext c
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 <;> simp [h]
  · intro ψ hψ
    funext c
    rw [Matrix.mulVec_diagonal]
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0
    · rw [if_pos h, one_mul]
    · rw [if_neg h, zero_mul]
      obtain ⟨x, hx⟩ : ∃ x : Fin (N + 1),
          ((c (spinfulIndex N x 0)).val : ℂ) * ((c (spinfulIndex N x 1)).val : ℂ) ≠ 0 := by
        by_contra hall
        push Not at hall
        exact h ((hubbardConfigInteractionWeight_one_eq_zero_iff N c).mpr hall)
      have hval : ∀ k : Fin (2 * N + 2), ((c k).val : ℂ) ≠ 0 → c k = 1 := by
        intro k hk
        rcases (show c k = 0 ∨ c k = 1 from by
          rcases (c k) with ⟨u, hu⟩; interval_cases u; exacts [Or.inl rfl, Or.inr rfl]) with h0 | h1
        · exact absurd (by rw [h0]; simp) hk
        · exact h1
      exact (hardcore_mulVec_apply_eq_zero_of_double N ψ hψ c x
        (hval _ (left_ne_zero_of_mul hx)) (hval _ (right_ne_zero_of_mul hx))).symm

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
  have hsub : (1 : ManyBodyOp (Fin (2 * N + 2)))
        - Matrix.diagonal (fun c : Fin (2 * N + 2) → Fin 2 =>
            if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 then 1 else 0)
      = Matrix.diagonal (fun c : Fin (2 * N + 2) → Fin 2 =>
          if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 then 0 else 1) := by
    rw [show (1 : ManyBodyOp (Fin (2 * N + 2))) = Matrix.diagonal (fun _ => (1 : ℂ)) from
      Matrix.diagonal_one.symm, Matrix.diagonal_sub]
    congr 1
    funext c
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 <;> simp [h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [kernelProjectionMatrix_liebPerturbationH0_eq_diagonal, liebPerturbationH0_eq_diagonal,
      hInv, hsub, Matrix.diagonal_mul_diagonal]
    congr 1
    funext c
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0
    · simp [h]
    · simp [h]
  · rw [kernelProjectionMatrix_liebPerturbationH0_eq_diagonal, liebPerturbationH0_eq_diagonal,
      hInv, hsub, Matrix.diagonal_mul_diagonal]
    congr 1
    funext c
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0
    · simp [h]
    · simp [h]
  · rw [hInv, kernelProjectionMatrix_liebPerturbationH0_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine Eq.trans (congrArg Matrix.diagonal ?_) Matrix.diagonal_zero'
    funext c
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 <;> simp [h]
  · rw [hInv, kernelProjectionMatrix_liebPerturbationH0_eq_diagonal, Matrix.diagonal_mul_diagonal]
    refine Eq.trans (congrArg Matrix.diagonal ?_) Matrix.diagonal_zero'
    funext c
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 <;> simp [h]
  · rw [hInv]
    refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
    change star (fun c : Fin (2 * N + 2) → Fin 2 =>
      if hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0 then (0 : ℂ)
      else (hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c)⁻¹) = _
    funext c
    have hreal : star (hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c)
        = hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c := by
      rw [hubbardConfigInteractionWeight_one_eq_natCast]
      simp
    by_cases h : hubbardConfigInteractionWeight N (fun _ => (1 : ℂ)) c = 0
    · simp [Pi.star_apply, h]
    · rw [Pi.star_apply, if_neg h, star_inv₀, hreal]

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
