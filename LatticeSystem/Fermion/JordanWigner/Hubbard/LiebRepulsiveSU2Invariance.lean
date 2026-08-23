import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSectorBridgeFinal
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSU2Invariance
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSpinSymmetryRaising
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorReduction

/-!
# `SU(2)` invariance of the symmetric repulsive Hubbard Hamiltonian (Tasaki §10.2.2, PR-12a)

Fifteenth installment of the Theorem 10.4 discharge arc (issue #5320). PR-11c's capstone
`liebRepulsive_exists_unique_casimir_sector`
(`LiebRepulsiveSectorBridgeFinal.lean`) takes the `SU(2)` commute/Hermiticity adapters for
`symmetricRepulsiveHubbardHamiltonian` as explicit hypotheses, since they were **not yet
formalized** for this Hamiltonian family (unlike `hubbardHamiltonian`,
`SaturatedFerromagnetism.lean`, and `attractiveHubbardHamiltonian`,
`LiebAttractiveSU2Invariance.lean`). This file supplies them, mirroring
`LiebAttractiveSU2Invariance.lean` line for line.

The site-dependent symmetric interaction
`Ĥint' = Σ_x U_x (n̂_{x,↑} − ½)(n̂_{x,↓} − ½)` (Tasaki eq. (10.2.6)) is **not** itself a multiple
of a `hubbardOnSiteInteractionSite`, so the attractive family's proofs do not clone verbatim.
Expanded
against a site-dependent `U`, it decomposes into three separately `SU(2)`-invariant summands:
`hubbardOnSiteInteractionSite N U − Σ_x (U_x/2) • n̂_x + ((Σ_x U_x)/4) • 1`
(`symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber`). For `Ŝ⁺`, the middle
summand's invariance reuses the existing per-site-number commutator
`totalSpinPlus_commute_fermionSiteNumber` (`TJSpinSymmetryRaising.lean`); no new commutator is
needed there. For `N̂↑`/`N̂↓`, the per-site-number commutators (`hsite` at lines 152 and 170
below) are new, proved inline from `fermionMultiNumber_commute`; `Ŝ³` and `N̂` are then free
corollaries of the `N̂↑`/`N̂↓` results.

This file also supplies the `Ne = 2·nUp` sector-arithmetic bridge that PR-12b's per-`s`
instantiation needs to match PR-11c's `liebHalfFillingSpinZVal`, and resolves the
`configSectorCompress_eq_submatrix` reference-0 debt
(`HubbardImpossibilityLowUVariationalCore.lean`, staged unconsumed since PR-11a → PR-11b →
PR-11c) by deletion, per
`lean-coding-conventions`'s "capstone 以外の参照 0 は装飾宣言" discipline: a fourth staging
round with no consumer is not an option, and PR-13 can re-derive the two-line corollary at its
actual point of use if one emerges.

## Main definitions and results

* `symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber` — the site-dependent expansion
  of `Ĥint'` into a `hubbardOnSiteInteractionSite` term, a per-site-number term, and a scalar.
* `symmetricRepulsiveHubbardHamiltonian_isHermitian` — Hermiticity of the symmetric repulsive
  Hamiltonian (kinetic part via `hubbardKinetic_isHermitian`, interaction part via
  `symmetricRepulsiveHubbardInteraction_eq_diagonal`).
* `fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian`,
  `fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian`,
  `fermionTotalUpNumber_commute_symmetricRepulsiveHubbardHamiltonian`,
  `fermionTotalDownNumber_commute_symmetricRepulsiveHubbardHamiltonian`,
  `fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian`,
  `fermionTotalNumber_commute_symmetricRepulsiveHubbardHamiltonian`,
  `fermionTotalSpinSquared_commute_symmetricRepulsiveHubbardHamiltonian` — the `SU(2)` generator
  and Casimir commutators.
* `liebHalfFillingSpinZVal_eq_of_two_mul` — `liebHalfFillingSpinZVal N nUp = ((Ne:ℂ) −
  ((N:ℂ)+1))/2` given `Ne = 2 * nUp`, keeping `nUp` primitive.
* `liebRepulsive_exists_unique_casimir_sector_unconditional` — the unconditional corollary of
  PR-11c's capstone with all four adapter hypotheses discharged by the above.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §9.3.3, p. 333 (eq. (9.3.35)); §10.2.2, pp. 350–353.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

variable {N : ℕ}

/-! ## The site-dependent expansion of the symmetric interaction -/

/-- **The site-dependent expansion.** Summing `symmetricHubbardOnSite_expand`
(`LiebRepulsiveShibaConjugation.lean:54`) against a site-dependent `U : Fin (N+1) → ℝ` gives
`Ĥint' = hubbardOnSiteInteractionSite N U − Σ_x (U_x/2) • n̂_x + ((Σ_x U_x)/4) • 1`, the
site-dependent generalization of PR-1's in-proof identity `hint`
(`LiebRepulsiveBalancedGround.lean:382`). At a constant `U`, the middle term collapses to
`(U/2) • N̂`, which is why PR-1 could shift by a scalar and the site-dependent case cannot (see
the arc's "Open obligation" record, issue #5320). -/
theorem symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber
    (N : ℕ) (U : Fin (N + 1) → ℝ) :
    symmetricRepulsiveHubbardInteraction N U
      = hubbardOnSiteInteractionSite N (fun x => (U x : ℂ))
        - (∑ x : Fin (N + 1), ((U x : ℂ) / 2) • fermionSiteNumber N x)
        + ((∑ x : Fin (N + 1), (U x : ℂ)) / 4) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
  simp only [symmetricRepulsiveHubbardInteraction, hubbardOnSiteInteractionSite]
  rw [Finset.sum_div, Finset.sum_smul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [symmetricHubbardOnSite_expand, fermionSiteNumber]
  module

/-! ## Hermiticity -/

/-- **The symmetric repulsive Hubbard Hamiltonian is Hermitian.** Kinetic part via
`hubbardKinetic_isHermitian` (real symmetric hopping); interaction part via
`symmetricRepulsiveHubbardInteraction_eq_diagonal`
(`LiebRepulsiveShibaInteraction.lean:87`, manifestly real diagonal entries). -/
theorem symmetricRepulsiveHubbardHamiltonian_isHermitian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) :
    (symmetricRepulsiveHubbardHamiltonian N T U).IsHermitian := by
  rw [symmetricRepulsiveHubbardHamiltonian]
  refine Matrix.IsHermitian.add (hubbardKinetic_isHermitian N fun i j => ?_) ?_
  · rw [← starRingEnd_apply, Complex.conj_ofReal]; exact_mod_cast hT i j
  · rw [symmetricRepulsiveHubbardInteraction_eq_diagonal]
    refine Matrix.isHermitian_diagonal_iff.mpr fun c => ?_
    rw [isSelfAdjoint_iff, Complex.star_def, symmetricRepulsiveInteractionDiag]
    simp only [map_sum, map_mul, map_sub, map_div₀, map_one, map_ofNat, map_natCast,
      Complex.conj_ofReal]

/-! ## `SU(2)` generator commutators -/

/-- `[Ŝ⁺_tot, Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian: the kinetic part commutes
by `fermionTotalSpinPlus_commute_hubbardKinetic`; the interaction commutes term-by-term via
`symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber`'s three summands
(`hubbardOnSiteInteractionSite` covered by `LiebAttractiveSU2Invariance.lean`, the site-number
term by `totalSpinPlus_commute_fermionSiteNumber` (`TJSpinSymmetryRaising.lean`), the scalar
multiple of `1` by `Commute.one_right`). -/
theorem fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalSpinPlus N) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  rw [symmetricRepulsiveHubbardHamiltonian,
    symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber]
  refine (fermionTotalSpinPlus_commute_hubbardKinetic N _).add_right (Commute.add_right
    (Commute.sub_right (fermionTotalSpinPlus_commute_hubbardOnSiteInteractionSite N _) ?_)
    ((Commute.one_right _).smul_right _))
  exact Commute.sum_right _ _ _ fun x _ =>
    (totalSpinPlus_commute_fermionSiteNumber N x).smul_right _

/-- `[Ŝ⁻_tot, Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian: derived from
`[Ŝ⁺_tot, Ĥ] = 0` by conjugate transposes, using `(Ŝ⁺_tot)ᴴ = Ŝ⁻_tot` and Hermiticity of `Ĥ`.
Clone of
`fermionTotalSpinMinus_commute_attractiveHubbardHamiltonian`
(`LiebAttractiveSU2Invariance.lean:81`); the conjugate-transpose step must spell
`Matrix.conjTranspose` explicitly since `congrArg` needs an explicit function argument
(the postfix `ᴴ` notation is not itself a function it can take). -/
theorem fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalSpinMinus N) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  have h_plus :=
    (fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian N T U).eq
  have h_H := symmetricRepulsiveHubbardHamiltonian_isHermitian N T hT U
  have h_adj := congrArg Matrix.conjTranspose h_plus
  simp only [Matrix.conjTranspose_mul, fermionTotalSpinPlus_conjTranspose N,
    h_H.eq] at h_adj
  exact h_adj.symm

/-- `[N̂_↑, Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian. -/
theorem fermionTotalUpNumber_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalUpNumber N) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  have hsite : ∀ x : Fin (N + 1),
      Commute (fermionTotalUpNumber N) (fermionSiteNumber N x) := by
    intro x
    unfold fermionTotalUpNumber fermionSiteNumber fermionUpNumber fermionDownNumber
    exact Commute.sum_left _ _ _ fun k _ => Commute.add_right
      (fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N k 0) (spinfulIndex N x 0))
      (fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N k 0) (spinfulIndex N x 1))
  rw [symmetricRepulsiveHubbardHamiltonian,
    symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber]
  exact (fermionTotalUpNumber_commute_hubbardKinetic N _).add_right (Commute.add_right
    (Commute.sub_right (fermionTotalUpNumber_commute_hubbardOnSiteInteractionSite _)
      (Commute.sum_right _ _ _ fun x _ => (hsite x).smul_right _))
    ((Commute.one_right _).smul_right _))

/-- `[N̂_↓, Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian. -/
theorem fermionTotalDownNumber_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalDownNumber N) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  have hsite : ∀ x : Fin (N + 1),
      Commute (fermionTotalDownNumber N) (fermionSiteNumber N x) := by
    intro x
    unfold fermionTotalDownNumber fermionSiteNumber fermionUpNumber fermionDownNumber
    exact Commute.sum_left _ _ _ fun k _ => Commute.add_right
      (fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N k 1) (spinfulIndex N x 0))
      (fermionMultiNumber_commute (2 * N + 1) (spinfulIndex N k 1) (spinfulIndex N x 1))
  rw [symmetricRepulsiveHubbardHamiltonian,
    symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber]
  exact (fermionTotalDownNumber_commute_hubbardKinetic N _).add_right (Commute.add_right
    (Commute.sub_right (fermionTotalDownNumber_commute_hubbardOnSiteInteractionSite _)
      (Commute.sum_right _ _ _ fun x _ => (hsite x).smul_right _))
    ((Commute.one_right _).smul_right _))

/-- `[Ŝ³_tot, Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian: free corollary of
`[N̂_↑, Ĥ] = [N̂_↓, Ĥ] = 0` and `Ŝ³ = (N̂_↑ − N̂_↓)/2`. -/
theorem fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalSpinZ N) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  unfold fermionTotalSpinZ
  exact ((fermionTotalUpNumber_commute_symmetricRepulsiveHubbardHamiltonian N T U).sub_left
    (fermionTotalDownNumber_commute_symmetricRepulsiveHubbardHamiltonian N T U)).smul_left _

/-- `[N̂, Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian: free corollary of
`[N̂_↑, Ĥ] = [N̂_↓, Ĥ] = 0` and `N̂ = N̂_↑ + N̂_↓`. -/
theorem fermionTotalNumber_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalNumber (2 * N + 1)) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  rw [fermionTotalNumber_eq_up_add_down]
  exact (fermionTotalUpNumber_commute_symmetricRepulsiveHubbardHamiltonian N T U).add_left
    (fermionTotalDownNumber_commute_symmetricRepulsiveHubbardHamiltonian N T U)

/-- **`[(Ŝ_tot)², Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian**: the Casimir
`(Ŝ_tot)² = Ŝ⁻_tot Ŝ⁺_tot + Ŝ³_tot(Ŝ³_tot + 1)` commutes with `Ĥ`, i.e. `Ĥ` is
`SU(2)` invariant. Assembled from the generator commutes above, exactly as
`fermionTotalSpinSquared_commute_attractiveHubbardHamiltonian`. -/
theorem fermionTotalSpinSquared_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalSpinSquared N) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  unfold fermionTotalSpinSquared
  apply Commute.add_left
  · exact (fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian N T hT U).mul_left
      (fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian N T U)
  · have h_z := fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N T U
    exact h_z.mul_left (h_z.add_left (Commute.one_left _))

/-! ## The `Ne = 2·nUp` sector-arithmetic bridge -/

/-- **The `Ne = 2·nUp` sector-arithmetic bridge.** `liebHalfFillingSpinZVal N nUp = ((Ne:ℂ) −
((N:ℂ)+1))/2` given `Ne = 2 * nUp`, stated with `nUp` primitive and `Ne = 2 * nUp` as an explicit
hypothesis (rather than `nUp = Ne / 2` as a conclusion) to avoid natural-number division in
downstream statements. Needed so that PR-12b's per-`s` instantiation can match PR-11c's
`liebHalfFillingSpinZVal N nUp` sector parameter against the `Ne`-indexed statement of Theorem
10.4 (`LiebRepulsiveHalfFillingDischarge.lean`). -/
theorem liebHalfFillingSpinZVal_eq_of_two_mul (N nUp Ne : ℕ) (hNe : Ne = 2 * nUp) :
    liebHalfFillingSpinZVal N nUp = ((Ne : ℂ) - ((N : ℂ) + 1)) / 2 := by
  subst hNe
  rw [liebHalfFillingSpinZVal]
  push_cast
  ring

/-! ## The unconditional capstone -/

/-- **The unconditional corollary of PR-11c's capstone.**
`liebRepulsive_exists_unique_casimir_sector` (`LiebRepulsiveSectorBridgeFinal.lean`) took
the four `SU(2)` commute/Hermiticity adapters as explicit hypotheses; this file has now supplied
all four for `symmetricRepulsiveHubbardHamiltonian`, so this corollary discharges them and
consumes PR-11c's previously reference-0 capstone, closing that debt. -/
theorem liebRepulsive_exists_unique_casimir_sector_unconditional (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ c : ℂ,
      numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
          (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c ≠ ⊥ ∧
        ∀ c' : ℂ, c' ≠ c →
          numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
              (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c' ≠ ⊥ →
            minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c)
                (symmetricRepulsiveHubbardHamiltonian N T U) <
              minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c')
                (symmetricRepulsiveHubbardHamiltonian N T U) :=
  liebRepulsive_exists_unique_casimir_sector N Ne hNe_even hNe_pos hNe_lt T hT_symm hbip
    hT_conn U hU_pos (symmetricRepulsiveHubbardHamiltonian_isHermitian N T hT_symm U)
    (fermionTotalNumber_commute_symmetricRepulsiveHubbardHamiltonian N T U).symm
    (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N T U).symm
    (fermionTotalSpinSquared_commute_symmetricRepulsiveHubbardHamiltonian N T hT_symm U).symm

/-! ## `Ĥ` commutes with the Cartesian generators `tJTotalSpinOne`/`tJTotalSpinTwo` (PR-14a) -/

/-- **The symmetric repulsive Hubbard Hamiltonian commutes with `Ŝ⁽¹⁾_tot = ½(Ŝ⁺+Ŝ⁻)`.** Repulsive
analogue of `attractiveHubbardHamiltonian_mul_tJTotalSpinOne`
(`LiebAttractiveFullSectorSU2Algebra.lean:201`), assembled from the `Ŝ⁺`/`Ŝ⁻` commutators above. -/
theorem symmetricRepulsiveHubbardHamiltonian_mul_tJTotalSpinOne
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    symmetricRepulsiveHubbardHamiltonian N T U * tJTotalSpinOne N
      = tJTotalSpinOne N * symmetricRepulsiveHubbardHamiltonian N T U := by
  have hcP := (fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian N T U).eq.symm
  have hcM :=
    (fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian N T hT_symm U).eq.symm
  rw [tJTotalSpinOne, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hcP, hcM]

/-- **The symmetric repulsive Hubbard Hamiltonian commutes with `Ŝ⁽²⁾_tot = −(i/2)(Ŝ⁺−Ŝ⁻)`.**
Repulsive analogue of `attractiveHubbardHamiltonian_mul_tJTotalSpinTwo`
(`LiebAttractiveFullSectorSU2Algebra.lean:211`), assembled from the `Ŝ⁺`/`Ŝ⁻` commutators above. -/
theorem symmetricRepulsiveHubbardHamiltonian_mul_tJTotalSpinTwo
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT_symm : ∀ i j, T i j = T j i) :
    symmetricRepulsiveHubbardHamiltonian N T U * tJTotalSpinTwo N
      = tJTotalSpinTwo N * symmetricRepulsiveHubbardHamiltonian N T U := by
  have hcP := (fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian N T U).eq.symm
  have hcM :=
    (fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian N T hT_symm U).eq.symm
  rw [tJTotalSpinTwo, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcP, hcM]

end LatticeSystem.Fermion
