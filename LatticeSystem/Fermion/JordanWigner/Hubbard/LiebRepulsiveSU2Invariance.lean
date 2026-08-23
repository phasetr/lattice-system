import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSectorBridgeFinal
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSU2Invariance
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJModel
import LatticeSystem.Fermion.JordanWigner.CreationNumberIdentities

/-!
# `SU(2)` invariance of the symmetric repulsive Hubbard Hamiltonian (Tasaki §10.2.2, PR-12a)

Fifteenth installment of the Theorem 10.4 discharge arc (issue #5320). PR-11c's capstone
`liebRepulsive_exists_unique_casimir_sector`
(`LiebRepulsiveSectorBridgeFinal.lean:192`) takes the `SU(2)` commute/Hermiticity adapters for
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
(`symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber`). The middle summand's
invariance needs one genuinely new commutator, `fermionTotalSpinPlus_commute_fermionSiteNumber`
(the `Ŝ³` and `N̂` analogues, `totalSpinZ_commute_fermionSiteNumber` and
`fermionTotalNumber_commute_fermionSiteNumber`, already exist in `TJSpinSymmetry.lean` /
`TJNumberCommute.lean`).

This file also supplies the `Ne = 2·nUp` sector-arithmetic bridge that PR-12b's per-`s`
instantiation needs to match PR-11c's `liebHalfFillingSpinZVal`, and resolves the
`configSectorCompress_eq_submatrix` reference-0 debt
(`HubbardImpossibilityLowUVariationalCore.lean`, staged unconsumed since PR-11a → PR-11b →
PR-11c) by deletion, per
`lean-coding-conventions`'s "capstone 以外の参照 0 は装飾宣言" discipline: a fourth staging
round with no consumer is not an option, and PR-13 can re-derive the two-line corollary at its
actual point of use if one emerges.

## Main definitions and results

* `fermionTotalSpinPlus_commute_fermionSiteNumber` — the one new commutator,
  `Commute Ŝ⁺_tot n̂_x`, proved via the four public CAR same-site number identities.
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

/-! ## The one new commutator -/

/-- **The one genuinely new commutator of this PR.** `[Ŝ⁺_tot, n̂_x] = 0`: the total spin-raising
operator commutes with the per-site total number `n̂_x = n̂_{x,↑} + n̂_{x,↓}`. Proved per term
of `Ŝ⁺_tot = Σ_k c†_{k,↑}c_{k,↓}`: for `k ≠ x` all four operators sit at distinct Jordan–Wigner
modes (cloning the `hkx` branch of `fermionSpinPlusTerm_commute_interactionTerm`); for `k = x`
both sides reduce to `c†_{x,↑}c_{x,↓}` via the four public CAR same-site number identities
(`fermionMultiCreation_mul_fermionMultiNumber_eq_zero`,
`fermionMultiNumber_mul_fermionMultiCreation_eq_fermionMultiCreation`,
`fermionMultiNumber_mul_fermionMultiAnnihilation_eq_zero`,
`fermionMultiAnnihilation_mul_fermionMultiNumber_eq_fermionMultiAnnihilation`). -/
theorem fermionTotalSpinPlus_commute_fermionSiteNumber (N : ℕ) (x : Fin (N + 1)) :
    Commute (fermionTotalSpinPlus N) (fermionSiteNumber N x) := by
  unfold fermionTotalSpinPlus fermionSiteNumber
  refine Commute.sum_left _ _ _ fun k _ => ?_
  by_cases hkx : k = x
  · subst hkx
    unfold fermionUpCreation fermionDownAnnihilation fermionUpNumber fermionDownNumber
    set j₀ := spinfulIndex N k 0
    set j₁ := spinfulIndex N k 1
    have hne : j₀ ≠ j₁ := spinfulIndex_up_ne_down N k k
    have h_an_nu : fermionMultiAnnihilation (2 * N + 1) j₁ * fermionMultiNumber (2 * N + 1) j₀
        = fermionMultiNumber (2 * N + 1) j₀ * fermionMultiAnnihilation (2 * N + 1) j₁ :=
      (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne hne).symm.eq
    have h_nd_cr : fermionMultiNumber (2 * N + 1) j₁ * fermionMultiCreation (2 * N + 1) j₀
        = fermionMultiCreation (2 * N + 1) j₀ * fermionMultiNumber (2 * N + 1) j₁ :=
      (fermionMultiNumber_commute_fermionMultiCreation_of_ne hne.symm).eq
    have hlhs : (fermionMultiCreation (2 * N + 1) j₀ * fermionMultiAnnihilation (2 * N + 1) j₁)
          * (fermionMultiNumber (2 * N + 1) j₀ + fermionMultiNumber (2 * N + 1) j₁)
        = fermionMultiCreation (2 * N + 1) j₀ * fermionMultiAnnihilation (2 * N + 1) j₁ := by
      rw [Matrix.mul_add, Matrix.mul_assoc, h_an_nu, ← Matrix.mul_assoc,
        fermionMultiCreation_mul_fermionMultiNumber_eq_zero, Matrix.zero_mul, zero_add,
        Matrix.mul_assoc,
        fermionMultiAnnihilation_mul_fermionMultiNumber_eq_fermionMultiAnnihilation]
    have hrhs : (fermionMultiNumber (2 * N + 1) j₀ + fermionMultiNumber (2 * N + 1) j₁)
          * (fermionMultiCreation (2 * N + 1) j₀ * fermionMultiAnnihilation (2 * N + 1) j₁)
        = fermionMultiCreation (2 * N + 1) j₀ * fermionMultiAnnihilation (2 * N + 1) j₁ := by
      rw [Matrix.add_mul, ← Matrix.mul_assoc,
        fermionMultiNumber_mul_fermionMultiCreation_eq_fermionMultiCreation, ← Matrix.mul_assoc,
        h_nd_cr, Matrix.mul_assoc, fermionMultiNumber_mul_fermionMultiAnnihilation_eq_zero,
        Matrix.mul_zero, add_zero]
    exact hlhs.trans hrhs.symm
  · have h_cr_nu : Commute (fermionUpCreation N k) (fermionUpNumber N x) := by
      unfold fermionUpCreation fermionUpNumber
      exact (fermionMultiNumber_commute_fermionMultiCreation_of_ne
        (fun g => hkx (spinfulIndex_up_injective N g.symm))).symm
    have h_cr_nd : Commute (fermionUpCreation N k) (fermionDownNumber N x) := by
      unfold fermionUpCreation fermionDownNumber
      exact (fermionMultiNumber_commute_fermionMultiCreation_of_ne
        (spinfulIndex_up_ne_down N k x).symm).symm
    have h_an_nu : Commute (fermionDownAnnihilation N k) (fermionUpNumber N x) := by
      unfold fermionDownAnnihilation fermionUpNumber
      exact (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
        (spinfulIndex_up_ne_down N x k)).symm
    have h_an_nd : Commute (fermionDownAnnihilation N k) (fermionDownNumber N x) := by
      unfold fermionDownAnnihilation fermionDownNumber
      exact (fermionMultiNumber_commute_fermionMultiAnnihilation_of_ne
        (fun g => hkx (spinfulIndex_down_injective N g.symm))).symm
    exact (h_cr_nu.mul_left h_an_nu).add_right (h_cr_nd.mul_left h_an_nd)

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
term by `fermionTotalSpinPlus_commute_fermionSiteNumber` above, the scalar multiple of `1` by
`Commute.one_right`). -/
theorem fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian
    (N : ℕ) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    Commute (fermionTotalSpinPlus N) (symmetricRepulsiveHubbardHamiltonian N T U) := by
  rw [symmetricRepulsiveHubbardHamiltonian,
    symmetricRepulsiveHubbardInteraction_eq_uniform_sub_siteNumber]
  refine (fermionTotalSpinPlus_commute_hubbardKinetic N _).add_right (Commute.add_right
    (Commute.sub_right (fermionTotalSpinPlus_commute_hubbardOnSiteInteractionSite N _) ?_)
    ((Commute.one_right _).smul_right _))
  exact Commute.sum_right _ _ _ fun x _ =>
    (fermionTotalSpinPlus_commute_fermionSiteNumber N x).smul_right _

/-- `[Ŝ⁻_tot, Ĥ] = 0` for the symmetric repulsive Hubbard Hamiltonian: derived from
`[Ŝ⁺_tot, Ĥ] = 0` by conjugate transposes, using `(Ŝ⁺_tot)ᴴ = Ŝ⁻_tot` and Hermiticity of `Ĥ`.
Clone of
`fermionTotalSpinMinus_commute_attractiveHubbardHamiltonian`
(`LiebAttractiveSU2Invariance.lean:81`); the conjugate-transpose step must spell
`Matrix.conjTranspose` explicitly (the postfix `ᴴ` fails to parse inside
`namespace LatticeSystem.Quantum`). -/
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
10.4 (`LiebRepulsive.lean:134`). -/
theorem liebHalfFillingSpinZVal_eq_of_two_mul (N nUp Ne : ℕ) (hNe : Ne = 2 * nUp) :
    liebHalfFillingSpinZVal N nUp = ((Ne : ℂ) - ((N : ℂ) + 1)) / 2 := by
  subst hNe
  rw [liebHalfFillingSpinZVal]
  push_cast
  ring

/-! ## The unconditional capstone -/

/-- **The unconditional corollary of PR-11c's capstone.**
`liebRepulsive_exists_unique_casimir_sector` (`LiebRepulsiveSectorBridgeFinal.lean:192`) took
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

end LatticeSystem.Fermion
