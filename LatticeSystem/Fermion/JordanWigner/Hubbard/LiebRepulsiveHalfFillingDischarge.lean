import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveWeightConfinement
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveBalancedGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveMultipletCompanion
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaInteraction
import LatticeSystem.Math.MatrixAnalysis.PiDiagonalEigenspace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Theorem 10.4 discharge: degenerate sublattice, uniform-disjunct assembly, capstone (PR-15b/15c)

Assembly layer for the Theorem 10.4 (Lieb repulsive Hubbard half-filling) discharge arc
(issue #5320). Covers the two pieces `liebRepulsive_symmetric_halfFilling_conditional`
(`LiebRepulsiveWeightConfinement.lean`, requiring `1 ≤ |A|` and `1 ≤ |B|`) does not:

* the **degenerate case** `|A| = 0 ∨ |B| = 0`, which forces the hopping matrix `T` to vanish and,
  via connectedness of the (now edgeless) hopping support graph, forces `N = 0` — a single-site
  model whose ground submodule is a single diagonal eigenspace, handled directly;
* the **uniform-disjunct transport**, converting the symmetric-form conjuncts at a constant `U` to
  the uniform-interaction Hamiltonian `repulsiveHubbardHamiltonian`, via
  `symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform`
  (`LiebRepulsiveBalancedGround.lean:363`);

and, at the end of this file (PR-15c), assembles both disjuncts into
`theorem_10_4_lieb_repulsive_half_filling`, the capstone of the discharge arc (formerly
`axiom theorem_10_4_lieb_repulsive_half_filling` in `LiebRepulsive.lean`, moved here since
`LiebRepulsive.lean` sits strictly upstream of this discharge chain).

## Main results

* `liebRepulsive_hopping_eq_zero_of_degenerate` — `|A| = 0 ∨ |B| = 0` forces `T = 0`.
* `liebRepulsive_degenerate_N_eq_zero` — a connected hopping support graph on a vanishing `T`
  forces `N = 0`.
* `liebRepulsive_degenerate_sublatticeImbalance_eq_one` — at `N = 0`, `sublatticeImbalance A = 1`
  for every bipartition `A`.
* `liebRepulsive_groundSubmodule_N0_eq_numberEigenspace` — at `N = 0` the ground submodule at
  `E₀ = −U₀/4` is the singly-occupied eigenspace of the total number operator.
* `liebRepulsive_singlyOccupied_card_eq_two` — that eigenspace has exactly two spanning
  configurations.
* `liebRepulsive_symmetric_halfFilling_degenerate` — the four Theorem 10.4 conjuncts for
  `symmetricRepulsiveHubbardHamiltonian` in the degenerate case `|A| = 0 ∨ |B| = 0`.
* `liebRepulsive_symmetric_halfFilling` — the four Theorem 10.4 conjuncts for
  `symmetricRepulsiveHubbardHamiltonian`, for **every** bipartition `A` (no `1 ≤ |A|`/`1 ≤ |B|`
  hypothesis), combining the conditional capstone with the degenerate case above.
* `liebRepulsive_uniform_of_symmetric` — transports the symmetric-form conjuncts at a constant `U`
  to the uniform-interaction Hamiltonian `repulsiveHubbardHamiltonian`.
* `theorem_10_4_lieb_repulsive_half_filling` — **Tasaki Theorem 10.4** itself, assembled from the
  two lemmas above by splitting `IsLiebRepulsiveModel`'s `IsLiebRepulsiveHamiltonian` disjunction.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-! ## Degeneracy reduction: `|A| = 0 ∨ |B| = 0` forces `T = 0` and `N = 0` -/

/-- If the bipartition sublattice `A` is empty, `HoppingRespectsBipartition` forces `T = 0`
(every entry is forced zero, since `x ∈ A` is vacuously false for every `x`). -/
private theorem liebRepulsive_hopping_eq_zero_of_A_card_eq_zero {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (hA : A.card = 0) : T = 0 := by
  ext x y
  rw [Matrix.zero_apply]
  by_contra hne
  have h := hbip hne
  rw [Finset.card_eq_zero.mp hA] at h
  simp at h

/-- If the complement sublattice `B = Aᶜ` is empty, `HoppingRespectsBipartition` forces `T = 0`
(every entry is forced zero, since `x ∈ A` is vacuously true for every `x`). -/
private theorem liebRepulsive_hopping_eq_zero_of_B_card_eq_zero {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (hB : (bipartitionComplement A).card = 0) : T = 0 := by
  have hall : ∀ z : Fin (N + 1), z ∈ A := by
    intro z
    by_contra hz
    have hmem : z ∈ bipartitionComplement A := by
      rw [bipartitionComplement, Finset.mem_filter]
      exact ⟨Finset.mem_univ z, hz⟩
    rw [Finset.card_eq_zero.mp hB] at hmem
    exact absurd hmem (Finset.notMem_empty z)
  ext x y
  rw [Matrix.zero_apply]
  by_contra hne
  exact (hbip hne).mp (hall x) (hall y)

/-- **Degenerate hopping vanishing.** `|A| = 0 ∨ |B| = 0` forces `T = 0`, combining the two
one-sided collapses above. -/
theorem liebRepulsive_hopping_eq_zero_of_degenerate {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (hdeg : A.card = 0 ∨ (bipartitionComplement A).card = 0) : T = 0 := by
  rcases hdeg with h | h
  · exact liebRepulsive_hopping_eq_zero_of_A_card_eq_zero hbip h
  · exact liebRepulsive_hopping_eq_zero_of_B_card_eq_zero hbip h

/-- **The degenerate case forces `N = 0`.** A vanishing hopping matrix has an edgeless support
graph (`hoppingSupportGraph T = ⊥`); if that graph is `Preconnected`, the vertex type `Fin (N + 1)`
is a subsingleton (`SimpleGraph.preconnected_bot_iff_subsingleton`), forcing `N = 0`. -/
theorem liebRepulsive_degenerate_N_eq_zero {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT_conn : (hoppingSupportGraph T).Preconnected) (hT0 : T = 0) : N = 0 := by
  have hbot : hoppingSupportGraph T = ⊥ := by
    ext x y
    simp [hoppingSupportGraph, SimpleGraph.fromRel_adj, hT0]
  rw [hbot, SimpleGraph.preconnected_bot_iff_subsingleton] at hT_conn
  have hcard := Fintype.card_le_one_iff_subsingleton.mpr hT_conn
  rw [Fintype.card_fin] at hcard
  omega

/-- **Sublattice imbalance is `1` at `N = 0`.** With a single site, every bipartition `A` has
`|A| + |B| = 1`, hence `||A| − |B|| = 1` regardless of which of `A`, `B` is empty. -/
theorem liebRepulsive_degenerate_sublatticeImbalance_eq_one {A : Finset (Fin (0 + 1))} :
    sublatticeImbalance A = 1 := by
  have hcard := bipartitionComplement_card_add 0 A
  rw [sublatticeImbalance]
  omega

/-! ## The `N = 0` case: a single diagonal eigenspace -/

/-- The single-site singly-occupied **spin-up** configuration: the up mode (even Jordan–Wigner
index `0`) is occupied, the down mode (odd index `1`) is empty. Definitionally the configuration
underlying `hubbardAllUpState 0`. -/
private def singleSiteUpConfig : Fin (2 * 0 + 2) → Fin 2 :=
  fun k => if k.val % 2 = 0 then 1 else 0

/-- The single-site singly-occupied **spin-down** configuration: the up mode is empty, the down
mode is occupied. -/
private def singleSiteDownConfig : Fin (2 * 0 + 2) → Fin 2 :=
  fun k => if k.val % 2 = 0 then 0 else 1

/-- `hubbardAllUpState 0` is the basis vector at `singleSiteUpConfig` (definitional unfolding of
`hubbardAllUpState` at `N = 0`). -/
private theorem hubbardAllUpState_zero :
    hubbardAllUpState 0 = basisVec singleSiteUpConfig := rfl

/-- The mode occupations of the two singly-occupied single-site configurations. -/
private theorem singleSiteConfig_val :
    (singleSiteUpConfig 0).val = 1 ∧ (singleSiteUpConfig 1).val = 0 ∧
      (singleSiteDownConfig 0).val = 0 ∧ (singleSiteDownConfig 1).val = 1 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The two singly-occupied single-site configurations are distinct. -/
private theorem singleSiteUpConfig_ne_downConfig :
    singleSiteUpConfig ≠ singleSiteDownConfig := by decide

/-- At `N = 0` the up mode is Jordan–Wigner index `0` and the down mode is index `1`. -/
private theorem spinfulIndex_zero_eq :
    spinfulIndex 0 (0 : Fin (0 + 1)) 0 = (0 : Fin (2 * 0 + 2)) ∧
      spinfulIndex 0 (0 : Fin (0 + 1)) 1 = (1 : Fin (2 * 0 + 2)) :=
  ⟨rfl, rfl⟩

/-- The single-site configurations of total occupation `1` are exactly the two singly-occupied
ones. -/
private theorem occupation_sum_eq_one_iff (c : Fin (2 * 0 + 2) → Fin 2) :
    (∑ j : Fin (2 * 0 + 2), (c j).val) = 1
      ↔ (c = singleSiteUpConfig ∨ c = singleSiteDownConfig) := by
  revert c
  decide

/-- Complex form of `occupation_sum_eq_one_iff`: the diagonal entry of the total number operator
equals `1` exactly on the two singly-occupied configurations. -/
private theorem numberDiag_zero_eq_one_iff (c : Fin (2 * 0 + 2) → Fin 2) :
    (∑ j : Fin (2 * 0 + 2), ((c j).val : ℂ)) = 1
      ↔ (c = singleSiteUpConfig ∨ c = singleSiteDownConfig) := by
  rw [← Nat.cast_sum, Nat.cast_eq_one]
  exact occupation_sum_eq_one_iff c

/-- With vanishing hopping the single-site symmetric repulsive Hamiltonian is the diagonal matrix
of the symmetric interaction. -/
private theorem symmetricRepulsiveHubbardHamiltonian_zero_eq_diagonal
    {T : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ} (hT0 : T = 0) (U : Fin (0 + 1) → ℝ) :
    symmetricRepulsiveHubbardHamiltonian 0 T U
      = Matrix.diagonal (symmetricRepulsiveInteractionDiag 0 U) := by
  have hkin : hubbardKinetic 0 (fun x y => ((T x y : ℝ) : ℂ)) = 0 := by
    subst hT0
    simp [hubbardKinetic]
  rw [symmetricRepulsiveHubbardHamiltonian, hkin, zero_add,
    symmetricRepulsiveHubbardInteraction_eq_diagonal]

/-- The single-site symmetric interaction diagonal, evaluated on a configuration:
`U₀ (c↑ − ½)(c↓ − ½)`. -/
private theorem symmetricRepulsiveInteractionDiag_zero_apply (U : Fin (0 + 1) → ℝ)
    (c : Fin (2 * 0 + 2) → Fin 2) :
    symmetricRepulsiveInteractionDiag 0 U c
      = (U 0 : ℂ) * ((((c 0).val : ℂ) - 1 / 2) * (((c 1).val : ℂ) - 1 / 2)) := by
  rw [symmetricRepulsiveInteractionDiag, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    spinfulIndex_zero_eq.1, spinfulIndex_zero_eq.2]

/-- At `N = 0` the interaction diagonal takes the value `−U₀/4` exactly on the two singly-occupied
configurations (the empty and the doubly-occupied one carry `+U₀/4`, distinct because `U₀ > 0`). -/
private theorem symmetricRepulsiveInteractionDiag_zero_eq_iff {U : Fin (0 + 1) → ℝ}
    (hU : 0 < U 0) (c : Fin (2 * 0 + 2) → Fin 2) :
    symmetricRepulsiveInteractionDiag 0 U c = -(U 0 : ℂ) / 4
      ↔ (c = singleSiteUpConfig ∨ c = singleSiteDownConfig) := by
  have hU0 : (U 0 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hU)
  have h0 : (c 0).val = 0 ∨ (c 0).val = 1 := by have := (c 0).isLt; omega
  have h1 : (c 1).val = 0 ∨ (c 1).val = 1 := by have := (c 1).isLt; omega
  rw [symmetricRepulsiveInteractionDiag_zero_apply, ← occupation_sum_eq_one_iff,
    Fin.sum_univ_two]
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] <;>
    simp only [Nat.cast_zero, Nat.cast_one]
  · exact ⟨fun h => absurd (by linear_combination (2 : ℂ) * h) hU0,
      fun h => absurd h (by norm_num)⟩
  · exact ⟨fun _ => trivial, fun _ => by ring⟩
  · exact ⟨fun _ => trivial, fun _ => by ring⟩
  · exact ⟨fun h => absurd (by linear_combination (2 : ℂ) * h) hU0,
      fun h => absurd h (by norm_num)⟩

/-- **The ground submodule at `N = 0` is the singly-occupied diagonal eigenspace.** With `T = 0`
the kinetic term vanishes, so `symmetricRepulsiveHubbardHamiltonian 0 T U` reduces to the diagonal
matrix `Matrix.diagonal (symmetricRepulsiveInteractionDiag 0 U)`, whose two singly-occupied
configurations carry the value `−U₀/4` and the other two carry `+U₀/4` (`U₀ := U 0 > 0`, distinct
values); consequently the `E₀ := −U₀/4` eigenspace of the Hamiltonian coincides with the
`1`-eigenspace of the total number operator, so the ground submodule
(`hubbardGroundSubmoduleAtElectronNumber … E₀ 1`, the `⊓` of the two) equals that single
eigenspace. -/
theorem liebRepulsive_groundSubmodule_N0_eq_numberEigenspace
    {T : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ} (hT0 : T = 0) {U : Fin (0 + 1) → ℝ}
    (hU_pos : ∀ x, 0 < U x) :
    hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian 0 T U)
        (-(U 0 : ℂ) / 4) 1
      = Module.End.eigenspace (fermionTotalNumber (2 * 0 + 1)).mulVecLin (1 : ℂ) := by
  have hH := symmetricRepulsiveHubbardHamiltonian_zero_eq_diagonal hT0 U
  have hN := fermionTotalNumber_eq_diagonal 0
  ext v
  simp only [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf, hH, hN, Nat.cast_one,
    mem_eigenspace_diagonal_mulVecLin_iff]
  refine ⟨fun h => h.2, fun h => ⟨fun i hi => h i ?_, h⟩⟩
  intro hcontra
  exact hi ((symmetricRepulsiveInteractionDiag_zero_eq_iff (hU_pos 0) i).mpr
    ((numberDiag_zero_eq_one_iff i).mp hcontra))

/-- **Fiber count at `N = 0`.** The two singly-occupied configurations of the single-site,
two-orbital (up/down) Fock space form a fiber of size exactly `2` under the total-number
constraint `∑ j, (c j).val = 1` (cast through `ℂ`); demoted to `ℕ` and counted by
`decide`. -/
theorem liebRepulsive_singlyOccupied_card_eq_two :
    Nat.card {c : Fin (2 * 0 + 2) → Fin 2 // ∑ j, ((c j).val : ℂ) = 1} = 2 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight numberDiag_zero_eq_one_iff),
    Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide

/-! ### The Casimir eigenvalue on the singly-occupied sector -/

/-- The single-site spin-`z` diagonal entry, evaluated: `½(c↑ − c↓)`. -/
private theorem spinZDiag_zero_apply (c : Fin (2 * 0 + 2) → Fin 2) :
    (1 / 2 : ℂ) * ((∑ x : Fin (0 + 1), ((c (spinfulIndex 0 x 0)).val : ℂ))
        - ∑ x : Fin (0 + 1), ((c (spinfulIndex 0 x 1)).val : ℂ))
      = (1 / 2 : ℂ) * (((c 0).val : ℂ) - ((c 1).val : ℂ)) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    add_zero, spinfulIndex_zero_eq.1, spinfulIndex_zero_eq.2]

/-- The Casimir acts by `3/4` on the spin-up singly-occupied basis vector (the `N = 0` instance of
`fermionTotalSpinSquared_mulVec_allUpState`, `S_max = 1/2`). -/
private theorem fermionTotalSpinSquared_zero_mulVec_upConfig :
    (fermionTotalSpinSquared 0).mulVec (basisVec singleSiteUpConfig)
      = (3 / 4 : ℂ) • basisVec singleSiteUpConfig := by
  have h := fermionTotalSpinSquared_mulVec_allUpState 0
  rw [hubbardAllUpState_zero] at h
  rw [h]
  congr 1
  norm_num

/-- A vector supported on the two singly-occupied single-site configurations is the corresponding
combination of their basis vectors. -/
private theorem eq_combination_of_singlyOccupied_support
    {v : (Fin (2 * 0 + 2) → Fin 2) → ℂ}
    (hv : ∀ c, c ≠ singleSiteUpConfig → c ≠ singleSiteDownConfig → v c = 0) :
    v = v singleSiteUpConfig • basisVec singleSiteUpConfig
      + v singleSiteDownConfig • basisVec singleSiteDownConfig := by
  funext c
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h1 : c = singleSiteUpConfig
  · rw [h1, basisVec_self, basisVec_of_ne singleSiteUpConfig_ne_downConfig, mul_one, mul_zero,
      add_zero]
  · by_cases h2 : c = singleSiteDownConfig
    · rw [h2, basisVec_self, basisVec_of_ne (Ne.symm singleSiteUpConfig_ne_downConfig), mul_one,
        mul_zero, zero_add]
    · rw [hv c h1 h2, basisVec_of_ne h1, basisVec_of_ne h2, mul_zero, mul_zero, add_zero]

/-- The Casimir acts by `3/4` on the spin-down singly-occupied basis vector. The companion is
produced by `liebRepulsive_su2_weight_transport` at `N = 0` from the all-up seed (`Jr = 1/2`,
`m₀ = 1/2`, `k = 1`, with the trivial Hamiltonian `T = 0`, `U = 0`, whose eigenvalue plays no role);
its weight `−1/2` confines it to the single configuration `singleSiteDownConfig`, so the Casimir
eigenvalue transfers to that basis vector. -/
private theorem fermionTotalSpinSquared_zero_mulVec_downConfig :
    (fermionTotalSpinSquared 0).mulVec (basisVec singleSiteDownConfig)
      = (3 / 4 : ℂ) • basisVec singleSiteDownConfig := by
  have hNdiag := fermionTotalNumber_eq_diagonal 0
  have hS3diag := fermionTotalSpinZ_eq_diagonal 0
  have hHdiag : symmetricRepulsiveHubbardHamiltonian 0 (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ)
      (fun _ => (0 : ℝ)) = Matrix.diagonal (symmetricRepulsiveInteractionDiag 0 (fun _ => 0)) :=
    symmetricRepulsiveHubbardHamiltonian_zero_eq_diagonal rfl _
  have hup_ne : (basisVec singleSiteUpConfig : (Fin (2 * 0 + 2) → Fin 2) → ℂ) ≠ 0 := by
    intro hzero
    have hone := congrFun hzero singleSiteUpConfig
    rw [basisVec_self] at hone
    exact one_ne_zero hone
  have hseedSq : (fermionTotalSpinSquared 0).mulVec (basisVec singleSiteUpConfig)
      = (((1 / 2 * (1 / 2 + 1) : ℝ)) : ℂ) • basisVec singleSiteUpConfig := by
    rw [fermionTotalSpinSquared_zero_mulVec_upConfig]
    congr 1
    norm_num
  have hseed3 : (fermionTotalSpinZ 0).mulVec (basisVec singleSiteUpConfig)
      = ((1 / 2 : ℝ) : ℂ) • basisVec singleSiteUpConfig := by
    have h := fermionTotalSpinZ_mulVec_allUpState 0
    rw [hubbardAllUpState_zero] at h
    rw [h]
    congr 1
    push_cast
    norm_num
  have hseedH : (symmetricRepulsiveHubbardHamiltonian 0
        (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ) (fun _ => (0 : ℝ))).mulVec
        (basisVec singleSiteUpConfig) = (0 : ℂ) • basisVec singleSiteUpConfig := by
    rw [hHdiag, diagonal_mulVec_basisVec, symmetricRepulsiveInteractionDiag_zero_apply]
    norm_num
  have hseedN : (fermionTotalNumber (2 * 0 + 1)).mulVec (basisVec singleSiteUpConfig)
      = (1 : ℂ) • basisVec singleSiteUpConfig := by
    rw [hNdiag, diagonal_mulVec_basisVec, ← Nat.cast_sum, Fin.sum_univ_two,
      singleSiteConfig_val.1, singleSiteConfig_val.2.1]
    norm_num
  obtain ⟨Ψ, hΨne, hΨsq, hΨ3, -, hΨN⟩ :=
    liebRepulsive_su2_weight_transport (N := 0) (0 : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ)
      (fun _ _ => rfl) (fun _ => (0 : ℝ)) (Jr := 1 / 2) (m₀ := 1 / 2) (E := 0) (Ne := 1)
      (by rw [ne_eq, WithLp.toLp_eq_zero]; exact hup_ne) (by norm_num)
      ((mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hseedSq)
      ((mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hseed3)
      ((mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hseedH)
      ((mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul _ _ _).mp hseedN)
      1 (by norm_num)
  obtain ⟨w, rfl⟩ : ∃ w : (Fin (2 * 0 + 2) → Fin 2) → ℂ, Ψ = WithLp.toLp 2 w :=
    ⟨WithLp.ofLp Ψ, rfl⟩
  rw [← mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul] at hΨsq hΨ3 hΨN
  rw [ne_eq, WithLp.toLp_eq_zero] at hΨne
  have hsupp : ∀ c, c ≠ singleSiteUpConfig → c ≠ singleSiteDownConfig → w c = 0 := by
    intro c h1 h2
    have hmem : w ∈ Module.End.eigenspace (fermionTotalNumber (2 * 0 + 1)).mulVecLin (1 : ℂ) := by
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact hΨN
    rw [hNdiag, mem_eigenspace_diagonal_mulVecLin_iff] at hmem
    exact hmem c fun hc => ((numberDiag_zero_eq_one_iff c).mp hc).elim h1 h2
  have hwup : w singleSiteUpConfig = 0 := by
    have hmem : w ∈ Module.End.eigenspace (fermionTotalSpinZ 0).mulVecLin
        (((1 / 2 - (1 : ℕ) : ℝ) : ℂ)) := by
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact hΨ3
    rw [hS3diag, mem_eigenspace_diagonal_mulVecLin_iff] at hmem
    refine hmem singleSiteUpConfig ?_
    rw [spinZDiag_zero_apply, singleSiteConfig_val.1, singleSiteConfig_val.2.1]
    push_cast
    norm_num
  have hdec := eq_combination_of_singlyOccupied_support hsupp
  rw [hwup, zero_smul, zero_add] at hdec
  have hwdown : w singleSiteDownConfig ≠ 0 := by
    intro hzero
    exact hΨne (by rw [hdec, hzero, zero_smul])
  rw [show (((1 / 2 * (1 / 2 + 1) : ℝ)) : ℂ) = (3 / 4 : ℂ) by norm_num, hdec,
    Matrix.mulVec_smul] at hΨsq
  refine (smul_right_inj hwdown).mp ?_
  rw [hΨsq, smul_comm]

/-- Every vector of the singly-occupied number eigenspace at `N = 0` carries Casimir eigenvalue
`3/4`: it is a combination of the two singly-occupied basis vectors, on each of which the Casimir
acts by `3/4`. -/
private theorem fermionTotalSpinSquared_zero_mulVec_of_mem
    {v : (Fin (2 * 0 + 2) → Fin 2) → ℂ}
    (hv : v ∈ Module.End.eigenspace (fermionTotalNumber (2 * 0 + 1)).mulVecLin (1 : ℂ)) :
    (fermionTotalSpinSquared 0).mulVec v = (3 / 4 : ℂ) • v := by
  rw [fermionTotalNumber_eq_diagonal 0, mem_eigenspace_diagonal_mulVecLin_iff] at hv
  have hsupp : ∀ c, c ≠ singleSiteUpConfig → c ≠ singleSiteDownConfig → v c = 0 :=
    fun c h1 h2 => hv c fun hc => ((numberDiag_zero_eq_one_iff c).mp hc).elim h1 h2
  have hdec := eq_combination_of_singlyOccupied_support hsupp
  calc (fermionTotalSpinSquared 0).mulVec v
      = (fermionTotalSpinSquared 0).mulVec (v singleSiteUpConfig • basisVec singleSiteUpConfig
          + v singleSiteDownConfig • basisVec singleSiteDownConfig) := by rw [← hdec]
    _ = (3 / 4 : ℂ) • (v singleSiteUpConfig • basisVec singleSiteUpConfig
          + v singleSiteDownConfig • basisVec singleSiteDownConfig) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
          fermionTotalSpinSquared_zero_mulVec_upConfig,
          fermionTotalSpinSquared_zero_mulVec_downConfig]
        module
    _ = (3 / 4 : ℂ) • v := by rw [← hdec]

/-- **The `N = 0` block.** The four Theorem 10.4 conjuncts for
`symmetricRepulsiveHubbardHamiltonian 0 T U`, `T = 0`, ground energy `E₀ = −U₀/4`: the ground
submodule is nonzero (conjunct (i)), the energy `E₀` is (uniquely) minimal — an equality, not an
inequality, since the ground submodule equals a single Hamiltonian eigenspace at `N = 0` (conjunct
(ii)), every element carries Casimir eigenvalue `3/4 = liebRepulsiveSpinCasimir A` for the unique
bipartition `A` of a one-point set (conjunct (iii), witnessed on the two spanning basis vectors via
`fermionTotalSpinSquared_mulVec_allUpState` and `liebRepulsive_su2_weight_transport`), and the
`finrank` is `2 = liebRepulsiveGroundMultiplicity A` (conjunct (iv), via
`finrank_eigenspace_diagonal_mulVecLin` and the fiber count above). -/
theorem liebRepulsive_symmetric_halfFilling_degenerate {A : Finset (Fin (N + 1))}
    (hdeg : A.card = 0 ∨ (bipartitionComplement A).card = 0)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hbip : HoppingRespectsBipartition A T) (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ E₀ : ℂ,
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥ ∧
      (∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ →
        E₀.re ≤ E.re) ∧
      (∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
        (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) ∧
      Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
        = liebRepulsiveGroundMultiplicity A := by
  have hT0 : T = 0 := liebRepulsive_hopping_eq_zero_of_degenerate hbip hdeg
  have hN0 : N = 0 := liebRepulsive_degenerate_N_eq_zero hT_conn hT0
  subst hN0
  have hG := liebRepulsive_groundSubmodule_N0_eq_numberEigenspace hT0 hU_pos
  have h4 : Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 0 T U) (-(U 0 : ℂ) / 4) 1) = 2 := by
    rw [hG, fermionTotalNumber_eq_diagonal 0, finrank_eigenspace_diagonal_mulVecLin]
    exact liebRepulsive_singlyOccupied_card_eq_two
  have h1 : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 0 T U) (-(U 0 : ℂ) / 4) 1 ≠ ⊥ := by
    intro hbot
    rw [hbot, finrank_bot] at h4
    exact absurd h4 (by norm_num)
  have h2 : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 0 T U) E 1 ≠ ⊥ → (-(U 0 : ℂ) / 4).re ≤ E.re := by
    intro E hE
    obtain ⟨v, hv, hvne⟩ := (Submodule.ne_bot_iff _).mp hE
    rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
      Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, Nat.cast_one] at hv
    have hv0 : v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian 0 T U) (-(U 0 : ℂ) / 4) 1 := by
      rw [hG]
      exact hv.2
    rw [hubbardGroundSubmoduleAtElectronNumber, Submodule.mem_inf,
      Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv0
    have hEeq : E = -(U 0 : ℂ) / 4 := by
      by_contra hne
      refine hvne ?_
      have hsub : (E - -(U 0 : ℂ) / 4) • v = 0 := by
        rw [sub_smul, ← hv.1, ← hv0.1, sub_self]
      exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
    rw [hEeq]
  have h3 : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 0 T U) (-(U 0 : ℂ) / 4) 1,
      (fermionTotalSpinSquared 0).mulVec v = (3 / 4 : ℂ) • v := by
    intro v hv
    rw [hG] at hv
    exact fermionTotalSpinSquared_zero_mulVec_of_mem hv
  have hcas : liebRepulsiveSpinCasimir A = 3 / 4 := by
    rw [liebRepulsiveSpinCasimir, liebRepulsive_degenerate_sublatticeImbalance_eq_one]
    norm_num
  have hmult : liebRepulsiveGroundMultiplicity A = 2 := by
    rw [liebRepulsiveGroundMultiplicity, liebRepulsive_degenerate_sublatticeImbalance_eq_one]
  exact ⟨-(U 0 : ℂ) / 4, h1, h2, by rw [hcas]; exact h3, by rw [hmult]; exact h4⟩

/-! ## The all-`A` symmetric-form theorem -/

/-- **The symmetric-form Theorem 10.4, for every bipartition `A`.** Combines
`liebRepulsive_symmetric_halfFilling_conditional` (`LiebRepulsiveWeightConfinement.lean`, the
`1 ≤ |A|` and `1 ≤ |B|` case) with the degenerate case above (`|A| = 0 ∨ |B| = 0`), by cases on
whether both sublattices are nonempty. Reference-0 within this PR; consumed by PR-15c's capstone. -/
theorem liebRepulsive_symmetric_halfFilling (N : ℕ) {A : Finset (Fin (N + 1))}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT_symm : ∀ x y, T x y = T y x)
    (hbip : HoppingRespectsBipartition A T) (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) :
    ∃ E₀ : ℂ,
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥ ∧
      (∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ →
        E₀.re ≤ E.re) ∧
      (∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
        (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) ∧
      Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
        = liebRepulsiveGroundMultiplicity A := by
  by_cases hA : 1 ≤ A.card
  · by_cases hB : 1 ≤ (bipartitionComplement A).card
    · exact liebRepulsive_symmetric_halfFilling_conditional N hA hB T hT_symm hbip hT_conn U hU_pos
    · exact liebRepulsive_symmetric_halfFilling_degenerate (Or.inr (by omega)) T hbip hT_conn U
        hU_pos
  · exact liebRepulsive_symmetric_halfFilling_degenerate (Or.inl (by omega)) T hbip hT_conn U
      hU_pos

/-! ## Uniform-disjunct transport -/

/-- **Uniform-disjunct transport.** Converts the all-`A` symmetric-form conjuncts at a constant
family `U` to the uniform-interaction Hamiltonian `repulsiveHubbardHamiltonian`, via the
ground-submodule equality `symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform`
(`LiebRepulsiveBalancedGround.lean:363`, an energy shift `E ↦ E − c` at
`c = −(U/4)(N + 1)` on the `Ne = N + 1` sector). Reference-0 within this PR; consumed by PR-15c's
capstone. -/
theorem liebRepulsive_uniform_of_symmetric (N : ℕ) {A : Finset (Fin (N + 1))}
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : ℝ)
    (h : ∃ E₀ : ℂ,
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)) E₀ (N + 1) ≠ ⊥ ∧
      (∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)) E (N + 1) ≠ ⊥ →
        E₀.re ≤ E.re) ∧
      (∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)) E₀ (N + 1),
        (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) ∧
      Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)) E₀ (N + 1))
        = liebRepulsiveGroundMultiplicity A) :
    ∃ E₀ : ℂ,
      hubbardGroundSubmoduleAtElectronNumber
          (repulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥ ∧
      (∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (repulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ →
        E₀.re ≤ E.re) ∧
      (∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
          (repulsiveHubbardHamiltonian N T U) E₀ (N + 1),
        (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) ∧
      Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
          (repulsiveHubbardHamiltonian N T U) E₀ (N + 1))
        = liebRepulsiveGroundMultiplicity A := by
  obtain ⟨E₀, hne, hmin, hcas, hrank⟩ := h
  have key : ∀ E : ℂ,
      hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)) E (N + 1)
        = hubbardGroundSubmoduleAtElectronNumber (repulsiveHubbardHamiltonian N T U)
            (E - (-(U : ℂ) / 2 * ((N + 1 : ℕ) : ℂ) + (U : ℂ) / 4 * ((N : ℂ) + 1))) (N + 1) :=
    fun E => symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform N T U (N + 1) E
  refine ⟨E₀ - (-(U : ℂ) / 2 * ((N + 1 : ℕ) : ℂ) + (U : ℂ) / 4 * ((N : ℂ) + 1)), ?_, ?_, ?_, ?_⟩
  · rw [← key]
    exact hne
  · intro E hE
    have hshift : hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U))
        (E + (-(U : ℂ) / 2 * ((N + 1 : ℕ) : ℂ) + (U : ℂ) / 4 * ((N : ℂ) + 1))) (N + 1) ≠ ⊥ := by
      rw [key, add_sub_cancel_right]
      exact hE
    have hle := hmin _ hshift
    simp only [Complex.sub_re, Complex.add_re] at hle ⊢
    linarith
  · rw [← key]
    exact hcas
  · rw [← key]
    exact hrank

/-! ## Theorem 10.4 capstone assembly -/

/-- **Tasaki Theorem 10.4** (Lieb's theorem for the repulsive Hubbard model at half-filling, 1st
ed., Springer 2020, §10.2.2, p. 350). For a bipartite real symmetric connected hopping matrix `T`
and a repulsive Hubbard Hamiltonian `H` (uniform or symmetric form), at half-filling `N = |Λ|`
(electron number `N + 1` on `Fin (N + 1)` sites), there is a ground energy `E₀` whose
`(N+1)`-electron ground subspace `G` is nonzero, minimal in energy, consists entirely of
total-spin `S₀ = ||A| − |B||/2` states (Casimir eigenvalue `S₀(S₀+1)`), and has dimension exactly
`|A| − |B| + 1` (the unavoidable SU(2) multiplet degeneracy). Assembled from
`liebRepulsive_symmetric_halfFilling` (the symmetric disjunct) and
`liebRepulsive_uniform_of_symmetric` (transporting the symmetric-form conjuncts at a constant `U`
to the uniform disjunct). -/
theorem theorem_10_4_lieb_repulsive_half_filling
    (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2)))
    (hModel : IsLiebRepulsiveModel A T H) :
    ∃ E₀ : ℂ,
      hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1) ≠ ⊥ ∧
      (∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber H E (N + 1) ≠ ⊥ →
        E₀.re ≤ E.re) ∧
      (∀ v ∈ hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1),
        (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v) ∧
      Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1))
        = liebRepulsiveGroundMultiplicity A := by
  obtain ⟨hsymm, hbip, hconn, hham⟩ := hModel
  rcases hham with ⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩
  · exact liebRepulsive_uniform_of_symmetric (A := A) N T U
      (liebRepulsive_symmetric_halfFilling N T hsymm hbip hconn (fun _ => U) (fun _ => hU))
  · exact liebRepulsive_symmetric_halfFilling N T hsymm hbip hconn U hU

end LatticeSystem.Fermion
