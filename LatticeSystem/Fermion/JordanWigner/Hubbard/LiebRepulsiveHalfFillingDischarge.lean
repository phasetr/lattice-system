import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveWeightConfinement
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveBalancedGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveMultipletCompanion
import LatticeSystem.Fermion.JordanWigner.Hubbard.SaturatedFerromagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaInteraction
import LatticeSystem.Math.MatrixAnalysis.PiDiagonalEigenspace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Theorem 10.4 discharge: degenerate sublattice + uniform-disjunct assembly (PR-15b)

Assembly layer for the Theorem 10.4 (Lieb repulsive Hubbard half-filling) discharge arc
(issue #5320, PR-15b). Covers the two pieces `liebRepulsive_symmetric_halfFilling_conditional`
(`LiebRepulsiveWeightConfinement.lean:497`, requiring `1 ≤ |A|` and `1 ≤ |B|`) does not:

* the **degenerate case** `|A| = 0 ∨ |B| = 0`, which forces the hopping matrix `T` to vanish and,
  via connectedness of the (now edgeless) hopping support graph, forces `N = 0` — a single-site
  model whose ground submodule is a single diagonal eigenspace, handled directly;
* the **uniform-disjunct transport**, converting the symmetric-form conjuncts at a constant `U` to
  the uniform-interaction Hamiltonian `repulsiveHubbardHamiltonian`, via
  `symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform`
  (`LiebRepulsiveBalancedGround.lean:363`).

This file does **not** touch `axiom theorem_10_4_lieb_repulsive_half_filling`
(`LiebRepulsive.lean:134`); assembling the two disjuncts into the axiom's exact statement and moving
it out of `LiebRepulsive.lean` is PR-15c's responsibility.

## Main results

* `liebRepulsive_hopping_eq_zero_of_degenerate` — `|A| = 0 ∨ |B| = 0` forces `T = 0`.
* `liebRepulsive_degenerate_N_eq_zero` — a connected hopping support graph on a vanishing `T`
  forces `N = 0`.
* `liebRepulsive_degenerate_sublatticeImbalance_eq_one` — at `N = 0`, `sublatticeImbalance A = 1`
  for every bipartition `A`.
* `liebRepulsive_symmetric_halfFilling_degenerate` — the four Theorem 10.4 conjuncts for
  `symmetricRepulsiveHubbardHamiltonian` in the degenerate case `|A| = 0 ∨ |B| = 0`.
* `liebRepulsive_symmetric_halfFilling` — the four Theorem 10.4 conjuncts for
  `symmetricRepulsiveHubbardHamiltonian`, for **every** bipartition `A` (no `1 ≤ |A|`/`1 ≤ |B|`
  hypothesis), combining the conditional capstone with the degenerate case above.
* `liebRepulsive_uniform_of_symmetric` — transports the symmetric-form conjuncts at a constant `U`
  to the uniform-interaction Hamiltonian `repulsiveHubbardHamiltonian`.

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
theorem liebRepulsive_hopping_eq_zero_of_A_card_eq_zero {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (hA : A.card = 0) : T = 0 := by
  sorry

/-- If the complement sublattice `B = Aᶜ` is empty, `HoppingRespectsBipartition` forces `T = 0`
(every entry is forced zero, since `x ∈ A` is vacuously true for every `x`). -/
theorem liebRepulsive_hopping_eq_zero_of_B_card_eq_zero {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (hB : (bipartitionComplement A).card = 0) : T = 0 := by
  sorry

/-- **Degenerate hopping vanishing.** `|A| = 0 ∨ |B| = 0` forces `T = 0`, combining the two
one-sided collapses above. -/
theorem liebRepulsive_hopping_eq_zero_of_degenerate {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    (hdeg : A.card = 0 ∨ (bipartitionComplement A).card = 0) : T = 0 := by
  sorry

/-- **The degenerate case forces `N = 0`.** A vanishing hopping matrix has an edgeless support
graph (`hoppingSupportGraph T = ⊥`); if that graph is `Preconnected`, the vertex type `Fin (N + 1)`
is a subsingleton (`SimpleGraph.preconnected_bot_iff_subsingleton`), forcing `N = 0`. -/
theorem liebRepulsive_degenerate_N_eq_zero {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT_conn : (hoppingSupportGraph T).Preconnected) (hT0 : T = 0) : N = 0 := by
  sorry

/-- **Sublattice imbalance is `1` at `N = 0`.** With a single site, every bipartition `A` has
`|A| + |B| = 1`, hence `||A| − |B|| = 1` regardless of which of `A`, `B` is empty. -/
theorem liebRepulsive_degenerate_sublatticeImbalance_eq_one {A : Finset (Fin (0 + 1))} :
    sublatticeImbalance A = 1 := by
  sorry

/-! ## The `N = 0` case: a single diagonal eigenspace -/

/-- **The ground submodule at `N = 0` is the singly-occupied diagonal eigenspace.** With `T = 0`
the kinetic term vanishes, so `symmetricRepulsiveHubbardHamiltonian 0 T U` reduces to the diagonal
matrix `Matrix.diagonal (symmetricRepulsiveInteractionDiag 0 U)`, whose two singly-occupied
configurations carry the value `−U₀/4` and the other two carry `+U₀/4` (`U₀ := U 0 > 0`, distinct
values); consequently the `E₀ := −U₀/4` eigenspace of the Hamiltonian coincides with the
`1`-eigenspace of the total number operator, so the ground submodule
(`hubbardGroundSubmoduleAtElectronNumber … E₀ 1`, the `⊓` of the two) equals that single
eigenspace. -/
theorem liebRepulsive_groundSubmodule_N0_eq_numberEigenspace (T : Matrix (Fin 1) (Fin 1) ℝ)
    (hT0 : T = 0) (U : Fin 1 → ℝ) (hU_pos : ∀ x, 0 < U x) :
    hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian 0 T U)
        (-(U 0 : ℂ) / 4) 1
      = Module.End.eigenspace (fermionTotalNumber 1).mulVecLin (1 : ℂ) := by
  sorry

/-- **Fiber count at `N = 0`.** The two singly-occupied configurations of the single-site,
two-orbital (up/down) Fock space form a fiber of size exactly `2` under the total-number
constraint `∑ j, (c j).val = 1` (cast through `ℂ`); demoted to `ℕ` and counted via
`piFinTwoEquiv`. -/
theorem liebRepulsive_singlyOccupied_card_eq_two :
    Nat.card {c : Fin 2 → Fin 2 // ∑ j, ((c j).val : ℂ) = 1} = 2 := by
  sorry

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
  sorry

/-! ## The all-`A` symmetric-form theorem -/

/-- **The symmetric-form Theorem 10.4, for every bipartition `A`.** Combines
`liebRepulsive_symmetric_halfFilling_conditional` (`LiebRepulsiveWeightConfinement.lean:497`, the
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
  sorry

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
  sorry

end LatticeSystem.Fermion
