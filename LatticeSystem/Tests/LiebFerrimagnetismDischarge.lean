import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismDischarge

/-!
# §10.2.3 Theorem 10.6 — universal assembly and axiom discharge (specification)

(Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020,
§10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).)

Specification suite for the not-yet-existing
`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebFerrimagnetismDischarge.lean` (PR-8, the final PR
of the Theorem 10.6 discharge arc, issue #5347), per the confirmed design
(`.self-local/docs/theorem-10-6-pr8-design.md`, 2026-08-24, layers C/D/E). The `example`s pin down
the exact signatures of the five **public** declarations: the tower ratio-transport equality (`C1`)
and its `S₀² ≤ …` corollary (`C2`), the universal ground-vector bound (`D2`), the assembled
symmetric-form bound (`E2`), and the capstone (`E3`, `theorem_10_6_lieb_ferrimagnetism`, now a
`theorem`, byte-identical signature to the axiom it replaces in `LiebFerrimagnetism.lean`). The
`private` declarations `B1` (`liebRepulsive_groundEnergy_eq_of_min`), `B2`
(`liebFerrimagnetism_symmetric_data`), `D1`
(`vectorExpectation_diagonal_of_crossTerm_zero`) and `E1` (`liebFerrimagnetism_N_zero`) are not
pinned here (repo convention: only public declarations get a `Tests/` pin, mirrored from
`Tests/LiebFerrimagnetismCenteredBound.lean`'s treatment of `D0`/`D2`/`D5`/`D6`).

This whole file is Red until `LiebFerrimagnetismDischarge.lean` is created: the import itself does
not resolve, and the theorem's *own compilability* is exactly the arc's acceptance condition
(`#print axioms LatticeSystem.Fermion.theorem_10_6_lieb_ferrimagnetism` = `[propext,
Classical.choice, Quot.sound]`, no `theorem_10_6_lieb_ferrimagnetism` axiom).

Notation: `L := sublatticeImbalance A`, `S₀ := (L : ℝ)/2`, `k₀ := L / 2` (ℕ division),
`γ₀ := liebRepulsiveSpinCasimir A`, `Ô² := fermionStaggeredCasimirOp N A`,
`w_k := ((fermionTotalSpinMinus N) ^ k).mulVec w`,
`G := hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1)`.
-/

namespace LatticeSystem.Tests.LiebFerrimagnetismDischarge

open Matrix Module LatticeSystem.Fermion LatticeSystem.Quantum

/-! ## `C1` — the tower ratio-transport equality -/

/-- **`C1`: the real expectation ratio of `Ô²` is the same on every tower member `w_k` as on the
highest-weight vector `w` itself**, `k` ranging over `0, …, L`. Needs Theorem 10.4's Casimir
conclusion `hcas` and the ground-membership/top-weight data (`hw0`, `hwG`, `hz`) but, unlike `D2`,
no hopping symmetry `hT` — the induction consumes only `liebRepulsive_ground_tower_ne_zero`
(no `hT`) and the generic ladder-ratio invariance
`fermionSpinMinus_expectationRatioRe_invariant`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    ∀ k : ℕ, k ≤ sublatticeImbalance A →
      (vectorExpectation (fermionStaggeredCasimirOp N A)
          (((fermionTotalSpinMinus N) ^ k).mulVec w)).re /
        (star (((fermionTotalSpinMinus N) ^ k).mulVec w) ⬝ᵥ
            ((fermionTotalSpinMinus N) ^ k).mulVec w).re
      = (vectorExpectation (fermionStaggeredCasimirOp N A) w).re / (star w ⬝ᵥ w).re :=
  liebFerrimagnetism_tower_ratioRe_eq N A T U E₀ (hcas := hcas) (hw0 := hw0) (hwG := hwG)
    (hz := hz)

/-! ## `C2` — the tower `S₀² ≤ …` bound -/

/-- **`C2`: every tower member `w_k` satisfies `S₀² ≤ ⟨Ô²⟩.re / ‖w_k‖²`**, `k` ranging over
`0, …, L`. `C1` chained at `k₀ = L/2` (legal since `k₀ ≤ L`) with the PR-7 centered-sector bound
`liebRepulsive_centered_ratioRe_ge_sq` (weakest-hypothesis form `D7`), whose sign pattern `hsign` on
the centered member `w_{k₀}` is the sole extra hypothesis over `C1`. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (hsign : ∀ x y : Fin (N + 1),
      (vectorExpectation (fermionSpinTransverse N x y)
          (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).im = 0 ∧
        (SameSublattice A x y →
            0 < (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re) ∧
          (¬ SameSublattice A x y →
            (vectorExpectation (fermionSpinTransverse N x y)
              (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re < 0)) :
    ∀ k : ℕ, k ≤ sublatticeImbalance A →
      ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
        (vectorExpectation (fermionStaggeredCasimirOp N A)
            (((fermionTotalSpinMinus N) ^ k).mulVec w)).re /
          (star (((fermionTotalSpinMinus N) ^ k).mulVec w) ⬝ᵥ
              ((fermionTotalSpinMinus N) ^ k).mulVec w).re :=
  liebFerrimagnetism_tower_ratioRe_ge_sq N A T U E₀ (hcas := hcas) (hw0 := hw0) (hwG := hwG)
    (hz := hz) (hsign := hsign)

/-! ## `D2` — the universal ground-vector bound -/

/-- **`D2`: every unit-norm ground vector `v ∈ G` (not just the highest-weight tower members)
satisfies `S₀² ≤ ⟨Ô²⟩.re`.** Unlike `C1`/`C2`, needs the hopping symmetry `hT` (consumed by
`liebRepulsive_ground_eq_span_tower`'s span identity) and Theorem 10.4's dimension count `hrank`,
plus the tower bound `hratio` (`C2`'s conclusion) to expand `v` in the tower basis and bound each
diagonal term. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    (hrank : Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
      = liebRepulsiveGroundMultiplicity A)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (hratio : ∀ k : ℕ, k ≤ sublatticeImbalance A →
      ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
        (vectorExpectation (fermionStaggeredCasimirOp N A)
            (((fermionTotalSpinMinus N) ^ k).mulVec w)).re /
          (star (((fermionTotalSpinMinus N) ^ k).mulVec w) ⬝ᵥ
              ((fermionTotalSpinMinus N) ^ k).mulVec w).re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hnorm : star v ⬝ᵥ v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re :=
  liebFerrimagnetism_bound_of_mem_ground N A T hT U E₀ (hcas := hcas) (hrank := hrank)
    (hw0 := hw0) (hwG := hwG) (hz := hz) (hratio := hratio) (v := v) (hv := hv) (hnorm := hnorm)

/-! ## `E2` — the assembled symmetric-form bound -/

/-- **`E2`: for the symmetric-form repulsive Hubbard model, every unit-norm ground vector `v`
satisfies `S₀² ≤ ⟨Ô²⟩.re`.** Assembles Theorem 10.4 (`hbip`, `hT_conn`, `hU`, `hGS_ne`, `hMin` give
`hcas`/`hrank`) with the `N = 0`/`N ≥ 1` split (`E1` vs. `D2`); no explicit `1 ≤ N` hypothesis
appears since the split is internal. -/
example (N : ℕ) (A : Finset (Fin (N + 1))) (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT : ∀ i j, T i j = T j i) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x) (E₀ : ℂ)
    (hGS_ne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hMin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hnorm : star v ⬝ᵥ v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re :=
  liebFerrimagnetism_symmetric N A T hT hbip hT_conn U hU E₀ (hGS_ne := hGS_ne) (hMin := hMin)
    (v := v) (hv := hv) (hnorm := hnorm)

/-! ## `E3` — the capstone: `theorem_10_6_lieb_ferrimagnetism`, axiom-free -/

/-- **`E3`: the capstone, byte-identical in signature to the deleted axiom of
`LiebFerrimagnetism.lean`.** Under the packaged Theorem 10.4/10.5 hypotheses
`IsLiebRepulsiveModel`, every normalized ground state `v` satisfies the ferrimagnetic bound
`S₀² ≤ ⟨(Ô_L)²⟩.re`. This pin is the arc's acceptance condition made executable: it fails to
compile until `LiebFerrimagnetismDischarge.lean` provides `theorem_10_6_lieb_ferrimagnetism` as a
`theorem` (not an `axiom`). -/
example {N : ℕ} (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2)))
    (hModel : IsLiebRepulsiveModel A T H)
    (E₀ : ℂ)
    (hGS_ne : hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1) ≠ ⊥)
    (hMin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber H E (N + 1) ≠ ⊥ →
      E₀.re ≤ E.re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1))
    (hnorm : dotProduct (star v) v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re :=
  theorem_10_6_lieb_ferrimagnetism A T H hModel E₀ (hGS_ne := hGS_ne) (hMin := hMin) (v := v)
    (hv := hv) (hnorm := hnorm)

end LatticeSystem.Tests.LiebFerrimagnetismDischarge
