import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveHomotopyContinuity
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveSU2Invariance

/-!
# Symmetric-form homotopy and `casimirSelector` constancy (Tasaki §10.2.2, PR-12b)

Sixteenth installment of the Theorem 10.4 discharge arc (issue #5320). PR-4
(`LiebRepulsiveHomotopyContinuity.lean`) built the homotopy `H_s` and its topological core
(`continuous_homotopyHamiltonian`, `casimirSelector_eq_const_of_locally_unique_strict_min`) for the
**uniform** repulsive Hubbard Hamiltonian only (scalar on-site coupling `U : ℝ`), leaving the
site-dependent symmetric form (Tasaki eq. (10.2.6), `U : Fin (N+1) → ℝ`) unreduced. PR-12a
(`LiebRepulsiveSU2Invariance.lean`) supplied `symmetricRepulsiveHubbardHamiltonian`'s `SU(2)`
adapters and its unconditional per-`s` existence-uniqueness capstone.

This file closes the site-dependent gap directly, at fixed site-dependent `U_x`, **without** ever
reducing to the uniform model: the on-site homotopy `U_s(x) := (1-s) U_x + s` is applied
*pointwise*, so PR-1's constant-`U` shift argument (documented as inapplicable to a site-dependent
potential in PR-4's module docstring) is never invoked, and `repulsiveSpinZSector_ground_unique`
(`LiebRepulsiveBalancedGround.lean:107`) — which already takes `U : Fin (N+1) → ℝ` — is applicable
at every `s` with no adapter.

## Main definitions and results

* `homotopyOnSiteFn` — the pointwise lift of PR-4's `homotopyOnSite` to a site-dependent coupling.
* `symmetricHomotopyHamiltonian` — the symmetric-form Hamiltonian homotopy
  `H_s := Ĥ^{rep,sym}(T_s, U_s)`, reusing PR-4's `homotopyHopping`/`liebEndpointHopping` verbatim
  for the hopping side.
* `symmetricHomotopyHamiltonian_zero` — `H_0` is the original symmetric repulsive model.
* `continuous_symmetricHomotopyHamiltonian` /
  `continuous_minEnergyOn_symmetricHomotopyHamiltonian` — continuity of `s ↦ H_s` and of the
  sector-restricted minimum energy along the homotopy.
* `symmetricHomotopy_exists_unique_casimir_sector` — the per-`s` existence-uniqueness instance
  (PR-12a's capstone applied at `T_s`, `U_s`, for every `s ∈ [0, 1]`).
* `symmetricHomotopy_casimirSelector_eq_const` — the assembled capstone: the occupied Casimir
  sector is constant along the whole homotopy, in particular `c 0 = c 1`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, p. 353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators Topology

variable {N : ℕ}

/-! ## The symmetric-form homotopy `T_s`, `U_s(·)`, `H_s` -/

/-- The **pointwise on-site coupling homotopy** `U_s(x) := (1 - s) U_x + s · 1`, the site-dependent
lift of PR-4's `homotopyOnSite` applied independently at each site. -/
def homotopyOnSiteFn (U : Fin (N + 1) → ℝ) (s : ℝ) : Fin (N + 1) → ℝ :=
  fun x => homotopyOnSite (U x) s

/-- The **symmetric-form Hamiltonian homotopy** `H_s`, built from PR-4's hopping homotopy
(`homotopyHopping`/`liebEndpointHopping`, reused verbatim) and the pointwise on-site homotopy
`homotopyOnSiteFn`, via the *symmetric* (site-dependent-`U`) repulsive Hubbard Hamiltonian. -/
noncomputable def symmetricHomotopyHamiltonian (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (lam : ℝ) (s : ℝ) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  symmetricRepulsiveHubbardHamiltonian N (homotopyHopping T (liebEndpointHopping A T lam) s)
    (homotopyOnSiteFn U s)

/-- **Base point**: at `s = 0` the symmetric-form homotopy is the original symmetric repulsive
Hubbard Hamiltonian, since `T_0 = T` and `U_s(x)|_{s=0} = U_x`. -/
theorem symmetricHomotopyHamiltonian_zero (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (lam : ℝ) :
    symmetricHomotopyHamiltonian N A T U lam 0 = symmetricRepulsiveHubbardHamiltonian N T U := by
  have hU : homotopyOnSiteFn U 0 = U := by
    funext x
    simp [homotopyOnSiteFn, homotopyOnSite]
  simp [symmetricHomotopyHamiltonian, homotopyHopping, hU]

/-- **On-site coupling stays positive, pointwise**: `homotopyOnSiteFn U s x` is positive for every
`s ∈ [0, 1]` and every site `x`, whenever `U` is pointwise positive — the site-dependent lift of
PR-4's `homotopyOnSite_pos`. -/
theorem homotopyOnSiteFn_pos {U : Fin (N + 1) → ℝ} (hU : ∀ x, 0 < U x) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) : ∀ x, 0 < homotopyOnSiteFn U s x :=
  fun x => homotopyOnSite_pos (hU x) hs

/-! ## Continuity of the symmetric-form homotopy -/

/-- **Continuity of the symmetric-form Hamiltonian homotopy**: `s ↦ H_s` is continuous, mirroring
`continuous_homotopyHamiltonian` (`LiebRepulsiveHomotopyContinuity.lean:262`) with the on-site term
replaced by the pointwise-affine `homotopyOnSiteFn`. -/
theorem continuous_symmetricHomotopyHamiltonian (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (lam : ℝ) :
    Continuous (fun s : ℝ => symmetricHomotopyHamiltonian N A T U lam s) := by
  have hhop : ∀ x y : Fin (N + 1), Continuous fun s : ℝ =>
      ((homotopyHopping T (liebEndpointHopping A T lam) s x y : ℝ) : ℂ) := by
    intro x y
    simp only [homotopyHopping, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact Complex.continuous_ofReal.comp (by fun_prop)
  have hons : ∀ x : Fin (N + 1), Continuous fun s : ℝ =>
      ((homotopyOnSiteFn U s x : ℝ) : ℂ) := by
    intro x
    simp only [homotopyOnSiteFn, homotopyOnSite]
    exact Complex.continuous_ofReal.comp (by fun_prop)
  simp only [symmetricHomotopyHamiltonian, symmetricRepulsiveHubbardHamiltonian, hubbardKinetic,
    symmetricRepulsiveHubbardInteraction]
  exact Continuous.add
    (continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => (hhop i j).smul continuous_const)
    (continuous_finset_sum _ fun x _ => (hons x).smul continuous_const)

/-- **Continuity of the sector-restricted minimum energy along the symmetric-form homotopy**: for
any fixed occupied Casimir sector `K_c`, `s ↦ minEnergyOn K_c H_s` is continuous
(`Continuous.minEnergyOn_comp` composed with `continuous_symmetricHomotopyHamiltonian`). -/
theorem continuous_minEnergyOn_symmetricHomotopyHamiltonian (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (lam : ℝ)
    {L m₀ c : ℂ} (hKc : numberSpinZCasimirSectorEuclidean N L m₀ c ≠ ⊥) :
    Continuous (fun s : ℝ => minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c)
      (symmetricHomotopyHamiltonian N A T U lam s)) :=
  Continuous.minEnergyOn_comp hKc (continuous_symmetricHomotopyHamiltonian A T U lam)

/-! ## Per-`s` existence-uniqueness of the occupied Casimir sector -/

/-- **Per-`s` existence-uniqueness**: PR-12a's unconditional capstone
`liebRepulsive_exists_unique_casimir_sector_unconditional`
(`LiebRepulsiveSU2Invariance.lean:239`) applied at the homotoped hopping `T_s` and on-site coupling
`U_s(·)`, for every `s ∈ [0, 1]`. The hopping side-conditions transport via PR-4's
`homotopyHopping_symm`/`_bipartite`/`_connected` and the on-site positivity via
`homotopyOnSiteFn_pos`; `L = (N:ℂ)+1` and `m₀ = ((Ne:ℂ) - ((N:ℂ)+1))/2` are `s`-independent. -/
theorem symmetricHomotopy_exists_unique_casimir_sector (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x)
    {lam : ℝ} (hlam : 0 < lam) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ∃ c : ℂ,
      numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
          (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c ≠ ⊥ ∧
        ∀ c' : ℂ, c' ≠ c →
          numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
              (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c' ≠ ⊥ →
            minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c)
                (symmetricHomotopyHamiltonian N A T U lam s) <
              minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c')
                (symmetricHomotopyHamiltonian N A T U lam s) :=
  liebRepulsive_exists_unique_casimir_sector_unconditional N Ne hNe_even hNe_pos hNe_lt
    (homotopyHopping T (liebEndpointHopping A T lam) s)
    (homotopyHopping_symm A T hT_symm lam s) (homotopyHopping_bipartite A T hbip lam s)
    (homotopyHopping_connected A T hT_conn hlam hs)
    (homotopyOnSiteFn U s) (homotopyOnSiteFn_pos hU_pos hs)

/-! ## The assembled capstone: `c 0 = c 1` -/

/-- **The assembled capstone**: the occupied Casimir sector of the symmetric-form homotopy is
constant along the whole homotopy — in particular the occupied Casimir sector of the original
symmetric repulsive model (`s = 0`, via `symmetricHomotopyHamiltonian_zero`) agrees with the
occupied Casimir sector at the homotopy's `s = 1` endpoint. Identifying that `s = 1` Hamiltonian
with the `λ`-endpoint model of PR-4/PR-11c (`symmetricHomotopyHamiltonian _ _ _ _ _ 1 =
symmetricRepulsiveHubbardHamiltonian _ (liebEndpointHopping _ _ _) (fun _ => 1)` holds, but not
`rfl`) is left to PR-13. Assembled from
`symmetricHomotopy_exists_unique_casimir_sector` (supplying `hStrict` pointwise via `choose`, with
the `minEnergyOn K_{c s} (H s) = E s` conjunct closed by `rfl` on `E s := minEnergyOn K_{c s} (H
s)`) and `continuous_minEnergyOn_symmetricHomotopyHamiltonian` (supplying `hCont`), through PR-4's
`casimirSelector_eq_const_of_locally_unique_strict_min`
(`LiebRepulsiveHomotopyContinuity.lean:316`). -/
theorem symmetricHomotopy_casimirSelector_eq_const (N Ne : ℕ)
    (hNe_even : Even Ne) (hNe_pos : 0 < Ne) (hNe_lt : Ne < 2 * (N + 1))
    {A : Finset (Fin (N + 1))} (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU_pos : ∀ x, 0 < U x) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℝ → ℂ,
      (∀ s ∈ Set.Icc (0 : ℝ) 1,
        numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
            (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) (c s) ≠ ⊥ ∧
          ∀ c' : ℂ, c' ≠ c s →
            numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c' ≠ ⊥ →
              minEnergyOn
                  (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                    (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c')
                  (symmetricHomotopyHamiltonian N A T U lam s) >
                minEnergyOn
                  (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                    (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) (c s))
                  (symmetricHomotopyHamiltonian N A T U lam s)) ∧
      c 0 = c 1 := by
  have hex : ∀ s : ℝ, ∃ cs : ℂ, s ∈ Set.Icc (0 : ℝ) 1 →
      numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
          (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) cs ≠ ⊥ ∧
        ∀ c' : ℂ, c' ≠ cs →
          numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
              (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c' ≠ ⊥ →
            minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) cs)
                (symmetricHomotopyHamiltonian N A T U lam s) <
              minEnergyOn
                (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
                  (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) c')
                (symmetricHomotopyHamiltonian N A T U lam s) := by
    intro s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · obtain ⟨cs, hcs⟩ := symmetricHomotopy_exists_unique_casimir_sector N Ne hNe_even hNe_pos
        hNe_lt T hT_symm hbip hT_conn U hU_pos hlam hs
      exact ⟨cs, fun _ => hcs⟩
    · exact ⟨0, fun hmem => absurd hmem hs⟩
  choose c hc using hex
  refine ⟨c, fun s hs => ⟨(hc s hs).1, fun c' hne hK => (hc s hs).2 c' hne hK⟩, ?_⟩
  exact casimirSelector_eq_const_of_locally_unique_strict_min
    (H := fun s => symmetricHomotopyHamiltonian N A T U lam s) (c := c)
    (E := fun s => minEnergyOn
      (numberSpinZCasimirSectorEuclidean N ((N : ℂ) + 1)
        (((Ne : ℂ) - ((N : ℂ) + 1)) / 2) (c s))
      (symmetricHomotopyHamiltonian N A T U lam s))
    (fun s hs => ⟨(hc s hs).1, rfl, fun c' hne hK => (hc s hs).2 c' hne hK⟩)
    (fun _ hK => continuous_minEnergyOn_symmetricHomotopyHamiltonian A T U lam hK)
    0 (by norm_num) 1 (by norm_num)

end LatticeSystem.Fermion
