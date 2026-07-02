import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOperatorLift

/-!
# A per-spin balanced (`Ŝ³ = 0`) sector ground vector for the attractive Hubbard model (§10.2.4)

Layer PR40e-pre2b toward discharging `theorem_10_2_lieb_attractive_unique_singlet`. The Lieb
spin-reflection-positivity endgame needs a ground vector supported on the **balanced**
Fock-config sector `N̂_↑ = N̂_↓ = k` (electron number `2k`), because only there is the Hermitian-`W`
`blockWCoeff` supported on a *principal* block `S_k × S_k` (the plain number sector gives a band on
which the connected-block argument fails).

This module instantiates the predicate/support-based sector-compression Core
(`configSector*`, in `HubbardImpossibilityLowUVariationalCore.lean`) at the balanced predicate
`P c := (Σ_i c_{i↑} = k) ∧ (Σ_i c_{i↓} = k)`.  No compression machinery is duplicated: it is the
same Core used by the number-sector instance, applied to a different predicate.  The per-spin
support restriction comes from the stage-(i) commutation lemmas
`attractiveHubbardHamiltonian_commute_fermionTotal{Up,Down}Number`.

## Main results

* `hubbardBalancedSectorPred`, `hubbardBalancedConfig` — the balanced predicate and its sector.
* `mulVec_apply_eq_zero_of_upNumber_ne` / `_downNumber_ne` — a spin-number eigenstate vanishes off
  its spin-`k` shell (per-spin analogs of `mulVec_apply_eq_zero_of_number_ne`).
* `fermionTotalUpNumber_mulVec_basisVec` / `_DownNumber` — the spin numbers are diagonal on `|c⟩`.
* `exists_attractive_balanced_ground` — a nonzero balanced eigenvector at the balanced
  sector-compression minimum eigenvalue, with `N̂_↑ φ = N̂_↓ φ = k·φ`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The per-spin balanced predicate**: a Fock configuration `c` has exactly `k` spin-up and `k`
spin-down electrons, `Σ_i c_{i↑} = k ∧ Σ_i c_{i↓} = k`.  The `Ŝ³ = 0` sector at electron number
`2k`. -/
abbrev hubbardBalancedSectorPred (N k : ℕ) : (Fin (2 * N + 2) → Fin 2) → Prop :=
  fun c => (∑ i : Fin (N + 1), (c (spinfulIndex N i 0)).val) = k
    ∧ (∑ i : Fin (N + 1), (c (spinfulIndex N i 1)).val) = k

/-- **The balanced configuration sector**: configurations with `k` up and `k` down electrons. -/
abbrev hubbardBalancedConfig (N k : ℕ) := configSector N (hubbardBalancedSectorPred N k)

/-- A spin-up-number eigenstate vanishes off its spin-`k` shell: if `N̂_↑ v = k • v` then `v w = 0`
whenever the up-count `Σ_i w_{i↑} ≠ k` (per-spin analog of `mulVec_apply_eq_zero_of_number_ne`). -/
theorem mulVec_apply_eq_zero_of_upNumber_ne (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (hv : (fermionTotalUpNumber N).mulVec v = k • v) (w : Fin (2 * N + 2) → Fin 2)
    (hne : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) ≠ k) : v w = 0 := by
  have h1 : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) * v w = k * v w := by
    rw [← fermionTotalUpNumber_mulVec_apply, hv, Pi.smul_apply, smul_eq_mul]
  have h2 : ((∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) - k) * v w = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

/-- A spin-down-number eigenstate vanishes off its spin-`k` shell: if `N̂_↓ v = k • v` then
`v w = 0` whenever the down-count `Σ_i w_{i↓} ≠ k`. -/
theorem mulVec_apply_eq_zero_of_downNumber_ne (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (hv : (fermionTotalDownNumber N).mulVec v = k • v) (w : Fin (2 * N + 2) → Fin 2)
    (hne : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) ≠ k) : v w = 0 := by
  have h1 : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) * v w = k * v w := by
    rw [← fermionTotalDownNumber_mulVec_apply, hv, Pi.smul_apply, smul_eq_mul]
  have h2 : ((∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) - k) * v w = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

/-- **`N̂_↑` is diagonal on a computational basis state**: `N̂_↑ |c⟩ = (Σ_i c_{i↑}) • |c⟩`. -/
theorem fermionTotalUpNumber_mulVec_basisVec (c : Fin (2 * N + 2) → Fin 2) :
    (fermionTotalUpNumber N).mulVec (basisVec c) =
      (∑ i : Fin (N + 1), ((c (spinfulIndex N i 0)).val : ℂ)) • basisVec c := by
  funext w
  rw [fermionTotalUpNumber_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : w = c
  · rw [h]
  · rw [basisVec_of_ne h, mul_zero, mul_zero]

/-- **`N̂_↓` is diagonal on a computational basis state**: `N̂_↓ |c⟩ = (Σ_i c_{i↓}) • |c⟩`. -/
theorem fermionTotalDownNumber_mulVec_basisVec (c : Fin (2 * N + 2) → Fin 2) :
    (fermionTotalDownNumber N).mulVec (basisVec c) =
      (∑ i : Fin (N + 1), ((c (spinfulIndex N i 1)).val : ℂ)) • basisVec c := by
  funext w
  rw [fermionTotalDownNumber_mulVec_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : w = c
  · rw [h]
  · rw [basisVec_of_ne h, mul_zero, mul_zero]

/-- **A balanced sector expansion is an `N̂_↑ = k` eigenvector.**  Each basis vector `|s⟩` in the
balanced sector has up-count `k`, so `N̂_↑` acts as `k` on the whole expansion. -/
theorem fermionTotalUpNumber_mulVec_configSectorExpansion_balanced (k : ℕ)
    (c : hubbardBalancedConfig N k → ℂ) :
    (fermionTotalUpNumber N).mulVec (configSectorExpansion N (hubbardBalancedSectorPred N k) c)
      = (k : ℂ) • configSectorExpansion N (hubbardBalancedSectorPred N k) c := by
  unfold configSectorExpansion
  rw [← Matrix.mulVecLin_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [map_smul, Matrix.mulVecLin_apply, fermionTotalUpNumber_mulVec_basisVec,
    show (∑ i : Fin (N + 1), ((s.val (spinfulIndex N i 0)).val : ℂ)) = (k : ℂ) from by
      exact_mod_cast s.property.1,
    smul_comm]

/-- **A balanced sector expansion is an `N̂_↓ = k` eigenvector.**  Each basis vector `|s⟩` in the
balanced sector has down-count `k`, so `N̂_↓` acts as `k` on the whole expansion. -/
theorem fermionTotalDownNumber_mulVec_configSectorExpansion_balanced (k : ℕ)
    (c : hubbardBalancedConfig N k → ℂ) :
    (fermionTotalDownNumber N).mulVec (configSectorExpansion N (hubbardBalancedSectorPred N k) c)
      = (k : ℂ) • configSectorExpansion N (hubbardBalancedSectorPred N k) c := by
  unfold configSectorExpansion
  rw [← Matrix.mulVecLin_apply, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [map_smul, Matrix.mulVecLin_apply, fermionTotalDownNumber_mulVec_basisVec,
    show (∑ i : Fin (N + 1), ((s.val (spinfulIndex N i 1)).val : ℂ)) = (k : ℂ) from by
      exact_mod_cast s.property.2,
    smul_comm]

/-- **A balanced (`Ŝ³ = 0`) sector ground vector.** For symmetric real hopping `T` and any site
attraction `U`, there is a nonzero vector `φ` with exactly `k` spin-up and `k` spin-down electrons
(`N̂_↑ φ = N̂_↓ φ = k·φ`) that is an eigenvector of the attractive Hamiltonian at the *balanced
sector compression's* minimum eigenvalue.  The per-spin support is transported through
`[Ĥ, N̂_↑] = [Ĥ, N̂_↓] = 0`; the compression is the same generic `configSector` Core used by the
number sector, instantiated at the balanced predicate. -/
theorem exists_attractive_balanced_ground (k : ℕ) [Nonempty (hubbardBalancedConfig N k)]
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ)
    (hT : ∀ i j, T i j = T j i) :
    ∃ φ : (Fin (2 * N + 2) → Fin 2) → ℂ, φ ≠ 0
      ∧ (fermionTotalUpNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (fermionTotalDownNumber N).mulVec φ = (k : ℂ) • φ
      ∧ (attractiveHubbardHamiltonian N T U).mulVec φ
          = ((hermitianMinEigenvalue (configSectorCompress_isHermitian
              (hubbardBalancedSectorPred N k)
              (attractiveHubbardHamiltonian_isHermitian T U hT)) : ℝ) : ℂ) • φ := by
  classical
  set hHW := configSectorCompress_isHermitian (hubbardBalancedSectorPred N k)
    (attractiveHubbardHamiltonian_isHermitian T U hT) with hHWd
  obtain ⟨c, hc0, hceig⟩ := exists_nonzero_eigenvector_hermitianMinEigenvalue hHW
  set Φ := configSectorExpansion N (hubbardBalancedSectorPred N k) c with hΦ
  have hUp : (fermionTotalUpNumber N).mulVec Φ = (k : ℂ) • Φ :=
    fermionTotalUpNumber_mulVec_configSectorExpansion_balanced k c
  have hDn : (fermionTotalDownNumber N).mulVec Φ = (k : ℂ) • Φ :=
    fermionTotalDownNumber_mulVec_configSectorExpansion_balanced k c
  refine ⟨Φ, configSectorExpansion_ne_zero (hubbardBalancedSectorPred N k) hc0, hUp, hDn, ?_⟩
  -- `Ĥ Φ` keeps the balanced eigenvalues (charge conservation), hence stays balanced-supported.
  have hHΦup : (fermionTotalUpNumber N).mulVec ((attractiveHubbardHamiltonian N T U).mulVec Φ)
      = (k : ℂ) • ((attractiveHubbardHamiltonian N T U).mulVec Φ) := by
    rw [Matrix.mulVec_mulVec,
      ← (attractiveHubbardHamiltonian_commute_fermionTotalUpNumber T U).eq,
      ← Matrix.mulVec_mulVec, hUp, Matrix.mulVec_smul]
  have hHΦdn : (fermionTotalDownNumber N).mulVec ((attractiveHubbardHamiltonian N T U).mulVec Φ)
      = (k : ℂ) • ((attractiveHubbardHamiltonian N T U).mulVec Φ) := by
    rw [Matrix.mulVec_mulVec,
      ← (attractiveHubbardHamiltonian_commute_fermionTotalDownNumber T U).eq,
      ← Matrix.mulVec_mulVec, hDn, Matrix.mulVec_smul]
  have hApres : ∀ w, ¬ hubbardBalancedSectorPred N k w →
      (attractiveHubbardHamiltonian N T U).mulVec Φ w = 0 := by
    intro w hw
    by_cases hup : (∑ i : Fin (N + 1), (w (spinfulIndex N i 0)).val) = k
    · have hdn : (∑ i : Fin (N + 1), (w (spinfulIndex N i 1)).val) ≠ k := fun h => hw ⟨hup, h⟩
      exact mulVec_apply_eq_zero_of_downNumber_ne _ (k : ℂ) hHΦdn w
        (fun hcast => hdn (by exact_mod_cast hcast))
    · exact mulVec_apply_eq_zero_of_upNumber_ne _ (k : ℂ) hHΦup w
        (fun hcast => hup (by exact_mod_cast hcast))
  exact configSectorExpansion_of_compress_eigen (hubbardBalancedSectorPred N k) hApres hceig

end LatticeSystem.Fermion
