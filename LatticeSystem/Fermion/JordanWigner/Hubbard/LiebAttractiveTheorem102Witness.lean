import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBalancedSectorGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveSectorConnectivity
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingDegeneracyUpper
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopActionCore

/-!
# Nonemptiness of the electron-number / balanced configuration sectors (Tasaki §10.2.1)

The full-`Ne`-sector singlet-uniqueness milestone
`attractiveHubbardFullSectorGround_unique_singlet` (feeding Tasaki §10.2.1 Theorem 10.2) carries
three `[Nonempty …]` class hypotheses on the fixed-count configuration sectors.  The axiom-facing
statement of Theorem 10.2 has only the arithmetic hypotheses `Even Ne`, `0 < Ne`, `Ne ≤ 2|Λ|`.
This file discharges the gap: for `k ≤ |Λ| = N + 1` (which follows from `Ne = 2k ≤ 2(N + 1)`) the
"first `k` sites occupied" configuration witnesses each of the required sectors.

* `nonempty_hubbardSpinCountSector_of_le` — the fixed up-count sector `Σ_x u_x = k`.
* `nonempty_hubbardBalancedConfig_of_le` — the balanced sector `N̂_↑ = N̂_↓ = k`.
* `nonempty_hubbardSectorConfig_of_le` — the total electron-number sector `Σ_j c_j = 2k`.

The single occupation-count identity `Σ_{i : Fin (N+1)} [i < k] = k` (for `k ≤ N + 1`) is reused
from `tJ_card_val_lt`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.1 (Theorem 10.2).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The number of sites `i : Fin (N+1)` with `i < k` contributes exactly `k` to the sum of the
indicator `[i < k]` (for `k ≤ N + 1`).  The counting core of the sector witnesses, obtained from
`tJ_card_val_lt`. -/
private theorem sum_ite_val_lt (k : ℕ) (hk : k ≤ N + 1) :
    (∑ i : Fin (N + 1), (if i.val < k then (1 : ℕ) else 0)) = k := by
  have h := tJ_card_val_lt (N := N) k hk
  rw [Finset.card_filter] at h
  exact h

/-- `spinfulIndex N i σ = 2i + σ` divides back to the site index `i`. -/
private theorem spinfulIndex_val_div_two (i : Fin (N + 1)) (σ : Fin 2) :
    (spinfulIndex N i σ).val / 2 = i.val := by
  have hval : (spinfulIndex N i σ).val = 2 * i.val + σ.val := by simp [spinfulIndex]
  have := σ.isLt
  omega

/-- **The fixed up-count sector is nonempty** for `k ≤ N + 1`: the configuration with the first `k`
up-sites occupied has up-count exactly `k`. -/
theorem nonempty_hubbardSpinCountSector_of_le {k : ℕ} (hk : k ≤ N + 1) :
    Nonempty (hubbardSpinCountSector N k) := by
  refine ⟨⟨fun i => if i.val < k then 1 else 0, ?_⟩⟩
  rw [show (∑ x : Fin (N + 1), ((if x.val < k then (1 : Fin 2) else 0).val))
        = ∑ x : Fin (N + 1), (if x.val < k then (1 : ℕ) else 0) from
      Finset.sum_congr rfl (fun x _ => by split <;> rfl)]
  exact sum_ite_val_lt k hk

/-- **The balanced configuration sector is nonempty** for `k ≤ N + 1`: the configuration with the
first `k` sites doubly occupied has `k` spin-up and `k` spin-down electrons. -/
theorem nonempty_hubbardBalancedConfig_of_le {k : ℕ} (hk : k ≤ N + 1) :
    Nonempty (hubbardBalancedConfig N k) := by
  refine ⟨⟨fun j => if j.val / 2 < k then 1 else 0, ?_, ?_⟩⟩
  · rw [show (∑ i : Fin (N + 1),
          ((if (spinfulIndex N i 0).val / 2 < k then (1 : Fin 2) else 0).val))
        = ∑ i : Fin (N + 1), (if i.val < k then (1 : ℕ) else 0) from
      Finset.sum_congr rfl (fun i _ => by rw [spinfulIndex_val_div_two i 0]; split <;> rfl)]
    exact sum_ite_val_lt k hk
  · rw [show (∑ i : Fin (N + 1),
          ((if (spinfulIndex N i 1).val / 2 < k then (1 : Fin 2) else 0).val))
        = ∑ i : Fin (N + 1), (if i.val < k then (1 : ℕ) else 0) from
      Finset.sum_congr rfl (fun i _ => by rw [spinfulIndex_val_div_two i 1]; split <;> rfl)]
    exact sum_ite_val_lt k hk

/-- **The total electron-number sector is nonempty** for `k ≤ N + 1`: the configuration with the
first `k` sites doubly occupied has total electron number `2k`. -/
theorem nonempty_hubbardSectorConfig_of_le {k : ℕ} (hk : k ≤ N + 1) :
    Nonempty (hubbardSectorConfig N (2 * k)) := by
  refine ⟨⟨fun j => if j.val / 2 < k then 1 else 0, ?_⟩⟩
  change (∑ j : Fin (2 * N + 2), ((if j.val / 2 < k then (1 : Fin 2) else 0).val)) = 2 * k
  rw [sum_spinful_reindex N (fun j => ((if j.val / 2 < k then (1 : Fin 2) else 0).val)),
    show (∑ i : Fin (N + 1), ∑ σ : Fin 2,
          ((if (spinfulIndex N i σ).val / 2 < k then (1 : Fin 2) else 0).val))
        = ∑ i : Fin (N + 1), 2 * (if i.val < k then (1 : ℕ) else 0) from
      Finset.sum_congr rfl (fun i _ => by
        rw [Fin.sum_univ_two, spinfulIndex_val_div_two i 0, spinfulIndex_val_div_two i 1]
        split <;> rfl),
    ← Finset.mul_sum, sum_ite_val_lt k hk]

end LatticeSystem.Fermion
