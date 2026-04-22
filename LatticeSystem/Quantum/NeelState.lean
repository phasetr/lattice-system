/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition
import LatticeSystem.Quantum.NeelState.Definition2D
import LatticeSystem.Quantum.NeelState.Definition3D
import LatticeSystem.Quantum.NeelState.BondAction.Chain
import LatticeSystem.Quantum.NeelState.BondAction.Square
import LatticeSystem.Quantum.MagnetizationSubspace
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.TimeReversalMulti

/-!
# Néel state on a bipartite even chain (Tasaki §2.5)

Façade module re-exporting the Néel state machinery. Currently
imports the chain `Definition` (Phase 2 PR 1) plus the in-progress
2D / 3D / TimeReversal / MarshallSign / InnerProduct / Energy
sections still residing in this file (Phase 2 follow-up PRs will
extract those into separate files under `NeelState/`).

The chain definitions live in `NeelState/Definition.lean`:
* `neelChainConfig`, `neelChainState`,
* `neelChainConfig_magnetization_zero`,
* `neelChainState_mem_magnetizationSubspace_zero`,
* `heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero`.

(Refactor Phase 2 PR 1, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Quantum

/-! ## `K = 1` Néel = `upDown` and time-reversal action -/

/-- The `K = 1` Néel chain configuration on `Fin 2` agrees with
the existing `upDown` configuration (both send `0 ↦ ↑` and
`1 ↦ ↓`). -/
theorem neelChainConfig_one_eq_upDown :
    neelChainConfig 1 = upDown := by
  funext i
  fin_cases i <;> rfl

/-- Time-reversal acts on the `K = 1` Néel state by sending it to
the negative of the swapped configuration:

  `Θ̂_tot (neelChainState 1) = -basisVec (basisSwap upDown 0 1)`,

i.e. `Θ̂_tot |↑↓⟩ = -|↓↑⟩` (the antiparallel pair flips, with
the per-down sign convention of `Θ̂`). -/
theorem timeReversalSpinHalfMulti_neelChainState_one :
    timeReversalSpinHalfMulti (neelChainState 1) =
      -basisVec (basisSwap upDown 0 1) := by
  unfold neelChainState
  rw [neelChainConfig_one_eq_upDown,
    timeReversalSpinHalfMulti_basisVec_upDown]

/-- Auxiliary alternating-product lemma. The product
`∏ i : Fin (2 * K), (if i.val % 2 = 0 then -1 else 1) = (-1)^K`,
since each adjacent pair `(2k, 2k+1)` contributes `(-1) · 1 = -1`.
Proof by induction on `K`, peeling the last two indices via
`Fin.prod_univ_castSucc` (mirror of `sum_alternating_sign`). -/
lemma prod_alternating_neg_one (K : ℕ) :
    (∏ i : Fin (2 * K), (if i.val % 2 = 0 then (-1 : ℂ) else 1))
      = (-1) ^ K := by
  induction K with
  | zero => simp
  | succ K' ih =>
    rw [show 2 * (K' + 1) = (2 * K' + 1) + 1 from by ring]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have h_last_outer :
        (if (Fin.last (2 * K' + 1)).val % 2 = 0 then (-1 : ℂ) else 1)
          = 1 := by
      have h1 : (Fin.last (2 * K' + 1)).val = 2 * K' + 1 := rfl
      rw [h1, show (2 * K' + 1) % 2 = 1 from by omega]
      simp
    have h_last_inner :
        (if ((Fin.last (2 * K')).castSucc :
            Fin (2 * K' + 1 + 1)).val % 2 = 0
          then (-1 : ℂ) else 1) = -1 := by
      have h1 : ((Fin.last (2 * K')).castSucc :
          Fin (2 * K' + 1 + 1)).val = 2 * K' := rfl
      rw [h1, show (2 * K') % 2 = 0 from by omega]
      simp
    have h_inner_eq :
        (∏ i : Fin (2 * K'),
          if (i.castSucc.castSucc : Fin (2 * K' + 1 + 1)).val % 2 = 0
            then (-1 : ℂ) else 1)
        = ∏ i : Fin (2 * K'),
            (if i.val % 2 = 0 then (-1 : ℂ) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rfl
    rw [h_inner_eq, h_last_inner, h_last_outer, ih]
    ring

/-- Tasaki §2.5 generalisation of #251 to arbitrary chain length:
the multi-spin time-reversal acts on the 1D Néel chain state by

  `Θ̂_tot (neelChainState K) =
    (-1)^K · basisVec (flipConfig (neelChainConfig K))`.

Proof: the per-site sign product collapses to `(-1)^K` since each
of the `K` even-indexed sites carries `σ = ↑`, contributing
`timeReversalSign 1 = -1` after `flipConfig`, while each of the
`K` odd-indexed sites contributes `+1`. -/
theorem timeReversalSpinHalfMulti_neelChainState (K : ℕ) :
    timeReversalSpinHalfMulti (neelChainState K) =
      ((-1 : ℂ) ^ K) • basisVec (flipConfig (neelChainConfig K)) := by
  unfold neelChainState
  rw [timeReversalSpinHalfMulti_basisVec]
  congr 1
  have h_pointwise : ∀ x : Fin (2 * K),
      timeReversalSign (flipConfig (neelChainConfig K) x) =
        (if x.val % 2 = 0 then (-1 : ℂ) else 1) := by
    intro x
    unfold flipConfig neelChainConfig timeReversalSign
    by_cases hp : x.val % 2 = 0
    · simp [hp]
    · simp [hp]
  rw [show (∏ x : Fin (2 * K),
        timeReversalSign (flipConfig (neelChainConfig K) x))
      = ∏ x : Fin (2 * K),
          (if x.val % 2 = 0 then (-1 : ℂ) else 1) from
      Finset.prod_congr rfl (fun i _ => h_pointwise i)]
  exact prod_alternating_neg_one K

/-! ## 2D Néel time-reversal action (general K, L) -/

/-- Auxiliary alternating-product lemma with parity offset (the
2D analogue of `prod_alternating_neg_one`, mirroring
`sum_alternating_sign_offset`). For any `parity, L : ℕ`,

  `∏ j : Fin (2 * L), (if (parity + j.val) % 2 = 0 then -1 else 1)
    = (-1)^L`.

Proof by induction on `L`, peeling the last two indices.
The product is independent of `parity` because exactly `L` of
the `2L` indices land in each parity class (regardless of offset). -/
lemma prod_alternating_neg_one_offset (parity L : ℕ) :
    (∏ j : Fin (2 * L),
      (if (parity + j.val) % 2 = 0 then (-1 : ℂ) else 1))
        = (-1) ^ L := by
  induction L with
  | zero => simp
  | succ L' ih =>
    rw [show 2 * (L' + 1) = (2 * L' + 1) + 1 from by ring]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have h_inner_eq :
        (∏ j : Fin (2 * L'),
          if (parity + (j.castSucc.castSucc :
                Fin (2 * L' + 1 + 1)).val) % 2 = 0
            then (-1 : ℂ) else 1) =
        ∏ j : Fin (2 * L'),
          (if (parity + j.val) % 2 = 0 then (-1 : ℂ) else 1) := by
      apply Finset.prod_congr rfl
      intro j _
      rfl
    rw [h_inner_eq, ih]
    have h_last_outer :
        (Fin.last (2 * L' + 1)).val = 2 * L' + 1 := rfl
    have h_last_inner :
        ((Fin.last (2 * L')).castSucc :
          Fin (2 * L' + 1 + 1)).val = 2 * L' := rfl
    rw [h_last_outer, h_last_inner]
    rcases Nat.mod_two_eq_zero_or_one parity with hp0 | hp1
    · have h1 : (parity + 2 * L') % 2 = 0 := by omega
      have h2 : (parity + (2 * L' + 1)) % 2 ≠ 0 := by omega
      rw [if_pos h1, if_neg h2]
      ring
    · have h1 : (parity + 2 * L') % 2 ≠ 0 := by omega
      have h2 : (parity + (2 * L' + 1)) % 2 = 0 := by omega
      rw [if_neg h1, if_pos h2]
      ring

/-- Tasaki §2.5 generalisation of #256 to arbitrary 2D
checkerboard size: the multi-spin time-reversal acts on the 2D
Néel state by

  `Θ̂_tot (neelSquareState K L) =
    basisVec (flipConfig (neelSquareConfig K L))`,

with no overall sign because the 2K · 2L = 4KL sites split
exactly into 2KL ups and 2KL downs, and `(-1)^(2KL) = 1`. -/
theorem timeReversalSpinHalfMulti_neelSquareState (K L : ℕ) :
    timeReversalSpinHalfMulti (neelSquareState K L) =
      basisVec (flipConfig (neelSquareConfig K L)) := by
  unfold neelSquareState
  rw [timeReversalSpinHalfMulti_basisVec]
  have hprod :
      (∏ p : Fin (2 * K) × Fin (2 * L),
          timeReversalSign (flipConfig (neelSquareConfig K L) p))
        = (1 : ℂ) := by
    rw [Fintype.prod_prod_type]
    have h_inner : ∀ i : Fin (2 * K),
        (∏ j : Fin (2 * L),
            timeReversalSign
              (flipConfig (neelSquareConfig K L) (i, j))) =
          (-1 : ℂ) ^ L := by
      intro i
      have h_pointwise : ∀ j : Fin (2 * L),
          timeReversalSign
              (flipConfig (neelSquareConfig K L) (i, j)) =
            (if (i.val + j.val) % 2 = 0 then (-1 : ℂ) else 1) := by
        intro j
        unfold flipConfig neelSquareConfig timeReversalSign
        by_cases hp : (i.val + j.val) % 2 = 0
        · simp [hp]
        · simp [hp]
      rw [Finset.prod_congr rfl (fun j _ => h_pointwise j)]
      exact prod_alternating_neg_one_offset i.val L
    rw [Finset.prod_congr rfl (fun i _ => h_inner i)]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul, show L * (2 * K) = 2 * (K * L) from by ring,
      pow_mul, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow]
  rw [hprod, one_smul]

/-! ## 2D Néel time-reversal action (K = L = 1 instance) -/

/-- Concrete time-reversal action on the 2D Néel state for the
`K = L = 1` checkerboard (4 sites). The `|Λ| = 4` is even and the
Néel configuration has equal numbers of ups and downs (2 each),
so the `(-1)^(# down spins in flip σ)` sign factor equals `1`:

  `Θ̂_tot (neelSquareState 1 1) =
    basisVec (flipConfig (neelSquareConfig 1 1))`.

This is the 2-dimensional analogue of the time-reversal
computation on the chain (#251). -/
theorem timeReversalSpinHalfMulti_neelSquareState_one_one :
    timeReversalSpinHalfMulti (neelSquareState 1 1) =
      basisVec (flipConfig (neelSquareConfig 1 1)) := by
  unfold neelSquareState
  rw [timeReversalSpinHalfMulti_basisVec]
  have hprod : (∏ p : Fin (2 * 1) × Fin (2 * 1),
        timeReversalSign (flipConfig (neelSquareConfig 1 1) p))
      = (1 : ℂ) := by
    rw [Fintype.prod_prod_type]
    rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two]
    simp [flipConfig, neelSquareConfig, timeReversalSign]
  rw [hprod, one_smul]

/-! ## 3D Néel time-reversal action (general K, L, M) -/

/-- Tasaki §2.5 generalisation of #257 to arbitrary 3D cubic
checkerboard size: the multi-spin time-reversal acts on the 3D
Néel state by

  `Θ̂_tot (neelCubicState K L M) =
    basisVec (flipConfig (neelCubicConfig K L M))`,

with no overall sign because the 8KLM sites split exactly into
4KLM ups and 4KLM downs, and `(-1)^(4KLM) = 1`. Reuses the
`prod_alternating_neg_one_offset` helper to collapse the
`k`-axis product first. -/
theorem timeReversalSpinHalfMulti_neelCubicState (K L M : ℕ) :
    timeReversalSpinHalfMulti (neelCubicState K L M) =
      basisVec (flipConfig (neelCubicConfig K L M)) := by
  unfold neelCubicState
  rw [timeReversalSpinHalfMulti_basisVec]
  have hprod :
      (∏ p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M),
          timeReversalSign (flipConfig (neelCubicConfig K L M) p))
        = (1 : ℂ) := by
    rw [Fintype.prod_prod_type]
    have h_inner : ∀ p : Fin (2 * K) × Fin (2 * L),
        (∏ k : Fin (2 * M),
            timeReversalSign
              (flipConfig (neelCubicConfig K L M) (p, k))) =
          (-1 : ℂ) ^ M := by
      intro p
      have h_pointwise : ∀ k : Fin (2 * M),
          timeReversalSign
              (flipConfig (neelCubicConfig K L M) (p, k)) =
            (if (p.1.val + p.2.val + k.val) % 2 = 0
              then (-1 : ℂ) else 1) := by
        intro k
        unfold flipConfig neelCubicConfig timeReversalSign
        by_cases hp : (p.1.val + p.2.val + k.val) % 2 = 0
        · simp [hp]
        · simp [hp]
      rw [Finset.prod_congr rfl (fun k _ => h_pointwise k)]
      exact prod_alternating_neg_one_offset (p.1.val + p.2.val) M
    rw [Finset.prod_congr rfl (fun p _ => h_inner p)]
    rw [Finset.prod_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [← pow_mul,
      show M * (2 * K * (2 * L)) = 2 * (2 * K * L * M) from by ring,
      pow_mul, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow]
  rw [hprod, one_smul]

/-! ## 3D Néel time-reversal action (K = L = M = 1 instance) -/

/-- Concrete time-reversal action on the 3D cubic Néel state for
the `K = L = M = 1` checkerboard (8 sites). The 8-site cube has
4 up spins and 4 down spins, so under `flipConfig` the resulting
`timeReversalSign` product is `(-1)^4 · 1^4 = 1`:

  `Θ̂_tot (neelCubicState 1 1 1) =
    basisVec (flipConfig (neelCubicConfig 1 1 1))`.

This is the 3-dimensional analogue of the time-reversal computations
on the 1D K = 1 chain (#251) and the 2D K = L = 1 plaquette (#256). -/
theorem timeReversalSpinHalfMulti_neelCubicState_one_one_one :
    timeReversalSpinHalfMulti (neelCubicState 1 1 1) =
      basisVec (flipConfig (neelCubicConfig 1 1 1)) := by
  unfold neelCubicState
  rw [timeReversalSpinHalfMulti_basisVec]
  have hprod :
      (∏ p : (Fin (2 * 1) × Fin (2 * 1)) × Fin (2 * 1),
          timeReversalSign (flipConfig (neelCubicConfig 1 1 1) p))
        = (1 : ℂ) := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type]
    rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two,
        Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_two,
        Fin.prod_univ_two]
    simp [flipConfig, neelCubicConfig, timeReversalSign]
  rw [hprod, one_smul]

/-! ## 3D cubic Néel per-bond `Ŝ_x · Ŝ_y` actions -/

/-- 3D x-axis bond `((i,j,k), (i+1,j,k))`: antiparallel under
the 3D checkerboard. Same `(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩`
decomposition. -/
theorem spinHalfDot_mulVec_neelCubicState_x_adjacent
    (K L M : ℕ) {i j k : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState K L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L M)
            (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
            (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K L M := by
  unfold neelCubicState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : ((i + 1) + j + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D y-axis bond `((i,j,k), (i,j+1,k))`. -/
theorem spinHalfDot_mulVec_neelCubicState_y_adjacent
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState K L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L M)
            (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
            (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K L M := by
  unfold neelCubicState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + (j + 1) + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + (j + 1) + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D z-axis bond `((i,j,k), (i,j,k+1))`. -/
theorem spinHalfDot_mulVec_neelCubicState_z_adjacent
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) (hk : k + 1 < 2 * M) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState K L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L M)
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K L M := by
  unfold neelCubicState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + j + (k + 1)) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + j + (k + 1)) % 2 = 0 := by omega
      simp [hp, hp1]

/-! ## 3D cubic Néel wrap-around bond actions (cubic torus BC) -/

/-- 3D x-axis wrap-around bond `((2K + 1, j), k) ~ ((0, j), k)`
on the 3D Néel state over `(Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M)`.
The shift `2K + 1` is odd so the bond is antiparallel; same
`(1/2)·|swap⟩ - (1/4)·|Φ_Néel⟩` decomposition. -/
theorem spinHalfDot_mulVec_neelCubicState_x_wrap
    (K L M : ℕ) {j k : ℕ} (hj : j < 2 * L) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
        (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
          (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))).mulVec
        (neelCubicState (K + 1) L M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig (K + 1) L M)
            (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
            (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
              (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState (K + 1) L M := by
  unfold neelCubicState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (j + k) with hjk0 | hjk1
    · have h1 : (2 * K + 1 + j + k) % 2 ≠ 0 := by omega
      simp [h1, hjk0]
    · have h1 : (2 * K + 1 + j + k) % 2 = 0 := by omega
      simp [h1, hjk1]

/-- 3D y-axis wrap-around bond `((i, 2L + 1), k) ~ ((i, 0), k)`
on the 3D Néel state over `(Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M)`. -/
theorem spinHalfDot_mulVec_neelCubicState_y_wrap
    (K L M : ℕ) {i k : ℕ} (hi : i < 2 * K) (hk : k < 2 * M) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
        (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
          (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))).mulVec
        (neelCubicState K (L + 1) M) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K (L + 1) M)
            (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
            (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
              (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))) -
        (1 / 4 : ℂ) • neelCubicState K (L + 1) M := by
  unfold neelCubicState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (i + k) with hik0 | hik1
    · have h1 : (i + (2 * L + 1) + k) % 2 ≠ 0 := by omega
      simp [h1, hik0]
    · have h1 : (i + (2 * L + 1) + k) % 2 = 0 := by omega
      simp [h1, hik1]

/-- 3D z-axis wrap-around bond `((i, j), 2M + 1) ~ ((i, j), 0)`
on the 3D Néel state over `(Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1))`. -/
theorem spinHalfDot_mulVec_neelCubicState_z_wrap
    (K L M : ℕ) {i j : ℕ} (hi : i < 2 * K) (hj : j < 2 * L) :
    (spinHalfDot
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
        (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
          (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))).mulVec
        (neelCubicState K L (M + 1)) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelCubicConfig K L (M + 1))
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
            (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
              (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))) -
        (1 / 4 : ℂ) • neelCubicState K L (M + 1) := by
  unfold neelCubicState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (i + j) with hij0 | hij1
    · have h1 : (i + j + (2 * M + 1)) % 2 ≠ 0 := by omega
      simp [h1, hij0]
    · have h1 : (i + j + (2 * M + 1)) % 2 = 0 := by omega
      simp [h1, hij1]

/-! ## Marshall sign on the parity-coloured chain (Tasaki §2.5)

The Marshall sign (Marshall 1955; Lieb-Mattis 1962; Tasaki §2.5) of
a spin configuration `σ : Fin (2 * K) → Fin 2` is, on the
bipartite chain `Fin (2 * K)` with sublattice `A` = even indices:

  `(-1)^(N_A^↓)`

where `N_A^↓` is the number of down spins on sublattice `A`. After
the Marshall basis change `|σ⟩ ↦ (-1)^(N_A^↓) |σ⟩`, the AF
Heisenberg Hamiltonian on a bipartite lattice has all non-positive
off-diagonal entries, which is the input to the
Perron-Frobenius-style proof of the Marshall-Lieb-Mattis
theorem. -/

/-- Generic graph-centric Marshall sign. For a finite vertex type
`V`, a sublattice-`A` indicator `A : V → Bool`, and a spin-1/2
configuration `σ : V → Fin 2`, returns `(-1)^(N_A^↓)`:

  `marshallSignOf A σ := ∏_{x ∈ A} (-1)^(σ x)`.

This is the generic form of the chain / 2D / 3D Marshall signs;
those are obtained by instantiating `A` with the corresponding
parity colouring. Aligns with the project-wide graph-centric
design philosophy (CLAUDE.local.md). -/
noncomputable def marshallSignOf {V : Type*} [Fintype V]
    (A : V → Bool) (σ : V → Fin 2) : ℂ :=
  ∏ x : V, if A x then ((-1 : ℂ) ^ (σ x : ℕ)) else 1

/-- Marshall sign of a spin-1/2 configuration on the
parity-coloured chain `Fin (2 * K)`: `(-1)^(N_A^↓)` with `A` =
even indices. Encoded as the product `∏_{x even} (-1)^(σ x)`. -/
noncomputable def marshallSignChainConfig (K : ℕ)
    (σ : Fin (2 * K) → Fin 2) : ℂ :=
  ∏ x : Fin (2 * K),
    (if x.val % 2 = 0 then ((-1 : ℂ) ^ (σ x : ℕ)) else 1)

/-- The Néel chain configuration has `Marshall sign = 1`: every
even-indexed site carries `↑ : Fin 2 := 0`, so each factor
`(-1)^(σ x) = 1` and the empty/down-count gives `(-1)^0 = 1`. -/
theorem marshallSignChainConfig_neelChainConfig (K : ℕ) :
    marshallSignChainConfig K (neelChainConfig K) = 1 := by
  unfold marshallSignChainConfig neelChainConfig
  apply Finset.prod_eq_one
  intro x _
  by_cases hp : x.val % 2 = 0
  · simp [hp]
  · simp [hp]

/-- 2D Marshall sign of a spin-1/2 configuration on the
checkerboard `Fin (2 * K) × Fin (2 * L)`: `(-1)^(N_A^↓)` with
`A` = sites with `(i + j)` even. Encoded as the product
`∏_{(i, j) with i+j even} (-1)^(σ (i, j))`. -/
noncomputable def marshallSignSquareConfig (K L : ℕ)
    (σ : Fin (2 * K) × Fin (2 * L) → Fin 2) : ℂ :=
  ∏ p : Fin (2 * K) × Fin (2 * L),
    (if (p.1.val + p.2.val) % 2 = 0
      then ((-1 : ℂ) ^ (σ p : ℕ)) else 1)

/-- The 2D checkerboard Néel configuration has `Marshall sign = 1`:
sublattice-A sites carry `↑`, so each contributing factor is
`(-1)^0 = 1`. -/
theorem marshallSignSquareConfig_neelSquareConfig (K L : ℕ) :
    marshallSignSquareConfig K L (neelSquareConfig K L) = 1 := by
  unfold marshallSignSquareConfig neelSquareConfig
  apply Finset.prod_eq_one
  intro p _
  by_cases hp : (p.1.val + p.2.val) % 2 = 0
  · simp [hp]
  · simp [hp]

/-- 3D Marshall sign of a spin-1/2 configuration on the cubic
checkerboard `(Fin (2 * K) × Fin (2 * L)) × Fin (2 * M)`:
`(-1)^(N_A^↓)` with `A` = sites with `(i + j + k)` even. -/
noncomputable def marshallSignCubicConfig (K L M : ℕ)
    (σ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) :
    ℂ :=
  ∏ p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M),
    (if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
      then ((-1 : ℂ) ^ (σ p : ℕ)) else 1)

/-- The 3D cubic checkerboard Néel configuration has
`Marshall sign = 1`: sublattice-A sites carry `↑`, so each
contributing factor is `(-1)^0 = 1`. -/
theorem marshallSignCubicConfig_neelCubicConfig (K L M : ℕ) :
    marshallSignCubicConfig K L M (neelCubicConfig K L M) = 1 := by
  unfold marshallSignCubicConfig neelCubicConfig
  apply Finset.prod_eq_one
  intro p _
  by_cases hp : (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
  · simp [hp]
  · simp [hp]

/-- All-up Marshall sign: `marshallSignChainConfig K (fun _ => 0) = 1`. -/
theorem marshallSignChainConfig_const_zero (K : ℕ) :
    marshallSignChainConfig K (fun _ : Fin (2 * K) => (0 : Fin 2)) = 1 := by
  unfold marshallSignChainConfig
  apply Finset.prod_eq_one
  intro x _
  by_cases hp : x.val % 2 = 0 <;> simp [hp]

/-- All-down Marshall sign: `marshallSignChainConfig K (fun _ => 1) = (-1)^K`
(every one of the `K` even-indexed sites carries `↓`). -/
theorem marshallSignChainConfig_const_one (K : ℕ) :
    marshallSignChainConfig K (fun _ : Fin (2 * K) => (1 : Fin 2)) =
      ((-1 : ℂ) ^ K) := by
  unfold marshallSignChainConfig
  rw [show (∏ x : Fin (2 * K),
        if x.val % 2 = 0 then ((-1 : ℂ) ^ ((1 : Fin 2) : ℕ)) else 1)
      = (∏ x : Fin (2 * K),
        if x.val % 2 = 0 then (-1 : ℂ) else 1) from
      Finset.prod_congr rfl (fun x _ => by
        by_cases hp : x.val % 2 = 0 <;> simp [hp])]
  exact prod_alternating_neg_one K

/-- 2D all-up Marshall sign: `+1`. -/
theorem marshallSignSquareConfig_const_zero (K L : ℕ) :
    marshallSignSquareConfig K L
        (fun _ : Fin (2 * K) × Fin (2 * L) => (0 : Fin 2)) = 1 := by
  unfold marshallSignSquareConfig
  apply Finset.prod_eq_one
  intro p _
  by_cases hp : (p.1.val + p.2.val) % 2 = 0 <;> simp [hp]

/-- 2D all-down Marshall sign: `+1` (since the even-A sublattice has
`2K · L = 2KL` sites — see proof — making `(-1)^(2KL) = 1`). -/
theorem marshallSignSquareConfig_const_one (K L : ℕ) :
    marshallSignSquareConfig K L
        (fun _ : Fin (2 * K) × Fin (2 * L) => (1 : Fin 2)) = 1 := by
  unfold marshallSignSquareConfig
  rw [show (∏ p : Fin (2 * K) × Fin (2 * L),
        if (p.1.val + p.2.val) % 2 = 0
          then ((-1 : ℂ) ^ ((1 : Fin 2) : ℕ)) else 1)
      = (∏ p : Fin (2 * K) × Fin (2 * L),
        if (p.1.val + p.2.val) % 2 = 0 then (-1 : ℂ) else 1) from
      Finset.prod_congr rfl (fun p _ => by
        by_cases hp : (p.1.val + p.2.val) % 2 = 0 <;> simp [hp])]
  rw [Fintype.prod_prod_type]
  have h_inner : ∀ i : Fin (2 * K),
      (∏ j : Fin (2 * L),
          if (i.val + j.val) % 2 = 0 then (-1 : ℂ) else 1) =
        (-1 : ℂ) ^ L := fun i => prod_alternating_neg_one_offset i.val L
  rw [Finset.prod_congr rfl (fun i _ => h_inner i)]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, show L * (2 * K) = 2 * (K * L) from by ring,
    pow_mul, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow]

/-- 3D all-up Marshall sign: `+1`. -/
theorem marshallSignCubicConfig_const_zero (K L M : ℕ) :
    marshallSignCubicConfig K L M
        (fun _ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) =>
          (0 : Fin 2)) = 1 := by
  unfold marshallSignCubicConfig
  apply Finset.prod_eq_one
  intro p _
  by_cases hp : (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
  · simp [hp]
  · simp [hp]

/-- 3D all-down Marshall sign: `+1` (since the cubic A-sublattice has
`4KLM` sites and `(-1)^(4KLM) = 1`). -/
theorem marshallSignCubicConfig_const_one (K L M : ℕ) :
    marshallSignCubicConfig K L M
        (fun _ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) =>
          (1 : Fin 2)) = 1 := by
  unfold marshallSignCubicConfig
  rw [show (∏ p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M),
        if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
          then ((-1 : ℂ) ^ ((1 : Fin 2) : ℕ)) else 1)
      = (∏ p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M),
        if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
          then (-1 : ℂ) else 1) from
      Finset.prod_congr rfl (fun p _ => by
        by_cases hp : (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
        · simp [hp]
        · simp [hp])]
  rw [Fintype.prod_prod_type]
  have h_inner : ∀ p : Fin (2 * K) × Fin (2 * L),
      (∏ k : Fin (2 * M),
          if (p.1.val + p.2.val + k.val) % 2 = 0 then (-1 : ℂ) else 1) =
        (-1 : ℂ) ^ M := fun p =>
    prod_alternating_neg_one_offset (p.1.val + p.2.val) M
  rw [Finset.prod_congr rfl (fun p _ => h_inner p)]
  rw [Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [← pow_mul,
    show M * (2 * K * (2 * L)) = 2 * (2 * K * L * M) from by ring,
    pow_mul, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow]

/-- The chain Marshall sign equals the generic `marshallSignOf`
applied to the even-parity sublattice indicator. -/
theorem marshallSignChainConfig_eq_marshallSignOf (K : ℕ)
    (σ : Fin (2 * K) → Fin 2) :
    marshallSignChainConfig K σ =
      marshallSignOf (fun x : Fin (2 * K) =>
        decide (x.val % 2 = 0)) σ := by
  unfold marshallSignChainConfig marshallSignOf
  refine Finset.prod_congr rfl (fun x _ => ?_)
  by_cases hp : x.val % 2 = 0 <;> simp [hp]

/-- The 2D Marshall sign equals the generic `marshallSignOf`
applied to the `(i + j)`-parity sublattice indicator. -/
theorem marshallSignSquareConfig_eq_marshallSignOf (K L : ℕ)
    (σ : Fin (2 * K) × Fin (2 * L) → Fin 2) :
    marshallSignSquareConfig K L σ =
      marshallSignOf
        (fun p : Fin (2 * K) × Fin (2 * L) =>
          decide ((p.1.val + p.2.val) % 2 = 0)) σ := by
  unfold marshallSignSquareConfig marshallSignOf
  refine Finset.prod_congr rfl (fun p _ => ?_)
  by_cases hp : (p.1.val + p.2.val) % 2 = 0 <;> simp [hp]

/-- The 3D Marshall sign equals the generic `marshallSignOf`
applied to the `(i + j + k)`-parity sublattice indicator. -/
theorem marshallSignCubicConfig_eq_marshallSignOf (K L M : ℕ)
    (σ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) :
    marshallSignCubicConfig K L M σ =
      marshallSignOf
        (fun p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) =>
          decide ((p.1.1.val + p.1.2.val + p.2.val) % 2 = 0)) σ := by
  unfold marshallSignCubicConfig marshallSignOf
  refine Finset.prod_congr rfl (fun p _ => ?_)
  by_cases hp : (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0 <;> simp [hp]

/-- Per-site Fin 2 identity used in the `flipConfig` Marshall sign
proofs: `(-1)^((1 - s).val) = (-1) · (-1)^s.val` for `s : Fin 2`.
At `s = 0`: `(-1)^1 = -1 = (-1) · 1 = (-1) · (-1)^0`; at `s = 1`:
`(-1)^0 = 1 = (-1) · (-1) = (-1) · (-1)^1`. -/
private lemma neg_one_pow_one_sub_fin_two (s : Fin 2) :
    ((-1 : ℂ) ^ ((1 - s).val : ℕ)) =
      (-1 : ℂ) * ((-1 : ℂ) ^ (s : ℕ)) := by
  fin_cases s
  · show ((-1 : ℂ) ^ ((1 - 0 : Fin 2).val : ℕ)) =
      (-1 : ℂ) * ((-1 : ℂ) ^ ((0 : Fin 2) : ℕ))
    simp
  · show ((-1 : ℂ) ^ ((1 - 1 : Fin 2).val : ℕ)) =
      (-1 : ℂ) * ((-1 : ℂ) ^ ((1 : Fin 2) : ℕ))
    simp

/-- Marshall sign under the global spin-flip on the chain:

  `marshallSignChainConfig K (flipConfig σ)
    = (-1)^K · marshallSignChainConfig K σ`.

Each of the `K` even-indexed sites contributes a factor of `-1`
under the flip, and these factor through via
`Finset.prod_mul_distrib` + `prod_alternating_neg_one`. -/
theorem marshallSignChainConfig_flipConfig (K : ℕ)
    (σ : Fin (2 * K) → Fin 2) :
    marshallSignChainConfig K (flipConfig σ) =
      ((-1 : ℂ) ^ K) * marshallSignChainConfig K σ := by
  unfold marshallSignChainConfig flipConfig
  rw [show (∏ x : Fin (2 * K),
        if x.val % 2 = 0 then ((-1 : ℂ) ^ ((1 - σ x).val : ℕ)) else 1)
      = (∏ x : Fin (2 * K),
        ((if x.val % 2 = 0 then (-1 : ℂ) else 1) *
         (if x.val % 2 = 0 then ((-1 : ℂ) ^ (σ x : ℕ)) else 1))) from ?_]
  · rw [Finset.prod_mul_distrib, prod_alternating_neg_one]
  · refine Finset.prod_congr rfl (fun x _ => ?_)
    by_cases hp : x.val % 2 = 0
    · simp only [hp, if_true, neg_one_pow_one_sub_fin_two]
    · simp [hp]

/-- 2D Marshall sign under the global spin-flip: factor is
`(-1)^(2KL) = 1`, so the sign is invariant. -/
theorem marshallSignSquareConfig_flipConfig (K L : ℕ)
    (σ : Fin (2 * K) × Fin (2 * L) → Fin 2) :
    marshallSignSquareConfig K L (flipConfig σ) =
      marshallSignSquareConfig K L σ := by
  unfold marshallSignSquareConfig flipConfig
  rw [show (∏ p : Fin (2 * K) × Fin (2 * L),
        if (p.1.val + p.2.val) % 2 = 0
          then ((-1 : ℂ) ^ ((1 - σ p).val : ℕ)) else 1)
      = (∏ p : Fin (2 * K) × Fin (2 * L),
        ((if (p.1.val + p.2.val) % 2 = 0 then (-1 : ℂ) else 1) *
         (if (p.1.val + p.2.val) % 2 = 0
          then ((-1 : ℂ) ^ (σ p : ℕ)) else 1))) from ?_]
  · rw [Finset.prod_mul_distrib]
    -- The sign-product `∏ (if even then -1 else 1)` equals `+1` via
    -- the row decomposition (column sums to (-1)^L, then ((-1)^L)^(2K) = 1).
    rw [show (∏ p : Fin (2 * K) × Fin (2 * L),
          if (p.1.val + p.2.val) % 2 = 0 then (-1 : ℂ) else 1)
        = (1 : ℂ) from ?_]
    · rw [one_mul]
    · rw [Fintype.prod_prod_type]
      have h_inner : ∀ i : Fin (2 * K),
          (∏ j : Fin (2 * L),
              if (i.val + j.val) % 2 = 0 then (-1 : ℂ) else 1) =
            (-1 : ℂ) ^ L := fun i =>
        prod_alternating_neg_one_offset i.val L
      rw [Finset.prod_congr rfl (fun i _ => h_inner i)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← pow_mul, show L * (2 * K) = 2 * (K * L) from by ring,
        pow_mul, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow]
  · refine Finset.prod_congr rfl (fun p _ => ?_)
    by_cases hp : (p.1.val + p.2.val) % 2 = 0
    · simp only [hp, if_true, neg_one_pow_one_sub_fin_two]
    · simp [hp]

/-- 3D Marshall sign under the global spin-flip: factor is
`(-1)^(4KLM) = 1`, so the sign is invariant. -/
theorem marshallSignCubicConfig_flipConfig (K L M : ℕ)
    (σ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) :
    marshallSignCubicConfig K L M (flipConfig σ) =
      marshallSignCubicConfig K L M σ := by
  unfold marshallSignCubicConfig flipConfig
  rw [show (∏ p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M),
        if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
          then ((-1 : ℂ) ^ ((1 - σ p).val : ℕ)) else 1)
      = (∏ p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M),
        ((if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
          then (-1 : ℂ) else 1) *
         (if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
          then ((-1 : ℂ) ^ (σ p : ℕ)) else 1))) from ?_]
  · rw [Finset.prod_mul_distrib]
    rw [show (∏ p : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M),
          if (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
            then (-1 : ℂ) else 1)
        = (1 : ℂ) from ?_]
    · rw [one_mul]
    · rw [Fintype.prod_prod_type]
      have h_inner : ∀ p : Fin (2 * K) × Fin (2 * L),
          (∏ k : Fin (2 * M),
              if (p.1.val + p.2.val + k.val) % 2 = 0
                then (-1 : ℂ) else 1) =
            (-1 : ℂ) ^ M := fun p =>
        prod_alternating_neg_one_offset (p.1.val + p.2.val) M
      rw [Finset.prod_congr rfl (fun p _ => h_inner p)]
      rw [Finset.prod_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
      rw [← pow_mul,
        show M * (2 * K * (2 * L)) = 2 * (2 * K * L * M) from by ring,
        pow_mul, show ((-1 : ℂ)) ^ 2 = 1 from by norm_num, one_pow]
  · refine Finset.prod_congr rfl (fun p _ => ?_)
    by_cases hp : (p.1.1.val + p.1.2.val + p.2.val) % 2 = 0
    · simp only [hp, if_true, neg_one_pow_one_sub_fin_two]
    · simp [hp]

/-- The Marshall-rotated chain basis state at configuration `σ`:
`|σ⟩_M := marshallSignChainConfig K σ · |σ⟩`. After the basis
change `|σ⟩ ↦ |σ⟩_M`, the AF Heisenberg Hamiltonian on the
bipartite chain has all non-positive off-diagonal entries — the
input to the Perron-Frobenius proof of MLM (Tasaki §2.5). -/
noncomputable def marshallChainState (K : ℕ)
    (σ : Fin (2 * K) → Fin 2) : (Fin (2 * K) → Fin 2) → ℂ :=
  marshallSignChainConfig K σ • basisVec σ

/-- The Marshall-rotated Néel chain state coincides with the
Néel chain state itself (since `marshallSignChainConfig K
(neelChainConfig K) = 1`). -/
theorem marshallChainState_neelChainConfig (K : ℕ) :
    marshallChainState K (neelChainConfig K) = neelChainState K := by
  unfold marshallChainState neelChainState
  rw [marshallSignChainConfig_neelChainConfig, one_smul]

/-- 2D Marshall-rotated checkerboard state. -/
noncomputable def marshallSquareState (K L : ℕ)
    (σ : Fin (2 * K) × Fin (2 * L) → Fin 2) :
    (Fin (2 * K) × Fin (2 * L) → Fin 2) → ℂ :=
  marshallSignSquareConfig K L σ • basisVec σ

/-- The Marshall-rotated 2D Néel state coincides with the 2D
Néel state itself. -/
theorem marshallSquareState_neelSquareConfig (K L : ℕ) :
    marshallSquareState K L (neelSquareConfig K L) =
      neelSquareState K L := by
  unfold marshallSquareState neelSquareState
  rw [marshallSignSquareConfig_neelSquareConfig, one_smul]

/-- 3D cubic Marshall-rotated checkerboard state. -/
noncomputable def marshallCubicState (K L M : ℕ)
    (σ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) :
    ((Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2) → ℂ :=
  marshallSignCubicConfig K L M σ • basisVec σ

/-- The Marshall-rotated 3D cubic Néel state coincides with the
3D cubic Néel state itself. -/
theorem marshallCubicState_neelCubicConfig (K L M : ℕ) :
    marshallCubicState K L M (neelCubicConfig K L M) =
      neelCubicState K L M := by
  unfold marshallCubicState neelCubicState
  rw [marshallSignCubicConfig_neelCubicConfig, one_smul]

/-! ## Marshall × time-reversal bridge on the Néel state -/

/-- Marshall sign of the *flipped* Néel chain configuration:
`marshallSignChainConfig K (flipConfig (neelChainConfig K)) = (-1)^K`.
Combines `_flipConfig` (factor `(-1)^K`) and `_neelChainConfig`
(base sign `+1`). -/
theorem marshallSignChainConfig_flipConfig_neelChainConfig (K : ℕ) :
    marshallSignChainConfig K (flipConfig (neelChainConfig K)) =
      (-1 : ℂ) ^ K := by
  rw [marshallSignChainConfig_flipConfig,
    marshallSignChainConfig_neelChainConfig, mul_one]

/-- 2D Marshall sign of the flipped Néel configuration: `+1`
(`flipConfig` invariance + base `+1`). -/
theorem marshallSignSquareConfig_flipConfig_neelSquareConfig (K L : ℕ) :
    marshallSignSquareConfig K L (flipConfig (neelSquareConfig K L)) = 1 := by
  rw [marshallSignSquareConfig_flipConfig,
    marshallSignSquareConfig_neelSquareConfig]

/-- 3D Marshall sign of the flipped Néel configuration: `+1`
(`flipConfig` invariance + base `+1`). -/
theorem marshallSignCubicConfig_flipConfig_neelCubicConfig
    (K L M : ℕ) :
    marshallSignCubicConfig K L M
        (flipConfig (neelCubicConfig K L M)) = 1 := by
  rw [marshallSignCubicConfig_flipConfig,
    marshallSignCubicConfig_neelCubicConfig]

/-- The Marshall-rotated *flipped* Néel chain state equals the
time-reversed Néel chain state:

  `marshallChainState K (flipConfig (neelChainConfig K))
    = Θ̂_tot · neelChainState K`.

Both sides equal `(-1)^K · basisVec (flipConfig (neelChainConfig K))`. -/
theorem marshallChainState_flipConfig_eq_timeReversalSpinHalfMulti
    (K : ℕ) :
    marshallChainState K (flipConfig (neelChainConfig K)) =
      timeReversalSpinHalfMulti (neelChainState K) := by
  unfold marshallChainState
  rw [marshallSignChainConfig_flipConfig_neelChainConfig,
    timeReversalSpinHalfMulti_neelChainState]

/-- The Marshall-rotated *flipped* 2D Néel state equals the
time-reversed 2D Néel state. -/
theorem marshallSquareState_flipConfig_eq_timeReversalSpinHalfMulti
    (K L : ℕ) :
    marshallSquareState K L (flipConfig (neelSquareConfig K L)) =
      timeReversalSpinHalfMulti (neelSquareState K L) := by
  unfold marshallSquareState
  rw [marshallSignSquareConfig_flipConfig_neelSquareConfig, one_smul,
    timeReversalSpinHalfMulti_neelSquareState]

/-- The Marshall-rotated *flipped* 3D cubic Néel state equals the
time-reversed 3D Néel state. -/
theorem marshallCubicState_flipConfig_eq_timeReversalSpinHalfMulti
    (K L M : ℕ) :
    marshallCubicState K L M (flipConfig (neelCubicConfig K L M)) =
      timeReversalSpinHalfMulti (neelCubicState K L M) := by
  unfold marshallCubicState
  rw [marshallSignCubicConfig_flipConfig_neelCubicConfig, one_smul,
    timeReversalSpinHalfMulti_neelCubicState]

/-! ## Néel state norm² = 1 (orthonormality of the basis vectors) -/

/-- 1D Néel chain state norm² = 1: `∑ τ, |Φ_Néel(τ)|² = 1`. Direct
consequence of `basisVec_inner` (orthonormality of basis vectors)
since `neelChainState K = basisVec (neelChainConfig K)`. -/
theorem neelChainState_norm_squared (K : ℕ) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ * neelChainState K τ = 1 := by
  unfold neelChainState
  rw [basisVec_inner]
  simp

/-- 2D Néel state norm² = 1. -/
theorem neelSquareState_norm_squared (K L : ℕ) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ * neelSquareState K L τ = 1 := by
  unfold neelSquareState
  rw [basisVec_inner]
  simp

/-- 3D cubic Néel state norm² = 1. -/
theorem neelCubicState_norm_squared (K L M : ℕ) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ * neelCubicState K L M τ = 1 := by
  unfold neelCubicState
  rw [basisVec_inner]
  simp

/-! ## Néel-state inner product against the swapped basis vector -/

/-- Orthogonality: the 1D Néel state is orthogonal to the swapped
basis vector at any adjacent (antiparallel) bond. Direct
consequence of `basisVec_inner` + `basisSwap_ne_self`
(swap of antiparallel pair changes the configuration). -/
theorem neelChainState_inner_basisVec_basisSwap_adjacent_eq_zero
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          basisVec (basisSwap (neelChainConfig K)
            (⟨i, by omega⟩ : Fin (2 * K)) ⟨i + 1, hi⟩) τ = 0 := by
  unfold neelChainState
  rw [basisVec_inner]
  rw [if_neg]
  apply basisSwap_ne_self
  · intro h
    have := congrArg Fin.val h
    simp at this
  · unfold neelChainConfig
    by_cases hp : i % 2 = 0
    · have hp1 : (i + 1) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + 1) % 2 = 0 := by omega
      simp [hp, hp1]

/-! ## Per-bond expectation `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = -1/4`

Combining the per-bond action (#23x: `spinHalfDot_mulVec_neelChain
State_adjacent`) with the orthogonality `⟨Φ_Néel, basisVec(swap)⟩
= 0` gives the bond expectation `-1/4` (Tasaki §2.5 (2.5.4)
ingredient). -/

/-- 1D Néel chain: per-adjacent-bond expectation of `Ŝ_x · Ŝ_y`
equals `-1/4`. -/
theorem neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((spinHalfDot
              (⟨i, by omega⟩ : Fin (2 * K))
              (⟨i + 1, hi⟩ : Fin (2 * K))).mulVec
            (neelChainState K)) τ = -(1 / 4 : ℂ) := by
  have h := spinHalfDot_mulVec_neelChainState_adjacent K hi
  simp_rw [h]
  simp_rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
  rw [Finset.sum_sub_distrib]
  simp_rw [show ∀ τ : Fin (2 * K) → Fin 2,
      neelChainState K τ * ((1 / 2 : ℂ) * basisVec
        (basisSwap (neelChainConfig K)
          (⟨i, by omega⟩ : Fin (2 * K))
          (⟨i + 1, hi⟩ : Fin (2 * K))) τ)
        = (1 / 2 : ℂ) *
          (neelChainState K τ *
            basisVec (basisSwap (neelChainConfig K)
              (⟨i, by omega⟩ : Fin (2 * K))
              (⟨i + 1, hi⟩ : Fin (2 * K))) τ) from fun τ => by ring]
  simp_rw [show ∀ τ : Fin (2 * K) → Fin 2,
      neelChainState K τ * ((1 / 4 : ℂ) * neelChainState K τ)
        = (1 / 4 : ℂ) *
          (neelChainState K τ * neelChainState K τ) from
      fun τ => by ring]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [neelChainState_inner_basisVec_basisSwap_adjacent_eq_zero K hi,
    neelChainState_norm_squared]
  ring

/-- 1D Néel chain: per-wrap-bond expectation
`⟨Φ_Néel(K+1), Ŝ_⟨2K+1⟩ · Ŝ_⟨0⟩ · Φ_Néel(K+1)⟩ = -1/4`. -/
theorem neelChainState_inner_spinHalfDot_wrap_eq_neg_one_quarter
    (K : ℕ) :
    ∑ τ : Fin (2 * (K + 1)) → Fin 2,
        neelChainState (K + 1) τ *
          ((spinHalfDot
              (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
              (⟨0, by omega⟩ : Fin (2 * (K + 1)))).mulVec
            (neelChainState (K + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelChainState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · unfold neelChainConfig
    have h1 : (2 * K + 1) % 2 = 1 := by omega
    simp [h1]

/-- 2D Néel: horizontal adjacent bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_horizontal_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((spinHalfDot
              ((⟨i, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L))
              ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L))).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    by_cases hp : (i + j) % 2 = 0
    · have hp1 : ((i + 1) + j) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 2D Néel: vertical adjacent bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_vertical_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((spinHalfDot
              ((⟨i, hi⟩, ⟨j, by omega⟩) :
                Fin (2 * K) × Fin (2 * L))
              ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
                Fin (2 * K) × Fin (2 * L))).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    by_cases hp : (i + j) % 2 = 0
    · have hp1 : (i + (j + 1)) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + (j + 1)) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 2D Néel: horizontal wrap bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_horizontal_wrap_eq_neg_one_quarter
    (K L : ℕ) {j : ℕ} (hj : j < 2 * L) :
    ∑ τ : Fin (2 * (K + 1)) × Fin (2 * L) → Fin 2,
        neelSquareState (K + 1) L τ *
          ((spinHalfDot
              ((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L))
              ((⟨0, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L))).mulVec
            (neelSquareState (K + 1) L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
    · have h1 : (2 * K + 1 + j) % 2 ≠ 0 := by omega
      simp [h1, hj0]
    · have h4 : (2 * K + 1 + j) % 2 = 0 := by omega
      simp [h4, hj1]

/-- 2D Néel: vertical wrap bond expectation = -1/4. -/
theorem neelSquareState_inner_spinHalfDot_vertical_wrap_eq_neg_one_quarter
    (K L : ℕ) {i : ℕ} (hi : i < 2 * K) :
    ∑ τ : Fin (2 * K) × Fin (2 * (L + 1)) → Fin 2,
        neelSquareState K (L + 1) τ *
          ((spinHalfDot
              ((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1)))
              ((⟨i, hi⟩, ⟨0, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1)))).mulVec
            (neelSquareState K (L + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have := congrArg Prod.snd h
    have hval := congrArg Fin.val this
    simp at hval
  · unfold neelSquareConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one i with hi0 | hi1
    · have h1 : (i + (2 * L + 1)) % 2 ≠ 0 := by omega
      simp [h1, hi0]
    · have h1 : (i + (2 * L + 1)) % 2 = 0 := by omega
      simp [h1, hi1]

/-- 3D Néel: x-axis adjacent bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_x_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((spinHalfDot
              (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
              (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : ((i + 1) + j + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D Néel: y-axis adjacent bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_y_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
              (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + (j + 1) + k) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + (j + 1) + k) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D Néel: z-axis adjacent bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_z_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) (hk : k + 1 < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · unfold neelCubicConfig
    simp only
    by_cases hp : (i + j + k) % 2 = 0
    · have hp1 : (i + j + (k + 1)) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + j + (k + 1)) % 2 = 0 := by omega
      simp [hp, hp1]

/-- 3D Néel: x-axis wrap bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_x_wrap_eq_neg_one_quarter
    (K L M : ℕ) {j k : ℕ}
    (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState (K + 1) L M τ *
          ((spinHalfDot
              (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
              (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))).mulVec
            (neelCubicState (K + 1) L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.fst h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (j + k) with hjk0 | hjk1
    · have h1 : (2 * K + 1 + j + k) % 2 ≠ 0 := by omega
      simp [h1, hjk0]
    · have h1 : (2 * K + 1 + j + k) % 2 = 0 := by omega
      simp [h1, hjk1]

/-- 3D Néel: y-axis wrap bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_y_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i k : ℕ}
    (hi : i < 2 * K) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M) → Fin 2,
        neelCubicState K (L + 1) M τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
              (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))).mulVec
            (neelCubicState K (L + 1) M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h1
    have hval := congrArg Fin.val h2
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (i + k) with hik0 | hik1
    · have h1 : (i + (2 * L + 1) + k) % 2 ≠ 0 := by omega
      simp [h1, hik0]
    · have h1 : (i + (2 * L + 1) + k) % 2 = 0 := by omega
      simp [h1, hik1]

/-! ## S^z S^z spin-spin correlation on the Néel state -/

/-- 1D Néel chain: per-adjacent-bond `Ŝ^(3)_x · Ŝ^(3)_y`
correlation:

  `⟨Φ_Néel, Ŝ^(3)_x · Ŝ^(3)_y · Φ_Néel⟩ = -1/4`

(diagonal `Ŝ^z·Ŝ^z` correlator at antiparallel bond). -/
theorem neelChainState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_adjacent_eq_neg_one_quarter
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((onSite (⟨i, by omega⟩ : Fin (2 * K)) spinHalfOp3 *
              onSite (⟨i + 1, hi⟩ : Fin (2 * K))
                spinHalfOp3).mulVec
            (neelChainState K)) τ = -(1 / 4 : ℂ) := by
  unfold neelChainState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelChainConfig spinHalfSign
  by_cases hp : i % 2 = 0
  · have hp1 : (i + 1) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + 1) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 1D Néel chain wrap-bond `Ŝ^(3)_x · Ŝ^(3)_y` correlation =
`-1/4`. -/
theorem neelChainState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_wrap_eq_neg_one_quarter
    (K : ℕ) :
    ∑ τ : Fin (2 * (K + 1)) → Fin 2,
        neelChainState (K + 1) τ *
          ((onSite (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
                spinHalfOp3 *
              onSite (⟨0, by omega⟩ : Fin (2 * (K + 1)))
                spinHalfOp3).mulVec
            (neelChainState (K + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelChainState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelChainConfig spinHalfSign
  have h1 : (2 * K + 1) % 2 = 1 := by omega
  simp [h1]; ring

/-- 2D Néel: horizontal adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_horizontal_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((onSite ((⟨i, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3 *
              onSite ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  by_cases hp : (i + j) % 2 = 0
  · have hp1 : ((i + 1) + j) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : ((i + 1) + j) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 2D Néel: vertical adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_vertical_adjacent_eq_neg_one_quarter
    (K L : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) :
    ∑ τ : Fin (2 * K) × Fin (2 * L) → Fin 2,
        neelSquareState K L τ *
          ((onSite ((⟨i, hi⟩, ⟨j, by omega⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3 *
              onSite ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
                Fin (2 * K) × Fin (2 * L)) spinHalfOp3).mulVec
            (neelSquareState K L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  by_cases hp : (i + j) % 2 = 0
  · have hp1 : (i + (j + 1)) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + (j + 1)) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 2D Néel: horizontal wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_horizontal_wrap_eq_neg_one_quarter
    (K L : ℕ) {j : ℕ} (hj : j < 2 * L) :
    ∑ τ : Fin (2 * (K + 1)) × Fin (2 * L) → Fin 2,
        neelSquareState (K + 1) L τ *
          ((onSite ((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L)) spinHalfOp3 *
              onSite ((⟨0, by omega⟩, ⟨j, hj⟩) :
                Fin (2 * (K + 1)) × Fin (2 * L)) spinHalfOp3).mulVec
            (neelSquareState (K + 1) L)) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one j with hj0 | hj1
  · have h1 : (2 * K + 1 + j) % 2 ≠ 0 := by omega
    simp [h1, hj0]; ring
  · have h4 : (2 * K + 1 + j) % 2 = 0 := by omega
    simp [h4, hj1]; ring

/-- 2D Néel: vertical wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelSquareState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_vertical_wrap_eq_neg_one_quarter
    (K L : ℕ) {i : ℕ} (hi : i < 2 * K) :
    ∑ τ : Fin (2 * K) × Fin (2 * (L + 1)) → Fin 2,
        neelSquareState K (L + 1) τ *
          ((onSite ((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1))) spinHalfOp3 *
              onSite ((⟨i, hi⟩, ⟨0, by omega⟩) :
                Fin (2 * K) × Fin (2 * (L + 1))) spinHalfOp3).mulVec
            (neelSquareState K (L + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelSquareState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelSquareConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one i with hi0 | hi1
  · have h1 : (i + (2 * L + 1)) % 2 ≠ 0 := by omega
    simp [h1, hi0]; ring
  · have h1 : (i + (2 * L + 1)) % 2 = 0 := by omega
    simp [h1, hi1]; ring

/-- 3D Néel: x adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_x_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((onSite (((⟨i, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i + 1, hi⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  by_cases hp : (i + j + k) % 2 = 0
  · have hp1 : ((i + 1) + j + k) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : ((i + 1) + j + k) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 3D Néel: y adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_y_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((onSite (((⟨i, hi⟩, ⟨j, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨j + 1, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  by_cases hp : (i + j + k) % 2 = 0
  · have hp1 : (i + (j + 1) + k) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + (j + 1) + k) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 3D Néel: z adjacent `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_z_adjacent_eq_neg_one_quarter
    (K L M : ℕ) {i j k : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) (hk : k + 1 < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState K L M τ *
          ((onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨k + 1, hk⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  by_cases hp : (i + j + k) % 2 = 0
  · have hp1 : (i + j + (k + 1)) % 2 ≠ 0 := by omega
    simp [hp, hp1]; ring
  · have hp1 : (i + j + (k + 1)) % 2 = 0 := by omega
    simp [hp, hp1]; ring

/-- 3D Néel: x wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_x_wrap_eq_neg_one_quarter
    (K L M : ℕ) {j k : ℕ}
    (hj : j < 2 * L) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M) → Fin 2,
        neelCubicState (K + 1) L M τ *
          ((onSite (((⟨2 * K + 1, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨0, by omega⟩, ⟨j, hj⟩), ⟨k, hk⟩) :
                (Fin (2 * (K + 1)) × Fin (2 * L)) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState (K + 1) L M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one (j + k) with hjk0 | hjk1
  · have h1 : (2 * K + 1 + j + k) % 2 ≠ 0 := by omega
    simp [h1, hjk0]; ring
  · have h1 : (2 * K + 1 + j + k) % 2 = 0 := by omega
    simp [h1, hjk1]; ring

/-- 3D Néel: y wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_y_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i k : ℕ}
    (hi : i < 2 * K) (hk : k < 2 * M) :
    ∑ τ : (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M) → Fin 2,
        neelCubicState K (L + 1) M τ *
          ((onSite (((⟨i, hi⟩, ⟨2 * L + 1, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨0, by omega⟩), ⟨k, hk⟩) :
                (Fin (2 * K) × Fin (2 * (L + 1))) × Fin (2 * M))
                spinHalfOp3).mulVec
            (neelCubicState K (L + 1) M)) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one (i + k) with hik0 | hik1
  · have h1 : (i + (2 * L + 1) + k) % 2 ≠ 0 := by omega
    simp [h1, hik0]; ring
  · have h1 : (i + (2 * L + 1) + k) % 2 = 0 := by omega
    simp [h1, hik1]; ring

/-- 3D Néel: z wrap `Ŝ^(3)_x · Ŝ^(3)_y` = -1/4. -/
theorem neelCubicState_inner_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_z_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)) → Fin 2,
        neelCubicState K L (M + 1) τ *
          ((onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
                spinHalfOp3 *
              onSite (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
                spinHalfOp3).mulVec
            (neelCubicState K L (M + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  rw [inner_basisVec_onSite_spinHalfOp3_mul_onSite_spinHalfOp3_basisVec]
  unfold neelCubicConfig spinHalfSign
  simp only
  rcases Nat.mod_two_eq_zero_or_one (i + j) with hij0 | hij1
  · have h1 : (i + j + (2 * M + 1)) % 2 ≠ 0 := by omega
    simp [h1, hij0]; ring
  · have h1 : (i + j + (2 * M + 1)) % 2 = 0 := by omega
    simp [h1, hij1]; ring

/-! ## Off-diagonal correlator (Ŝ^x · Ŝ^x + Ŝ^y · Ŝ^y) on Néel -/

/-- 1D Néel chain: per-adjacent-bond off-diagonal correlator
`(Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y)` vanishes:

  `⟨Φ_Néel, (Ŝ_x · Ŝ_y - Ŝ^(3)_x · Ŝ^(3)_y) · Φ_Néel⟩ = 0`.

Direct from the generic
`inner_basisVec_spinHalfDot_sub_szsz_basisVec_antiparallel`. The
off-diagonal part is entirely supported on swap states. -/
theorem neelChainState_inner_off_diagonal_correlator_adjacent_eq_zero
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((spinHalfDot
              (⟨i, by omega⟩ : Fin (2 * K))
              (⟨i + 1, hi⟩ : Fin (2 * K)) -
              (onSite (⟨i, by omega⟩ : Fin (2 * K))
                  spinHalfOp3 *
                onSite (⟨i + 1, hi⟩ : Fin (2 * K))
                  spinHalfOp3) :
              ManyBodyOp (Fin (2 * K))).mulVec
            (neelChainState K)) τ = 0 := by
  unfold neelChainState
  apply inner_basisVec_spinHalfDot_sub_szsz_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · unfold neelChainConfig
    by_cases hp : i % 2 = 0
    · have hp1 : (i + 1) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + 1) % 2 = 0 := by omega
      simp [hp, hp1]

/-! ## Parallel-bond expectation `+1/4` on the Néel chain -/

/-- 1D Néel chain: same-sublattice (parallel) `Ŝ_x · Ŝ_y`
expectation:

  `⟨Φ_Néel, Ŝ_x · Ŝ_y · Φ_Néel⟩ = +1/4`

for any pair `x ≠ y` with the same parity (`x.val % 2 = y.val % 2`).
For example, `(0, 2)` (both even, both `↑`) or `(1, 3)` (both
odd, both `↓`). Direct from the generic
`inner_basisVec_spinHalfDot_basisVec_parallel`. -/
theorem neelChainState_inner_spinHalfDot_parallel_eq_one_quarter
    (K : ℕ) {x y : Fin (2 * K)} (hxy : x ≠ y)
    (h_par : x.val % 2 = y.val % 2) :
    ∑ τ : Fin (2 * K) → Fin 2,
        neelChainState K τ *
          ((spinHalfDot x y).mulVec (neelChainState K)) τ =
      (1 / 4 : ℂ) := by
  unfold neelChainState
  apply inner_basisVec_spinHalfDot_basisVec_parallel hxy
  unfold neelChainConfig
  by_cases hp : x.val % 2 = 0
  · have hp1 : y.val % 2 = 0 := h_par ▸ hp
    simp [hp, hp1]
  · have hp1 : y.val % 2 ≠ 0 := h_par ▸ hp
    simp [hp, hp1]

/-! ## Heisenberg energy expectation on the Néel state -/

/-- 1D Néel chain at `K = 1` (2-site open chain): the Heisenberg
energy expectation equals `J/2`:

  `⟨Φ_Néel(K=1), H_open(N=1, J) · Φ_Néel(K=1)⟩ = J/2`.

Combines `openChainHeisenbergHamiltonian_two_site_eq`
(`H = -2J · spinHalfDot 0 1`) with the per-bond expectation
`-1/4` from `neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter`,
giving `-2J · (-1/4) = J/2` (positive for `J > 0`, consistent with
the convention `H = -2J Σ S·S` where `J > 0` is ferromagnetic and
the Néel state is a high-energy variational ansatz). -/
theorem neelChainState_energy_expectation_K1 (J : ℝ) :
    ∑ τ : Fin 2 → Fin 2,
        neelChainState 1 τ *
          ((heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
            (neelChainState 1)) τ = (J / 2 : ℂ) := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  -- ∑ τ, v τ * ((-2J) • (M.mulVec v)) τ = (-2J) · ∑ τ, v τ * (M.mulVec v) τ
  simp_rw [Pi.smul_apply, smul_eq_mul]
  simp_rw [show ∀ τ : Fin 2 → Fin 2,
      neelChainState 1 τ *
        ((-(2 * J) : ℂ) *
          (Matrix.mulVec (spinHalfDot (0 : Fin 2) 1)
            (neelChainState 1)) τ) =
      (-(2 * J) : ℂ) *
        (neelChainState 1 τ *
          (Matrix.mulVec (spinHalfDot (0 : Fin 2) 1)
            (neelChainState 1)) τ) from
      fun τ => by ring]
  rw [← Finset.mul_sum]
  -- Apply the per-bond expectation = -1/4 (with i = 0)
  have h : ∑ τ : Fin (2 * 1) → Fin 2, neelChainState 1 τ *
      ((spinHalfDot (⟨0, by decide⟩ : Fin (2 * 1))
          (⟨0 + 1, by decide⟩ : Fin (2 * 1))).mulVec
        (neelChainState 1)) τ = -(1 / 4 : ℂ) :=
    neelChainState_inner_spinHalfDot_adjacent_eq_neg_one_quarter 1
      (by decide)
  -- Identify (⟨0, _⟩ : Fin (2 * 1)) with (0 : Fin 2)
  -- Both reduce to the same Fin 2 element
  show (-(2 * J) : ℂ) *
      (∑ τ : Fin 2 → Fin 2, neelChainState 1 τ *
        (Matrix.mulVec (spinHalfDot (0 : Fin 2) (1 : Fin 2))
          (neelChainState 1)) τ) =
    (J / 2 : ℂ)
  have hzero : (⟨0, by decide⟩ : Fin (2 * 1)) = (0 : Fin 2) := rfl
  have hone : (⟨0 + 1, by decide⟩ : Fin (2 * 1)) = (1 : Fin 2) := rfl
  rw [hzero, hone] at h
  rw [h]
  push_cast
  ring

/-- 3D Néel: z-axis wrap bond expectation = -1/4. -/
theorem neelCubicState_inner_spinHalfDot_z_wrap_eq_neg_one_quarter
    (K L M : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j < 2 * L) :
    ∑ τ : (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)) → Fin 2,
        neelCubicState K L (M + 1) τ *
          ((spinHalfDot
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨2 * M + 1, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))
              (((⟨i, hi⟩, ⟨j, hj⟩), ⟨0, by omega⟩) :
                (Fin (2 * K) × Fin (2 * L)) × Fin (2 * (M + 1)))).mulVec
            (neelCubicState K L (M + 1))) τ = -(1 / 4 : ℂ) := by
  unfold neelCubicState
  apply inner_basisVec_spinHalfDot_basisVec_antiparallel
  · intro h
    have h1 := congrArg Prod.snd h
    have hval := congrArg Fin.val h1
    simp at hval
  · unfold neelCubicConfig
    simp only
    rcases Nat.mod_two_eq_zero_or_one (i + j) with hij0 | hij1
    · have h1 : (i + j + (2 * M + 1)) % 2 ≠ 0 := by omega
      simp [h1, hij0]
    · have h1 : (i + j + (2 * M + 1)) % 2 = 0 := by omega
      simp [h1, hij1]

end LatticeSystem.Quantum
