/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.Definition
import LatticeSystem.Quantum.NeelState.Definition2D
import LatticeSystem.Quantum.NeelState.Definition3D
import LatticeSystem.Quantum.TimeReversalMulti
import LatticeSystem.Quantum.TimeReversalMulti.Heisenberg

/-!
# Time-reversal action on the Néel state (Tasaki §2.3 ↔ §2.5)

The multi-spin time-reversal `Θ̂_tot` (Tasaki §2.3) acts on the
1D / 2D / 3D Néel states by sending them to a sign-decorated
`flipConfig`-image:

  `Θ̂_tot (neelChainState K) = (-1)^K · basisVec (flipConfig (neelChainConfig K))`,
  `Θ̂_tot (neelSquareState K L) = basisVec (flipConfig (neelSquareConfig K L))`,
  `Θ̂_tot (neelCubicState K L M) = basisVec (flipConfig (neelCubicConfig K L M))`.

The 1D sign factor `(-1)^K` is captured by the helper
`prod_alternating_neg_one`. The 2D and 3D cases give `+1` because
the sublattice site counts are even (`(-1)^(2KL) = (-1)^(4KLM) = 1`).

(Refactor Phase 2 PR 7 — seventh step of the NeelState 7-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

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

end LatticeSystem.Quantum
