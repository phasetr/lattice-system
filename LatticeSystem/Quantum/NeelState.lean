/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MagnetizationSubspace

/-!
# Néel state on a bipartite even chain (Tasaki §2.5)

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
§2.5 eq. (2.5.2), p. 37 defines the **Néel state** on a bipartite
lattice `Λ = A ⊔ B` (with sublattices `A` and `B`) for spin `S`:

  `|Φ_Néel⟩ := (⊗_{x ∈ A} |ψ_x^S⟩) ⊗ (⊗_{y ∈ B} |ψ_y^{-S}⟩)`.

For a bipartite lattice with `|A| = |B|`, the Néel state lies in
the zero-magnetization sector `H_0` (Tasaki §2.2 (2.2.10)) since
the contributions from `A` (each `+S`) and `B` (each `-S`) cancel.

This module formalises the `S = 1/2` case on the natural bipartite
chain `Fin (2 * K)` (vertices alternately coloured `A` = even
indices, `B` = odd indices). The Néel configuration is
`σ_x := if x.val is even then ↑ else ↓`. We prove:

* `neelChainConfig_magnetization_zero` — the configuration has
  total magnetisation `0`;
* `neelChainState_mem_magnetizationSubspace_zero` — the
  corresponding basis vector lies in the `Ŝ_tot^(3) = 0`
  eigenspace.

Strict bipartite-graph machinery (`SimpleGraph.IsBipartite`) is
not invoked here: the alternating two-colouring on `Fin (2 * K)`
is built directly from index parity, which suffices for the
S = 1/2 chain. Lifting to general bipartite graphs `(Λ, B)` with
`|A| = |B|` is deferred and would build on
`SimpleGraph.IsBipartiteWith` from Mathlib.
-/

namespace LatticeSystem.Quantum

open Matrix LatticeSystem.Quantum

/-- The Néel chain configuration on `Fin (2 * K)`: the alternating
two-colouring assigning `↑ : Fin 2 := 0` to even indices and
`↓ : Fin 2 := 1` to odd indices. -/
def neelChainConfig (K : ℕ) : Fin (2 * K) → Fin 2 :=
  fun i => if i.val % 2 = 0 then 0 else 1

/-- The Néel chain state on `Fin (2 * K)` for `S = 1/2`: the
many-body basis vector for the alternating up/down configuration
(Tasaki §2.5 eq. (2.5.2) at `S = 1/2`). -/
noncomputable def neelChainState (K : ℕ) :
    (Fin (2 * K) → Fin 2) → ℂ :=
  basisVec (neelChainConfig K)

/-- Auxiliary parity-sum lemma. The alternating sum
`∑ i : Fin (2 * K), (if i.val % 2 = 0 then 1 else -1)` vanishes,
since each adjacent pair `(2k, 2k+1)` contributes `1 + (-1) = 0`.
Proof by induction on `K`, peeling off the last two indices via
`Fin.sum_univ_castSucc`. -/
private lemma sum_alternating_sign (K : ℕ) :
    (∑ i : Fin (2 * K), (if i.val % 2 = 0 then (1 : ℤ) else -1))
      = 0 := by
  induction K with
  | zero => simp
  | succ K' ih =>
    rw [show 2 * (K' + 1) = (2 * K' + 1) + 1 from by ring]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h_last_outer_neg :
        (if (Fin.last (2 * K' + 1)).val % 2 = 0 then (1 : ℤ) else -1)
          = -1 := by
      have h1 : (Fin.last (2 * K' + 1)).val = 2 * K' + 1 := rfl
      rw [h1, show (2 * K' + 1) % 2 = 1 from by omega]
      norm_num
    have h_last_inner_pos :
        (if ((Fin.last (2 * K')).castSucc :
            Fin (2 * K' + 1 + 1)).val % 2 = 0
          then (1 : ℤ) else -1) = 1 := by
      have h1 : ((Fin.last (2 * K')).castSucc :
          Fin (2 * K' + 1 + 1)).val = 2 * K' := rfl
      rw [h1, show (2 * K') % 2 = 0 from by omega]
      norm_num
    have h_inner_eq :
        (∑ i : Fin (2 * K'),
          if (i.castSucc.castSucc : Fin (2 * K' + 1 + 1)).val % 2 = 0
            then (1 : ℤ) else -1)
        = ∑ i : Fin (2 * K'),
            (if i.val % 2 = 0 then (1 : ℤ) else -1) := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    rw [h_inner_eq, h_last_inner_pos, h_last_outer_neg, ih]
    ring

/-- The Néel chain configuration has zero total magnetisation:
half the sites carry `+1`, half carry `-1`. -/
theorem neelChainConfig_magnetization_zero (K : ℕ) :
    magnetization (Fin (2 * K)) (neelChainConfig K) = 0 := by
  unfold magnetization neelChainConfig spinSign
  have h_inner : ∀ i : Fin (2 * K),
      (if (if i.val % 2 = 0 then (0 : Fin 2) else 1) = 0
        then (1 : ℤ) else -1)
        = (if i.val % 2 = 0 then (1 : ℤ) else -1) := by
    intro i
    by_cases hp : i.val % 2 = 0
    · simp [hp]
    · simp [hp]
  simp_rw [h_inner]
  exact sum_alternating_sign K

/-- The Néel chain state lies in the zero-magnetisation sector
`H_0 = ker(Ŝ_tot^(3))`. Specialisation to `S = 1/2` and the
parity-coloured chain `Fin (2 * K)` of Tasaki §2.5 eq. (2.5.2). -/
theorem neelChainState_mem_magnetizationSubspace_zero (K : ℕ) :
    neelChainState K ∈
      magnetizationSubspace (Fin (2 * K)) (0 : ℂ) := by
  unfold neelChainState
  have h := basisVec_mem_magnetizationSubspace
    (Λ := Fin (2 * K)) (neelChainConfig K)
  rw [neelChainConfig_magnetization_zero] at h
  simpa using h

end LatticeSystem.Quantum
