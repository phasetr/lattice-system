/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MagnetizationSubspace
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.HeisenbergChain
import LatticeSystem.Quantum.TimeReversalMulti

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

/-- For any Heisenberg-type coupling `J : Fin (2*K) → Fin (2*K) → ℂ`,
the action of `H = heisenbergHamiltonian J` on the Néel chain state
again lies in the zero-magnetisation sector `H_0`. This is an
immediate corollary of the SU(2) invariance
`heisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem`
(Tasaki §2.2 eq. (2.2.13), p. 23) applied to the Néel state in
`H_0` (Tasaki §2.5 eq. (2.5.2), p. 37). The Néel state is *not*
itself an eigenstate (Tasaki §2.5 (2.5.3)), but it cannot leak
into other magnetisation sectors. -/
theorem heisenbergHamiltonian_mulVec_neelChainState_mem_magnetizationSubspace_zero
    (K : ℕ) (J : Fin (2 * K) → Fin (2 * K) → ℂ) :
    (heisenbergHamiltonian J).mulVec (neelChainState K) ∈
      magnetizationSubspace (Fin (2 * K)) (0 : ℂ) :=
  heisenbergHamiltonian_mulVec_mem_magnetizationSubspace_of_mem
    (Λ := Fin (2 * K)) J
    (neelChainState_mem_magnetizationSubspace_zero K)

/-- Tasaki §2.5 eq. (2.5.3), p. 37 (concrete chain instance):
on every adjacent bond `(i, i+1)` of the chain `Fin (2 * K)`, the
two-site spin inner product `Ŝ_x · Ŝ_y` acts on the Néel state by

  `Ŝ_x · Ŝ_y · |Φ_Néel⟩
    = (1/2) |swap_{x, y} Φ_Néel⟩ - (1/4) |Φ_Néel⟩`,

since adjacent indices have opposite parities and hence opposite
Néel spins (antiparallel case). One-line corollary of the generic
`spinHalfDot_mulVec_basisVec_antiparallel` (Tasaki §2.2 (2.2.19),
antiparallel) instantiated at `σ = neelChainConfig K` and the
parity-derived `σ x ≠ σ y` certificate. -/
theorem spinHalfDot_mulVec_neelChainState_adjacent
    (K : ℕ) {i : ℕ} (hi : i + 1 < 2 * K) :
    (spinHalfDot
        (⟨i, by omega⟩ : Fin (2 * K))
        (⟨i + 1, hi⟩ : Fin (2 * K))).mulVec (neelChainState K) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig K)
            (⟨i, by omega⟩ : Fin (2 * K))
            (⟨i + 1, hi⟩ : Fin (2 * K)))
        - (1 / 4 : ℂ) • neelChainState K := by
  unfold neelChainState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · -- σ_Néel ⟨i⟩ ≠ σ_Néel ⟨i + 1⟩: opposite parities
    unfold neelChainConfig
    simp only
    by_cases hp : i % 2 = 0
    · have hp1 : (i + 1) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : (i + 1) % 2 = 0 := by omega
      simp [hp, hp1]

/-- Two-site Néel computation (`K = 1`): the open-chain
Heisenberg Hamiltonian `H_open(N=1, J)` acts on the Néel state
`|Φ_Néel⟩ = |↑↓⟩` by

  `H · |Φ_Néel⟩ = -J · |↓↑⟩ + (J/2) · |Φ_Néel⟩`,

which decomposes the bond `(0, 1)` action via the antiparallel
formula. This is the explicit `K = 1` instance of the bond-by-bond
calculation `spinHalfDot_mulVec_neelChainState_adjacent` lifted
through `H_open(N=1, J) = -2J · spinHalfDot 0 1`. The
non-eigenstate character of the Néel state is plain: the
right-hand side has two distinct basis components. -/
theorem heisenbergHamiltonian_openChainCoupling_one_mulVec_neelChainState_one
    (J : ℝ) :
    (heisenbergHamiltonian (openChainCoupling 1 J)).mulVec
        (neelChainState 1) =
      (-(J : ℂ)) • basisVec
          (basisSwap (neelChainConfig 1)
            (⟨0, by decide⟩ : Fin (2 * 1))
            (⟨1, by decide⟩ : Fin (2 * 1))) +
        ((J : ℂ) / 2) • neelChainState 1 := by
  rw [openChainHeisenbergHamiltonian_two_site_eq, Matrix.smul_mulVec]
  have h := spinHalfDot_mulVec_neelChainState_adjacent 1 (i := 0)
    (by decide)
  -- Replace (0 : Fin 2) by ⟨0, _⟩ and (1 : Fin 2) by ⟨1, _⟩ in the goal.
  show (-(2 * (J : ℂ))) •
      (spinHalfDot (⟨0, by decide⟩ : Fin (2 * 1))
        (⟨1, by decide⟩ : Fin (2 * 1))).mulVec (neelChainState 1) =
    (-(J : ℂ)) • basisVec
        (basisSwap (neelChainConfig 1)
          (⟨0, by decide⟩ : Fin (2 * 1))
          (⟨1, by decide⟩ : Fin (2 * 1))) +
      ((J : ℂ) / 2) • neelChainState 1
  rw [h]
  module

/-- Companion of `spinHalfDot_mulVec_neelChainState_adjacent` for
the **wrap-around** bond `(2K - 1, 0)` of the periodic chain
`cycleGraph (2 * (K + 1))`. For `K ≥ 0` (so chain length
`2 * (K + 1) ≥ 2`), the indices `2*K + 1` and `0` carry opposite
parities, so the bond is again antiparallel:

  `Ŝ_⟨2K+1⟩ · Ŝ_⟨0⟩ · |Φ_Néel⟩
    = (1/2) · |swap_{2K+1, 0} Φ_Néel⟩ - (1/4) · |Φ_Néel⟩`.

Together with `spinHalfDot_mulVec_neelChainState_adjacent` this
covers every bond of the periodic chain `cycleGraph (2*(K+1))`. -/
theorem spinHalfDot_mulVec_neelChainState_wrap (K : ℕ) :
    (spinHalfDot
        (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
        (⟨0, by omega⟩ : Fin (2 * (K + 1)))).mulVec
        (neelChainState (K + 1)) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelChainConfig (K + 1))
            (⟨2 * K + 1, by omega⟩ : Fin (2 * (K + 1)))
            (⟨0, by omega⟩ : Fin (2 * (K + 1))))
        - (1 / 4 : ℂ) • neelChainState (K + 1) := by
  unfold neelChainState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have := congrArg Fin.val h
    simp at this
  · -- σ_Néel ⟨2K+1⟩ = 1, σ_Néel ⟨0⟩ = 0 (opposite parities)
    unfold neelChainConfig
    simp only
    have h1 : (2 * K + 1) % 2 = 1 := by omega
    simp [h1]

/-! ## 2D Néel (checkerboard) state on `Fin (2K) × Fin (2L)`

Tasaki §2.5 eq. (2.5.2) defines the Néel state on a *bipartite*
lattice. The 2D square lattice with even sides is bipartite via
the parity sum colouring `(i, j) ↦ (i.val + j.val) % 2` (each
sublattice is a checkerboard). The corresponding Néel
configuration is `σ(i, j) := if (i.val + j.val) % 2 = 0 then ↑
else ↓`.

This module formalises the simplest 2D analogue of the
`neelChainConfig` chain definition. -/

/-- The 2D checkerboard Néel configuration on
`Fin (2 * K) × Fin (2 * L)`: the spin at site `(i, j)` is `↑` if
`(i.val + j.val)` is even, `↓` otherwise. -/
def neelSquareConfig (K L : ℕ) :
    Fin (2 * K) × Fin (2 * L) → Fin 2 :=
  fun p => if (p.1.val + p.2.val) % 2 = 0 then 0 else 1

/-- The 2D Néel state on `Fin (2 * K) × Fin (2 * L)` for `S = 1/2`
(Tasaki §2.5 eq. (2.5.2) checkerboard instance). -/
noncomputable def neelSquareState (K L : ℕ) :
    (Fin (2 * K) × Fin (2 * L) → Fin 2) → ℂ :=
  basisVec (neelSquareConfig K L)

/-- 1D parity-sum lemma with a fixed parity offset: for any
`parity : ℕ` and `L : ℕ`,

  `Σ_{j : Fin (2*L)} (if (parity + j.val) % 2 = 0 then 1 else -1) = 0`.

Proof by induction on `L`, peeling the last two indices. -/
private lemma sum_alternating_sign_offset (parity L : ℕ) :
    (∑ j : Fin (2 * L),
      (if (parity + j.val) % 2 = 0 then (1 : ℤ) else -1)) = 0 := by
  induction L with
  | zero => simp
  | succ L' ih =>
    rw [show 2 * (L' + 1) = (2 * L' + 1) + 1 from by ring]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have h_inner_eq :
        (∑ j : Fin (2 * L'),
          if (parity + (j.castSucc.castSucc :
                Fin (2 * L' + 1 + 1)).val) % 2 = 0
            then (1 : ℤ) else -1) =
        ∑ j : Fin (2 * L'),
          (if (parity + j.val) % 2 = 0 then (1 : ℤ) else -1) := by
      apply Finset.sum_congr rfl
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
      rw [if_pos h1, if_neg h2]; ring
    · have h1 : (parity + 2 * L') % 2 ≠ 0 := by omega
      have h2 : (parity + (2 * L' + 1)) % 2 = 0 := by omega
      rw [if_neg h1, if_pos h2]; ring

/-- The 2D Néel configuration on `Fin (2K) × Fin (2L)` has zero
total magnetisation: each row contributes a vanishing alternating
column sum (per `sum_alternating_sign_offset` at `parity = i.val`). -/
theorem neelSquareConfig_magnetization_zero (K L : ℕ) :
    magnetization (Fin (2 * K) × Fin (2 * L))
        (neelSquareConfig K L) = 0 := by
  unfold magnetization
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro i _
  unfold neelSquareConfig spinSign
  have h_inner : ∀ j : Fin (2 * L),
      (if ((if (i.val + j.val) % 2 = 0 then (0 : Fin 2) else 1) = 0)
        then (1 : ℤ) else -1) =
      (if (i.val + j.val) % 2 = 0 then (1 : ℤ) else -1) := by
    intro j
    by_cases hp : (i.val + j.val) % 2 = 0
    · simp [hp]
    · simp [hp]
  simp_rw [h_inner]
  exact sum_alternating_sign_offset i.val L

/-- The 2D Néel state on `Fin (2*K) × Fin (2*L)` lies in the
zero-magnetisation sector `H_0`. -/
theorem neelSquareState_mem_magnetizationSubspace_zero (K L : ℕ) :
    neelSquareState K L ∈
      magnetizationSubspace (Fin (2 * K) × Fin (2 * L)) (0 : ℂ) := by
  unfold neelSquareState
  have h := basisVec_mem_magnetizationSubspace
    (Λ := Fin (2 * K) × Fin (2 * L)) (neelSquareConfig K L)
  rw [neelSquareConfig_magnetization_zero] at h
  simpa using h

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

/-! ## 2D Néel per-bond `Ŝ_x · Ŝ_y` action -/

/-- Tasaki §2.5 eq. (2.5.3) per-bond action for the **horizontal**
nearest-neighbour bond `((i, j), (i+1, j))` of the 2D
checkerboard Néel state. The two endpoints have opposite parities
(`(i + j)` vs `(i + 1 + j)` differ by 1), so the bond is
antiparallel and the action is

  `Ŝ_(i,j) · Ŝ_(i+1,j) · |Φ_Néel⟩
    = (1/2) · |swap_{(i,j),(i+1,j)} Φ_Néel⟩
        - (1/4) · |Φ_Néel⟩`. -/
theorem spinHalfDot_mulVec_neelSquareState_horizontal_adjacent
    (K L : ℕ) {i j : ℕ}
    (hi : i + 1 < 2 * K) (hj : j < 2 * L) :
    (spinHalfDot
        ((⟨i, by omega⟩, ⟨j, hj⟩) :
          Fin (2 * K) × Fin (2 * L))
        ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
          Fin (2 * K) × Fin (2 * L))).mulVec
        (neelSquareState K L) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelSquareConfig K L)
            ((⟨i, by omega⟩, ⟨j, hj⟩) :
              Fin (2 * K) × Fin (2 * L))
            ((⟨i + 1, hi⟩, ⟨j, hj⟩) :
              Fin (2 * K) × Fin (2 * L)))
        - (1 / 4 : ℂ) • neelSquareState K L := by
  unfold neelSquareState
  apply spinHalfDot_mulVec_basisVec_antiparallel
  · intro h
    have := congrArg Prod.fst h
    have hval := congrArg Fin.val this
    simp at hval
  · -- Opposite parities: (i + j) and (i + 1 + j) differ by 1
    unfold neelSquareConfig
    simp only
    by_cases hp : (i + j) % 2 = 0
    · have hp1 : ((i + 1) + j) % 2 ≠ 0 := by omega
      simp [hp, hp1]
    · have hp1 : ((i + 1) + j) % 2 = 0 := by omega
      simp [hp, hp1]

/-- Vertical-bond analogue: `((i, j), (i, j+1))` is also
antiparallel with the same `(1/2) swap - (1/4) Néel` decomposition. -/
theorem spinHalfDot_mulVec_neelSquareState_vertical_adjacent
    (K L : ℕ) {i j : ℕ}
    (hi : i < 2 * K) (hj : j + 1 < 2 * L) :
    (spinHalfDot
        ((⟨i, hi⟩, ⟨j, by omega⟩) :
          Fin (2 * K) × Fin (2 * L))
        ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
          Fin (2 * K) × Fin (2 * L))).mulVec
        (neelSquareState K L) =
      (1 / 2 : ℂ) • basisVec
          (basisSwap (neelSquareConfig K L)
            ((⟨i, hi⟩, ⟨j, by omega⟩) :
              Fin (2 * K) × Fin (2 * L))
            ((⟨i, hi⟩, ⟨j + 1, hj⟩) :
              Fin (2 * K) × Fin (2 * L)))
        - (1 / 4 : ℂ) • neelSquareState K L := by
  unfold neelSquareState
  apply spinHalfDot_mulVec_basisVec_antiparallel
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

end LatticeSystem.Quantum
