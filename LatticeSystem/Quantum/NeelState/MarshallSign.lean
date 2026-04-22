/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.NeelState.TimeReversal

/-!
# Marshall sign on the parity-coloured chain (Tasaki §2.5)

The Marshall sign (Marshall 1955; Lieb-Mattis 1962; Tasaki §2.5) of
a spin configuration `σ : Fin (2 * K) → Fin 2` is, on the
bipartite chain `Fin (2 * K)` with sublattice `A` = even indices:

  `(-1)^(N_A^↓)`

where `N_A^↓` is the number of down spins on sublattice `A`. After
the Marshall basis change `|σ⟩ ↦ (-1)^(N_A^↓) |σ⟩`, the AF
Heisenberg Hamiltonian on a bipartite lattice has all non-positive
off-diagonal entries, which is the input to the
Perron-Frobenius-style proof of the Marshall-Lieb-Mattis
theorem.

This module collects:
- `marshallSignOf` (generic graph-centric form),
- chain / 2D / 3D specialisations,
- evaluation on Néel + on constant configurations,
- behaviour under `flipConfig`,
- Marshall-rotated state definitions,
- Marshall × time-reversal bridge.

(Refactor Phase 2 PR 8 — eighth step of the NeelState 7-file
split, plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

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
`|σ⟩_M := marshallSignChainConfig K σ · |σ⟩`. -/
noncomputable def marshallChainState (K : ℕ)
    (σ : Fin (2 * K) → Fin 2) : (Fin (2 * K) → Fin 2) → ℂ :=
  marshallSignChainConfig K σ • basisVec σ

/-- The Marshall-rotated Néel chain state coincides with the
Néel chain state itself. -/
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

/-- Marshall sign of the *flipped* Néel chain configuration. -/
theorem marshallSignChainConfig_flipConfig_neelChainConfig (K : ℕ) :
    marshallSignChainConfig K (flipConfig (neelChainConfig K)) =
      (-1 : ℂ) ^ K := by
  rw [marshallSignChainConfig_flipConfig,
    marshallSignChainConfig_neelChainConfig, mul_one]

/-- 2D Marshall sign of the flipped Néel configuration: `+1`. -/
theorem marshallSignSquareConfig_flipConfig_neelSquareConfig (K L : ℕ) :
    marshallSignSquareConfig K L (flipConfig (neelSquareConfig K L)) = 1 := by
  rw [marshallSignSquareConfig_flipConfig,
    marshallSignSquareConfig_neelSquareConfig]

/-- 3D Marshall sign of the flipped Néel configuration: `+1`. -/
theorem marshallSignCubicConfig_flipConfig_neelCubicConfig
    (K L M : ℕ) :
    marshallSignCubicConfig K L M
        (flipConfig (neelCubicConfig K L M)) = 1 := by
  rw [marshallSignCubicConfig_flipConfig,
    marshallSignCubicConfig_neelCubicConfig]

/-- The Marshall-rotated *flipped* Néel chain state equals the
time-reversed Néel chain state. -/
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

end LatticeSystem.Quantum
