/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MagnetizationSubspace
import LatticeSystem.Quantum.SpinDot
import LatticeSystem.Quantum.HeisenbergChain

/-!
# Néel state definition (Tasaki §2.5)

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
§2.5 eq. (2.5.2), p. 37 defines the **Néel state** on a bipartite
lattice `Λ = A ⊔ B` (with sublattices `A` and `B`) for spin `S`:

  `|Φ_Néel⟩ := (⊗_{x ∈ A} |ψ_x^S⟩) ⊗ (⊗_{y ∈ B} |ψ_y^{-S}⟩)`.

For a bipartite lattice with `|A| = |B|`, the Néel state lies in
the zero-magnetization sector `H_0` (Tasaki §2.2 (2.2.10)) since
the contributions from `A` (each `+S`) and `B` (each `-S`) cancel.

This module formalises the **chain** `S = 1/2` case
(`Fin (2 * K)`). The 2D / 3D extensions live in further files
under this directory; the legacy `Quantum/NeelState.lean` is the
façade re-exporting all of them.

(Refactor Phase 2 PR 1 — first step of the NeelState 7-file split,
plan v4 §3.1.)
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## Generic graph-centric Néel state -/

/-- Generic Néel configuration from a sublattice indicator
`A : V → Bool`. Sites with `A x = true` carry `↑ : Fin 2 := 0`,
sites with `A x = false` carry `↓ : Fin 2 := 1`.

This is the canonical Néel configuration on the bipartite
graph `(V, A)`. The chain / 2D / 3D `neelXyzConfig` definitions
below are obtained by instantiating `A` with the corresponding
parity colouring and bridged via `_eq_neelConfigOf`. (Refactor
Phase 3 PR 3.) -/
def neelConfigOf {V : Type*} (A : V → Bool) : V → Fin 2 :=
  fun x => if A x then 0 else 1

/-- Generic Néel state: the many-body basis vector at
`neelConfigOf A`. -/
noncomputable def neelStateOf {V : Type*} [Fintype V] [DecidableEq V]
    (A : V → Bool) : (V → Fin 2) → ℂ :=
  basisVec (neelConfigOf A)

/-- If two sites lie in different sublattices (`A x ≠ A y`) then
their Néel spins differ. The two `Fin 2` cases collapse: if
`A x = true, A y = false` then `(0 : Fin 2) ≠ 1`, and vice versa. -/
theorem neelConfigOf_apply_ne_of_ne {V : Type*} (A : V → Bool)
    {x y : V} (h : A x ≠ A y) :
    neelConfigOf A x ≠ neelConfigOf A y := by
  unfold neelConfigOf
  by_cases hx : A x = true
  · have hy : A y = false := by
      rcases hb : A y with _ | _
      · rfl
      · exact absurd (hx.trans hb.symm) h
    simp [hx, hy]
  · have hxF : A x = false := by
      rcases hb : A x with _ | _
      · rfl
      · exact absurd hb hx
    have hy : A y = true := by
      rcases hb : A y with _ | _
      · exact absurd (hxF.trans hb.symm) h
      · rfl
    simp [hxF, hy]

/-- Generic Néel bond action across an antiparallel bond
(Tasaki §2.5 eq. (2.5.3), graph-centric form). For
`A : V → Bool` and a bond `(x, y)` with `x ≠ y` and
`A x ≠ A y`,

  `Ŝ_x · Ŝ_y · |Φ_Néel(A)⟩
    = (1/2) · |swap_{x, y} Φ_Néel(A)⟩
        - (1/4) · |Φ_Néel(A)⟩`.

This is the single primitive of which the chain / 2D / 3D
adjacent and wrap-around bond actions are corollaries via
`neelXyzConfig_eq_neelConfigOf` (chain in `Definition.lean`,
square in `Definition2D.lean`, cubic in `Definition3D.lean`).
(Refactor Phase 3 PR 3.) -/
theorem spinHalfDot_mulVec_neelStateOf_antiparallel
    {V : Type*} [Fintype V] [DecidableEq V] (A : V → Bool)
    {x y : V} (hxy : x ≠ y) (hA : A x ≠ A y) :
    (spinHalfDot x y).mulVec (neelStateOf A) =
      (1 / 2 : ℂ) • basisVec (basisSwap (neelConfigOf A) x y)
        - (1 / 4 : ℂ) • neelStateOf A := by
  unfold neelStateOf
  exact spinHalfDot_mulVec_basisVec_antiparallel hxy _
    (neelConfigOf_apply_ne_of_ne A hA)

/-! ## Chain Néel state -/

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

/-- Chain bridge: the Néel chain configuration is the generic
`neelConfigOf` evaluated on the even-parity sublattice
indicator. -/
theorem neelChainConfig_eq_neelConfigOf (K : ℕ) :
    neelChainConfig K =
      neelConfigOf (fun x : Fin (2 * K) => decide (x.val % 2 = 0)) := by
  unfold neelChainConfig neelConfigOf
  funext x
  by_cases hp : x.val % 2 = 0 <;> simp [hp]

/-- Chain bridge (state form): immediate corollary of
`neelChainConfig_eq_neelConfigOf`. -/
theorem neelChainState_eq_neelStateOf (K : ℕ) :
    neelChainState K =
      neelStateOf (fun x : Fin (2 * K) => decide (x.val % 2 = 0)) := by
  unfold neelChainState neelStateOf
  rw [neelChainConfig_eq_neelConfigOf]

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

end LatticeSystem.Quantum
