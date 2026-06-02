import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreProjection

/-!
# Hubbard one-hole hard-core basis states

This file continues the Tasaki §11.2 Nagaoka-ferromagnetism infrastructure.
It defines the one-hole hard-core basis states `|Φ_{x,σ}⟩`: the computational
basis configurations in which exactly one spinful site `x` (the hole) is
empty and every other site carries exactly one electron of spin `σ(j)`.

These are the basis states of the infinite-`U` / one-hole Nagaoka sector
(Tasaki, 1st edition, §11.2, eq. (11.2.3)). Because each state is a single
computational basis vector `basisVec`, orthonormality is immediate from
`basisVec_inner`, and the no-double-occupancy property places every state in
`hubbardHardcoreSubspace`. Each state is consequently fixed by the hard-core
projection `hubbardHardcoreProjection`.

The relation to Tasaki's ordered Jordan–Wigner creation-operator products
(which carries fermion signs, relevant to the hopping matrix elements
(11.2.5)) is deferred to the effective-Hamiltonian layer; here the states are
defined sign-free as occupation configurations.

Tracked in Issue #4130. References: Tasaki, *Physics and Mathematics of
Quantum Many-Body Systems*, 1st edition, §11.2, pp. 381-388; this file
formalizes unnumbered one-hole hard-core basis infrastructure used before
Theorems 11.5 and 11.7.

## JW-index convention

In the spinful JW chain on `Fin (2 * N + 2)`, site `i` spin-up is JW index
`2 * i` (even) and spin-down is `2 * i + 1` (odd); occupation value `1` means
occupied, `0` empty. Booleans encode spin: `true = ↑`, `false = ↓`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Auxiliary: number operator annihilates an empty orbital -/

/-- A site-occupation number operator annihilates any computational basis
vector whose orbital `j` is empty: `n_j · |c⟩ = 0` when `c j = 0`. The
diagonal number operator `n_j = onSite j (σ⁻σ⁺)` has `σ⁻σ⁺ = diag(0,1)`, so
the empty value `c j = 0` zeroes every term. -/
private theorem fermionMultiNumber_mulVec_basisVec_eq_zero_of_empty
    (M : ℕ) (j : Fin (M + 1)) (c : Fin (M + 1) → Fin 2) (h : c j = 0) :
    (fermionMultiNumber M j).mulVec (basisVec c) = 0 := by
  rw [fermionMultiNumber_eq_onSite, onSite_mulVec_basisVec]
  funext τ
  apply Finset.sum_eq_zero
  intro k _
  rw [h]
  fin_cases k <;>
    simp [spinHalfOpMinus, spinHalfOpPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-- Spin-up version: `n_{i,↑} · |c⟩ = 0` when the up-orbital at site `i` is
empty. -/
private theorem fermionUpNumber_mulVec_basisVec_eq_zero_of_empty
    (N : ℕ) (i : Fin (N + 1)) (c : Fin (2 * N + 2) → Fin 2)
    (h : c (spinfulIndex N i 0) = 0) :
    (fermionUpNumber N i).mulVec (basisVec c) = 0 := by
  unfold fermionUpNumber
  exact fermionMultiNumber_mulVec_basisVec_eq_zero_of_empty (2 * N + 1)
    (spinfulIndex N i 0) c h

/-- Spin-down version: `n_{i,↓} · |c⟩ = 0` when the down-orbital at site `i`
is empty. -/
private theorem fermionDownNumber_mulVec_basisVec_eq_zero_of_empty
    (N : ℕ) (i : Fin (N + 1)) (c : Fin (2 * N + 2) → Fin 2)
    (h : c (spinfulIndex N i 1) = 0) :
    (fermionDownNumber N i).mulVec (basisVec c) = 0 := by
  unfold fermionDownNumber
  exact fermionMultiNumber_mulVec_basisVec_eq_zero_of_empty (2 * N + 1)
    (spinfulIndex N i 1) c h

/-- The double-occupancy operator annihilates a basis vector whose up-orbital
at site `i` is empty (commute `n_↑ n_↓ = n_↓ n_↑`, then `n_↑` kills it). -/
private theorem hubbardDoubleOccupancy_mulVec_basisVec_eq_zero_of_up_empty
    (N : ℕ) (i : Fin (N + 1)) (c : Fin (2 * N + 2) → Fin 2)
    (h : c (spinfulIndex N i 0) = 0) :
    (hubbardDoubleOccupancy N i).mulVec (basisVec c) = 0 := by
  unfold hubbardDoubleOccupancy
  rw [(fermionUpNumber_commute_fermionDownNumber N i).eq, ← Matrix.mulVec_mulVec,
    fermionUpNumber_mulVec_basisVec_eq_zero_of_empty N i c h, Matrix.mulVec_zero]

/-- The double-occupancy operator annihilates a basis vector whose
down-orbital at site `i` is empty (`n_↓` kills it directly). -/
private theorem hubbardDoubleOccupancy_mulVec_basisVec_eq_zero_of_down_empty
    (N : ℕ) (i : Fin (N + 1)) (c : Fin (2 * N + 2) → Fin 2)
    (h : c (spinfulIndex N i 1) = 0) :
    (hubbardDoubleOccupancy N i).mulVec (basisVec c) = 0 := by
  unfold hubbardDoubleOccupancy
  rw [← Matrix.mulVec_mulVec,
    fermionDownNumber_mulVec_basisVec_eq_zero_of_empty N i c h, Matrix.mulVec_zero]

/-! ## The one-hole hard-core configuration -/

/-- The occupation configuration of the one-hole hard-core state `|Φ_{x,σ}⟩`:
site `x` is the hole (both orbitals empty), and every other site `j` carries
exactly one electron, spin `↑` (up-orbital occupied) if `σ j = true`, spin `↓`
(down-orbital occupied) otherwise. -/
def hubbardOneHoleConfig (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) :
    Fin (2 * N + 2) → Fin 2 :=
  fun k =>
    let s : Fin (N + 1) :=
      ⟨k.val / 2, by
        have hk := k.isLt
        exact (Nat.div_lt_iff_lt_mul (by norm_num)).mpr (by omega)⟩
    if s.val = x.val then 0
    else if k.val % 2 = 0 then (if σ s then 1 else 0)
    else (if σ s then 0 else 1)

/-- Value of the one-hole configuration at the up-orbital `2 * i` of site
`i`: empty at the hole, otherwise occupied iff `σ i`. -/
theorem hubbardOneHoleConfig_apply_up
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) (i : Fin (N + 1)) :
    hubbardOneHoleConfig N x σ (spinfulIndex N i 0)
      = if i.val = x.val then 0 else if σ i then 1 else 0 := by
  have hsite : (spinfulIndex N i 0).val / 2 = i.val := by
    simp [spinfulIndex]
  have hmod : (spinfulIndex N i 0).val % 2 = 0 := by
    simp [spinfulIndex]
  simp only [hubbardOneHoleConfig, hsite, hmod, if_true]

/-- Value of the one-hole configuration at the down-orbital `2 * i + 1` of
site `i`: empty at the hole, otherwise occupied iff `¬ σ i`. -/
theorem hubbardOneHoleConfig_apply_down
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) (i : Fin (N + 1)) :
    hubbardOneHoleConfig N x σ (spinfulIndex N i 1)
      = if i.val = x.val then 0 else if σ i then 0 else 1 := by
  have hval : (spinfulIndex N i 1).val = 2 * i.val + 1 := by
    simp [spinfulIndex]
  have hsite : (spinfulIndex N i 1).val / 2 = i.val := by
    rw [hval, Nat.mul_add_div (by norm_num)]; norm_num
  have hmod : (spinfulIndex N i 1).val % 2 = 1 := by
    rw [hval, Nat.mul_add_mod]
  simp [hubbardOneHoleConfig, hsite, hmod]

/-! ## The one-hole hard-core basis states -/

/-- The one-hole hard-core basis state `|Φ_{x,σ}⟩`: the computational basis
vector for the configuration with a hole at site `x` and spin `σ` on the
other sites (Tasaki §11.2, eq. (11.2.3)). -/
noncomputable def hubbardHardcoreBasisState (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) : (Fin (2 * N + 2) → Fin 2) → ℂ :=
  basisVec (hubbardOneHoleConfig N x σ)

/-- Each one-hole hard-core basis state lies in the hard-core subspace: at
every site at least one orbital is empty, so the double-occupancy operator
vanishes on it. -/
theorem hubbardHardcoreBasisState_mem_hardcoreSubspace
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) :
    hubbardHardcoreBasisState N x σ ∈ hubbardHardcoreSubspace N := by
  rw [mem_hubbardHardcoreSubspace_iff]
  intro i
  unfold hubbardHardcoreBasisState
  by_cases hix : i.val = x.val
  · -- hole site: up-orbital empty
    refine hubbardDoubleOccupancy_mulVec_basisVec_eq_zero_of_up_empty N i _ ?_
    rw [hubbardOneHoleConfig_apply_up, if_pos hix]
  · by_cases hσ : σ i
    · -- spin up: down-orbital empty
      refine hubbardDoubleOccupancy_mulVec_basisVec_eq_zero_of_down_empty N i _ ?_
      rw [hubbardOneHoleConfig_apply_down, if_neg hix, if_pos hσ]
    · -- spin down: up-orbital empty
      refine hubbardDoubleOccupancy_mulVec_basisVec_eq_zero_of_up_empty N i _ ?_
      rw [hubbardOneHoleConfig_apply_up, if_neg hix, if_neg hσ]

/-- The hard-core projection fixes every one-hole hard-core basis state. -/
theorem hubbardHardcoreProjection_mulVec_basisState
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) :
    (hubbardHardcoreProjection N).mulVec (hubbardHardcoreBasisState N x σ) =
      hubbardHardcoreBasisState N x σ :=
  hubbardHardcoreProjection_mulVec_eq_self_of_mem N
    (hubbardHardcoreBasisState_mem_hardcoreSubspace N x σ)

/-- Orthonormality of the one-hole hard-core basis states: the real bilinear
pairing of `|Φ_{x,σ}⟩` and `|Φ_{x',σ'}⟩` is `1` when their configurations
coincide and `0` otherwise. -/
theorem hubbardHardcoreBasisState_inner
    (N : ℕ) (x x' : Fin (N + 1)) (σ σ' : Fin (N + 1) → Bool) :
    ∑ τ : Fin (2 * N + 2) → Fin 2,
        hubbardHardcoreBasisState N x σ τ * hubbardHardcoreBasisState N x' σ' τ =
      if hubbardOneHoleConfig N x' σ' = hubbardOneHoleConfig N x σ then 1 else 0 := by
  unfold hubbardHardcoreBasisState
  exact basisVec_inner (hubbardOneHoleConfig N x σ) (hubbardOneHoleConfig N x' σ')

/-- Each one-hole hard-core basis state is normalised: its self-overlap is
`1`. -/
theorem hubbardHardcoreBasisState_self_inner
    (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool) :
    ∑ τ : Fin (2 * N + 2) → Fin 2,
        hubbardHardcoreBasisState N x σ τ * hubbardHardcoreBasisState N x σ τ = 1 := by
  rw [hubbardHardcoreBasisState_inner, if_pos rfl]

end LatticeSystem.Fermion
