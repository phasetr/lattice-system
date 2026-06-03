import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaGlobalMin

/-!
# Magnetization sectors of the one-hole Tasaki basis (Tasaki §11.2.2)

This file begins the formalization of **Tasaki Theorem 11.7** (the uniqueness
half of Nagaoka's theorem): with non-negative hopping `t ≥ 0`, `N = |Λ| - 1`,
`U = ∞`, *and the connectivity condition (Definition 11.6)*, the one-hole
ground states are exactly the `2 S_max + 1` ferromagnetic multiplet members.

The proof of Theorem 11.7 applies Perron–Frobenius to `-M` (the negated Tasaki
matrix `M = `[`tasakiEffReMatrix`]) **separately on each fixed total
`S_z^{(3)}` sector**, where `M` is block-diagonal.  This file sets up that
block structure:

* [`configMag`] — the total `S_z^{(3)}` (doubled, an integer) read off directly
  from an occupation configuration, so configurations with equal occupations
  have equal magnetization by construction.
* [`holeSpinMag`] — the magnetization of a one-hole Tasaki basis index
  `⟨x, σ⟩`, defined through its occupation configuration.
* [`configMag_hubbardSpinMove`] — hopping the hole preserves the magnetization
  (Tasaki (11.2.4); physically the electrons only rearrange).
* [`tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne`] — `M` is block-diagonal with
  respect to `holeSpinMag`: an off-sector matrix element vanishes.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.2, Definition 11.6 and Theorem 11.7.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The (doubled) total `S_z^{(3)}` magnetization read off an occupation
configuration `c : Fin (2N+2) → Fin 2` of the spinful chain: each site `i`
contributes `(occupation of its ↑-orbital) − (occupation of its ↓-orbital)`.
For a singly-occupied site this is `±1`; for an empty (hole) or doubly-occupied
site it is `0`.  Because it depends only on the occupations, two configurations
that are *equal as functions* have equal `configMag`. -/
def configMag (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : ℤ :=
  ∑ i : Fin (N + 1),
    (((c (spinfulIndex N i 0)).val : ℤ) - ((c (spinfulIndex N i 1)).val : ℤ))

/-- The (doubled) total `S_z^{(3)}` magnetization of the one-hole Tasaki basis
index `⟨x, σ⟩`, defined through its occupation configuration so that it depends
only on that configuration. -/
def holeSpinMag (N : ℕ) (p : (x : Fin (N + 1)) × HoleSpin N x) : ℤ :=
  configMag N (hubbardOneHoleConfig N p.1 p.2.val)

/-- The magnetization of a one-hole configuration, expressed sitewise: the hole
site contributes `0`, every other site contributes `+1` for spin `↑` and `−1`
for spin `↓`. -/
theorem configMag_hubbardOneHoleConfig (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    configMag N (hubbardOneHoleConfig N x σ) =
      ∑ i : Fin (N + 1), (if i = x then (0 : ℤ) else if σ i then 1 else -1) := by
  unfold configMag
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_down]
  simp only [Fin.val_inj]
  by_cases h : i = x
  · simp [h]
  · rw [if_neg h]
    by_cases hσ : σ i <;> simp [h, hσ]

/-- **Hopping the hole preserves magnetization** (Tasaki (11.2.4)).  Moving the
electron at `y` into the hole at `x` (turning `|Φ_{x,σ}⟩` into a basis state at
hole `y`) does not change the total `S_z^{(3)}`: the electrons merely rearrange.
-/
theorem configMag_hubbardSpinMove (N : ℕ) (x y : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) (hxy : x ≠ y) :
    configMag N (hubbardOneHoleConfig N y (hubbardSpinMove N σ x y)) =
      configMag N (hubbardOneHoleConfig N x σ) := by
  rw [configMag_hubbardOneHoleConfig, configMag_hubbardOneHoleConfig,
    ← sub_eq_zero, ← Finset.sum_sub_distrib]
  have key : ∀ i : Fin (N + 1),
      ((if i = y then (0 : ℤ) else if hubbardSpinMove N σ x y i then 1 else -1)
        - (if i = x then (0 : ℤ) else if σ i then 1 else -1))
      = (if i = x then (if σ y then (1 : ℤ) else -1) else 0)
        + (if i = y then -(if σ y then (1 : ℤ) else -1) else 0) := by
    intro i
    by_cases hix : i = x <;> by_cases hiy : i = y
    · exact absurd (hix ▸ hiy : x = y) hxy
    · subst hix; simp [hiy, hubbardSpinMove]
    · simp_all
    · simp [hubbardSpinMove, hix, hiy]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ x, Finset.sum_ite_eq' Finset.univ y]
  simp

/-- **The Tasaki matrix is block-diagonal in magnetization.**  A matrix element
`M_{⟨y,τ⟩, ⟨x,σ⟩}` between one-hole basis states of different total `S_z^{(3)}`
vanishes — `Ĥ_eff` conserves `S_z^{(3)}`, so it preserves each magnetization
sector.  (Here `M = `[`tasakiEffReMatrix`].) -/
theorem tasakiEffReMatrix_eq_zero_of_holeSpinMag_ne (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (q p : (x : Fin (N + 1)) × HoleSpin N x)
    (h : holeSpinMag N q ≠ holeSpinMag N p) :
    tasakiEffReMatrix N t q p = 0 := by
  obtain ⟨y, τ⟩ := q
  obtain ⟨x, σ⟩ := p
  unfold tasakiEffReMatrix
  by_cases hxy : x = y
  · -- diagonal block (same hole site) is unreachable here, but the entry is 0
    simp [hxy]
  · rw [if_neg (by simpa using hxy)]
    rw [if_neg ?_, mul_zero]
    intro hcfg
    apply h
    change configMag N (hubbardOneHoleConfig N y τ.val) =
      configMag N (hubbardOneHoleConfig N x σ.val)
    rw [← hcfg, configMag_hubbardSpinMove N x y σ.val hxy]

end LatticeSystem.Fermion
