import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem
import LatticeSystem.Math.PerronFrobenius

/-!
# Tasaki Theorem 11.5: existence of the ferromagnetic ground state

The capstone `weakNagaoka_spinMultiplet`
(`Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean`) reduces the weak Nagaoka
theorem to the *existence* of a nonzero highest-weight `Ĥ_eff`-eigenvector — a
ferromagnetic ground state. This file constructs that state via Perron–Frobenius
applied to the one-hole hopping problem in the maximal-`Ŝ^z` (all-up) sector.

In the all-up sector `{|Φ_{x,↑}⟩ : x ∈ Λ}` the effective Hamiltonian acts as the
single-hole hopping operator whose matrix is `⟨Φ_{y,↑}|Ĥ_eff|Φ_{x,↑}⟩ = -t_{x,y}`
(off-diagonal) with vanishing diagonal (no self-hopping). Perron–Frobenius is
applied to the *non-negative symmetric* matrix `A_{x,y} = t_{x,y}` (the negative
of the Hamiltonian block): its top eigenvalue `μ` has a strictly positive
eigenvector `ξ`, which corresponds to the *lowest* `Ĥ_eff` energy `-μ` — the
ferromagnetic ground state `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩`.

This commit sets up the hopping matrix and its Perron–Frobenius prerequisites
(non-negativity and Hermitian symmetry).

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, Theorem 11.5, pp. 382-385.
-/

namespace LatticeSystem.Fermion

open Matrix

/-! ## The all-up-sector hole-hopping matrix -/

/-- The one-hole hopping matrix in the maximal-`Ŝ^z` (all-up) sector:
`A_{x,y} = t_{x,y}` for `x ≠ y`, with vanishing diagonal. This is the negative of
the `Ĥ_eff` block on `{|Φ_{x,↑}⟩}` (whose entries are `-t_{x,y}`), so its
Perron–Frobenius top eigenvector is the ground state of `Ĥ_eff` in this sector. -/
noncomputable def nagaokaHoleHoppingMatrix (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun x y => if x = y then 0 else t x y

/-- Off-diagonal entries of the hopping matrix are the hopping amplitudes. -/
theorem nagaokaHoleHoppingMatrix_apply_of_ne (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    {x y : Fin (N + 1)} (hxy : x ≠ y) :
    nagaokaHoleHoppingMatrix N t x y = t x y := by
  rw [nagaokaHoleHoppingMatrix, if_neg hxy]

/-- The hopping matrix has vanishing diagonal. -/
theorem nagaokaHoleHoppingMatrix_apply_self (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (x : Fin (N + 1)) :
    nagaokaHoleHoppingMatrix N t x x = 0 := by
  rw [nagaokaHoleHoppingMatrix, if_pos rfl]

/-- The hopping matrix is entrywise non-negative when the hopping amplitudes are
(`t ≥ 0`) — a Perron–Frobenius prerequisite. -/
theorem nagaokaHoleHoppingMatrix_nonneg (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hpos : ∀ i j, 0 ≤ t i j) (x y : Fin (N + 1)) :
    0 ≤ nagaokaHoleHoppingMatrix N t x y := by
  rw [nagaokaHoleHoppingMatrix]
  split
  · exact le_refl 0
  · exact hpos x y

/-- The hopping matrix is symmetric when the hopping is (`t_{x,y} = t_{y,x}`). -/
theorem nagaokaHoleHoppingMatrix_isSymm (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hsymm : ∀ i j, t i j = t j i) :
    (nagaokaHoleHoppingMatrix N t).IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, nagaokaHoleHoppingMatrix]
  by_cases hxy : x = y
  · subst hxy; simp
  · rw [if_neg hxy, if_neg (fun h => hxy h.symm), hsymm y x]

/-- The hopping matrix is Hermitian (real symmetric) — the input form required by
`exists_pos_eigenvec_max`. -/
theorem nagaokaHoleHoppingMatrix_isHermitian (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hsymm : ∀ i j, t i j = t j i) :
    (nagaokaHoleHoppingMatrix N t).IsHermitian := by
  ext x y
  rw [Matrix.conjTranspose_apply, star_trivial]
  by_cases hxy : x = y
  · rw [hxy]
  · rw [nagaokaHoleHoppingMatrix_apply_of_ne N t (fun h => hxy h.symm),
      nagaokaHoleHoppingMatrix_apply_of_ne N t hxy, hsymm y x]

/-! ## The Perron–Frobenius ground eigenvector of the hopping matrix -/

/-- **Perron–Frobenius eigenvector of the all-up hopping matrix.** Under
irreducibility of the hopping (the connectivity condition; here a hypothesis,
to be supplied from graph connectivity for Theorem 11.7), the hopping matrix has
a strictly positive eigenvector `ξ` at its top eigenvalue `μ`. Since the matrix
is `−Ĥ_eff` on the all-up sector, `ξ` is the ferromagnetic *ground* state
configuration of `Ĥ_eff` (lowest energy `−μ`). -/
theorem exists_nagaokaHole_pf_eigenvector (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hsymm : ∀ i j, t i j = t j i)
    (hIrred : (nagaokaHoleHoppingMatrix N t).IsIrreducible) :
    ∃ (μ : ℝ) (ξ : Fin (N + 1) → ℝ),
      (nagaokaHoleHoppingMatrix N t) *ᵥ ξ = μ • ξ ∧ ξ ≠ 0 ∧ ∀ x, 0 < ξ x :=
  LatticeSystem.Math.PerronFrobenius.exists_pos_eigenvec_max
    (nagaokaHoleHoppingMatrix_isHermitian N t hsymm) hIrred

/-! ## The ferromagnetic ground state vector -/

/-- The ferromagnetic state `|Φ_↑⟩ = Σ_x ξ_x |Φ^T_{x,↑}⟩` built from a hopping
eigenvector `ξ`: a superposition over hole positions of the all-up Tasaki basis
states. With `ξ` the Perron–Frobenius eigenvector this is the ferromagnetic
ground state. -/
noncomputable def pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℝ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  ∑ x : Fin (N + 1), (ξ x : ℂ) • tasakiState N ⟨x, holeSpinUp N x⟩

/-- `Ŝ^+_tot` annihilates the ferromagnetic state: it is a highest-weight state
(all electrons spin-up, none to raise). -/
theorem fermionTotalSpinPlus_mulVec_pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℝ) :
    (fermionTotalSpinPlus N).mulVec (pfFerroState N ξ) = 0 := by
  unfold pfFerroState
  rw [Matrix.mulVec_sum]
  apply Finset.sum_eq_zero
  intro x _
  rw [Matrix.mulVec_smul,
    show tasakiState N ⟨x, holeSpinUp N x⟩ = hubbardTasakiBasisState N x (fun _ => true) from rfl,
    fermionTotalSpinPlus_mulVec_hubbardTasakiBasisStateUp, smul_zero]

/-- `Ŝ^z_tot` acts on the ferromagnetic state with eigenvalue `N/2 = S_max`: it is
the maximal-spin state. -/
theorem fermionTotalSpinZ_mulVec_pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℝ) :
    (fermionTotalSpinZ N).mulVec (pfFerroState N ξ) =
      ((N : ℂ) / 2) • pfFerroState N ξ := by
  unfold pfFerroState
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec_smul,
    show tasakiState N ⟨x, holeSpinUp N x⟩ = hubbardTasakiBasisState N x (fun _ => true) from rfl,
    fermionTotalSpinZ_mulVec_hubbardTasakiBasisStateUp, smul_comm]

/-- The ferromagnetic state is nonzero when the eigenvector is strictly positive:
its squared norm is `Σ_x ξ_x² > 0` by orthonormality of the Tasaki basis. -/
theorem pfFerroState_ne_zero (N : ℕ) (ξ : Fin (N + 1) → ℝ) (hξ : ∀ x, 0 < ξ x) :
    pfFerroState N ξ ≠ 0 := by
  classical
  intro h
  set ψ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ :=
    fun p => if p.2 = holeSpinUp N p.1 then ξ p.1 else 0 with hψdef
  have hexp : pfFerroState N ξ = ∑ p, (ψ p : ℂ) • tasakiState N p := by
    rw [pfFerroState, Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_eq_single (holeSpinUp N x)
      (fun σ _ hσ => by simp only [hψdef, if_neg hσ, Complex.ofReal_zero, zero_smul])
      (fun hmem => absurd (Finset.mem_univ _) hmem)]
    simp only [hψdef, if_pos rfl]
  have hnorm := tasakiExpansion_normSq N ψ
  rw [← hexp, h] at hnorm
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hnorm
  have hsum : (∑ p, (ψ p) ^ 2) = 0 := by exact_mod_cast hnorm.symm
  have hpos : 0 < ∑ p, (ψ p) ^ 2 := by
    refine Finset.sum_pos' (fun p _ => sq_nonneg _)
      ⟨⟨Classical.arbitrary (Fin (N + 1)), holeSpinUp N _⟩, Finset.mem_univ _, ?_⟩
    simp only [hψdef, if_pos rfl]
    exact pow_pos (hξ _) 2
  linarith

end LatticeSystem.Fermion
