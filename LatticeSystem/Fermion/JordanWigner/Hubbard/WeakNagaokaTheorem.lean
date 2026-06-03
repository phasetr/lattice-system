import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaoka
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianSpinSymmetry

/-!
# Tasaki Theorem 11.5 (weak version of Nagaoka's theorem)

This file builds toward Tasaki Theorem 11.5: for a Hubbard model with
`t_{x,y} = t_{y,x} ≥ 0` (and `t_{i,i} = 0`), `N = |Λ| − 1` electrons, `U ↑ ∞`,
among the ground states of the effective Hamiltonian there are at least
`(2 S_max + 1)` states with total spin `S_tot = S_max = N/2`.

The first ingredient (this commit) is that the *ferromagnetic hole state*
`|Φ_{x,(↑)}⟩` — the one-hole state with every occupied site spin-up — lies in
the maximal-spin sector: `(Ŝ_tot)² |Φ_{x,(↑)}⟩ = S_max(S_max+1) |Φ_{x,(↑)}⟩`
with `S_max = N/2`. Indeed `Ŝ^+_tot` annihilates it (no down electrons to
raise) and `Ŝ^z_tot` acts with eigenvalue `N/2` (the `N` up electrons).

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, Theorem 11.5, pp. 382-385.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Diagonal action of a number operator on a basis state -/

/-- The site-occupation number operator acts diagonally on a computational
basis state with the occupation value as eigenvalue:
`n_j · |c⟩ = (c j) • |c⟩`. -/
theorem fermionMultiNumber_mulVec_basisVec (N : ℕ) (j : Fin (N + 1))
    (c : Fin (N + 1) → Fin 2) :
    (fermionMultiNumber N j).mulVec (basisVec c) = ((c j).val : ℂ) • basisVec c := by
  rw [fermionMultiNumber_eq_onSite, onSite_mulVec_basisVec]
  funext τ
  rw [Fin.sum_univ_two]
  rcases (show c j = 0 ∨ c j = 1 from by
    rcases (c j) with ⟨v, hv⟩; interval_cases v; exacts [Or.inl rfl, Or.inr rfl])
    with hcj | hcj
  · rw [hcj]
    simp [spinHalfOpMinus, spinHalfOpPlus, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hcj, show Function.update c j 1 = c from by rw [← hcj]; exact Function.update_eq_self _ _]
    simp [spinHalfOpMinus, spinHalfOpPlus, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## The ferromagnetic hole state is maximal-spin -/

/-- The ferromagnetic hole configuration: hole at `x`, every other site spin-up. -/
private def ferroHoleConfig (N : ℕ) (x : Fin (N + 1)) : Fin (2 * N + 2) → Fin 2 :=
  hubbardOneHoleConfig N x (fun _ => true)

/-- The number of spin-up occupied sites in the ferromagnetic hole state is `N`. -/
private theorem ferroHole_up_count (N : ℕ) (x : Fin (N + 1)) :
    (∑ k : Fin (N + 1), (ferroHoleConfig N x (spinfulIndex N k 0)).val) = N := by
  have hval : ∀ k, (ferroHoleConfig N x (spinfulIndex N k 0)).val =
      if k ≠ x then 1 else 0 := by
    intro k
    rw [ferroHoleConfig, hubbardOneHoleConfig_apply_up]
    by_cases hk : k = x <;> simp_all [Fin.ext_iff]
  simp_rw [hval]
  rw [Finset.sum_boole, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ x)]
  simp

end LatticeSystem.Fermion
