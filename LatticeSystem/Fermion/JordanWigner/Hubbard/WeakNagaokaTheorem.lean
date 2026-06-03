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

/-- The down-orbital is empty at every site in the ferromagnetic hole state. -/
private theorem ferroHole_down_zero (N : ℕ) (x : Fin (N + 1)) (k : Fin (N + 1)) :
    ferroHoleConfig N x (spinfulIndex N k 1) = 0 := by
  rw [ferroHoleConfig, hubbardOneHoleConfig_apply_down]
  by_cases hk : k.val = x.val <;> simp [hk]

/-- The total spin-up number acts on the ferromagnetic hole state with
eigenvalue `N` (the number of electrons). -/
private theorem fermionTotalUpNumber_mulVec_ferroHole (N : ℕ) (x : Fin (N + 1)) :
    (fermionTotalUpNumber N).mulVec (basisVec (ferroHoleConfig N x)) =
      (N : ℂ) • basisVec (ferroHoleConfig N x) := by
  unfold fermionTotalUpNumber fermionUpNumber
  rw [Matrix.sum_mulVec]
  rw [Finset.sum_congr rfl (fun k _ =>
    fermionMultiNumber_mulVec_basisVec (2 * N + 1) (spinfulIndex N k 0) _)]
  rw [← Finset.sum_smul]
  congr 1
  rw [← Nat.cast_sum, ferroHole_up_count]

/-- The total spin-down number annihilates the ferromagnetic hole state. -/
private theorem fermionTotalDownNumber_mulVec_ferroHole (N : ℕ) (x : Fin (N + 1)) :
    (fermionTotalDownNumber N).mulVec (basisVec (ferroHoleConfig N x)) = 0 := by
  unfold fermionTotalDownNumber fermionDownNumber
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro k _
  rw [fermionMultiNumber_mulVec_basisVec, ferroHole_down_zero]
  simp

/-- `Ŝ^z_tot` acts on the ferromagnetic hole state with eigenvalue `N/2 = S_max`. -/
private theorem fermionTotalSpinZ_mulVec_ferroHole (N : ℕ) (x : Fin (N + 1)) :
    (fermionTotalSpinZ N).mulVec (basisVec (ferroHoleConfig N x)) =
      ((N : ℂ) / 2) • basisVec (ferroHoleConfig N x) := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec, fermionTotalUpNumber_mulVec_ferroHole,
    fermionTotalDownNumber_mulVec_ferroHole, sub_zero, smul_smul]
  congr 1
  ring

/-- `Ŝ^+_tot` annihilates the ferromagnetic hole state (no down electrons). -/
private theorem fermionTotalSpinPlus_mulVec_ferroHole (N : ℕ) (x : Fin (N + 1)) :
    (fermionTotalSpinPlus N).mulVec (basisVec (ferroHoleConfig N x)) = 0 := by
  unfold fermionTotalSpinPlus fermionUpCreation fermionDownAnnihilation
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro k _
  rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec,
    if_neg (by rw [ferroHole_down_zero]; decide), Matrix.mulVec_zero]

/-- **The ferromagnetic hole state is maximal-spin** (the `S_tot = S_max` part
of Theorem 11.5): `(Ŝ_tot)² |Φ_{x,(↑)}⟩ = S_max(S_max+1) |Φ_{x,(↑)}⟩` with
`S_max = N/2`. -/
theorem fermionTotalSpinSquared_mulVec_ferroHole (N : ℕ) (x : Fin (N + 1)) :
    (fermionTotalSpinSquared N).mulVec (basisVec (ferroHoleConfig N x)) =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) • basisVec (ferroHoleConfig N x) := by
  unfold fermionTotalSpinSquared
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, fermionTotalSpinPlus_mulVec_ferroHole,
    Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, Matrix.add_mulVec,
    Matrix.one_mulVec, fermionTotalSpinZ_mulVec_ferroHole, Matrix.mulVec_add,
    Matrix.mulVec_smul, fermionTotalSpinZ_mulVec_ferroHole, smul_smul, ← add_smul]
  congr 1
  ring

/-! ## The spin-lowering multiplet is energy-degenerate -/

/-- `Ŝ^-_tot` maps an `Ĥ_eff`-eigenvector to an eigenvector at the same energy
(since `[Ĥ_eff, Ŝ^-_tot] = 0`): the spin-lowering multiplet of a ground state
is degenerate. -/
theorem hubbardEffectiveHamiltonian_mulVec_spinMinus
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℂ)
    (hv : (hubbardEffectiveHamiltonian N t U).mulVec v = E • v) :
    (hubbardEffectiveHamiltonian N t U).mulVec ((fermionTotalSpinMinus N).mulVec v) =
      E • ((fermionTotalSpinMinus N).mulVec v) := by
  rw [Matrix.mulVec_mulVec,
    ← (fermionTotalSpinMinus_commute_hubbardEffectiveHamiltonian N t U hJ hU).eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

end LatticeSystem.Fermion
