import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem

/-!
# Tasaki Theorem 11.5: existence of the ferromagnetic ground state

The capstone `weakNagaoka_spinMultiplet`
(`Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean`) reduces the weak Nagaoka
theorem to the *existence* of a nonzero highest-weight `Ĥ_eff`-eigenvector — a
ferromagnetic ground state. Following Tasaki's §11.2.1 proof, this is obtained by
the variational (Schwarz) argument, **not** by Perron–Frobenius (PF and the
connectivity/irreducibility condition belong to §11.2.2, Theorem 11.7):

1. Take an arbitrary ground state `|Φ_GS⟩` of `Ĥ_eff`, expanded in the one-hole
   hard-core Tasaki basis with (real) coefficients `ϕ(x, σ)` (eq. (11.2.6)).
2. Ferromagnetize it: `ξ_x = (Σ_σ ϕ(x, σ)²)^{1/2}` (eq. (11.2.7)) and
   `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩` (eq. (11.2.8)).
3. The Schwarz inequality (eq. (11.2.9), already formalized as
   `hubbardWeakNagaoka_energy_bound`) gives `⟨Φ_↑|Ĥ_eff|Φ_↑⟩ ≤ ⟨Φ_GS|Ĥ_eff|Φ_GS⟩`,
   and `|Φ_↑⟩` has the same norm (`tasakiFerro_normSq_eq`), so `|Φ_↑⟩` is also a
   ground state.
4. `|Φ_↑⟩` is a highest-weight maximal-spin state, so `weakNagaoka_spinMultiplet`
   produces the full `(2 S_max + 1)`-multiplet.

This file builds the ferromagnetic state `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩` and its
highest-weight (maximal-spin) and nonvanishing properties.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, Theorem 11.5, pp. 382-385.
-/

namespace LatticeSystem.Fermion

open Matrix

/-! ## The ferromagnetic state -/

/-- The ferromagnetic state `|Φ_↑⟩ = Σ_x ξ_x |Φ^T_{x,↑}⟩` (Tasaki eq. (11.2.8))
built from real weights `ξ`: a superposition over hole positions of the all-up
Tasaki basis states. With `ξ_x` the ferromagnetized coefficients (`ferroXi`) of a
ground state, this is the ferromagnetic ground state `|Φ_↑⟩`. -/
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

/-- The ferromagnetic state is nonzero when the weights are strictly positive: its
squared norm is `Σ_x ξ_x² > 0` by orthonormality of the Tasaki basis. -/
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

/-! ## The effective Hamiltonian conserves particle number

These prepare the operator-lift step: `Ĥ_eff` maps the one-hole hard-core sector
to itself (it preserves both the hard-core constraint and the electron number),
so its action on the Tasaki basis stays in the span of the basis. -/

/-- The same-site double-occupancy operator commutes with the total electron
number (it is a product of number operators). -/
theorem hubbardDoubleOccupancy_commute_fermionTotalNumber (N : ℕ) (i : Fin (N + 1)) :
    Commute (hubbardDoubleOccupancy N i) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardDoubleOccupancy fermionUpNumber fermionDownNumber
  exact (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N i 0)).mul_left
    (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N i 1))

/-- Each hard-core factor `1 - n_{i,↑} n_{i,↓}` commutes with the total electron
number. -/
theorem hubbardHardcoreFactor_commute_fermionTotalNumber (N : ℕ) (i : Fin (N + 1)) :
    Commute (hubbardHardcoreFactor N i) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHardcoreFactor
  exact (Commute.one_left _).sub_left (hubbardDoubleOccupancy_commute_fermionTotalNumber N i)

/-- The hard-core projection commutes with the total electron number. -/
theorem hubbardHardcoreProjection_commute_fermionTotalNumber (N : ℕ) :
    Commute (hubbardHardcoreProjection N) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHardcoreProjection
  exact (Finset.noncommProd_commute _ _ _ _
    (fun i _ => (hubbardHardcoreFactor_commute_fermionTotalNumber N i).symm)).symm

/-- **`Ĥ_eff` conserves the total electron number** `[Ĥ_eff, N̂] = 0`: it is built
from the number-conserving Hubbard Hamiltonian compressed by the
number-conserving hard-core projection. Hence `Ĥ_eff` preserves the fixed-electron
sectors, in particular the one-hole hard-core sector. -/
theorem hubbardEffectiveHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardEffectiveHamiltonian N t U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardEffectiveHamiltonian
  exact ((hubbardHardcoreProjection_commute_fermionTotalNumber N).mul_left
    (hubbardHamiltonian_commute_fermionTotalNumber N t U)).mul_left
    (hubbardHardcoreProjection_commute_fermionTotalNumber N)

end LatticeSystem.Fermion
