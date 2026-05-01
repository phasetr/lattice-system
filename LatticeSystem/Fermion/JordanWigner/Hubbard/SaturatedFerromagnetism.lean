import LatticeSystem.Fermion.JordanWigner.Hubbard.AllUpState

/-!
# Hubbard saturated ferromagnetism: Definition 11.1 (Tasaki §11.1.1)

This file defines the total-spin Casimir `(Ŝ_tot)²`, the predicate for saturated
ferromagnetism (Definition 11.1), and proves basic structural results for the all-up
state that underlie Proposition 11.2.

| Lean name | Statement |
|---|---|
| `fermionTotalSpinSquared` | Casimir `(Ŝ_tot)² = Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z + 1)` |
| `fermionTotalUpNumber_mulVec_allUpState` | `N_↑ · \|↑…↑⟩ = (N+1) • \|↑…↑⟩` |
| `fermionTotalDownNumber_mulVec_allUpState` | `N_↓ · \|↑…↑⟩ = 0` |
| `fermionTotalSpinZ_mulVec_allUpState` | `Ŝ^z_tot · \|↑…↑⟩ = ((N+1)/2) • \|↑…↑⟩` |
| `fermionTotalSpinPlus_mulVec_allUpState` | `Ŝ⁺_tot · \|↑…↑⟩ = 0` |
| `fermionTotalSpinSquared_mulVec_allUpState` | `(Ŝ_tot)² · \|↑…↑⟩ = S_max(S_max+1) • \|↑…↑⟩` |
| `fermionTotalSpinSquared_commute_hubbardHamiltonian` | `[(Ŝ_tot)², H] = 0` |
| `isSaturatedFerromagnet` | Definition 11.1: every ground state has `(Ŝ_tot)² = S_max(S_max+1)` |

Reference: H. Tasaki, §11.1.1, pp. 372–374.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

/-! ## Total-spin Casimir -/

/-- The total-spin Casimir `(Ŝ_tot)² = Ŝ⁻_tot Ŝ⁺_tot + Ŝ^z_tot(Ŝ^z_tot + 1)`.

From `[Ŝ⁺, Ŝ⁻] = 2Ŝ_z` one derives `Ŝ² = Ŝ⁻Ŝ⁺ + Ŝ_z(Ŝ_z + 1)`, which
gives `Ŝ²|S, M⟩ = S(S+1)|S, M⟩` for the highest-weight state with `Ŝ⁺|S,S⟩ = 0`.

Reference: Tasaki §11.1.1, p. 372. -/
noncomputable def fermionTotalSpinSquared (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  fermionTotalSpinMinus N * fermionTotalSpinPlus N +
    fermionTotalSpinZ N * (fermionTotalSpinZ N + 1)

/-! ## Total number actions on the all-up state -/

/-- `N_↑ = Σ_i n_{i,↑}` counts all `N+1` up-spin electrons:
`N_↑ · |↑…↑⟩ = (N+1 : ℂ) • |↑…↑⟩`. -/
theorem fermionTotalUpNumber_mulVec_allUpState (N : ℕ) :
    (fermionTotalUpNumber N).mulVec (hubbardAllUpState N) =
      ((N + 1 : ℕ) : ℂ) • hubbardAllUpState N := by
  unfold fermionTotalUpNumber
  rw [Matrix.sum_mulVec]
  simp only [fermionUpNumber_mulVec_allUpState]
  rw [Finset.sum_const, Finset.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]

/-- `N_↓ = Σ_i n_{i,↓}` annihilates the all-up state:
`N_↓ · |↑…↑⟩ = 0`. -/
theorem fermionTotalDownNumber_mulVec_allUpState (N : ℕ) :
    (fermionTotalDownNumber N).mulVec (hubbardAllUpState N) = 0 := by
  unfold fermionTotalDownNumber
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  exact fermionDownNumber_mulVec_allUpState N i

/-! ## Spin component actions on the all-up state -/

/-- `Ŝ^z_tot = (1/2)(N_↑ − N_↓)` has eigenvalue `(N+1)/2` on the all-up state.

Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinZ_mulVec_allUpState (N : ℕ) :
    (fermionTotalSpinZ N).mulVec (hubbardAllUpState N) =
      (((N + 1 : ℕ) : ℂ) / 2) • hubbardAllUpState N := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Matrix.sub_mulVec,
    fermionTotalUpNumber_mulVec_allUpState, fermionTotalDownNumber_mulVec_allUpState,
    sub_zero, smul_smul,
    show (1 / 2 : ℂ) * ((N + 1 : ℕ) : ℂ) = (((N + 1 : ℕ) : ℂ) / 2) from by push_cast; ring]

/-- `Ŝ⁺_tot = Σ_i c†_{i,↑} c_{i,↓}` annihilates the all-up state:
`Ŝ⁺_tot · |↑…↑⟩ = 0` (highest-weight state: no down electrons to raise).

Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinPlus_mulVec_allUpState (N : ℕ) :
    (fermionTotalSpinPlus N).mulVec (hubbardAllUpState N) = 0 := by
  unfold fermionTotalSpinPlus
  rw [Matrix.sum_mulVec]
  apply Finset.sum_eq_zero
  intro i _
  rw [← Matrix.mulVec_mulVec,
    fermionDownAnnihilation_mulVec_allUpState, Matrix.mulVec_zero]

/-! ## Casimir eigenvalue on the all-up state -/

set_option maxHeartbeats 400000 in
-- The repeated Ŝ_z mulVec rewrites over the Casimir expansion exceed the default limit.
/-- `(Ŝ_tot)²` acts on the all-up state with eigenvalue `S_max(S_max+1)` where
`S_max = (N+1)/2`: `(Ŝ_tot)² · |↑…↑⟩ = ((N+1)/2 · ((N+1)/2 + 1)) • |↑…↑⟩`.

Uses `Ŝ⁺|allUp⟩ = 0` and `Ŝ_z|allUp⟩ = ((N+1)/2)|allUp⟩`.

Reference: Tasaki §11.1.1, p. 372. -/
theorem fermionTotalSpinSquared_mulVec_allUpState (N : ℕ) :
    (fermionTotalSpinSquared N).mulVec (hubbardAllUpState N) =
      (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) •
        hubbardAllUpState N := by
  unfold fermionTotalSpinSquared
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    fermionTotalSpinPlus_mulVec_allUpState, Matrix.mulVec_zero, zero_add]
  -- goal: (Ŝ_z * (Ŝ_z + 1)) *ᵥ allUp = S_max(S_max+1) • allUp
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    fermionTotalSpinZ_mulVec_allUpState]
  -- goal: Ŝ_z *ᵥ (S_max • allUp + allUp) = S_max(S_max+1) • allUp
  rw [Matrix.mulVec_add, Matrix.mulVec_smul,
    fermionTotalSpinZ_mulVec_allUpState,
    smul_smul, ← add_smul]
  congr 1
  ring

/-! ## Casimir commutes with the Hamiltonian -/

/-- `(Ŝ_tot)²` commutes with the Hubbard Hamiltonian:
`[(Ŝ_tot)², H] = 0`.

Follows from `[Ŝ⁺, H] = [Ŝ⁻, H] = [Ŝ_z, H] = 0` (SU(2) invariance, proved in
SpinSymmetry.lean). The Hermiticity conditions `hJ`, `hU` are needed for
the `Ŝ⁻` commutator.

Reference: Tasaki §9.3.3, p. 333; §11.1.1, p. 372. -/
theorem fermionTotalSpinSquared_commute_hubbardHamiltonian
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U) :
    Commute (fermionTotalSpinSquared N) (hubbardHamiltonian N t U) := by
  unfold fermionTotalSpinSquared
  apply Commute.add_left
  · -- [Ŝ⁻Ŝ⁺, H] = 0
    exact (fermionTotalSpinMinus_commute_hubbardHamiltonian N t U
        (hJ := hJ) (hU := hU)).mul_left
      (fermionTotalSpinPlus_commute_hubbardHamiltonian N t U)
  · -- [Ŝ_z(Ŝ_z + 1), H] = 0
    have h_z := fermionTotalSpinZ_commute_hubbardHamiltonian N t U
    exact h_z.mul_left (h_z.add_left (Commute.one_left _))

/-! ## Definition 11.1: saturated ferromagnetism -/

/-- **Definition 11.1** (Tasaki §11.1.1, p. 372): the Hubbard model exhibits
*saturated ferromagnetism* if there exists a ground-state energy `E₀` such that
every `H`-eigenvector with eigenvalue `E₀` is also a `(Ŝ_tot)²`-eigenvector
with eigenvalue `S_max(S_max + 1) = (N+1)/2 · ((N+1)/2 + 1)`.

The "minimum eigenvalue" condition is implicit in `E₀` being the true ground-state
energy; a separate predicate can impose `E₀ = min_spec (hubbardHamiltonian N t U)`. -/
def isSaturatedFerromagnet
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) : Prop :=
  ∃ E₀ : ℂ,
    ∀ v : (Fin (2 * N + 2) → Fin 2) → ℂ,
      v ≠ 0 →
      (hubbardHamiltonian N t U).mulVec v = E₀ • v →
        (fermionTotalSpinSquared N).mulVec v =
          (((N + 1 : ℕ) : ℂ) / 2 * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • v

/-! ## SU(2) commutator algebra -/

/-- Key lemma: `[Ŝ^z_tot, c†_{i,↓} c_{i,↑}] = -(c†_{i,↓} c_{i,↑})` for each site.

Proof: `[N_↑, A] = -A` (cross-spin + same-spin annihilation commutator) and
`[N_↓, A] = A` (same-spin creation + cross-spin commutator), so
`[Ŝ_z, A] = (1/2)(-A - A) = -A`. -/
private theorem spinZ_commutator_spinMinus_summand (N : ℕ) (i : Fin (N + 1)) :
    fermionTotalSpinZ N * (fermionDownCreation N i * fermionUpAnnihilation N i) -
      (fermionDownCreation N i * fermionUpAnnihilation N i) * fermionTotalSpinZ N =
      -(fermionDownCreation N i * fermionUpAnnihilation N i) := by
  -- [N_↑, c↓†·c↑] = -c↓†·c↑: N_↑ commutes with c↓†, so N_↑·(c↓†·c↑) = c↓†·(N_↑·c↑)
  have h_up : fermionTotalUpNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) -
      (fermionDownCreation N i * fermionUpAnnihilation N i) * fermionTotalUpNumber N =
      -(fermionDownCreation N i * fermionUpAnnihilation N i) := by
    have hstep : fermionTotalUpNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) =
        fermionDownCreation N i * (fermionTotalUpNumber N * fermionUpAnnihilation N i) := by
      rw [← Matrix.mul_assoc, (fermionTotalUpNumber_commute_fermionDownCreation N i).eq,
          Matrix.mul_assoc]
    rw [hstep, Matrix.mul_assoc, ← Matrix.mul_sub,
        fermionTotalUpNumber_commutator_fermionUpAnnihilation, Matrix.mul_neg]
  -- [N_↓, c↓†·c↑] = c↓†·c↑: [N_↓, c↓†] = c↓†, N_↓ commutes with c↑
  have h_down : fermionTotalDownNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) -
      (fermionDownCreation N i * fermionUpAnnihilation N i) * fermionTotalDownNumber N =
      (fermionDownCreation N i * fermionUpAnnihilation N i) := by
    have hstep1 : fermionTotalDownNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) =
        (fermionTotalDownNumber N * fermionDownCreation N i) * fermionUpAnnihilation N i := by
      rw [← Matrix.mul_assoc]
    have hstep2 : (fermionDownCreation N i * fermionUpAnnihilation N i) * fermionTotalDownNumber N =
        (fermionDownCreation N i * fermionTotalDownNumber N) * fermionUpAnnihilation N i := by
      rw [Matrix.mul_assoc, (fermionTotalDownNumber_commute_fermionUpAnnihilation N i).symm.eq,
          ← Matrix.mul_assoc]
    rw [hstep1, hstep2, ← Matrix.sub_mul, fermionTotalDownNumber_commutator_fermionDownCreation]
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_sub, Matrix.sub_mul, Matrix.mul_sub]
  -- Goal: (1/2) • (N_↑*A - N_↓*A - (A*N_↑ - A*N_↓)) = -A
  have h_rearrange :
      fermionTotalUpNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) -
        fermionTotalDownNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) -
        (fermionDownCreation N i * fermionUpAnnihilation N i * fermionTotalUpNumber N -
          fermionDownCreation N i * fermionUpAnnihilation N i * fermionTotalDownNumber N) =
      (fermionTotalUpNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) -
        fermionDownCreation N i * fermionUpAnnihilation N i * fermionTotalUpNumber N) -
      (fermionTotalDownNumber N * (fermionDownCreation N i * fermionUpAnnihilation N i) -
        fermionDownCreation N i * fermionUpAnnihilation N i * fermionTotalDownNumber N) := by
    abel
  rw [h_rearrange, h_up, h_down]
  -- Goal: (1/2 : ℂ) • (-A - A) = -A where A = fermionDownCreation N i * fermionUpAnnihilation N i
  have h2 : -(fermionDownCreation N i * fermionUpAnnihilation N i) -
      fermionDownCreation N i * fermionUpAnnihilation N i =
      (-2 : ℂ) • (fermionDownCreation N i * fermionUpAnnihilation N i) := by
    have hrhs : (-2 : ℂ) • (fermionDownCreation N i * fermionUpAnnihilation N i) =
        -(fermionDownCreation N i * fermionUpAnnihilation N i +
          fermionDownCreation N i * fermionUpAnnihilation N i) := by
      rw [show (-2 : ℂ) = -(2 : ℂ) from by norm_num, neg_smul, two_smul]
    rw [hrhs]; abel
  rw [h2, smul_smul, show (1 / 2 : ℂ) * -2 = -1 from by norm_num]
  exact neg_one_smul ℂ _

/-- `[Ŝ^z_tot, Ŝ^-_tot] = -Ŝ^-_tot` — the SU(2) algebra relation.

Each site contributes `[Ŝ_z, c†_{i,↓} c_{i,↑}] = -(c†_{i,↓} c_{i,↑})`.

Reference: Tasaki §9.3.3, p. 332. -/
theorem fermionTotalSpinZ_commutator_fermionTotalSpinMinus (N : ℕ) :
    fermionTotalSpinZ N * fermionTotalSpinMinus N -
      fermionTotalSpinMinus N * fermionTotalSpinZ N =
      -fermionTotalSpinMinus N := by
  unfold fermionTotalSpinMinus
  rw [Matrix.mul_sum, Matrix.sum_mul]
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact spinZ_commutator_spinMinus_summand N i

/-! ## Eigenvalue preservation -/

/-- Applying `Ŝ^-_tot` preserves eigenvalues of the Hubbard Hamiltonian:
if `H · v = E · v` then `H · (Ŝ⁻ · v) = E · (Ŝ⁻ · v)`.

Follows from `[Ŝ⁻, H] = 0`. Hermiticity conditions are needed for
`fermionTotalSpinMinus_commute_hubbardHamiltonian`.

Reference: Tasaki §11.1.1, p. 373. -/
theorem fermionTotalSpinMinus_mulVec_preserves_hamiltonian_eigenvalue
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℂ)
    (hv : (hubbardHamiltonian N t U).mulVec v = E • v) :
    (hubbardHamiltonian N t U).mulVec
      ((fermionTotalSpinMinus N).mulVec v) = E • (fermionTotalSpinMinus N).mulVec v := by
  rw [Matrix.mulVec_mulVec,
    (fermionTotalSpinMinus_commute_hubbardHamiltonian N t U (hJ := hJ) (hU := hU)).symm.eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- If `Ŝ_z · v = m · v`, then `Ŝ_z · (Ŝ⁻ · v) = (m - 1) · (Ŝ⁻ · v)`:
applying `Ŝ⁻` decrements the `Ŝ_z` eigenvalue by 1.

Follows from `[Ŝ^z, Ŝ⁻] = -Ŝ⁻`.

Reference: Tasaki §2.4, eq. (2.4.9); §11.1.1, p. 373. -/
theorem fermionTotalSpinZ_mulVec_spinMinus_step
    (N : ℕ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (m : ℂ)
    (hv : (fermionTotalSpinZ N).mulVec v = m • v) :
    (fermionTotalSpinZ N).mulVec ((fermionTotalSpinMinus N).mulVec v) =
      (m - 1) • (fermionTotalSpinMinus N).mulVec v := by
  -- From [Ŝ_z, Ŝ⁻] = -Ŝ⁻: Ŝ_z·Ŝ⁻ = Ŝ⁻·Ŝ_z - Ŝ⁻
  have h_eq : fermionTotalSpinZ N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinZ N - fermionTotalSpinMinus N := by
    have h := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
    calc fermionTotalSpinZ N * fermionTotalSpinMinus N
        = (fermionTotalSpinZ N * fermionTotalSpinMinus N -
            fermionTotalSpinMinus N * fermionTotalSpinZ N) +
            fermionTotalSpinMinus N * fermionTotalSpinZ N := by abel
      _ = -fermionTotalSpinMinus N + fermionTotalSpinMinus N * fermionTotalSpinZ N := by
            rw [h]
      _ = fermionTotalSpinMinus N * fermionTotalSpinZ N - fermionTotalSpinMinus N := by abel
  rw [Matrix.mulVec_mulVec, h_eq, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_smul, sub_smul, one_smul]

end LatticeSystem.Fermion
