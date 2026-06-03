import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaoka
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianSpinSymmetry
import Mathlib.LinearAlgebra.Eigenspace.Basic

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

/-- `Ŝ^z_tot` acts on the `k`-fold lowered ferromagnetic hole state with
eigenvalue `N/2 − k`: the spin-lowering tower has distinct `Ŝ^z` eigenvalues
(the basis for its linear independence). -/
theorem fermionTotalSpinZ_mulVec_spinMinusPow_ferroHole (N : ℕ) (x : Fin (N + 1))
    (k : ℕ) :
    (fermionTotalSpinZ N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) =
      ((N : ℂ) / 2 - k) •
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) := by
  have hcomm : fermionTotalSpinZ N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinZ N - fermionTotalSpinMinus N := by
    have h := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, Nat.cast_zero, sub_zero,
      fermionTotalSpinZ_mulVec_ferroHole]
  | succ k ih =>
    have hexp : ((fermionTotalSpinMinus N) ^ (k + 1)).mulVec
          (basisVec (ferroHoleConfig N x)) =
        (fermionTotalSpinMinus N).mulVec
          (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hexp, Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, Nat.cast_succ]
    module

/-! ## The SU(2) ladder commutator `[Ŝ⁺, Ŝ⁻] = 2 Ŝ^z` -/

/-- Per-site contribution to `[Ŝ^+_tot, Ŝ^-_tot]`:
`[Ŝ^+_tot, c^†_{j,↓} c_{j,↑}] = n_{j,↑} − n_{j,↓}`, using
`[Ŝ^+_tot, c^†_{j,↓}] = c^†_{j,↑}` and `[Ŝ^+_tot, c_{j,↑}] = −c_{j,↓}`. -/
private theorem fermionTotalSpinPlus_commutator_spinMinusTerm (N : ℕ) (j : Fin (N + 1)) :
    fermionTotalSpinPlus N * (fermionDownCreation N j * fermionUpAnnihilation N j) -
        (fermionDownCreation N j * fermionUpAnnihilation N j) * fermionTotalSpinPlus N =
      fermionUpNumber N j - fermionDownNumber N j := by
  have hSa : fermionTotalSpinPlus N * fermionDownCreation N j =
      fermionDownCreation N j * fermionTotalSpinPlus N + fermionUpCreation N j := by
    have h := fermionDownCreation_commutator_fermionTotalSpinPlus N j
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have hSb : fermionTotalSpinPlus N * fermionUpAnnihilation N j =
      fermionUpAnnihilation N j * fermionTotalSpinPlus N - fermionDownAnnihilation N j := by
    have h := fermionUpAnnihilation_commutator_fermionTotalSpinPlus N j
    rw [sub_eq_iff_eq_add] at h; rw [h]; abel
  have hn_up : fermionUpNumber N j =
      fermionUpCreation N j * fermionUpAnnihilation N j := rfl
  have hn_dn : fermionDownNumber N j =
      fermionDownCreation N j * fermionDownAnnihilation N j := rfl
  calc fermionTotalSpinPlus N * (fermionDownCreation N j * fermionUpAnnihilation N j) -
        (fermionDownCreation N j * fermionUpAnnihilation N j) * fermionTotalSpinPlus N
      = (fermionTotalSpinPlus N * fermionDownCreation N j) * fermionUpAnnihilation N j -
          (fermionDownCreation N j * fermionUpAnnihilation N j) * fermionTotalSpinPlus N := by
        rw [← Matrix.mul_assoc]
    _ = (fermionDownCreation N j * fermionTotalSpinPlus N + fermionUpCreation N j) *
            fermionUpAnnihilation N j -
          (fermionDownCreation N j * fermionUpAnnihilation N j) * fermionTotalSpinPlus N := by
        rw [hSa]
    _ = fermionDownCreation N j *
            (fermionTotalSpinPlus N * fermionUpAnnihilation N j) +
          fermionUpCreation N j * fermionUpAnnihilation N j -
          (fermionDownCreation N j * fermionUpAnnihilation N j) * fermionTotalSpinPlus N := by
        rw [add_mul, Matrix.mul_assoc]
    _ = fermionDownCreation N j *
            (fermionUpAnnihilation N j * fermionTotalSpinPlus N -
              fermionDownAnnihilation N j) +
          fermionUpCreation N j * fermionUpAnnihilation N j -
          (fermionDownCreation N j * fermionUpAnnihilation N j) * fermionTotalSpinPlus N := by
        rw [hSb]
    _ = fermionUpCreation N j * fermionUpAnnihilation N j -
          fermionDownCreation N j * fermionDownAnnihilation N j := by noncomm_ring
    _ = fermionUpNumber N j - fermionDownNumber N j := by rw [hn_up, hn_dn]

/-- **The SU(2) ladder commutator** `[Ŝ^+_tot, Ŝ^-_tot] = 2 Ŝ^z_tot`
(Tasaki §9.3.3, p. 332): the precursor to the ladder-norm identity
`‖Ŝ^-_tot v‖² = ⟨v | Ŝ^+_tot Ŝ^-_tot | v⟩` used to prove the spin-lowering
multiplet is nonzero. -/
theorem fermionTotalSpinPlus_commutator_fermionTotalSpinMinus (N : ℕ) :
    fermionTotalSpinPlus N * fermionTotalSpinMinus N -
        fermionTotalSpinMinus N * fermionTotalSpinPlus N =
      (2 : ℂ) • fermionTotalSpinZ N := by
  unfold fermionTotalSpinMinus
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun j _ => fermionTotalSpinPlus_commutator_spinMinusTerm N j),
    Finset.sum_sub_distrib]
  simp only [fermionTotalSpinZ, smul_smul]
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, one_smul]
  rfl

/-! ## The Casimir operator commutes with the lowering operator -/

/-- **`[(Ŝ_tot)², Ŝ^-_tot] = 0`**: the total-spin Casimir commutes with the
lowering operator, so the entire spin-lowering tower `(Ŝ^-_tot)^k |Φ⟩` stays in
a single total-spin sector. Derived from the SU(2) algebra
`[Ŝ^+_tot, Ŝ^-_tot] = 2 Ŝ^z_tot` and `[Ŝ^z_tot, Ŝ^-_tot] = −Ŝ^-_tot`: both
sides of `(Ŝ_tot)² Ŝ^-_tot = Ŝ^-_tot (Ŝ_tot)²` reduce to
`Ŝ^- Ŝ^- Ŝ^+ + Ŝ^- Ŝ^z Ŝ^z + Ŝ^- Ŝ^z`. -/
theorem fermionTotalSpinSquared_commute_fermionTotalSpinMinus (N : ℕ) :
    Commute (fermionTotalSpinSquared N) (fermionTotalSpinMinus N) := by
  have hPM : fermionTotalSpinPlus N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinPlus N +
        (2 : ℂ) • fermionTotalSpinZ N := by
    have h := fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N
    rwa [sub_eq_iff_eq_add'] at h
  have hZM : fermionTotalSpinZ N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinZ N - fermionTotalSpinMinus N := by
    have h := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  show fermionTotalSpinSquared N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinSquared N
  unfold fermionTotalSpinSquared
  set P := fermionTotalSpinPlus N
  set M := fermionTotalSpinMinus N
  set Z := fermionTotalSpinZ N
  have e1 : M * P * M = M * M * P + (2 : ℂ) • (M * Z) := by
    rw [Matrix.mul_assoc, hPM, mul_add, mul_smul_comm, ← Matrix.mul_assoc]
  have e2 : Z * Z * M = M * Z * Z - (2 : ℂ) • (M * Z) + M := by
    calc Z * Z * M
        = Z * (Z * M) := Matrix.mul_assoc Z Z M
      _ = Z * (M * Z - M) := by rw [hZM]
      _ = Z * (M * Z) - Z * M := by rw [mul_sub]
      _ = (Z * M) * Z - Z * M := by rw [← Matrix.mul_assoc]
      _ = (M * Z - M) * Z - (M * Z - M) := by simp only [hZM]
      _ = M * Z * Z - (2 : ℂ) • (M * Z) + M := by rw [sub_mul]; module
  have hL : (M * P + Z * (Z + 1)) * M = M * M * P + M * Z * Z + M * Z := by
    calc (M * P + Z * (Z + 1)) * M
        = M * P * M + (Z * Z + Z) * M := by rw [add_mul, mul_add, mul_one]
      _ = M * P * M + (Z * Z * M + Z * M) := by rw [add_mul]
      _ = (M * M * P + (2 : ℂ) • (M * Z)) +
            ((M * Z * Z - (2 : ℂ) • (M * Z) + M) + (M * Z - M)) := by
            rw [e1, e2, hZM]
      _ = M * M * P + M * Z * Z + M * Z := by module
  have hR : M * (M * P + Z * (Z + 1)) = M * M * P + M * Z * Z + M * Z := by
    noncomm_ring
  rw [hL, hR]

/-! ## Raising-after-lowering via the Casimir -/

/-- **`Ŝ^+_tot Ŝ^-_tot = (Ŝ_tot)² − Ŝ^z_tot (Ŝ^z_tot − 1)`**: the
raising-after-lowering product expressed through the Casimir. On a state with
Casimir eigenvalue `S(S+1)` and `Ŝ^z` eigenvalue `m`, this gives
`Ŝ^+_tot Ŝ^-_tot = S(S+1) − m(m−1)`, which is the squared norm of the lowered
state and the engine behind the spin-multiplet's nonvanishing. Derived from the
Casimir definition `(Ŝ_tot)² = Ŝ^-_tot Ŝ^+_tot + Ŝ^z_tot (Ŝ^z_tot + 1)` and the
ladder commutator `Ŝ^+_tot Ŝ^-_tot = Ŝ^-_tot Ŝ^+_tot + 2 Ŝ^z_tot`. -/
theorem fermionTotalSpinPlus_mul_fermionTotalSpinMinus (N : ℕ) :
    fermionTotalSpinPlus N * fermionTotalSpinMinus N =
      fermionTotalSpinSquared N -
        fermionTotalSpinZ N * (fermionTotalSpinZ N - 1) := by
  have hPM : fermionTotalSpinPlus N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinPlus N +
        (2 : ℂ) • fermionTotalSpinZ N := by
    have h := fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N
    rwa [sub_eq_iff_eq_add'] at h
  rw [hPM]
  unfold fermionTotalSpinSquared
  rw [two_smul]
  noncomm_ring

/-! ## The spin-lowering multiplet is nonzero -/

/-- The Casimir is constant along the spin-lowering tower:
`(Ŝ_tot)² (Ŝ^-_tot)^k |Φ_{x,(↑)}⟩ = S_max(S_max+1) (Ŝ^-_tot)^k |Φ_{x,(↑)}⟩`
with `S_max = N/2`, since `[(Ŝ_tot)², Ŝ^-_tot] = 0` and the base state has
maximal spin. So the whole tower lies in the `S_tot = S_max` sector. -/
theorem fermionTotalSpinSquared_mulVec_spinMinusPow_ferroHole (N : ℕ) (x : Fin (N + 1))
    (k : ℕ) :
    (fermionTotalSpinSquared N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) •
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) := by
  rw [Matrix.mulVec_mulVec,
    (Commute.pow_right (fermionTotalSpinSquared_commute_fermionTotalSpinMinus N) k).eq,
    ← Matrix.mulVec_mulVec, fermionTotalSpinSquared_mulVec_ferroHole, Matrix.mulVec_smul]

/-- `Ŝ^+_tot Ŝ^-_tot` acts on the `k`-fold lowered ferromagnetic hole state with
eigenvalue `S_max(S_max+1) − m(m−1)` where `m = N/2 − k`: combining the Casimir
tower, the `Ŝ^z` tower, and `Ŝ^+_tot Ŝ^-_tot = (Ŝ_tot)² − Ŝ^z_tot(Ŝ^z_tot − 1)`.
This eigenvalue equals `(k+1)(N−k)` and drives the multiplet's nonvanishing. -/
theorem fermionTotalSpinPlusMinus_mulVec_spinMinusPow_ferroHole (N : ℕ) (x : Fin (N + 1))
    (k : ℕ) :
    (fermionTotalSpinPlus N * fermionTotalSpinMinus N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1) -
          ((N : ℂ) / 2 - k) * ((N : ℂ) / 2 - k - 1)) •
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) := by
  rw [fermionTotalSpinPlus_mul_fermionTotalSpinMinus, Matrix.sub_mulVec,
    fermionTotalSpinSquared_mulVec_spinMinusPow_ferroHole,
    ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    fermionTotalSpinZ_mulVec_spinMinusPow_ferroHole,
    Matrix.mulVec_sub, Matrix.mulVec_smul,
    fermionTotalSpinZ_mulVec_spinMinusPow_ferroHole]
  module

/-- **The spin-lowering multiplet is nonzero**: `(Ŝ^-_tot)^k |Φ_{x,(↑)}⟩ ≠ 0`
for every `k ≤ N`. Purely algebraic, no inner product: if it vanished then
`Ŝ^+_tot (Ŝ^-_tot)^{k+1} |Φ⟩ = (Ŝ^+ Ŝ^-) (Ŝ^-)^k |Φ⟩ = (k+1)(N−k) (Ŝ^-)^k|Φ⟩`
would also vanish, but `(k+1)(N−k) ≠ 0` for `k < N` and `(Ŝ^-)^k|Φ⟩ ≠ 0` by
induction. This gives the `(2 S_max + 1) = N+1` distinct members of the
degenerate ground-state multiplet. -/
theorem spinMinusPow_ferroHole_ne_zero (N : ℕ) (x : Fin (N + 1)) :
    ∀ k : ℕ, k ≤ N →
      ((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x)) ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _ h
    rw [pow_zero, Matrix.one_mulVec] at h
    have h2 := congrFun h (ferroHoleConfig N x)
    rw [Pi.zero_apply, basisVec_self] at h2
    exact one_ne_zero h2
  | succ k ih =>
    intro hk hzero
    have hk' : k ≤ N := Nat.le_of_succ_le hk
    have hklt : k < N := hk
    have hψk := ih hk'
    have hc : (N : ℂ) / 2 * ((N : ℂ) / 2 + 1) -
        ((N : ℂ) / 2 - k) * ((N : ℂ) / 2 - k - 1) ≠ 0 := by
      have heq : (N : ℂ) / 2 * ((N : ℂ) / 2 + 1) -
          ((N : ℂ) / 2 - k) * ((N : ℂ) / 2 - k - 1) = ((k : ℂ) + 1) * ((N : ℂ) - k) := by
        ring
      rw [heq]
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      rw [sub_ne_zero]
      exact_mod_cast (Nat.ne_of_lt hklt).symm
    have harg : (fermionTotalSpinMinus N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) = 0 := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']; exact hzero
    have key := fermionTotalSpinPlusMinus_mulVec_spinMinusPow_ferroHole N x k
    rw [← Matrix.mulVec_mulVec, harg, Matrix.mulVec_zero] at key
    rcases smul_eq_zero.mp key.symm with h | h
    · exact hc h
    · exact hψk h

/-! ## Linear independence of the spin multiplet -/

/-- **The spin-lowering multiplet is linearly independent**: the `N + 1` states
`(Ŝ^-_tot)^k |Φ_{x,(↑)}⟩` for `k ∈ {0, …, N}` are linearly independent, because
they are nonzero eigenvectors of `Ŝ^z_tot` with the pairwise-distinct eigenvalues
`N/2 − k`. Together with energy degeneracy this exhibits the
`(2 S_max + 1) = N + 1` degenerate ground states of the weak Nagaoka theorem. -/
theorem spinMinusPow_ferroHole_linearIndependent (N : ℕ) (x : Fin (N + 1)) :
    LinearIndependent ℂ (fun k : Fin (N + 1) =>
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec (basisVec (ferroHoleConfig N x))) := by
  apply Module.End.eigenvectors_linearIndependent' (fermionTotalSpinZ N).mulVecLin
    (fun k : Fin (N + 1) => (N : ℂ) / 2 - (k : ℕ))
  · intro a b hab
    rw [sub_right_inj] at hab
    have h2 : (a : ℕ) = (b : ℕ) := by exact_mod_cast hab
    exact Fin.ext h2
  · intro k
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact fermionTotalSpinZ_mulVec_spinMinusPow_ferroHole N x (k : ℕ)
    · exact spinMinusPow_ferroHole_ne_zero N x (k : ℕ) (Nat.le_of_lt_succ k.isLt)
