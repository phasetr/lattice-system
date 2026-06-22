import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaoka
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonianSpinSymmetry
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Weak Nagaoka theorem: SU(2) ladder / Casimir foundation

Foundational layer extracted from `WeakNagaokaTheorem.lean` for build speed
(Tasaki §9.3.3, Theorem 11.5 core).  This file develops the ferromagnetic-hole-state
spin data (`ferroHoleConfig`, total up/down-number and `Ŝ^z`/`Ŝ⁺` action), the all-up
highest-weight identification, the energy degeneracy of the spin-lowering multiplet, and
the SU(2) ladder commutator `[Ŝ⁺, Ŝ⁻] = 2 Ŝ^z` with the Casimir–lowering commutation.

The raising-after-lowering Casimir identities, the multiplet non-vanishing / linear
independence, the whole-tower energy degeneracy, and the weak Nagaoka spin multiplet
(plus the ferromagnetic-hole highest-weight state) are kept in the capstone module
`WeakNagaokaTheorem.lean`.

To let the capstone reuse the hole-state spin data across the module boundary,
`ferroHoleConfig` and `fermionTotalSpinZ_mulVec_ferroHole` are module-public here; the
remaining hole-state helper lemmas stay `private`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed., Springer, 2020), §9.3.3 (Theorem 11.5 core).
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
def ferroHoleConfig (N : ℕ) (x : Fin (N + 1)) : Fin (2 * N + 2) → Fin 2 :=
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
theorem fermionTotalSpinZ_mulVec_ferroHole (N : ℕ) (x : Fin (N + 1)) :
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

/-! ## The all-up Tasaki basis state is a highest-weight maximal-spin state -/

/-- `Ŝ^+_tot` annihilates the all-up Tasaki basis state
`|Φ^T_{x,↑}⟩ = ε • |Φ_{x,↑}⟩` (no down electrons to raise). -/
theorem fermionTotalSpinPlus_mulVec_hubbardTasakiBasisStateUp (N : ℕ) (x : Fin (N + 1)) :
    (fermionTotalSpinPlus N).mulVec (hubbardTasakiBasisState N x (fun _ => true)) = 0 := by
  rw [hubbardTasakiBasisState_eq_smul_basisVec, Matrix.mulVec_smul,
    show hubbardOneHoleConfig N x (fun _ => true) = ferroHoleConfig N x from rfl,
    fermionTotalSpinPlus_mulVec_ferroHole, smul_zero]

/-- `Ŝ^z_tot` acts on the all-up Tasaki basis state with eigenvalue `N/2 = S_max`. -/
theorem fermionTotalSpinZ_mulVec_hubbardTasakiBasisStateUp (N : ℕ) (x : Fin (N + 1)) :
    (fermionTotalSpinZ N).mulVec (hubbardTasakiBasisState N x (fun _ => true)) =
      ((N : ℂ) / 2) • (hubbardTasakiBasisState N x (fun _ => true)) := by
  rw [hubbardTasakiBasisState_eq_smul_basisVec, Matrix.mulVec_smul,
    show hubbardOneHoleConfig N x (fun _ => true) = ferroHoleConfig N x from rfl,
    fermionTotalSpinZ_mulVec_ferroHole, smul_comm]

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

/-- **Abstract `Ŝ^z` tower.** If `Ŝ^z_tot v = (N/2) v` then
`Ŝ^z_tot (Ŝ^-_tot)^k v = (N/2 − k) (Ŝ^-_tot)^k v`: each application of `Ŝ^-_tot`
lowers the `Ŝ^z` eigenvalue by one, via `[Ŝ^z_tot, Ŝ^-_tot] = −Ŝ^-_tot`. -/
theorem fermionTotalSpinZ_mulVec_spinMinusPow (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℕ)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((N : ℂ) / 2) • v) :
    (fermionTotalSpinZ N).mulVec (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      ((N : ℂ) / 2 - k) • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  have hcomm : fermionTotalSpinZ N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinZ N - fermionTotalSpinMinus N := by
    have h := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, Nat.cast_zero, sub_zero]
    exact hsz
  | succ k ih =>
    have hexp : ((fermionTotalSpinMinus N) ^ (k + 1)).mulVec v =
        (fermionTotalSpinMinus N).mulVec
          (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hexp, Matrix.mulVec_mulVec, hcomm, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, Nat.cast_succ]
    module

/-- `Ŝ^z_tot` acts on the `k`-fold lowered ferromagnetic hole state with
eigenvalue `N/2 − k` (instance of the abstract `Ŝ^z` tower at the maximal-spin
ferromagnetic hole state; distinct eigenvalues power the linear independence). -/
theorem fermionTotalSpinZ_mulVec_spinMinusPow_ferroHole (N : ℕ) (x : Fin (N + 1))
    (k : ℕ) :
    (fermionTotalSpinZ N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) =
      ((N : ℂ) / 2 - k) •
        (((fermionTotalSpinMinus N) ^ k).mulVec (basisVec (ferroHoleConfig N x))) :=
  fermionTotalSpinZ_mulVec_spinMinusPow N (basisVec (ferroHoleConfig N x)) k
    (fermionTotalSpinZ_mulVec_ferroHole N x)

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
  change fermionTotalSpinSquared N * fermionTotalSpinMinus N =
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

end LatticeSystem.Fermion
