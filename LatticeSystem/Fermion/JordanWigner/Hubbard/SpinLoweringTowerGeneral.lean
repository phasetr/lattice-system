import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem

/-!
# General highest-weight SU(2) lowering tower

The spin-lowering tower lemmas in `WeakNagaokaTheorem.lean`
(`spinMinusPow_linearIndependent`, `fermionTotalSpinZ_mulVec_spinMinusPow`, …)
hardcode the highest weight to the *chain maximum* `N/2`: they assume
`Ŝ^z_tot v = (N/2) v`.  That is exactly the saturated ferromagnet of the
half-filled one-hole sector used in Tasaki §11.2 (weak Nagaoka).

Tasaki's flat-band ferromagnetism (§11.3.1, Theorem 11.11) instead has only
`|E| = K + 1` electrons on `2K + 2` physical sites, so its highest-weight state
`|Φα,all↑⟩` carries `Ŝ^z_tot = (K+1)/2 < N/2 = (2K+1)/2`.  The `N/2`-specialised
tower lemmas therefore do not apply.

This module re-derives the same SU(2) ladder algebra at an **arbitrary** highest
weight, in two layers:

* a *formula* layer parametrised by a general eigenvalue `m : ℂ` (and Casimir
  eigenvalue `lam : ℂ`): `Ŝ^z`/`Ŝ^+ Ŝ^-`/`(Ŝ_tot)²` acting on `(Ŝ^-_tot)^k v`;
* a *finite-tower* layer parametrised by a step count `L : ℕ` (highest weight
  `m = L/2`): nonvanishing and linear independence of the `L + 1` lowered states.

The underlying commutator identities (`[Ŝ^z, Ŝ^-] = -Ŝ^-`, `[(Ŝ_tot)², Ŝ^-] = 0`,
`Ŝ^+ Ŝ^- = (Ŝ_tot)² - Ŝ^z(Ŝ^z - 1)`) are reused verbatim from
`WeakNagaokaTheorem.lean`; only the eigenvalue arithmetic is generalised.  The
old `N/2` lemmas are the `m = N/2` / `L = N` special cases and are left
untouched (they are merged dependencies of the Nagaoka theorems).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.2.1 (SU(2) tower) and §11.3.1 (flat-band highest weight).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- **General `Ŝ^z` tower.** If `Ŝ^z_tot v = m v` for an arbitrary `m : ℂ`, then
`Ŝ^z_tot (Ŝ^-_tot)^k v = (m − k) (Ŝ^-_tot)^k v`: each lowering step decreases the
`Ŝ^z` eigenvalue by one (general highest weight `m`, not just the chain maximum
`N/2`). -/
theorem fermionTotalSpinZ_mulVec_spinMinusPow_general (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (m : ℂ) (k : ℕ)
    (hsz : (fermionTotalSpinZ N).mulVec v = m • v) :
    (fermionTotalSpinZ N).mulVec (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      (m - k) • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
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

/-- **General highest-weight Casimir value.** A highest-weight state
(`Ŝ^+_tot v = 0`) with `Ŝ^z_tot v = m v` is a `(Ŝ_tot)²` eigenvector at
`m(m + 1)`, for an arbitrary `m : ℂ`. -/
theorem fermionTotalSpinSquared_mulVec_of_isTop_general (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (m : ℂ)
    (htop : (fermionTotalSpinPlus N).mulVec v = 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = m • v) :
    (fermionTotalSpinSquared N).mulVec v = (m * (m + 1)) • v := by
  unfold fermionTotalSpinSquared
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, htop, Matrix.mulVec_zero, zero_add,
    ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hsz, Matrix.mulVec_add,
    Matrix.mulVec_smul, hsz, smul_smul, ← add_smul]
  congr 1
  ring

/-- **General `Ŝ^+ Ŝ^-` ladder eigenvalue.** With `Ŝ^z_tot v = m v` and
`(Ŝ_tot)² v = lam v` (arbitrary `m, lam : ℂ`),
`Ŝ^+_tot Ŝ^-_tot (Ŝ^-_tot)^k v = (lam − (m−k)(m−k−1)) (Ŝ^-_tot)^k v`. -/
theorem fermionTotalSpinPlusMinus_mulVec_spinMinusPow_general (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (m lam : ℂ) (k : ℕ)
    (hsz : (fermionTotalSpinZ N).mulVec v = m • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v = lam • v) :
    (fermionTotalSpinPlus N * fermionTotalSpinMinus N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      (lam - (m - k) * (m - k - 1)) •
        (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  rw [fermionTotalSpinPlus_mul_fermionTotalSpinMinus, Matrix.sub_mulVec,
    fermionTotalSpinSquared_mulVec_spinMinusPow N v _ k hcas,
    ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    fermionTotalSpinZ_mulVec_spinMinusPow_general N v m k hsz,
    Matrix.mulVec_sub, Matrix.mulVec_smul,
    fermionTotalSpinZ_mulVec_spinMinusPow_general N v m k hsz]
  module

/-- **General finite-tower nonvanishing.** A nonzero highest-weight state with
`Ŝ^z_tot v = (L/2) v` and `(Ŝ_tot)² v = (L/2)(L/2 + 1) v` (highest weight
`m = L/2` for a step count `L : ℕ`) has nonzero lowered states `(Ŝ^-_tot)^k v`
for every `k ≤ L`: the ladder only terminates after `L` steps because
`lam − (m−k)(m−k−1) = (k+1)(L−k) ≠ 0` for `k < L`. -/
theorem spinMinusPow_ne_zero_general (N L : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hv : v ≠ 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((L : ℂ) / 2) • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v =
      ((L : ℂ) / 2 * ((L : ℂ) / 2 + 1)) • v) :
    ∀ k : ℕ, k ≤ L → ((fermionTotalSpinMinus N) ^ k).mulVec v ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _ h
    rw [pow_zero, Matrix.one_mulVec] at h
    exact hv h
  | succ k ih =>
    intro hk hzero
    have hk' : k ≤ L := Nat.le_of_succ_le hk
    have hklt : k < L := hk
    have hψk := ih hk'
    have hc : (L : ℂ) / 2 * ((L : ℂ) / 2 + 1) -
        ((L : ℂ) / 2 - k) * ((L : ℂ) / 2 - k - 1) ≠ 0 := by
      have heq : (L : ℂ) / 2 * ((L : ℂ) / 2 + 1) -
          ((L : ℂ) / 2 - k) * ((L : ℂ) / 2 - k - 1) = ((k : ℂ) + 1) * ((L : ℂ) - k) := by
        ring
      rw [heq]
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      rw [sub_ne_zero]
      exact_mod_cast (Nat.ne_of_lt hklt).symm
    have harg : (fermionTotalSpinMinus N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']; exact hzero
    have key := fermionTotalSpinPlusMinus_mulVec_spinMinusPow_general N v
      ((L : ℂ) / 2) ((L : ℂ) / 2 * ((L : ℂ) / 2 + 1)) k hsz hcas
    rw [← Matrix.mulVec_mulVec, harg, Matrix.mulVec_zero] at key
    rcases smul_eq_zero.mp key.symm with h | h
    · exact hc h
    · exact hψk h

/-- **General finite-tower linear independence.** For a nonzero highest-weight
state with `Ŝ^z_tot v = (L/2) v` and `(Ŝ_tot)² v = (L/2)(L/2 + 1) v`, the
`L + 1` lowered states `(Ŝ^-_tot)^k v` (`k = 0, …, L`) are linearly independent
(distinct `Ŝ^z` eigenvalues `L/2 − k`). -/
theorem spinMinusPow_linearIndependent_general (N L : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hv : v ≠ 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((L : ℂ) / 2) • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v =
      ((L : ℂ) / 2 * ((L : ℂ) / 2 + 1)) • v) :
    LinearIndependent ℂ (fun k : Fin (L + 1) =>
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) := by
  apply Module.End.eigenvectors_linearIndependent' (fermionTotalSpinZ N).mulVecLin
    (fun k : Fin (L + 1) => (L : ℂ) / 2 - (k : ℕ))
  · intro a b hab
    rw [sub_right_inj] at hab
    have h2 : (a : ℕ) = (b : ℕ) := by exact_mod_cast hab
    exact Fin.ext h2
  · intro k
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact fermionTotalSpinZ_mulVec_spinMinusPow_general N v ((L : ℂ) / 2) (k : ℕ) hsz
    · exact spinMinusPow_ne_zero_general N L v hv hsz hcas (k : ℕ) (Nat.le_of_lt_succ k.isLt)

/-- **General highest-weight spin multiplet.** A nonzero highest-weight state
`v` (`Ŝ^+_tot v = 0`, `Ŝ^z_tot v = (L/2) v`) generates an `(L + 1)`-dimensional
maximal-spin multiplet: the lowered states `(Ŝ^-_tot)^k v` (`k = 0, …, L`) are
linearly independent and all carry total spin `(Ŝ_tot)² = (L/2)(L/2 + 1)`.  This
is the SU(2) tower at an arbitrary highest weight `m = L/2`, the form needed for
Tasaki's flat-band ferromagnet (`L = |E| = K + 1`, where `N = 2K + 1`). -/
theorem highestWeight_spinMultiplet_general (N L : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hv : v ≠ 0)
    (htop : (fermionTotalSpinPlus N).mulVec v = 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((L : ℂ) / 2) • v) :
    LinearIndependent ℂ (fun k : Fin (L + 1) =>
        ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) ∧
      (∀ k : Fin (L + 1), (fermionTotalSpinSquared N).mulVec
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) =
        ((L : ℂ) / 2 * ((L : ℂ) / 2 + 1)) •
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v)) := by
  have hcas := fermionTotalSpinSquared_mulVec_of_isTop_general N v ((L : ℂ) / 2) htop hsz
  refine ⟨spinMinusPow_linearIndependent_general N L v hv hsz hcas, fun k => ?_⟩
  exact fermionTotalSpinSquared_mulVec_spinMinusPow N v _ (k : ℕ) hcas

end LatticeSystem.Fermion
