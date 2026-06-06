import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorReduction
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJNumberCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingSpinCompress

/-!
# Tasaki 11.5: eigenvalue tracking along the spin-raising tower (Prop 11.24 E3b PR2)

The iterated total raising `(Ŝ⁺_tot)^k` tracks the conserved/raised quantities of a sector ground
state along the way up to the highest weight:

* `fermionTotalSpinZ_mulVec_spinPlusPow` — each step raises the `Ŝ³` eigenvalue by one
  (`Ŝ³ (Ŝ⁺)^k v = (m + k)(Ŝ⁺)^k v`), the raising mirror of the lowering tower
  `fermionTotalSpinZ_mulVec_spinMinusPow_general`.
* `tJHamiltonian_mulVec_spinPlusPow` — the energy is preserved (`Ĥ_tJ (Ŝ⁺)^k v = μ (Ŝ⁺)^k v`), since
  `[Ĥ_tJ, Ŝ⁺_tot] = 0`.
* `fermionTotalNumber_mulVec_spinPlusPow` — the electron number is preserved (`N̂ (Ŝ⁺)^k v = Ne
  (Ŝ⁺)^k v`), since `[N̂, Ŝ⁺_tot] = 0`.

So `(Ŝ⁺)^k Φ₀`, when nonzero, is a fixed-`Ne`, energy-`μ` eigenvector at `Ŝ³ = ½ + k` — the building
blocks for raising the strictly-positive Perron–Frobenius ground vector to a nonzero highest weight.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

variable {N : ℕ}

/-- **`Ŝ³` raises by one along the raising tower.**  `Ŝ³ (Ŝ⁺)^k v = (m + k) (Ŝ⁺)^k v` — each `Ŝ⁺`
step increases the `Ŝ³` eigenvalue by one (mirror of the lowering tower). -/
theorem fermionTotalSpinZ_mulVec_spinPlusPow (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (m : ℂ) (k : ℕ)
    (hsz : (fermionTotalSpinZ N).mulVec v = m • v) :
    (fermionTotalSpinZ N).mulVec (((fermionTotalSpinPlus N) ^ k).mulVec v) =
      (m + k) • (((fermionTotalSpinPlus N) ^ k).mulVec v) := by
  have hcomm : fermionTotalSpinZ N * fermionTotalSpinPlus N =
      fermionTotalSpinPlus N * fermionTotalSpinZ N + fermionTotalSpinPlus N := by
    have h := fermionTotalSpinZ_commutator_fermionTotalSpinPlus N
    rw [sub_eq_iff_eq_add] at h
    rw [h]; abel
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.one_mulVec, Nat.cast_zero, add_zero]
    exact hsz
  | succ k ih =>
    have hexp : ((fermionTotalSpinPlus N) ^ (k + 1)).mulVec v =
        (fermionTotalSpinPlus N).mulVec
          (((fermionTotalSpinPlus N) ^ k).mulVec v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hexp, Matrix.mulVec_mulVec, hcomm, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.mulVec_smul, Nat.cast_succ]
    module

/-- **The energy is preserved along the raising tower.**  Since `[Ĥ_tJ, Ŝ⁺_tot] = 0`, every
`(Ŝ⁺)^k v` of an `Ĥ_tJ`-eigenvector at `μ` is again an `Ĥ_tJ`-eigenvector at `μ`. -/
theorem tJHamiltonian_mulVec_spinPlusPow (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (μ : ℂ) (k : ℕ)
    (hH : (tJHamiltonian N G τ J).mulVec v = μ • v) :
    (tJHamiltonian N G τ J).mulVec (((fermionTotalSpinPlus N) ^ k).mulVec v) =
      μ • (((fermionTotalSpinPlus N) ^ k).mulVec v) := by
  have hcomm : Commute (tJHamiltonian N G τ J) ((fermionTotalSpinPlus N) ^ k) :=
    ((fermionTotalSpinPlus_commute_tJHamiltonian N G τ J).symm).pow_right k
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hH, Matrix.mulVec_smul]

/-- **The electron number is preserved along the raising tower.**  Since `[N̂, Ŝ⁺_tot] = 0`, every
`(Ŝ⁺)^k v` of an `N̂`-eigenvector at `Ne` is again an `N̂`-eigenvector at `Ne`. -/
theorem fermionTotalNumber_mulVec_spinPlusPow (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (ν : ℂ) (k : ℕ)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec v = ν • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec (((fermionTotalSpinPlus N) ^ k).mulVec v) =
      ν • (((fermionTotalSpinPlus N) ^ k).mulVec v) := by
  have hcomm : Commute (fermionTotalNumber (2 * N + 1)) ((fermionTotalSpinPlus N) ^ k) :=
    ((fermionTotalSpinPlus_commute_fermionTotalNumber N).symm).pow_right k
  rw [Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hN, Matrix.mulVec_smul]

end LatticeSystem.Fermion
