import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinTotHermitian
import LatticeSystem.Math.TasakiAppendixA.AngularSpinHalfSector

/-!
# Tasaki §11.5: the spin-½ sector reduction for the t-J model (Theorem A.17)

Tasaki's proof of Proposition 11.24 opens with: "Theorem A.17 guarantees that any eigenstate of
`Ĥ_tJ` has its copy in the `Ŝ³_tot = 1/2` subspace."  We formalize exactly this: since the
ferromagnetic t-J Hamiltonian is SU(2)-invariant (Issue #4230 PR1) and self-adjoint, Theorem A.17
applies, so **every eigenvalue of `Ĥ_tJ` has an eigenstate `Φ` with `Ŝ³_tot Φ = 0` or
`Ŝ³_tot Φ = (1/2) Φ`.**  The angular-momentum data are the Cartesian total-spin components
`Ŝ⁽¹⁾ = ½(Ŝ⁺+Ŝ⁻)`, `Ŝ⁽²⁾ = −(i/2)(Ŝ⁺−Ŝ⁻)`, `Ŝ⁽³⁾ = Ŝ³_tot`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443 (citing Theorem A.17, p. 473).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- `[Ŝ³_tot, Ŝ⁺_tot] = Ŝ⁺_tot`, by adjoint of `[Ŝ³_tot, Ŝ⁻_tot] = −Ŝ⁻_tot`. -/
theorem fermionTotalSpinZ_commutator_fermionTotalSpinPlus (N : ℕ) :
    fermionTotalSpinZ N * fermionTotalSpinPlus N -
      fermionTotalSpinPlus N * fermionTotalSpinZ N = fermionTotalSpinPlus N := by
  have h := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
  have hadj := congrArg Matrix.conjTranspose h
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_neg,
    fermionTotalSpinMinus_conjTranspose, (fermionTotalSpinZ_isHermitian N).eq] at hadj
  linear_combination (norm := noncomm_ring) -hadj

/-- The first Cartesian total-spin component `Ŝ⁽¹⁾_tot = ½(Ŝ⁺_tot + Ŝ⁻_tot)`. -/
noncomputable def tJTotalSpinOne (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) • (fermionTotalSpinPlus N + fermionTotalSpinMinus N)

/-- The second Cartesian total-spin component `Ŝ⁽²⁾_tot = −(i/2)(Ŝ⁺_tot − Ŝ⁻_tot)`. -/
noncomputable def tJTotalSpinTwo (N : ℕ) : ManyBodyOp (Fin (2 * N + 2)) :=
  (-(Complex.I / 2)) • (fermionTotalSpinPlus N - fermionTotalSpinMinus N)

/-- `Ŝ⁽¹⁾_tot` is self-adjoint. -/
theorem tJTotalSpinOne_isHermitian (N : ℕ) : (tJTotalSpinOne N).IsHermitian := by
  rw [Matrix.IsHermitian, tJTotalSpinOne, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    fermionTotalSpinPlus_conjTranspose, fermionTotalSpinMinus_conjTranspose,
    show star (1 / 2 : ℂ) = 1 / 2 by norm_num [Complex.ext_iff, Complex.star_def]]
  module

/-- `Ŝ⁽²⁾_tot` is self-adjoint. -/
theorem tJTotalSpinTwo_isHermitian (N : ℕ) : (tJTotalSpinTwo N).IsHermitian := by
  rw [Matrix.IsHermitian, tJTotalSpinTwo, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    fermionTotalSpinPlus_conjTranspose, fermionTotalSpinMinus_conjTranspose,
    show star (-(Complex.I / 2)) = Complex.I / 2 by simp [Complex.ext_iff]; norm_num]
  module

/-- `Ĥ_tJ` commutes with `Ŝ⁽¹⁾_tot`. -/
theorem tJHamiltonian_mul_tJTotalSpinOne (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    tJHamiltonian N G τ J * tJTotalSpinOne N = tJTotalSpinOne N * tJHamiltonian N G τ J := by
  have hcP := (fermionTotalSpinPlus_commute_tJHamiltonian N G τ J).eq.symm
  have hcM := (fermionTotalSpinMinus_commute_tJHamiltonian N G τ J).eq.symm
  rw [tJTotalSpinOne, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hcP, hcM]

/-- `Ĥ_tJ` commutes with `Ŝ⁽²⁾_tot`. -/
theorem tJHamiltonian_mul_tJTotalSpinTwo (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    tJHamiltonian N G τ J * tJTotalSpinTwo N = tJTotalSpinTwo N * tJHamiltonian N G τ J := by
  have hcP := (fermionTotalSpinPlus_commute_tJHamiltonian N G τ J).eq.symm
  have hcM := (fermionTotalSpinMinus_commute_tJHamiltonian N G τ J).eq.symm
  rw [tJTotalSpinTwo, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hcP, hcM]

/-- `[Ŝ⁽¹⁾_tot, Ŝ⁽²⁾_tot] = i Ŝ³_tot`. -/
theorem tJTotalSpin_su2_12 (N : ℕ) :
    tJTotalSpinOne N * tJTotalSpinTwo N - tJTotalSpinTwo N * tJTotalSpinOne N
      = Complex.I • fermionTotalSpinZ N := by
  have hPM : fermionTotalSpinPlus N * fermionTotalSpinMinus N -
      fermionTotalSpinMinus N * fermionTotalSpinPlus N = (2 : ℂ) • fermionTotalSpinZ N :=
    fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N
  have hexp : tJTotalSpinOne N * tJTotalSpinTwo N - tJTotalSpinTwo N * tJTotalSpinOne N
      = (Complex.I / 2) • (fermionTotalSpinPlus N * fermionTotalSpinMinus N -
        fermionTotalSpinMinus N * fermionTotalSpinPlus N) := by
    rw [tJTotalSpinOne, tJTotalSpinTwo, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, smul_smul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul]
    module
  rw [hexp, hPM, smul_smul]
  norm_num

/-- `[Ŝ⁽²⁾_tot, Ŝ³_tot] = i Ŝ⁽¹⁾_tot`. -/
theorem tJTotalSpin_su2_23 (N : ℕ) :
    tJTotalSpinTwo N * fermionTotalSpinZ N - fermionTotalSpinZ N * tJTotalSpinTwo N
      = Complex.I • tJTotalSpinOne N := by
  have hZM := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
  have hZP := fermionTotalSpinZ_commutator_fermionTotalSpinPlus N
  have hexp : tJTotalSpinTwo N * fermionTotalSpinZ N - fermionTotalSpinZ N * tJTotalSpinTwo N
      = (-(Complex.I / 2)) • ((fermionTotalSpinPlus N * fermionTotalSpinZ N -
          fermionTotalSpinZ N * fermionTotalSpinPlus N) -
        (fermionTotalSpinMinus N * fermionTotalSpinZ N -
          fermionTotalSpinZ N * fermionTotalSpinMinus N)) := by
    rw [tJTotalSpinTwo, Matrix.smul_mul, Matrix.mul_smul]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    module
  rw [hexp,
    show fermionTotalSpinPlus N * fermionTotalSpinZ N - fermionTotalSpinZ N * fermionTotalSpinPlus N
      = -fermionTotalSpinPlus N by linear_combination (norm := noncomm_ring) -hZP,
    show fermionTotalSpinMinus N * fermionTotalSpinZ N -
        fermionTotalSpinZ N * fermionTotalSpinMinus N = fermionTotalSpinMinus N by
      linear_combination (norm := noncomm_ring) -hZM, tJTotalSpinOne]
  module

/-- `[Ŝ³_tot, Ŝ⁽¹⁾_tot] = i Ŝ⁽²⁾_tot`. -/
theorem tJTotalSpin_su2_31 (N : ℕ) :
    fermionTotalSpinZ N * tJTotalSpinOne N - tJTotalSpinOne N * fermionTotalSpinZ N
      = Complex.I • tJTotalSpinTwo N := by
  have hZM := fermionTotalSpinZ_commutator_fermionTotalSpinMinus N
  have hZP := fermionTotalSpinZ_commutator_fermionTotalSpinPlus N
  have hexp : fermionTotalSpinZ N * tJTotalSpinOne N - tJTotalSpinOne N * fermionTotalSpinZ N
      = (1 / 2 : ℂ) • ((fermionTotalSpinZ N * fermionTotalSpinPlus N -
          fermionTotalSpinPlus N * fermionTotalSpinZ N) +
        (fermionTotalSpinZ N * fermionTotalSpinMinus N -
          fermionTotalSpinMinus N * fermionTotalSpinZ N)) := by
    rw [tJTotalSpinOne, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_add, Matrix.add_mul]
    module
  rw [hexp, hZP,
    show fermionTotalSpinZ N * fermionTotalSpinMinus N -
        fermionTotalSpinMinus N * fermionTotalSpinZ N = -fermionTotalSpinMinus N by
      linear_combination (norm := noncomm_ring) hZM, tJTotalSpinTwo]
  rw [smul_smul, show Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) by
    rw [mul_neg, ← mul_div_assoc, Complex.I_mul_I]; norm_num]
  module

/-- **Tasaki §11.5 spin-½ sector reduction (Theorem A.17 applied to `Ĥ_tJ`).**  Every eigenvalue `E`
of `Ĥ_tJ` (witnessed by some `v ≠ 0`) has a corresponding eigenstate `Φ ≠ 0` with `Ŝ³_tot Φ = 0` or
`Ŝ³_tot Φ = (1/2) Φ`. -/
theorem tJHamiltonian_eigenstate_spin_zero_or_half (N : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) {E : ℂ} {v : (Fin (2 * N + 2) → Fin 2) → ℂ} (hv : v ≠ 0)
    (hEv : (tJHamiltonian N G τ J).mulVec v = E • v) :
    ∃ Φ : (Fin (2 * N + 2) → Fin 2) → ℂ, Φ ≠ 0 ∧
      (tJHamiltonian N G τ J).mulVec Φ = E • Φ ∧
      ((fermionTotalSpinZ N).mulVec Φ = 0 ∨
        (fermionTotalSpinZ N).mulVec Φ = ((1 / 2 : ℝ) : ℂ) • Φ) :=
  LatticeSystem.Math.ham_eigenstate_spin_zero_or_half (tJHamiltonian N G τ J) (tJTotalSpinOne N)
    (tJTotalSpinTwo N)
    (fermionTotalSpinZ N) (tJHamiltonian_isHermitian N G τ J) (tJTotalSpinOne_isHermitian N)
    (tJTotalSpinTwo_isHermitian N) (fermionTotalSpinZ_isHermitian N)
    (tJHamiltonian_mul_tJTotalSpinOne N G τ J) (tJHamiltonian_mul_tJTotalSpinTwo N G τ J)
    (fermionTotalSpinZ_commute_tJHamiltonian N G τ J).eq.symm (tJTotalSpin_su2_12 N)
    (tJTotalSpin_su2_23 N)
    (tJTotalSpin_su2_31 N) hv hEv

end LatticeSystem.Fermion
