import LatticeSystem.Fermion.JordanWigner.Hubbard.TJFillingSpinCompress

/-!
# Tasaki 11.5: the compressed `Ĥ_tJ`, `Ŝ⁽ᵅ⁾` satisfy the A.17 hypotheses (Prop 11.24 PR-E2 ≥)

The `W`-compressions `Ĥ_W = compress(Ĥ_tJ)` and `Ŝ⁽ᵅ⁾_W = compress(Ŝ⁽ᵅ⁾)` inherit, via the
compression homomorphism (`tJFillingCompress_mul_of_right_preserves`) and `compress` linearity,
all the hypotheses of the matrix Theorem A.17: each is Hermitian
(`tJFillingCompress_isHermitian`), the `Ŝ⁽ᵅ⁾_W` satisfy the `su(2)` relations
(`tJFillingCompress_su2_12/23/31`), and `Ĥ_W` commutes with each `Ŝ⁽ᵅ⁾_W`
(`tJFillingCompress_tJHamiltonian_commute_*`).  This lets A.17 be applied at the filling index to
locate, at any energy of `Ĥ_W`, an eigenstate in the `Ŝ³ = ½` (or `0`) sector — the final input to
`groundEnergyAtFilling = μ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443; Appendix A.3.2 Theorem A.17.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph

variable {N : ℕ}

/-- `compress` is `ℂ`-homogeneous: `compress(c • A) = c • compress(A)`. -/
theorem tJFillingCompress_smul (Ne : ℕ) (c : ℂ) (A : ManyBodyOp (Fin (2 * N + 2))) :
    tJFillingCompress N Ne (c • A) = c • tJFillingCompress N Ne A := by
  unfold tJFillingCompress
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- `compress` is additive on differences: `compress(A - B) = compress(A) - compress(B)`. -/
theorem tJFillingCompress_sub (Ne : ℕ) (A B : ManyBodyOp (Fin (2 * N + 2))) :
    tJFillingCompress N Ne (A - B) = tJFillingCompress N Ne A - tJFillingCompress N Ne B := by
  unfold tJFillingCompress
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- `compress` preserves Hermiticity: `compress(A)ᴴ = compress(Aᴴ) = compress(A)` for Hermitian
`A`. -/
theorem tJFillingCompress_isHermitian (Ne : ℕ) {A : ManyBodyOp (Fin (2 * N + 2))}
    (hA : A.IsHermitian) : (tJFillingCompress N Ne A).IsHermitian := by
  change (tJFillingCompress N Ne A)ᴴ = tJFillingCompress N Ne A
  unfold tJFillingCompress
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hA.eq, Matrix.mul_assoc]

/-- The compressed `Ŝ⁽¹⁾_W, Ŝ⁽²⁾_W, Ŝ³_W` satisfy `[Ŝ⁽¹⁾_W, Ŝ⁽²⁾_W] = i Ŝ³_W`. -/
theorem tJFillingCompress_su2_12 (Ne : ℕ) :
    tJFillingCompress N Ne (tJTotalSpinOne N) * tJFillingCompress N Ne (tJTotalSpinTwo N) -
        tJFillingCompress N Ne (tJTotalSpinTwo N) * tJFillingCompress N Ne (tJTotalSpinOne N) =
      Complex.I • tJFillingCompress N Ne (fermionTotalSpinZ N) := by
  rw [tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJTotalSpinTwo Ne),
    tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJTotalSpinOne Ne),
    ← tJFillingCompress_sub, tJTotalSpin_su2_12, tJFillingCompress_smul]

/-- The compressed operators satisfy `[Ŝ⁽²⁾_W, Ŝ³_W] = i Ŝ⁽¹⁾_W`. -/
theorem tJFillingCompress_su2_23 (Ne : ℕ) :
    tJFillingCompress N Ne (tJTotalSpinTwo N) * tJFillingCompress N Ne (fermionTotalSpinZ N) -
        tJFillingCompress N Ne (fermionTotalSpinZ N) * tJFillingCompress N Ne (tJTotalSpinTwo N) =
      Complex.I • tJFillingCompress N Ne (tJTotalSpinOne N) := by
  rw [tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_fermionTotalSpinZ Ne),
    tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJTotalSpinTwo Ne),
    ← tJFillingCompress_sub, tJTotalSpin_su2_23, tJFillingCompress_smul]

/-- The compressed operators satisfy `[Ŝ³_W, Ŝ⁽¹⁾_W] = i Ŝ⁽²⁾_W`. -/
theorem tJFillingCompress_su2_31 (Ne : ℕ) :
    tJFillingCompress N Ne (fermionTotalSpinZ N) * tJFillingCompress N Ne (tJTotalSpinOne N) -
        tJFillingCompress N Ne (tJTotalSpinOne N) * tJFillingCompress N Ne (fermionTotalSpinZ N) =
      Complex.I • tJFillingCompress N Ne (tJTotalSpinTwo N) := by
  rw [tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJTotalSpinOne Ne),
    tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_fermionTotalSpinZ Ne),
    ← tJFillingCompress_sub, tJTotalSpin_su2_31, tJFillingCompress_smul]

/-- `Ĥ_W` commutes with `Ŝ⁽¹⁾_W`. -/
theorem tJFillingCompress_tJHamiltonian_commute_one (Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    tJFillingCompress N Ne (tJHamiltonian N G τ J) * tJFillingCompress N Ne (tJTotalSpinOne N) =
      tJFillingCompress N Ne (tJTotalSpinOne N) * tJFillingCompress N Ne (tJHamiltonian N G τ J) := by
  rw [tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJTotalSpinOne Ne),
    tJHamiltonian_mul_tJTotalSpinOne,
    ← tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJHamiltonian Ne G τ J)]

/-- `Ĥ_W` commutes with `Ŝ⁽²⁾_W`. -/
theorem tJFillingCompress_tJHamiltonian_commute_two (Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    tJFillingCompress N Ne (tJHamiltonian N G τ J) * tJFillingCompress N Ne (tJTotalSpinTwo N) =
      tJFillingCompress N Ne (tJTotalSpinTwo N) * tJFillingCompress N Ne (tJHamiltonian N G τ J) := by
  rw [tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJTotalSpinTwo Ne),
    tJHamiltonian_mul_tJTotalSpinTwo,
    ← tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJHamiltonian Ne G τ J)]

/-- `Ĥ_W` commutes with `Ŝ³_W`. -/
theorem tJFillingCompress_tJHamiltonian_commute_three (Ne : ℕ) (G : SimpleGraph (Fin (N + 1)))
    [DecidableRel G.Adj] (τ J : ℝ) :
    tJFillingCompress N Ne (tJHamiltonian N G τ J) * tJFillingCompress N Ne (fermionTotalSpinZ N) =
      tJFillingCompress N Ne (fermionTotalSpinZ N) *
        tJFillingCompress N Ne (tJHamiltonian N G τ J) := by
  rw [tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_fermionTotalSpinZ Ne),
    (fermionTotalSpinZ_commute_tJHamiltonian N G τ J).eq.symm,
    ← tJFillingCompress_mul_of_right_preserves Ne _ (preservesTJFillingW_tJHamiltonian Ne G τ J)]

end LatticeSystem.Fermion
