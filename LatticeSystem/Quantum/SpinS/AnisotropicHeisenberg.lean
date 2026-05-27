import LatticeSystem.Quantum.SpinS.Heisenberg
import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# The anisotropic (XXZ + single-ion) antiferromagnetic Heisenberg Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori), foundational definition.

Tasaki's anisotropic Hamiltonian (2.5.14):
`Ĥ = Σ_{x,y} J_{x,y} (Ŝ_x⁽¹⁾Ŝ_y⁽¹⁾ + Ŝ_x⁽²⁾Ŝ_y⁽²⁾ + λ Ŝ_x⁽³⁾Ŝ_y⁽³⁾) + D Σ_x (Ŝ_x⁽³⁾)²`,
with `λ` the Ising anisotropy and `D` the crystal-field (single-ion) anisotropy.  Unlike the
isotropic Heisenberg model it is only U(1)-invariant (commutes with `Ŝ³_tot`, not with
`(Ŝ_tot)²`).

This file introduces the two-site XXZ term `spinSDotXXZ`, the single-ion term
`singleIonAnisotropyS`, and the full Hamiltonian `anisotropicHeisenbergS`, and proves it is
Hermitian for real parameters and reduces to the isotropic Heisenberg Hamiltonian at
`λ = 1, D = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43 (eq. 2.5.14).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The two-site **XXZ** term `Ŝ_x⁽¹⁾Ŝ_y⁽¹⁾ + Ŝ_x⁽²⁾Ŝ_y⁽²⁾ + λ Ŝ_x⁽³⁾Ŝ_y⁽³⁾`. -/
noncomputable def spinSDotXXZ (x y : Λ) (lam : ℂ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
    onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) +
    lam • (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N))

/-- Definitional unfolding of `spinSDotXXZ`. -/
theorem spinSDotXXZ_def (x y : Λ) (lam : ℂ) (N : ℕ) :
    spinSDotXXZ x y lam N =
      onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
        onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N) +
        lam • (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) := rfl

/-- At `λ = 1` the XXZ term is the isotropic spin-`S` dot product. -/
theorem spinSDotXXZ_one (x y : Λ) (N : ℕ) :
    spinSDotXXZ x y 1 N = spinSDot x y N := by
  rw [spinSDotXXZ_def, spinSDot_def, one_smul]

/-- The two-site XXZ term is Hermitian for a real anisotropy `λ`. -/
theorem spinSDotXXZ_isHermitian (x y : Λ) {lam : ℂ} (hlam : star lam = lam) (N : ℕ) :
    (spinSDotXXZ x y lam N : ManyBodyOpS Λ N).IsHermitian := by
  have hcomm : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      (onSiteS x A : ManyBodyOpS Λ N) * onSiteS y A = onSiteS y A * onSiteS x A := by
    intro A
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact onSiteS_mul_onSiteS_of_ne hxy A A
  unfold spinSDotXXZ
  refine Matrix.IsHermitian.add (Matrix.IsHermitian.add ?_ ?_) ?_
  · exact Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp1_isHermitian N))
      (onSiteS_isHermitian y (spinSOp1_isHermitian N)) (hcomm _)
  · exact Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp2_isHermitian N))
      (onSiteS_isHermitian y (spinSOp2_isHermitian N)) (hcomm _)
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hlam,
      (Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp3_isHermitian N))
        (onSiteS_isHermitian y (spinSOp3_isHermitian N)) (hcomm _)).eq]

/-- The **single-ion anisotropy** term `D Σ_x (Ŝ_x⁽³⁾)²`. -/
noncomputable def singleIonAnisotropyS (D : ℂ) (N : ℕ) : ManyBodyOpS Λ N :=
  D • ∑ x : Λ, onSiteS x (spinSOp3 N) * onSiteS x (spinSOp3 N)

/-- The single-ion term vanishes at `D = 0`. -/
theorem singleIonAnisotropyS_zero (N : ℕ) :
    singleIonAnisotropyS (Λ := Λ) 0 N = 0 := by
  rw [singleIonAnisotropyS, zero_smul]

/-- The single-ion term is Hermitian for a real crystal field `D`. -/
theorem singleIonAnisotropyS_isHermitian {D : ℂ} (hD : star D = D) (N : ℕ) :
    (singleIonAnisotropyS (Λ := Λ) D N).IsHermitian := by
  unfold singleIonAnisotropyS Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hD, Matrix.conjTranspose_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ =>
    (Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp3_isHermitian N))
      (onSiteS_isHermitian x (spinSOp3_isHermitian N)) rfl).eq)

/-- The **anisotropic (XXZ + single-ion) Heisenberg Hamiltonian** (Tasaki (2.5.14)). -/
noncomputable def anisotropicHeisenbergS (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) :
    ManyBodyOpS Λ N :=
  (∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZ x y lam N) + singleIonAnisotropyS D N

/-- Definitional unfolding of `anisotropicHeisenbergS`. -/
theorem anisotropicHeisenbergS_def (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) :
    anisotropicHeisenbergS (Λ := Λ) J lam D N =
      (∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZ x y lam N) + singleIonAnisotropyS D N := rfl

/-- At `λ = 1, D = 0` the anisotropic Hamiltonian is the isotropic Heisenberg Hamiltonian. -/
theorem anisotropicHeisenbergS_one_zero (J : Λ → Λ → ℂ) (N : ℕ) :
    anisotropicHeisenbergS (Λ := Λ) J 1 0 N = heisenbergHamiltonianS J N := by
  rw [anisotropicHeisenbergS_def, singleIonAnisotropyS_zero, add_zero, heisenbergHamiltonianS_def]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  rw [spinSDotXXZ_one]

/-- The anisotropic Hamiltonian is Hermitian for real coupling, anisotropy, and crystal
field (`star (J x y) = J x y`, `star λ = λ`, `star D = D`). -/
theorem anisotropicHeisenbergS_isHermitian_of_real
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    {lam : ℂ} (hlam : star lam = lam) {D : ℂ} (hD : star D = D) (N : ℕ) :
    (anisotropicHeisenbergS (Λ := Λ) J lam D N).IsHermitian := by
  refine Matrix.IsHermitian.add ?_ (singleIonAnisotropyS_isHermitian hD N)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun x _ => by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun y _ => by
      rw [Matrix.conjTranspose_smul, hJ, (spinSDotXXZ_isHermitian x y hlam N).eq]))

end LatticeSystem.Quantum
