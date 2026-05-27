import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg

/-!
# The axis-swapped anisotropic Hamiltonian (Tasaki 2.5.15)

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

Tasaki relabels the spin axes `2 ↔ 3` of the anisotropic Hamiltonian (2.5.14) to obtain the
unitarily-equivalent (2.5.15)
`Ĥ' = Σ_{x,y} J_{x,y} (Ŝ¹_x Ŝ¹_y + λ Ŝ²_x Ŝ²_y + Ŝ³_x Ŝ³_y) + D Σ_x (Ŝ²_x)²`,
in which the anisotropy now sits in the transverse plane.  Its ladder form (2.5.16) then has
`Ŝ⁺Ŝ⁺ / Ŝ⁻Ŝ⁻` terms that change magnetization by `±2`, coupling sectors into the two parity
blocks where the Perron–Frobenius degeneracy bound `≤ 2` is proved.  This file introduces
`Ĥ'` and proves it Hermitian for real parameters.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43 (eq. 2.5.15).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The axis-swapped two-site term `Ŝ¹_x Ŝ¹_y + λ Ŝ²_x Ŝ²_y + Ŝ³_x Ŝ³_y` (anisotropy on
axis 2). -/
noncomputable def spinSDotXXZSwap (x y : Λ) (lam : ℂ) (N : ℕ) : ManyBodyOpS Λ N :=
  onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
    lam • (onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)) +
    onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)

/-- Definitional unfolding of `spinSDotXXZSwap`. -/
theorem spinSDotXXZSwap_def (x y : Λ) (lam : ℂ) (N : ℕ) :
    spinSDotXXZSwap x y lam N =
      onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N) +
        lam • (onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) := rfl

/-- The axis-swapped two-site term is Hermitian for a real anisotropy `λ`. -/
theorem spinSDotXXZSwap_isHermitian (x y : Λ) {lam : ℂ} (hlam : star lam = lam) (N : ℕ) :
    (spinSDotXXZSwap x y lam N : ManyBodyOpS Λ N).IsHermitian := by
  have hcomm : ∀ A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ,
      (onSiteS x A : ManyBodyOpS Λ N) * onSiteS y A = onSiteS y A * onSiteS x A := by
    intro A
    by_cases hxy : x = y
    · subst hxy; rfl
    · exact onSiteS_mul_onSiteS_of_ne hxy A A
  unfold spinSDotXXZSwap
  refine Matrix.IsHermitian.add (Matrix.IsHermitian.add ?_ ?_) ?_
  · exact Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp1_isHermitian N))
      (onSiteS_isHermitian y (spinSOp1_isHermitian N)) (hcomm _)
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_smul, hlam,
      (Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp2_isHermitian N))
        (onSiteS_isHermitian y (spinSOp2_isHermitian N)) (hcomm _)).eq]
  · exact Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp3_isHermitian N))
      (onSiteS_isHermitian y (spinSOp3_isHermitian N)) (hcomm _)

/-- The axis-swapped single-ion term `D Σ_x (Ŝ²_x)²`. -/
noncomputable def singleIonAnisotropyS2 (D : ℂ) (N : ℕ) : ManyBodyOpS Λ N :=
  D • ∑ x : Λ, onSiteS x (spinSOp2 N) * onSiteS x (spinSOp2 N)

/-- The axis-swapped single-ion term is Hermitian for a real crystal field `D`. -/
theorem singleIonAnisotropyS2_isHermitian {D : ℂ} (hD : star D = D) (N : ℕ) :
    (singleIonAnisotropyS2 (Λ := Λ) D N).IsHermitian := by
  unfold singleIonAnisotropyS2 Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hD, Matrix.conjTranspose_sum]
  congr 1
  exact Finset.sum_congr rfl (fun x _ =>
    (Matrix.IsHermitian.mul_of_commute (onSiteS_isHermitian x (spinSOp2_isHermitian N))
      (onSiteS_isHermitian x (spinSOp2_isHermitian N)) rfl).eq)

/-- The **axis-swapped anisotropic Hamiltonian** (Tasaki (2.5.15)). -/
noncomputable def axisSwappedAnisotropicHeisenbergS (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) :
    ManyBodyOpS Λ N :=
  (∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N) + singleIonAnisotropyS2 D N

/-- Definitional unfolding of `axisSwappedAnisotropicHeisenbergS`. -/
theorem axisSwappedAnisotropicHeisenbergS_def (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) :
    axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N =
      (∑ x : Λ, ∑ y : Λ, J x y • spinSDotXXZSwap x y lam N) + singleIonAnisotropyS2 D N := rfl

/-- The axis-swapped Hamiltonian is Hermitian for real coupling, anisotropy, and crystal
field. -/
theorem axisSwappedAnisotropicHeisenbergS_isHermitian_of_real
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, star (J x y) = J x y)
    {lam : ℂ} (hlam : star lam = lam) {D : ℂ} (hD : star D = D) (N : ℕ) :
    (axisSwappedAnisotropicHeisenbergS (Λ := Λ) J lam D N).IsHermitian := by
  refine Matrix.IsHermitian.add ?_ (singleIonAnisotropyS2_isHermitian hD N)
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl (fun x _ => by
    rw [Matrix.conjTranspose_sum]
    exact Finset.sum_congr rfl (fun y _ => by
      rw [Matrix.conjTranspose_smul, hJ, (spinSDotXXZSwap_isHermitian x y hlam N).eq]))

end LatticeSystem.Quantum
