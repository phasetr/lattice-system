import LatticeSystem.Quantum.SpinS.AnisotropicHeisenberg
import LatticeSystem.Quantum.SpinS.MultiSiteDotComm
import LatticeSystem.Quantum.SpinS.Magnetization

/-!
# U(1) invariance of the anisotropic Heisenberg Hamiltonian

Issue #3739 (Tasaki §2.5 Theorem 2.4, Mattis–Nishimori).

The anisotropic XXZ + single-ion Hamiltonian (2.5.14) is no longer SU(2)-invariant, but it
retains **U(1) invariance**: it commutes with the total `Ŝ³_tot`.  Indeed every site `Ŝ³`
commutes with `Ŝ³_tot`, so the single-ion term and the longitudinal part `Ŝ³Ŝ³` do; and the
transverse part `Ŝ¹Ŝ¹ + Ŝ²Ŝ²` commutes because the isotropic `Ŝ_x · Ŝ_y` does
(`spinSDot_commutator_totalSpinSOp3`) and `spinSDotXXZ = spinSDot + (λ−1) Ŝ³Ŝ³`.

This is the symmetry that lets the Mattis–Nishimori argument work sector-by-sector in the
`Ŝ³_tot` eigenspaces.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.4, p. 43.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- Each site `Ŝ³` commutes with the total `Ŝ³_tot` (all `Ŝ³` operators commute). -/
theorem onSiteS_spinSOp3_commute_totalSpinSOp3 (x : Λ) (N : ℕ) :
    Commute (onSiteS x (spinSOp3 N) : ManyBodyOpS Λ N) (totalSpinSOp3 Λ N) := by
  rw [totalSpinSOp3]
  refine Commute.sum_right _ _ _ (fun z _ => ?_)
  by_cases hxz : x = z
  · subst hxz; exact Commute.refl _
  · exact onSiteS_commute_of_ne hxz _ _

/-- The longitudinal two-site term `Ŝ³_x Ŝ³_y` commutes with `Ŝ³_tot`. -/
theorem onSiteS_spinSOp3_mul_onSiteS_spinSOp3_commute_totalSpinSOp3 (x y : Λ) (N : ℕ) :
    Commute (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) : ManyBodyOpS Λ N)
      (totalSpinSOp3 Λ N) :=
  (onSiteS_spinSOp3_commute_totalSpinSOp3 x N).mul_left
    (onSiteS_spinSOp3_commute_totalSpinSOp3 y N)

/-- `spinSDotXXZ = spinSDot + (λ − 1) Ŝ³_x Ŝ³_y`. -/
theorem spinSDotXXZ_eq_spinSDot_add (x y : Λ) (lam : ℂ) (N : ℕ) :
    spinSDotXXZ x y lam N =
      spinSDot x y N + (lam - 1) • (onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N)) := by
  rw [spinSDotXXZ_def, spinSDot_def, sub_smul, one_smul]
  abel

/-- The two-site XXZ term commutes with `Ŝ³_tot`. -/
theorem spinSDotXXZ_commute_totalSpinSOp3 (x y : Λ) (lam : ℂ) (N : ℕ) :
    Commute (spinSDotXXZ x y lam N : ManyBodyOpS Λ N) (totalSpinSOp3 Λ N) := by
  rw [spinSDotXXZ_eq_spinSDot_add]
  refine Commute.add_left ?_ ?_
  · exact sub_eq_zero.mp (spinSDot_commutator_totalSpinSOp3 x y N)
  · exact (onSiteS_spinSOp3_mul_onSiteS_spinSOp3_commute_totalSpinSOp3 x y N).smul_left _

/-- The single-ion anisotropy term commutes with `Ŝ³_tot`. -/
theorem singleIonAnisotropyS_commute_totalSpinSOp3 (D : ℂ) (N : ℕ) :
    Commute (singleIonAnisotropyS (Λ := Λ) D N) (totalSpinSOp3 Λ N) := by
  rw [singleIonAnisotropyS]
  refine Commute.smul_left ?_ _
  exact Commute.sum_left _ _ _
    (fun x _ => onSiteS_spinSOp3_mul_onSiteS_spinSOp3_commute_totalSpinSOp3 x x N)

/-- **U(1) invariance**: the anisotropic Heisenberg Hamiltonian commutes with `Ŝ³_tot`. -/
theorem anisotropicHeisenbergS_commute_totalSpinSOp3 (J : Λ → Λ → ℂ) (lam D : ℂ) (N : ℕ) :
    Commute (anisotropicHeisenbergS (Λ := Λ) J lam D N) (totalSpinSOp3 Λ N) := by
  rw [anisotropicHeisenbergS_def]
  refine Commute.add_left ?_ (singleIonAnisotropyS_commute_totalSpinSOp3 D N)
  refine Commute.sum_left _ _ _ (fun x _ => Commute.sum_left _ _ _ (fun y _ => ?_))
  exact (spinSDotXXZ_commute_totalSpinSOp3 x y lam N).smul_left _

/-- **Magnetization-sector preservation**: the anisotropic Hamiltonian maps each `Ŝ³_tot`
eigenspace `magSubspaceS Λ N M` into itself. -/
theorem anisotropicHeisenbergS_mulVec_mem_magSubspaceS_of_mem
    {J : Λ → Λ → ℂ} {lam D : ℂ} {M : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ∈ magSubspaceS Λ N M) :
    (anisotropicHeisenbergS (Λ := Λ) J lam D N).mulVec v ∈ magSubspaceS Λ N M := by
  rw [mem_magSubspaceS_iff] at hv ⊢
  rw [Matrix.mulVec_mulVec, ← (anisotropicHeisenbergS_commute_totalSpinSOp3 J lam D N).eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

end LatticeSystem.Quantum
