import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinSTargetConditionalBridge
import LatticeSystem.Quantum.SpinS.AnisotropicSectorPFAtMin

/-!
# General spin-S balanced-sector PF at the anisotropic target

Issue #412 — Tasaki §2.5 Theorem 2.4.

This file supplies the general spin-`S` balanced-sector Perron--Frobenius
input used by the target uniqueness bridge.  The core PF/minimum theorem is
already available for arbitrary spin parameter `N`; the first theorem below
only chooses a finite strict diagonal shift.  The remaining wrappers compose it
with the PR #4087 target bridge, removing the explicit balanced-sector PF
callback while leaving the full `finrank <= 2` and balanced/full ground-energy
equality inputs explicit.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, pp. 43--44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

set_option linter.style.longLine false in
/-- **General spin-S balanced-sector Perron--Frobenius simplicity at the target
point**: the anisotropic target sector matrix has a one-dimensional ground
eigenspace in the chosen magnetization sector. -/
theorem anisotropicHeisenbergS_balanced_sector_pf_at_target
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    {lam D : ℝ} :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS_magSector_submatrix (Λ := Λ) J (lam : ℂ) (D : ℂ)
        N M_balanced))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) : ℝ) : ℂ)) ≤ 1 := by
  classical
  let c : ℝ :=
    Finset.univ.sup' Finset.univ_nonempty
      (fun σ : magConfigS Λ N M_balanced =>
        dressedAnisotropicHeisenbergSReMatrixOnMagSector
          A J (lam : ℂ) (D : ℂ) N M_balanced σ σ) + 1
  have hc_strict : ∀ σ : magConfigS Λ N M_balanced,
      dressedAnisotropicHeisenbergSReMatrixOnMagSector
        A J (lam : ℂ) (D : ℂ) N M_balanced σ σ < c := by
    intro σ
    have hle :
        dressedAnisotropicHeisenbergSReMatrixOnMagSector
          A J (lam : ℂ) (D : ℂ) N M_balanced σ σ ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun τ : magConfigS Λ N M_balanced =>
            dressedAnisotropicHeisenbergSReMatrixOnMagSector
              A J (lam : ℂ) (D : ℂ) N M_balanced τ τ) :=
      Finset.le_sup'
        (fun τ : magConfigS Λ N M_balanced =>
          dressedAnisotropicHeisenbergSReMatrixOnMagSector
            A J (lam : ℂ) (D : ℂ) N M_balanced τ τ)
        (Finset.mem_univ σ)
    dsimp [c]
    linarith
  have hJ_bipartite : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAeq
    by_contra hne
    exact (hJbip x y hne) hAeq
  have hraw :=
    anisotropicHeisenbergS_magSector_submatrix_finrank_le_one_at_hermitianMinEigenvalue
      (Λ := Λ) (N := N) A (J := J) (lam := (lam : ℂ)) (D := (D : ℂ))
      (M := M_balanced) hJim hJnn hJpos hJ_sym hJ_bipartite
      (by simp) (by simp) (c := c) hc_strict hA_ne hB_ne hN
  have hmin_eq :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_of_real
          (Λ := Λ) (N := N) (M := M_balanced) (lam := (lam : ℂ)) (D := (D : ℂ))
          (fun x y => by
            rw [Complex.star_def, Complex.conj_eq_iff_im]
            exact hJim x y)
          (by rw [Complex.star_def, Complex.conj_ofReal])
          (by rw [Complex.star_def, Complex.conj_ofReal])) :=
    hermitianMinEigenvalue_eq_of_spectrum_eq _ _ rfl
  rw [hmin_eq]
  exact hraw

set_option linter.style.longLine false in
/-- **General spin-S target ground eigenspace `finrank <= 1` with balanced-sector
PF discharged**: the remaining explicit inputs are the full target
`finrank <= 2` bound and balanced-sector/full-ground equality. -/
theorem anisotropicHeisenbergS_target_finrank_le_one_of_balanced_eq_full
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (h_balanced_eq_full :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ)) ≤ 1 := by
  classical
  have hpf :=
    anisotropicHeisenbergS_balanced_sector_pf_at_target
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced (lam := lam) (D := D)
  exact
    anisotropicHeisenbergS_target_finrank_le_one_of_balanced_sector_pf
      (Λ := Λ) (N := N) (J := J) hJ_star M_balanced h_balanced
      h_balanced_eq_full h_full_le_two hpf

set_option linter.style.longLine false in
/-- **General spin-S target ground states have zero total magnetization with
balanced-sector PF discharged**. -/
theorem anisotropicHeisenbergS_target_groundState_zero_magnetization_of_balanced_eq_full
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (hN : 1 ≤ N)
    (M_balanced : ℕ)
    [Nonempty (magConfigS Λ N M_balanced)]
    (h_balanced : ((Fintype.card Λ : ℂ) * (N : ℂ) / 2) - (M_balanced : ℂ) = 0)
    {lam D : ℝ}
    (h_balanced_eq_full :
      hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := N) (M := M_balanced) hJ_star lam D) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D))
    (h_full_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (Λ := Λ) J (lam : ℂ) (D : ℂ) N))
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
            ℝ) : ℂ)) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_gs : (anisotropicHeisenbergS J (lam : ℂ) (D : ℂ) N).mulVec Φ =
      ((hermitianMinEigenvalue
        (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
          ℝ) : ℂ) • Φ) :
    (totalSpinSOp3 Λ N).mulVec Φ = 0 := by
  classical
  have huniq :=
    anisotropicHeisenbergS_target_finrank_le_one_of_balanced_eq_full
      (Λ := Λ) (N := N) A hJim hJnn hJpos hJbip hJ_star hJ_sym hA_ne hB_ne hN
      M_balanced h_balanced h_balanced_eq_full h_full_le_two
  exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
    (Λ := Λ) (N := N) J (lam : ℂ) (D : ℂ)
    ((hermitianMinEigenvalue
      (anisotropicHeisenbergS_full_isHermitian_real (Λ := Λ) hJ_star N lam D) :
        ℝ) : ℂ)
    huniq hΦ_ne hΦ_gs

end LatticeSystem.Quantum
