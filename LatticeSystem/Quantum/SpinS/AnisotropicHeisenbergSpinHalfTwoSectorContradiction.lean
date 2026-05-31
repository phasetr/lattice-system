import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingContradictionConditional
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergGlobalMinFinrankLeTwo

/-!
# Spin-1/2 embedded two-sector contradiction at the global min energy

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

Combines:
- PR #3966 `anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two`
  (embedded two-sector contradiction at any μ with `finrank ≤ 2`).
- PR #3970 `spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min`
  (`finrank ≤ 2` at `μ = hermitianMinEigenvalue Ĥ` for spin-1/2).

Conclusion: for spin-1/2 obligation-(1) hypotheses, if two nonzero sector
vectors `Φ_admis` (centered-zero) and `Φ_nonadmis` (non-centered-zero) have
embeddings that are eigenvectors of `Ĥ` at the SPECIFIC energy
`hermitianMinEigenvalue Ĥ`, we get `False`.

This is the spin-1/2 unconditional packaging of #3966 at the global min energy.
Combined with the IVT crossing chain + first-crossing identification, this is
the final algebraic step of obligation (2).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 embedded two-sector contradiction at the global min**: under the
spin-1/2 obligation (1) hypotheses, two nonzero sector eigenvectors at
`hermitianMinEigenvalue Ĥ` with one centered-zero and one non-centered-zero
produce `False`. -/
theorem spinHalf_anisotropicHeisenbergS_embedded_two_sector_contradiction_at_global_min
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {lam : ℂ} (hlam : lam.im = 0) (hlb : -1 < lam.re) (hub : lam.re < 1)
    {D : ℂ} (hDim : D.im = 0) (hDpos : 0 < D.re)
    {c : ℝ}
    (hc_strict : ∀ σ : Λ → Fin (1 + 1),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (hlam_star : star lam = lam) (hD_star : star D = D)
    {M_admis : ℕ} {Φ_admis : magConfigS Λ 1 M_admis → ℂ}
    (hΦ_admis_ne : Φ_admis ≠ 0)
    (h_admis_zero : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_admis : ℂ) = 0)
    (hΦ_admis_eig : (anisotropicHeisenbergS J lam D 1).mulVec
        (magSectorEmbedding Φ_admis) =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
            hJ_star hlam_star hD_star) : ℝ) : ℂ) •
        magSectorEmbedding Φ_admis)
    {M_nonadmis : ℕ} {Φ_nonadmis : magConfigS Λ 1 M_nonadmis → ℂ}
    (hΦ_nonadmis_ne : Φ_nonadmis ≠ 0)
    (h_nonadmis_ne_zero :
      (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_nonadmis : ℂ)) ≠ 0)
    (hΦ_nonadmis_eig : (anisotropicHeisenbergS J lam D 1).mulVec
        (magSectorEmbedding Φ_nonadmis) =
        ((hermitianMinEigenvalue
          (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1)
            hJ_star hlam_star hD_star) : ℝ) : ℂ) •
        magSectorEmbedding Φ_nonadmis) :
    False :=
  anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J lam D _
    (spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min
      A hJim hJnn hJpos hJself hJbip hlam hlb hub hDim hDpos
      hc_strict hA_ne hB_ne hJ_star hlam_star hD_star)
    hΦ_admis_ne h_admis_zero hΦ_admis_eig
    hΦ_nonadmis_ne h_nonadmis_ne_zero hΦ_nonadmis_eig

end LatticeSystem.Quantum
