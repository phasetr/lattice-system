import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingDualSectorGroundExplicit
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingTPos
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergSpinHalfFinrankLeTwoAtPath
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergCrossingContradictionConditional

/-!
# Spin-1/2 Tasaki §2.5 Theorem 2.4 obligation (2) — axiomatic capstone

Issue #3739 — Tasaki §2.5 Theorem 2.4 obligation (2).

The conditional capstone proving spin-1/2 obligation (2) under TWO explicit
axioms:
- **(2-IVT-c) STRICT GAP at (1, 0)**: `E_M_balanced(1, 0) < E_M(1, 0)` (SU(2)
  Casimir-based strict outside-sector bound; deferred sub-chain).
- **(2-IVT-first-crossing) FIRST-CROSSING IDENTIFICATION**: for `t ∈ (0, 1]`,
  the sector-`M_balanced` min energy equals the global Ĥ min energy
  (sup analysis; deferred).

Conclusion: under the obligation (1) hypotheses (PR #3970 family) + the strict
gap + the first-crossing identification, for the spin-1/2 anisotropic Hamiltonian
at any `(λ', D')` in strict region (i), every sector `M` with `M ≠ M_balanced`
satisfies
`hermitianMinEigenvalue (Ĥ_M(λ', D')) > hermitianMinEigenvalue (Ĥ_M_balanced(λ', D'))`.

Composes:
- PR #3977 (explicit-μ dual sector ground at IVT crossing).
- PR #3978 (IVT crossing point `t > 0` under strict initial gap).
- PR #3976 (spin-1/2 finrank ≤ 2 at global min for `t ∈ (0, 1]`).
- PR #3966 (embedded two-sector contradiction at finrank ≤ 2).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43–44.
-/

namespace LatticeSystem.Quantum

open Matrix Module Set

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **Spin-1/2 obligation (2) axiomatic capstone**: under the obligation (1)
hypotheses + the (2-IVT-c) strict gap + the first-crossing energy identification,
for any sector `M` with non-trivial centered magnetization, the per-sector min
eigenvalue at `(λ', D')` is strictly greater than the `M_balanced`-sector min
eigenvalue. -/
theorem spinHalf_anisotropicHeisenbergS_obligation_2_axiomatic
    (A : Λ → Bool) {J : Λ → Λ → ℂ}
    (hJim : ∀ x y, (J x y).im = 0) (hJnn : ∀ x y, 0 ≤ (J x y).re)
    (hJpos : ∀ x y, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJself : ∀ x, J x x = 0) (hJbip : ∀ x y, J x y ≠ 0 → A x ≠ A y)
    {c : ℝ}
    (hc_strict : ∀ (lam D : ℂ) (σ : Λ → Fin (1 + 1)),
      dressedAxisSwappedAnisotropicHeisenbergSReMatrix A J lam D 1 σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    [Nonempty (parityConfigS Λ 1 0)] [Nonempty (parityConfigS Λ 1 1)]
    (hJ_star : ∀ x y, star (J x y) = J x y)
    (M_balanced : ℕ) (M : ℕ)
    [Nonempty (magConfigS Λ 1 M_balanced)] [Nonempty (magConfigS Λ 1 M)]
    (h_balanced : ((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M_balanced : ℂ) = 0)
    (hM_ne_balanced :
      (((Fintype.card Λ : ℂ) * ((1 : ℕ) : ℂ) / 2) - (M : ℂ)) ≠ 0)
    {lam' D' : ℝ}
    (hlam'_lb : -1 < lam') (hlam'_ub : lam' < 1) (hD' : 0 < D')
    -- (2-IVT-c) AXIOM: strict gap at (1, 0).
    (axiom_strict_gap :
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star 1 0) <
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M) hJ_star 1 0))
    -- (2-IVT-first-crossing) AXIOM: per-sector min (sector M_balanced) equals
    -- the global Ĥ min along the path for t ∈ (0, 1].
    (axiom_first_crossing :
      ∀ t : ℝ, 0 < t → t ≤ 1 →
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
            (Λ := Λ) (N := 1) (M := M_balanced) hJ_star
            (anisotropicHeisenbergParametricPath lam' D' t).1
            (anisotropicHeisenbergParametricPath lam' D' t).2) =
        hermitianMinEigenvalue
          (anisotropicHeisenbergS_isHermitian_of_real (Λ := Λ) (N := 1) hJ_star
            (show star ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) =
                ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ) from by
              rw [Complex.star_def, Complex.conj_ofReal])
            (show star ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) =
                ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) from by
              rw [Complex.star_def, Complex.conj_ofReal]))) :
    hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M_balanced) hJ_star lam' D') <
      hermitianMinEigenvalue
        (anisotropicHeisenbergS_magSector_submatrix_isHermitian_real
          (Λ := Λ) (N := 1) (M := M) hJ_star lam' D') := by
  by_contra hle
  push_neg at hle
  -- Apply PR #3978: crossing point t with 0 < t ≤ 1.
  obtain ⟨t, ht_pos, ht_le, hteq⟩ :=
    anisotropicHeisenbergS_parametric_gap_crossing_t_pos
      (Λ := Λ) hJ_star (N := 1) M_balanced M lam' D' axiom_strict_gap hle
  -- At this t > 0, get the sector ground full-eigenvectors directly via PR #3963.
  obtain ⟨Φ_bal, hΦ_bal_ne, hΦ_bal_eig, hΦ_bal_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M_balanced
  obtain ⟨Φ_M, hΦ_M_ne, hΦ_M_eig, hΦ_M_mem⟩ :=
    exists_sectorGround_full_eigenvector_anisotropicHeisenbergS (Λ := Λ) hJ_star
      (anisotropicHeisenbergParametricPath lam' D' t).1
      (anisotropicHeisenbergParametricPath lam' D' t).2 1 M
  -- Convert sector-M eigenvalue (sector-M min at γ(t)) to sector-M_balanced min via hteq.
  rw [← hteq] at hΦ_M_eig
  -- Apply axiom_first_crossing at t.
  have hμ_eq := axiom_first_crossing t ht_pos ht_le
  rw [hμ_eq] at hΦ_bal_eig hΦ_M_eig
  -- Apply PR #3976: finrank ≤ 2 at the global min at γ(t).
  have h_finrank :=
    spinHalf_anisotropicHeisenbergS_eigenspace_finrank_le_two_at_global_min_path
      A hJim hJnn hJpos hJself hJbip hc_strict hA_ne hB_ne hJ_star
      hlam'_lb hlam'_ub hD' ht_pos ht_le
  -- Apply PR #3966: embedded two-sector contradiction.
  exact anisotropicHeisenbergS_embedded_two_sector_contradiction_finrank_le_two
    J ((anisotropicHeisenbergParametricPath lam' D' t).1 : ℂ)
      ((anisotropicHeisenbergParametricPath lam' D' t).2 : ℂ) _
    h_finrank hΦ_bal_ne h_balanced hΦ_bal_eig
    hΦ_M_ne hM_ne_balanced hΦ_M_eig

end LatticeSystem.Quantum
