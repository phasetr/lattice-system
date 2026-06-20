import LatticeSystem.Quantum.SpinS.ConnectedFerrimagneticLRO
import LatticeSystem.Quantum.SpinS.StaggeredCasimirSU2Invariance
import LatticeSystem.Quantum.SpinS.WeightPreservingExpectationSum
import LatticeSystem.Quantum.SpinS.AnisotropicSectorProjectionEigenvector
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction

set_option linter.unusedSectionVars false

/-!
# Tasaki §4.1 Theorem 4.4 (Shen–Qiu–Tian): universal-form assembly infrastructure

Infrastructure toward discharging the documented axiom `shenQiuTian_ferrimagnetic_lro`
(`FerrimagneticLRO.lean`) for the universal form quantified over *every* normalized ground
state `Φ` of the connected bipartite antiferromagnetic spin-`S` Heisenberg model
(Issue #4604).

## Strategy (Tasaki chain (4.1.16), assembled over magnetization sectors)

The squared staggered order operator `(Ô_Λ)² = staggeredCasimirOpS A N` is `SU(2)`
invariant, so it commutes with `Ŝ_tot^{(3)}` (`staggeredCasimirOpS_commute_op3'`).  Hence the
standard expectation `⟨Φ, (Ô)² Φ⟩` splits as a finite sum over magnetization sectors `M` of the
diagonal expectations on the weight components `Φ_M`
(`weightPreserving_expectation_eq_sum_sector`), and likewise `‖Φ‖² = Σ_M ‖Φ_M‖²`
(`star_dotProduct_self_eq_sum_sector`).

This file provides the graph-agnostic pieces of that assembly:

* `exists_strict_diag_bound_dressedHeisenbergSReMatrix`: the diagonal Perron shift `c`;
* `staggeredCasimirOpS_compl`: invariance of `(Ô)²` under the global sublattice flip
  (so the bound is orientation-symmetric);
* `staggeredCasimirOpS_N_zero`: trivial-spin (`N = 0`) vanishing;
* `heisenbergHamiltonianS_magSectorProjection_eigen`: a weight component of an `H`-eigenvector
  is an `H`-eigenvector;
* `chain_bound_marshall_sector`: **Tasaki's chain (4.1.16) at a Marshall sector vector of
  arbitrary weight** — `(γ − m²) ‖w‖² ≤ ⟨w, (Ô)² w⟩.re` for a Marshall-positive sector vector
  `w` that is a Casimir eigenvector at `γ` and a `Ŝ_tot^{(3)}` eigenvector at the real weight
  `m`.  This generalises the centered chain
  (`ferrimagnetic_lro_connected_centered`) to non-zero weight, with the longitudinal square
  contributing `−m²`.

The remaining ingredient — the `SU(2)` Rayleigh-ratio constancy across the spin multiplet,
transferring `chain_bound_marshall_sector` from a near-central admissible sector (where
`γ − m² ≥ S_tot²`) to every admissible sector via
`su2_expectationRatioRe_ladder_iterate_invariant` and the one-dimensional Marshall ground
sectors — is not yet assembled here; the axiom `shenQiuTian_ferrimagnetic_lro` therefore
remains in `FerrimagneticLRO.lean`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4.1 Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78
(Shen, Qiu, Tian [59]); §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Strict diagonal bound exists.** Over the finite, nonempty configuration type
`Λ → Fin (N + 1)`, the diagonal of `dressedHeisenbergSReMatrix A J N` is bounded
strictly above by `c := (univ.sup' diag) + 1`. -/
theorem exists_strict_diag_bound_dressedHeisenbergSReMatrix
    [Nonempty Λ] (A : Λ → Bool) (J : Λ → Λ → ℂ) (N : ℕ) :
    ∃ c : ℝ, ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c := by
  classical
  haveI : Nonempty (Λ → Fin (N + 1)) := inferInstance
  refine ⟨(Finset.univ.sup' Finset.univ_nonempty
      (fun σ => dressedHeisenbergSReMatrix A J N σ σ)) + 1, fun σ => ?_⟩
  have hle : dressedHeisenbergSReMatrix A J N σ σ ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun σ => dressedHeisenbergSReMatrix A J N σ σ) :=
    Finset.le_sup' (f := fun σ => dressedHeisenbergSReMatrix A J N σ σ) (Finset.mem_univ σ)
  linarith

/-- **Global sign flip leaves the staggered Casimir operator unchanged.** Flipping the
sublattice assignment `A ↦ ¬A` negates both `ε`-factors, so their product — and hence
`staggeredCasimirOpS` — is invariant. -/
theorem staggeredCasimirOpS_compl (A : Λ → Bool) (N : ℕ) :
    staggeredCasimirOpS (fun x => ! A x) N = staggeredCasimirOpS A N := by
  unfold staggeredCasimirOpS
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  congr 1
  by_cases hx : A x <;> by_cases hy : A y <;> simp [hx, hy]

/-- `staggeredCasimirOpS` commutes with `Ŝ_tot^{(3)}`, hence with the magnetization
operator: this is the weight-preservation needed for the sector decomposition. -/
theorem staggeredCasimirOpS_commute_op3' (A : Λ → Bool) (N : ℕ) :
    Commute (staggeredCasimirOpS A N) (totalSpinSOp3 Λ N) :=
  staggeredCasimirOpS_commute_totalSpinSOp3 A N

/-- **Weight-component squared norm decomposition.** Applying the weight-preserving
expectation sum to the identity operator gives `‖Φ‖² = Σ_M ‖Φ_M‖²` (real parts). -/
theorem star_dotProduct_self_eq_sum_sector (Φ : (Λ → Fin (N + 1)) → ℂ) :
    (star Φ ⬝ᵥ Φ).re =
      ∑ M ∈ Finset.range (Fintype.card Λ * N + 1),
        (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          magSectorEmbedding (magSectorRestriction (M := M) Φ)).re := by
  have h := weightPreserving_expectation_eq_sum_sector (1 : ManyBodyOpS Λ N)
    (Commute.one_left _) Φ
  simp only [Matrix.one_mulVec] at h
  rw [h, Complex.re_sum]

/-- **Weight component of a Heisenberg eigenvector is a Heisenberg eigenvector.** Via the
reduction `anisotropicHeisenbergS J 1 0 = heisenbergHamiltonianS J`. -/
theorem heisenbergHamiltonianS_magSectorProjection_eigen
    (J : Λ → Λ → ℂ) {μ : ℂ} (M : ℕ) {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : (heisenbergHamiltonianS J N).mulVec v = μ • v) :
    (heisenbergHamiltonianS J N).mulVec
        (magSectorEmbedding (magSectorRestriction (M := M) v)) =
      μ • magSectorEmbedding (magSectorRestriction (M := M) v) := by
  rw [← anisotropicHeisenbergS_one_zero J N] at hv ⊢
  exact anisotropicHeisenbergS_magSectorProjection_eigen J 1 0 μ M hv

/-- **Chain (4.1.16) at a Marshall sector vector (general weight).**  For a Marshall-form
sector vector `w = magSectorEmbedding (marshallSignS · v)` (`v > 0`) at sector `M`, which is a
total-Casimir eigenvector at `γ` and a `Ŝ_tot^{(3)}` eigenvector at the real weight `m`, the
staggered-order expectation dominates `(γ − m²) ‖w‖²`.  This is Tasaki's chain (4.1.16) without
the centering assumption: the cross-term step (PR2) needs the Marshall form, and the longitudinal
square contributes `−m²` rather than `0`. -/
theorem chain_bound_marshall_sector
    (A : Λ → Bool) {M : ℕ} {v : magConfigS Λ N M → ℝ} (hv_pos : ∀ σ, 0 < v σ)
    {γ m : ℝ}
    (hcas : (totalSpinSSquared Λ N).mulVec
        (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        ((γ : ℝ) : ℂ) • magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hweight : (totalSpinSOp3 Λ N).mulVec
        (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        ((m : ℝ) : ℂ) • magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    (γ - m ^ 2) *
        (star (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ⬝ᵥ
          magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))).re ≤
      (star (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ⬝ᵥ
        (staggeredCasimirOpS A N).mulVec
          (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))).re := by
  classical
  set w : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS Λ N M =>
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hwdef
  set nrm : ℝ := (star w ⬝ᵥ w).re with hnrm
  have hΦ_marshall : w =
      magSectorEmbedding (fun σ : magConfigS Λ N M => marshallSignS A σ.1 * (v σ : ℂ)) := by
    rw [hwdef]; congr 1; funext σ
    rw [Complex.ofReal_mul]; congr 1; exact (marshallSignS_eq_ofReal_re A σ.1).symm
  -- Step 1 (PR1): staggered transverse ≤ full squared staggered order parameter.
  have hstep1 := staggeredTransverse_expectation_le_staggeredCasimir_expectation A N w
  -- Step 2 (PR2): unstaggered transverse double sum ≤ staggered transverse.
  have hstep2 :=
    noStaggeringTransverse_expectation_le_staggeredTransverse_expectation_of_marshall_sector
      A v hv_pos w hΦ_marshall
  -- Step 3: the unstaggered transverse expectation equals `⟨(Ŝ_tot)² − (Ŝ³)² ⟩ = γ‖w‖² − m²‖w‖²`.
  have hstep3 : (star w ⬝ᵥ
        ((∑ x : Λ, ∑ y : Λ,
          (spinSSiteOp1 x N * spinSSiteOp1 y N +
            spinSSiteOp2 x N * spinSSiteOp2 y N)).mulVec w)).re =
      (γ - m ^ 2) * nrm := by
    rw [noStaggeringTransverseSum_eq_totalSpinSSquared_sub_op3_sq Λ N,
      Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
    have hcasval : (star w ⬝ᵥ (totalSpinSSquared Λ N).mulVec w).re = γ * nrm := by
      rw [hcas, dotProduct_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, hnrm]; ring
    have hop3sq : (star w ⬝ᵥ
        ((totalSpinSOp3 Λ N * totalSpinSOp3 Λ N).mulVec w)).re = m ^ 2 * nrm := by
      rw [← Matrix.mulVec_mulVec, hweight, Matrix.mulVec_smul, hweight, smul_smul,
        dotProduct_smul, smul_eq_mul]
      have hcast : ((m : ℝ) : ℂ) * ((m : ℝ) : ℂ) = (((m ^ 2 : ℝ)) : ℂ) := by
        push_cast; ring
      rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hnrm]; ring
    rw [hcasval, hop3sq]; ring
  linarith [hstep1, hstep2, hstep3]

/-- At trivial spin (`N = 0`) the staggered Casimir operator vanishes. -/
theorem staggeredCasimirOpS_N_zero (A : Λ → Bool) :
    (staggeredCasimirOpS A 0 : ManyBodyOpS Λ 0) = 0 := by
  unfold staggeredCasimirOpS
  refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun y _ => ?_))
  rw [spinSDot_N_zero_total x y, smul_zero]

end LatticeSystem.Quantum
