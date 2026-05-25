import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.MarshallSign
import LatticeSystem.Quantum.SpinS.SaturatedFullLadderOrthogonality
import LatticeSystem.Quantum.SpinS.TotalSquared

/-!
# Tasaki §2.5 Theorem 2.3 — total-spin determination (overlap positivity)

Sound Perron–Frobenius route (Issue #3542; see
`.self-local/docs/tasaki-2-5-pf-route-design.md`).  The remaining global
obligation of the route is to show that the per-sector Marshall-positive
Heisenberg ground state lies in the predicted toy ground-state subspace
(i.e. has the predicted total spin `S_tot = (|A| − |B|)·N/2`).

Tasaki's argument (§2.5, p.42, via the toy Hamiltonian 2.5.10–2.5.12)
turns on the fact that two Marshall-positive vectors in the same
magnetization sector have a strictly positive overlap — the Marshall
signs cancel in the term-by-term product and what remains is a sum of
strictly positive numbers.  This file develops that overlap positivity.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.3 Marshall-positive sector overlap
positivity**: the term-by-term product of two Marshall-signed sector
weights `marshallSignS · v` and `marshallSignS · w` with `v, w > 0` is the
Marshall-sign-free product `v · w`, so its sum over a non-empty sector is
strictly positive.

This is the elementary positivity behind Tasaki's overlap argument: the
overlap of two Marshall-positive vectors in the same magnetization sector
cannot vanish. -/
theorem tasaki23_marshallPositive_sector_dotProduct_pos
    (A : V → Bool) {N M : ℕ} [Nonempty (magConfigS V N M)]
    {v w : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ) (hw_pos : ∀ σ, 0 < w σ) :
    0 <
      ∑ σ : magConfigS V N M,
        ((marshallSignS A σ.1).re * v σ) * ((marshallSignS A σ.1).re * w σ) := by
  have hterm : ∀ σ : magConfigS V N M,
      ((marshallSignS A σ.1).re * v σ) * ((marshallSignS A σ.1).re * w σ) =
        v σ * w σ := by
    intro σ
    have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
      marshallSignS_re_sq A σ.1
    calc
      ((marshallSignS A σ.1).re * v σ) * ((marshallSignS A σ.1).re * w σ)
          = ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * (v σ * w σ) := by
            ring
      _ = v σ * w σ := by rw [hsq, one_mul]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  exact Finset.sum_pos (fun σ _ => mul_pos (hv_pos σ) (hw_pos σ))
    ⟨Classical.choice inferInstance, Finset.mem_univ _⟩

/-- **Sector overlap as a sector sum**: the full-space conjugate-linear
overlap `star (magSectorEmbedding Φ) ⬝ᵥ magSectorEmbedding Ψ` collapses to
the sector sum `∑ σ, star (Φ σ) * Ψ σ`, since the embeddings vanish outside
the magnetization-`M` sector. -/
theorem tasaki23_magSectorEmbedding_dotProduct
    {N M : ℕ} (Φ Ψ : magConfigS V N M → ℂ) :
    star (magSectorEmbedding Φ) ⬝ᵥ magSectorEmbedding Ψ =
      ∑ σ : magConfigS V N M, star (Φ σ) * Ψ σ := by
  classical
  simp only [dotProduct, Pi.star_apply]
  have hfull :
      (∑ τ : V → Fin (N + 1),
          star (magSectorEmbedding Φ τ) * magSectorEmbedding Ψ τ) =
        ∑ τ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
          star (magSectorEmbedding Φ τ) * magSectorEmbedding Ψ τ := by
    refine (Finset.sum_filter_of_ne (p := fun ρ => magSumS ρ = M) ?_).symm
    intro τ _ hne
    by_contra h
    rw [magSectorEmbedding_apply_of_not_mem Ψ h, mul_zero] at hne
    exact hne rfl
  rw [hfull]
  symm
  calc
    (∑ σ : magConfigS V N M, star (Φ σ) * Ψ σ)
        = ∑ σ : magConfigS V N M,
            star (magSectorEmbedding Φ σ.1) * magSectorEmbedding Ψ σ.1 := by
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          rw [magSectorEmbedding_apply_subtype, magSectorEmbedding_apply_subtype]
    _ = ∑ τ ∈ Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M),
            star (magSectorEmbedding Φ τ) * magSectorEmbedding Ψ τ :=
          (Finset.sum_subtype
            (Finset.univ.filter (fun ρ : V → Fin (N + 1) => magSumS ρ = M))
            (p := fun ρ => magSumS ρ = M)
            (fun ρ => by simp [Finset.mem_filter])
            (fun ρ => star (magSectorEmbedding Φ ρ) * magSectorEmbedding Ψ ρ)).symm

/-- **Tasaki §2.5 Theorem 2.3 Marshall-positive overlap is non-zero**: the
conjugate overlap of two Marshall-positive sector vectors
`magSectorEmbedding (marshallSignS · v)` and `magSectorEmbedding (marshallSignS · w)`
(`v, w > 0`) over a non-empty sector is a strictly positive real, hence
non-zero. -/
theorem tasaki23_marshallPositive_overlap_ne_zero
    (A : V → Bool) {N M : ℕ} [Nonempty (magConfigS V N M)]
    {v w : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ) (hw_pos : ∀ σ, 0 < w σ) :
    star (magSectorEmbedding
        (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ⬝ᵥ
      magSectorEmbedding
        (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) ≠ 0 := by
  rw [tasaki23_magSectorEmbedding_dotProduct]
  have hcast :
      (∑ σ : magConfigS V N M,
          star (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ) *
            (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ)) =
        (((∑ σ : magConfigS V N M,
            ((marshallSignS A σ.1).re * v σ) *
              ((marshallSignS A σ.1).re * w σ)) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [Complex.star_def, map_mul, Complex.conj_ofReal]
  rw [hcast]
  have hpos :=
    tasaki23_marshallPositive_sector_dotProduct_pos A hv_pos hw_pos
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

/-- **Tasaki §2.5 Theorem 2.3 Marshall-positive total-Casimir transfer**:
two Marshall-positive sector vectors in the same non-empty magnetization
sector that are total-Casimir eigenvectors at real eigenvalues `α`, `β`
must share their eigenvalue, `α = β`.

This is Tasaki's overlap argument (§2.5, p.42): the Marshall-positive
overlap is non-zero, so the orthogonality of total-Casimir eigenvectors at
distinct eigenvalues forces the eigenvalues to coincide.  It is the bridge
that will transfer the predicted total spin from the toy-Hamiltonian ground
state to the antiferromagnetic Perron–Frobenius ground state. -/
theorem tasaki23_marshallPositive_casimir_eigenvalue_eq
    (A : V → Bool) {N M : ℕ} [Nonempty (magConfigS V N M)]
    {v w : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ) (hw_pos : ∀ σ, 0 < w σ)
    {α β : ℂ} (hα : star α = α) (hβ : star β = β)
    (hv_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        α • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hw_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) =
        β • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) :
    α = β := by
  by_contra hαβ
  exact tasaki23_marshallPositive_overlap_ne_zero A hv_pos hw_pos
    (Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne
      (totalSpinSSquared_isHermitian V N) hα hβ hv_cas hw_cas hαβ)

end LatticeSystem.Quantum
