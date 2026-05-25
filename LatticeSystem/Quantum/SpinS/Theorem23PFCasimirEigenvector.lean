import LatticeSystem.Math.PerronFrobeniusSimple
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSector
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall

/-!
# Tasaki §2.5 Theorem 2.3 — the Perron ground state is a total-Casimir eigenvector

Sound Perron–Frobenius route (Issue #3542; see
`.self-local/docs/tasaki-2-5-pf-route-design.md`).  Step 1 of the total-spin
determination: the per-sector Marshall-positive Heisenberg ground state is a
joint eigenvector of the total Casimir `(Ŝtot)²`.

The mechanism is geometric simplicity of the Perron eigenvalue
(`PerronFrobenius.eigenvec_proportional_of_pos_eigenvec`): the shifted dressed
Heisenberg sector matrix is irreducible and non-negative, so its Perron
eigenspace is one-dimensional.  Since `[Ĥ, (Ŝtot)²] = 0`, applying `(Ŝtot)²`
to the ground state stays in that eigenspace, hence is a scalar multiple of
the ground state.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Math.PerronFrobenius

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Geometric simplicity of the dressed sector Perron eigenvalue**: any real
eigenvector `w` of the shifted dressed Heisenberg sector matrix at the Perron
eigenvalue `r` (with strictly positive Perron eigenvector `v`) is a scalar
multiple of `v`.  Specialisation of
`PerronFrobenius.eigenvec_proportional_of_pos_eigenvec` to the irreducible
shifted dressed sector matrix. -/
theorem tasaki23_shiftedDressed_sector_eigenvec_proportional
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {r : ℝ} {v w : magConfigS V N M → ℝ}
    (hv : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec v = r • v)
    (hv_pos : ∀ σ, 0 < v σ)
    (hw : (shiftedDressedSReMatrixOnMagSector A J N c M).mulVec w = r • w) :
    ∃ s : ℝ, w = s • v :=
  eigenvec_proportional_of_pos_eigenvec
    (isIrreducible_shiftedDressedSReMatrixOnMagSector A N c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate)
    hv hv_pos hw

/-- **One-dimensionality of the Heisenberg sector ground eigenspace**: if `φ`
is a Marshall-positive eigenvector of the (un-dressed) Heisenberg sector matrix
at `μ` (i.e. `marshallSignS · φ > 0`), then every real eigenvector `w` of the
same sector matrix at the same `μ` is a scalar multiple of `φ`.

Marshall-conjugates `φ` and `w` to eigenvectors of the shifted dressed sector
matrix (where `marshallSignS · φ > 0` is the strictly positive Perron
eigenvector), applies the geometric simplicity
`tasaki23_shiftedDressed_sector_eigenvec_proportional`, and conjugates back. -/
theorem tasaki23_heis_sector_eigenvec_proportional_of_marshallPositive
    (A : V → Bool) {J : V → V → ℂ} (N : ℕ) (c : ℝ) {M : ℕ}
    [Nonempty (magConfigS V N M)]
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_pos : ∀ x y : V, (bipartiteCompleteGraphOf A).Adj x y → 0 < (J x y).re)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μ : ℝ} {φ w : magConfigS V N M → ℝ}
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ • φ)
    (hφ_pos : ∀ σ, 0 < (marshallSignS A σ.1).re * φ σ)
    (hw : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec w = μ • w) :
    ∃ s : ℝ, w = s • φ := by
  have hφs :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c
      (dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hφ)
  have hws :=
    shiftedDressedSReMatrixOnMagSector_mulVec_of_dressed_eigenvec A J N c
      (dressedHeisenbergSReMatrixOnMagSector_mulVec_of_heis_eigenvec A N hJ_real hw)
  obtain ⟨s, hs⟩ :=
    tasaki23_shiftedDressed_sector_eigenvec_proportional A N c hJ_real hJ_pos
      hJ_nn hJ_sym hJ_bipartite hc_strict h_intermediate hφs hφ_pos hws
  refine ⟨s, ?_⟩
  funext σ
  have hi := congrFun hs σ
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  have hsq : (marshallSignS A σ.1).re * (marshallSignS A σ.1).re = 1 :=
    marshallSignS_re_sq A σ.1
  calc
    w σ = ((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * w σ := by
          rw [hsq, one_mul]
    _ = (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * w σ) := by ring
    _ = (marshallSignS A σ.1).re * (s * ((marshallSignS A σ.1).re * φ σ)) := by rw [hi]
    _ = s * (((marshallSignS A σ.1).re * (marshallSignS A σ.1).re) * φ σ) := by ring
    _ = s * φ σ := by rw [hsq, one_mul]

end LatticeSystem.Quantum
