import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.Theorem23Sectors
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshall
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique

/-!
# Global minimality of the common ground-state energy (sector min–max engine)

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) — TIER 5.

The full Heisenberg Hamiltonian block-diagonalises over magnetisation sectors, so the
minimum of its spectrum is the minimum over sectors of the per-sector smallest eigenvalue.
Within each sector the dressed real matrix is symmetric and its smallest eigenvalue is the
Marshall-positive Perron–Frobenius one (`…_eigenvalue_ge_of_marshallPositive`,
Collatz–Wielandt).

This file assembles the **sector min–max engine**: given the common ground-state energy
`μ` realised by a Marshall-positive ground state in every *admissible* sector (#3732), and
a lower bound `hOutside` for the *non-admissible* sectors, every full-space eigenvalue
`μ'` satisfies `μ ≤ μ'`.  The non-admissible bound `hOutside` is the Lieb–Mattis energy
monotonicity `E(S_tot)` for `|S_z|` beyond the band — isolated here as an explicit
hypothesis to be discharged separately.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
*Ordering Energy Levels of Interacting Spin Systems*, J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A non-zero vector has a non-zero magnetisation-sector restriction in some sector. -/
private theorem exists_magSectorRestriction_ne_zero {N : ℕ}
    {Ψ : (V → Fin (N + 1)) → ℂ} (hΨ : Ψ ≠ 0) :
    ∃ M, magSectorRestriction (M := M) Ψ ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hΨ
  rw [eq_sum_magSectorEmbedding_magSectorRestriction Ψ]
  refine Finset.sum_eq_zero (fun M _ => ?_)
  rw [h M, magSectorEmbedding_zero]

omit [DecidableEq V] in
/-- A non-empty sector underlies any non-zero restriction. -/
private theorem nonempty_magConfigS_of_restriction_ne_zero {N M : ℕ}
    {Ψ : (V → Fin (N + 1)) → ℂ} (hne : magSectorRestriction (M := M) Ψ ≠ 0) :
    Nonempty (magConfigS V N M) := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact hne (funext (fun τ => (h.false τ).elim))

/-- **Global minimality of the common energy (sector min–max engine).** Let `μ` be an
energy realised by a Marshall-positive ground state of the connected bipartite
antiferromagnetic coupling `J` in every admissible sector (`hcommon`), and suppose every
non-admissible sector has all real eigenvalues `≥ μ` (`hOutside`).  Then `μ` is a lower
bound for the whole spectrum of `heisenbergHamiltonianS J N`: every non-zero full-space
eigenvector at energy `μ'` satisfies `μ ≤ μ'`. -/
theorem tasaki23_eigenvalue_ge_common
    (A : V → Bool) (N : ℕ) (c : ℝ)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    {μ : ℝ}
    (hcommon : ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ vM : magConfigS V N M → ℝ, (∀ σ, 0 < vM σ) ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
            (fun σ => (marshallSignS A σ.1).re * vM σ) =
          μ • (fun σ => (marshallSignS A σ.1).re * vM σ))
    (hOutside : ∀ {M : ℕ}, M ∉ tasaki23GroundStateSectors (V := V) A N →
      ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
        μ ≤ μM)
    {μ' : ℝ} {Ψ' : (V → Fin (N + 1)) → ℂ}
    (hΨ_ne : Ψ' ≠ 0)
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ') :
    μ ≤ μ' := by
  classical
  -- A non-zero sector restriction `W` at some sector `M`, an eigenvector of the complex
  -- sector matrix at `μ'`.
  obtain ⟨M, hW_ne⟩ := exists_magSectorRestriction_ne_zero hΨ_ne
  haveI : Nonempty (magConfigS V N M) := nonempty_magConfigS_of_restriction_ne_zero hW_ne
  set W := magSectorRestriction (M := M) Ψ' with hWdef
  have hW_eig : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec W = (μ' : ℂ) • W :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen J hΨ
  -- Extract a non-zero *real* sector eigenvector `φ` at `μ'` from `W`'s real/imaginary part.
  obtain ⟨φ, hφ_ne, hφ⟩ :
      ∃ φ : magConfigS V N M → ℝ, φ ≠ 0 ∧
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ' • φ := by
    by_cases hre : (fun σ => (W σ).re) = (0 : magConfigS V N M → ℝ)
    · refine ⟨fun σ => (W σ).im, ?_,
        heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec N hJ_real hW_eig⟩
      intro him
      apply hW_ne
      funext τ
      have hr := congrFun hre τ
      have hi := congrFun him τ
      simp only [Pi.zero_apply] at hr hi ⊢
      exact Complex.ext hr hi
    · exact ⟨fun σ => (W σ).re, hre,
        heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real hW_eig⟩
  -- Compare with the per-sector lower bound.
  by_cases hMmem : M ∈ tasaki23GroundStateSectors (V := V) A N
  · -- Admissible sector: the Marshall-positive common ground state bounds `μ'` below by `μ`.
    obtain ⟨vM, hvM_pos, hReEig⟩ := hcommon M hMmem
    refine heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive A N c
      hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hReEig ?_ hφ_ne hφ
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hvM_pos σ
  · -- Non-admissible sector: the supplied outside bound applies directly.
    exact hOutside hMmem hφ_ne hφ

end LatticeSystem.Quantum
