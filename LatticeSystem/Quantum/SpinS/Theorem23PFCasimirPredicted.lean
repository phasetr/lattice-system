import LatticeSystem.Quantum.SpinS.Theorem23PFTotalSpin
import LatticeSystem.Quantum.SpinS.Theorem23PFCasimirEigenvector
import LatticeSystem.Quantum.SpinS.TotalSquared
import LatticeSystem.Quantum.SpinS.Theorem23Sectors

/-!
# Tasaki §2.5 Theorem 2.3 — pinning the ground-state Casimir value via overlap

Sound Perron–Frobenius route (Issue #3542; see
`.self-local/docs/tasaki-2-5-pf-route-design.md`).  Tasaki's overlap step
(§2.5, eq. 2.5.12): the antiferromagnetic Heisenberg ground state and the
toy-Hamiltonian ground state are both Marshall positive, so their overlap is
non-zero, and since both are total-Casimir eigenvectors their Casimir values
coincide.  As the toy ground state sits at the predicted total spin, the
actual ground state inherits the predicted total-Casimir value.

This module supplies the eigenvalue-realness lemma and the resulting pin:
given any Marshall-positive total-Casimir witness at the predicted value in
the same magnetization sector (the toy ground state), the per-sector
Perron–Frobenius ground state is a total-Casimir eigenvector at exactly the
predicted value `tasaki23PredictedCasimirValue A N`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Realness of a Hermitian eigenvalue**: an eigenvalue of a Hermitian
matrix that has a non-zero eigenvector is fixed by complex conjugation. -/
theorem isHermitian_eigenvalue_star_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {γ : ℂ} {v : n → ℂ} (hv : A.mulVec v = γ • v) (hv_ne : v ≠ 0) :
    star γ = γ := by
  have hquad : star v ⬝ᵥ A.mulVec v = γ * (star v ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  have hleft : Matrix.vecMul (star v) A = star γ • star v := by
    rw [show A = A.conjTranspose from hA.symm, ← Matrix.star_mulVec, hv, star_smul]
  have hquad2 : star v ⬝ᵥ A.mulVec v = star γ * (star v ⬝ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, hleft, smul_dotProduct, smul_eq_mul]
  have hz : star v ⬝ᵥ v ≠ 0 := by
    have hsum : star v ⬝ᵥ v = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
      rw [dotProduct, Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Pi.star_apply, Complex.star_def, mul_comm, Complex.mul_conj]
    rw [hsum, Ne, Complex.ofReal_eq_zero]
    intro hsum0
    apply hv_ne
    funext i
    have hi0 : Complex.normSq (v i) = 0 := by
      by_contra hne
      have hpos : 0 < ∑ j, Complex.normSq (v j) :=
        Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
          ⟨i, Finset.mem_univ i,
            lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne)⟩
      rw [hsum0] at hpos
      exact lt_irrefl _ hpos
    simpa using (Complex.normSq_eq_zero.mp hi0)
  have heq : γ * (star v ⬝ᵥ v) = star γ * (star v ⬝ᵥ v) := hquad.symm.trans hquad2
  have hsub : (γ - star γ) * (star v ⬝ᵥ v) = 0 := by rw [sub_mul, heq, sub_self]
  have : γ - star γ = 0 := (mul_eq_zero.mp hsub).resolve_right hz
  exact (sub_eq_zero.mp this).symm

/-- **Ground-state total-Casimir value is the predicted value (overlap pin)**:
given a Marshall-positive total-Casimir eigenvector `w` at the predicted value
`tasaki23PredictedCasimirValue A N` in magnetization sector `M` (the
toy-Hamiltonian ground state), the per-sector Perron–Frobenius ground state
`Φ = magSectorEmbedding (marshallSignS · v)` (`v > 0`, `Ĥ Φ = μ Φ`) is itself a
total-Casimir eigenvector at exactly the predicted value.

Tasaki's overlap argument: `Φ` is a total-Casimir eigenvector at some real `γ`
(`tasaki23_pf_groundState_casimir_eigenvector` + `isHermitian_eigenvalue_star_eq`);
the Marshall-positive overlap with `w` is non-zero, so
`tasaki23_marshallPositive_casimir_eigenvalue_eq` forces `γ = predicted`. -/
theorem tasaki23_pf_groundState_casimir_eq_predicted_of_witness
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
    {μ : ℝ} {v w : magConfigS V N M → ℝ}
    (hv_pos : ∀ σ, 0 < v σ) (hw_pos : ∀ σ, 0 < w σ)
    (hH :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        (μ : ℂ) • magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hw_cas :
      (totalSpinSSquared V N).mulVec
          (magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
          magSectorEmbedding
            (fun σ => (((marshallSignS A σ.1).re * w σ : ℝ) : ℂ))) :
    (totalSpinSSquared V N).mulVec
        (magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
      ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
        magSectorEmbedding
          (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) := by
  obtain ⟨γ, hγ⟩ :=
    tasaki23_pf_groundState_casimir_eigenvector A N c hJ_real hJ_pos hJ_nn
      hJ_sym hJ_bipartite hc_strict h_intermediate hv_pos hH
  have hγ_real : star γ = γ :=
    isHermitian_eigenvalue_star_eq (totalSpinSSquared_isHermitian V N) hγ
      (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)
  have hpred_real :
      star ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hγ_eq : γ = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) :=
    tasaki23_marshallPositive_casimir_eigenvalue_eq A hv_pos hw_pos hγ_real
      hpred_real hγ hw_cas
  rw [← hγ_eq]
  exact hγ

end LatticeSystem.Quantum
