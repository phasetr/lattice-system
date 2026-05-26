import LatticeSystem.Quantum.SpinS.SublatticeMagWeightComponent
import LatticeSystem.Quantum.SpinS.SublatticeHighestWeightExistence
import LatticeSystem.Quantum.SpinS.SublatticeCasimirHighestWeightBound

/-!
# Sublattice Casimir spectral max bound `(Ŝ_A)² ≤ s_A(s_A+1)`

This completes the sublattice analytic ingredient for Issue #3658 (the witness
construction completing the sound Tasaki §2.5 Theorem 2.3 route, #3542): every
eigenvalue of the sublattice Casimir `(Ŝ_A)²` is at most `s_A(s_A+1)` with
`s_A = |A|·N/2`.

Highest-weight argument (sublattice version): a non-zero eigenvector has a
non-zero sublattice-magnetization-weight component (`SublatticeMagWeightComponent.lean`);
raising it with `Ŝ_A^+` terminates (`SublatticeHighestWeightExistence.lean`),
producing a highest-weight vector for which `(Ŝ_A)² = M(M+1)` with `|M| ≤ s_A`
(`SublatticeCasimirHighestWeightBound.lean`), hence the eigenvalue is
`M(M+1) ≤ s_A(s_A+1)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Sublattice Casimir spectral max bound**: every eigenvalue `γ` of `(Ŝ_A)²`
(with a non-zero eigenvector) satisfies `γ.re ≤ s_A(s_A+1)`, `s_A = |A|·N/2`. -/
theorem sublatticeSpinSquaredS_eigenvalue_re_le_sA (A : Λ → Bool)
    {γ : ℂ} {v : (Λ → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hcas : (sublatticeSpinSquaredS N A).mulVec v = γ • v) :
    γ.re ≤
      (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) * (N : ℝ) / 2) + 1) := by
  obtain ⟨k, hk_ne, hk_cas, hk_mem⟩ :=
    sublatticeSpinSquaredS_eigenvec_exists_weight_component A hv hcas
  obtain ⟨M, w', hw'_ne, hw'_mem, hw'_ker, hw'_cas⟩ :=
    sublatticeExists_highestWeight_eigenvector A k.val hk_ne hk_mem hk_cas
  exact sublatticeSpinSquaredS_highestWeight_eigenvalue_re_le A hw'_ne hw'_mem hw'_ker hw'_cas

end LatticeSystem.Quantum
