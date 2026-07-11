/-
First-order vanishing of the susceptibility perturbation on the even ring
(Tasaki §4.1 Theorem 4.2, susceptibility sum rule (4.1.41), issue #4777, PR-χ2a).

Expanding the bond-square field Hamiltonian to second order in the field strength `λ` (reduction
`(★)`, `ringBondSquareFieldHamiltonian_eq`), the linear-in-`λ` perturbation is the Zeeman operator
`V = Σ_z (kOf h)_z · Ŝ³_z` (`kOf = ringBondSquareLinField`, Tasaki's `−Ô_b`, (4.1.38), book p.84).
Tasaki's second-order perturbation formula (4.1.39) has no first-order correction because the
ground-state expectation `⟨Φ|V|Φ⟩` vanishes.  This file proves that vanishing for a unique ground
state `Φ` of the field-free ring Heisenberg Hamiltonian `H₀ = ringFieldHamiltonian n N 0`.

The mechanism is the axis-1 spin reversal `Θ = manyBodyReversalS`, a real symmetric involution that
commutes with `H₀` and reverses each `Ŝ³_z` (`Θ Ŝ³_z Θ = -Ŝ³_z`), hence reverses `V` (`Θ V Θ = -V`).
On a unique ground state `Θ Φ = δ Φ` with `δ = ±1` (shared eigenspace lemma), so
`⟨Φ|V|Φ⟩ = ⟨Θ Φ|V|Θ Φ⟩ = (δ δ̄)⟨Φ|Θ V Θ|Φ⟩ = -⟨Φ|V|Φ⟩ = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020, §4.1,
eqs. (4.1.38)–(4.1.39), book p. 84.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareField
import LatticeSystem.Quantum.SpinS.AndersonTowerTanakaMoments
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction
import LatticeSystem.Quantum.SpinS.AnisotropicReflectionEigenspace
import LatticeSystem.Math.MatrixAnalysis.UniqueEigenspaceInvolution

namespace LatticeSystem.Quantum

open Matrix Module

variable {n N : ℕ}

/-- **The field-free ring field Hamiltonian is the ring Heisenberg Hamiltonian**:
`ringFieldHamiltonian n N 0 = heisenbergHamiltonianS (ringCoupling (2n)) N`, since the Zeeman sum
vanishes at zero field. -/
theorem ringFieldHamiltonian_zero (n N : ℕ) :
    ringFieldHamiltonian n N 0 = heisenbergHamiltonianS (ringCoupling (2 * n)) N := by
  rw [ringFieldHamiltonian,
    Finset.sum_eq_zero (fun z _ => by rw [Pi.zero_apply, Complex.ofReal_zero, zero_smul]), add_zero]

/-- **`Θ` commutes with the field-free ring Hamiltonian** `H₀ = ringFieldHamiltonian n N 0`.  Via
`ringFieldHamiltonian_zero` and the reduction `anisotropicHeisenbergS J 1 0 = heisenbergHamiltonianS
J`, this is the `λ = 1, D = 0` case of `anisotropicHeisenbergS_mul_manyBodyReversalS`. -/
theorem ringFieldHamiltonian_zero_mul_manyBodyReversalS (n N : ℕ) :
    ringFieldHamiltonian n N 0 * manyBodyReversalS (Fin (2 * n)) N
      = manyBodyReversalS (Fin (2 * n)) N * ringFieldHamiltonian n N 0 := by
  rw [ringFieldHamiltonian_zero, ← anisotropicHeisenbergS_one_zero]
  exact anisotropicHeisenbergS_mul_manyBodyReversalS (ringCoupling (2 * n)) 1 0

/-- **`Θ` reverses the linear field operator** `V = Σ_z (kOf h)_z · Ŝ³_z`:
`Θ V Θ = -V`.  Each site term is conjugated by the reversal `F Ŝ³ F = -Ŝ³`
(`spinReversalS_conj_spinSOp3`), lifted site-by-site (`manyBodyReversalS_conj_onSiteS`), and the
real coefficients pass through the scalar multiplication. -/
theorem manyBodyReversalS_conj_ringBondSquareLinFieldOp (n N : ℕ) [NeZero n]
    (h : Fin (2 * n) → ℝ) :
    manyBodyReversalS (Fin (2 * n)) N
        * (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N))
        * manyBodyReversalS (Fin (2 * n)) N
      = -(∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)) := by
  rw [Matrix.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [mul_smul_comm, smul_mul_assoc, ← smul_neg]
  congr 1
  rw [manyBodyReversalS_conj_onSiteS, spinReversalS_conj_spinSOp3, onSiteS_neg]

/-- **First-order vanishing** `⟨Φ|V|Φ⟩ = 0` (Tasaki §4.1 (4.1.39), book p.84): the Zeeman
perturbation `V = Σ_z (kOf h)_z · Ŝ³_z` of the susceptibility expansion has zero expectation in a
unique ground state `Φ` of the field-free ring Hamiltonian `H₀ = ringFieldHamiltonian n N 0`.  The
axis-1 reversal `Θ` fixes `Φ` up to a sign `δ = ±1` (`exists_involution_eigenvalue_of_unique_
eigenspace`, via `ringFieldHamiltonian_zero_mul_manyBodyReversalS` and the involution
`manyBodyReversalS_mul_self`) and reverses `V` (`manyBodyReversalS_conj_ringBondSquareLinFieldOp`),
so the vanishing brick `dotProduct_mulVec_eq_zero_of_conj_anti` applies. -/
theorem ringBondSquareLinFieldOp_groundState_expectation_zero (n N : ℕ) [NeZero n]
    (h : Fin (2 * n) → ℝ) {μ : ℂ} {Φ : (Fin (2 * n) → Fin (N + 1)) → ℂ} (hΦ_ne : Φ ≠ 0)
    (huniq : finrank ℂ ↥(End.eigenspace (Matrix.toLin' (ringFieldHamiltonian n N 0)) μ) ≤ 1)
    (hΦ : (ringFieldHamiltonian n N 0).mulVec Φ = μ • Φ) :
    star Φ ⬝ᵥ (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ = 0 := by
  obtain ⟨δ, hΘΦ_eq, hδ2_eq⟩ :=
    LatticeSystem.Math.exists_involution_eigenvalue_of_unique_eigenspace
      (ringFieldHamiltonian n N 0) (manyBodyReversalS (Fin (2 * n)) N) μ huniq hΦ_ne hΦ
      (ringFieldHamiltonian_zero_mul_manyBodyReversalS n N) (manyBodyReversalS_mul_self _ N)
  refine dotProduct_mulVec_eq_zero_of_conj_anti _ _ _ (δ := δ)
    (manyBodyReversalS_conjTranspose (Fin (2 * n)) N) hΘΦ_eq ?_
    (manyBodyReversalS_conj_ringBondSquareLinFieldOp n N h)
  -- `δ * δ̄ = 1` from `δ² = 1` (`δ = ±1`, both of unit modulus).
  have hself : δ * δ = 1 := by rw [← pow_two]; exact hδ2_eq
  rcases mul_self_eq_one_iff.mp hself with h1 | h1
  · rw [h1, star_one, mul_one]
  · rw [h1, star_neg, star_one, neg_mul_neg, mul_one]

end LatticeSystem.Quantum
