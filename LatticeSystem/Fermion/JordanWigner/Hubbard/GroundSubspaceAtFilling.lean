import LatticeSystem.Fermion.JordanWigner.Hubbard.SectorMinEnergy
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreSubspace
import LatticeSystem.Quantum.SpinS.RayleighOnEigenvector
import LatticeSystem.Quantum.SpinS.RayleighOnVecBddBelow
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Fixed-electron-number hard-core ground subspace (Tasaki §11.5)

Generic machinery for the §11.5 metallic-ferromagnetism results, where the relevant Hilbert
space is the *no-double-occupancy* (hard-core) subspace at a **fixed electron number** `N_e`
(unlike the §11.4 results, which compare total-spin sectors at the flat-band filling without a
hard-core constraint).  For any many-body Hamiltonian `H` on the spinful Jordan–Wigner
backbone we define the candidate states, the ground energy, and the ground subspace at filling
`N_e`.  Both the ferromagnetic t-J model (Proposition 11.24) and the d = 1 decorated Hubbard
model (Theorem 11.26) phrase their ground-state statements on this subspace.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2–§11.5.3 (pp. 442–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-- The **fixed-electron-number hard-core states**: unit vectors of `EuclideanSpace ℂ` over
the computational configurations that are `N̂`-eigenvectors at the electron number `N_e` and
lie in the no-double-occupancy subspace `H_{N_e}^hc`.  These are the candidate states over
which the ground energy of a hard-core model at filling `N_e` is taken. -/
def fillingHardcoreStates (M Ne : ℕ) :
    Set (EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2)) :=
  {φ | ‖φ‖ = 1 ∧
    (fermionTotalNumber (2 * M + 1)).mulVec φ.ofLp = (Ne : ℂ) • φ.ofLp ∧
    φ.ofLp ∈ hubbardHardcoreSubspace M}

/-- **The ground-state energy of `H` at filling `N_e`**: the infimum of `rayleighOnVec H` over
the unit, `N_e`-electron, hard-core states `fillingHardcoreStates M Ne` — the minimum energy
of the model on its physical Hilbert space `H_{N_e}^hc`. -/
noncomputable def groundEnergyAtFilling {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (Ne : ℕ) : ℝ :=
  ⨅ φ : fillingHardcoreStates M Ne, rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp

/-- **The ground subspace of `H` at filling `N_e`**: the `H`-eigenspace at the ground energy
`groundEnergyAtFilling H Ne`, intersected with the `N_e`-electron number sector and the
no-double-occupancy subspace `H_{N_e}^hc`.  Its dimension is the ground-state degeneracy. -/
noncomputable def groundSubmoduleAtFilling {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (Ne : ℕ) : Submodule ℂ ((Fin (2 * M + 2) → Fin 2) → ℂ) :=
  Module.End.eigenspace H.mulVecLin (groundEnergyAtFilling H Ne : ℂ) ⊓
    Module.End.eigenspace (fermionTotalNumber (2 * M + 1)).mulVecLin (Ne : ℂ) ⊓
    hubbardHardcoreSubspace M

/-! ## The variational bound on the ground energy -/

/-- A unit `EuclideanSpace` vector is matrix-side normalised: `⟨φ, φ⟩ = Σ_i |φ_i|² = 1`. -/
theorem dotProduct_star_ofLp_self_eq_one {M : ℕ}
    {φ : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2)} (h : ‖φ‖ = 1) :
    dotProduct (star φ.ofLp) φ.ofLp = 1 := by
  have hsum : (∑ i, ‖φ.ofLp i‖ ^ 2 : ℝ) = 1 := by
    have key : ‖φ‖ ^ 2 = ∑ i, ‖φ.ofLp i‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    rw [h, one_pow] at key
    exact key.symm
  have : dotProduct (star φ.ofLp) φ.ofLp = ((∑ i, ‖φ.ofLp i‖ ^ 2 : ℝ) : ℂ) := by
    simp only [dotProduct, Pi.star_apply, RCLike.star_def]
    push_cast
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [this, hsum, Complex.ofReal_one]

/-- The ground energy at filling is a genuine lower bound: the Rayleigh range over the
fixed-filling hard-core unit states is bounded below (by `-Σ_{i,j} ‖H i j‖`, since every such
state is matrix-side normalised). -/
theorem groundEnergyAtFilling_bddBelow {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2))) (Ne : ℕ) :
    BddBelow (Set.range
      (fun φ : fillingHardcoreStates M Ne =>
        rayleighOnVec H (φ : EuclideanSpace ℂ _).ofLp)) := by
  refine ⟨-(∑ i, ∑ j, ‖H i j‖), ?_⟩
  rintro _ ⟨φ, rfl⟩
  exact neg_le_of_abs_le
    (abs_rayleighOnVec_le_sum_entryNorms_of_unit H
      (dotProduct_star_ofLp_self_eq_one φ.property.1))

/-- **Variational bound on the ground energy.** Any nonzero `N_e`-electron hard-core eigenvector
of `H` with (real) eigenvalue `μ` witnesses `groundEnergyAtFilling H Ne ≤ μ`: its normalisation is
an admissible state whose Rayleigh quotient is `μ`. -/
theorem groundEnergyAtFilling_le_of_eigenvector {M : ℕ} (H : ManyBodyOp (Fin (2 * M + 2)))
    (Ne : ℕ) {w : (Fin (2 * M + 2) → Fin 2) → ℂ} (hw : w ≠ 0) (μ : ℝ)
    (hN : (fermionTotalNumber (2 * M + 1)).mulVec w = (Ne : ℂ) • w)
    (hhc : w ∈ hubbardHardcoreSubspace M) (heig : H.mulVec w = (μ : ℂ) • w) :
    groundEnergyAtFilling H Ne ≤ μ := by
  classical
  set e : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2) := (WithLp.equiv 2 _).symm w with he
  have he_of : e.ofLp = w := rfl
  have he0 : e ≠ 0 := fun h => hw (by rw [← he_of, h]; rfl)
  have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr he0
  -- the normalised admissible state
  set φ : EuclideanSpace ℂ (Fin (2 * M + 2) → Fin 2) := ((‖e‖⁻¹ : ℝ) : ℂ) • e with hφ
  have hφ_of : φ.ofLp = ((‖e‖⁻¹ : ℝ) : ℂ) • w := by rw [hφ]; rfl
  have hφ_norm : ‖φ‖ = 1 := by
    rw [hφ, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ hne]
  -- admissibility: number eigenvector and hard-core
  have hφ_N : (fermionTotalNumber (2 * M + 1)).mulVec φ.ofLp = (Ne : ℂ) • φ.ofLp := by
    rw [hφ_of, Matrix.mulVec_smul, hN, smul_comm]
  have hφ_hc : φ.ofLp ∈ hubbardHardcoreSubspace M := by
    rw [hφ_of]; exact Submodule.smul_mem _ _ hhc
  have hmem : φ ∈ fillingHardcoreStates M Ne := ⟨hφ_norm, hφ_N, hφ_hc⟩
  -- the Rayleigh quotient of the normalised eigenvector is μ
  have hφ_eig : H.mulVec φ.ofLp = (μ : ℂ) • φ.ofLp := by
    rw [hφ_of, Matrix.mulVec_smul, heig, smul_comm]
  have hray : rayleighOnVec H φ.ofLp = μ := by
    rw [rayleighOnVec_eq_re_of_eigenvector H φ.ofLp (μ : ℂ) hφ_eig
      (dotProduct_star_ofLp_self_eq_one hφ_norm), Complex.ofReal_re]
  -- conclude via ciInf_le_of_le
  refine ciInf_le_of_le (groundEnergyAtFilling_bddBelow H Ne) ⟨φ, hmem⟩ ?_
  rw [hray]

end LatticeSystem.Fermion
