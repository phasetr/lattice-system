import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingDegeneracyUpper
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHalfFillingDegeneracyLower
import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems

/-!
# Tasaki 11.5.3: the half-filling t-J ground subspace is the maximal-spin multiplet (Theorem 11.26)

Assembling the half-filling degeneracy bounds — `finrank G = N+2` (`le_antisymm` of the upper bound
#4331 and the SU(2)-tower lower bound #4326) — with the maximal `(Ŝ_tot)²` eigenvalue on the all-up
SU(2) tower (which spans `G`, since its `N+2` linearly independent members exhaust the dimension)
gives the half-filling case of Theorem 11.26:

* `tJ_halfFilling_isMaximalSpinMultiplet` —
  `IsMaximalSpinMultipletSubmodule N G (N+1)` (ground `S_tot = (N+1)/2`, `(N+2)`-fold degenerate).

This is the boundary (`Ne = N+1`, ferromagnetic-Heisenberg) case of the t-J side of Theorem 11.26,
the half-filling counterpart of the metallic `Ne < N+1` Proposition 11.24 (`proposition_11_24`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

variable {N : ℕ}

/-- **The half-filling t-J ground subspace is the maximal-spin multiplet.**  At half filling
`Ne = N+1` the d=1 ferromagnetic t-J ground subspace is the maximal-spin `(N+2)`-fold multiplet:
`finrank = N+2` and every ground state is an `(Ŝ_tot)²` eigenvector at `S_max(S_max+1)`,
`S_max = (N+1)/2`. -/
theorem tJ_halfFilling_isMaximalSpinMultiplet (τ J : ℝ) (hJ : 0 < J) :
    IsMaximalSpinMultipletSubmodule N
      (groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1)) (N + 1) := by
  classical
  set G := groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) (N + 1) with hG
  have hfin : finrank ℂ ↥G = N + 1 + 1 :=
    le_antisymm (tJ_halfFilling_groundSubmodule_finrank_le τ J hJ)
      (tJ_halfFilling_groundSubmodule_finrank_ge τ J hJ)
  refine ⟨hfin, ?_⟩
  -- the all-up state is a highest-weight ground state
  set Ω : (Fin (2 * N + 2) → Fin 2) → ℂ := hubbardAllUpState N with hΩ
  have hΩne : Ω ≠ 0 := hubbardAllUpState_ne_zero N
  have hΩtop : (fermionTotalSpinPlus N).mulVec Ω = 0 := fermionTotalSpinPlus_mulVec_allUpState N
  have hΩsz : (fermionTotalSpinZ N).mulVec Ω = (((N + 1 : ℕ) : ℂ) / 2) • Ω :=
    fermionTotalSpinZ_mulVec_allUpState N
  obtain ⟨hLI, hSq⟩ := highestWeight_spinMultiplet_general N (N + 1) Ω hΩne hΩtop hΩsz
  set tower : Fin (N + 1 + 1) → (Fin (2 * N + 2) → Fin 2) → ℂ :=
    fun k => ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω with htower
  -- every tower member is a ground state (energy `0`, `N+1` electrons, hard-core)
  have hmem : ∀ k : Fin (N + 1 + 1), tower k ∈ G := by
    intro k
    have hHk : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec (tower k) = 0 := by
      have hcomm : Commute (tJHamiltonian N (cycleGraph (N + 1)) τ J)
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_tJHamiltonian N (cycleGraph (N + 1)) τ J).symm).pow_right _
      rw [htower, Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩ,
        tJHamiltonian_mulVec_allUpState_eq_zero, Matrix.mulVec_zero]
    have hNk : (fermionTotalNumber (2 * N + 1)).mulVec (tower k) =
        (((N + 1 : ℕ) : ℂ)) • (tower k) := by
      have hcomm : Commute (fermionTotalNumber (2 * N + 1))
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_fermionTotalNumber N).symm).pow_right _
      rw [htower, Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩ,
        fermionTotalNumber_mulVec_allUpState, Matrix.mulVec_smul]
    rw [hG, groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
      Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply]
    refine ⟨⟨?_, hNk⟩, fermionTotalSpinMinus_pow_mulVec_mem_hardcore N (k : ℕ)
      (hΩ ▸ hubbardAllUpState_mem_hardcore N)⟩
    rw [hHk, tJ_groundEnergyAtFilling_eq_zero τ J hJ, Complex.ofReal_zero, zero_smul]
  -- the tower spans `G` (its `N+2` linearly independent members exhaust the dimension)
  have hGLI : LinearIndependent ℂ (fun k : Fin (N + 1 + 1) => (⟨tower k, hmem k⟩ : G)) :=
    LinearIndependent.of_comp G.subtype hLI
  have hcard : Fintype.card (Fin (N + 1 + 1)) = finrank ℂ ↥G := by rw [Fintype.card_fin, hfin]
  have hspan := hGLI.span_eq_top_of_card_eq_finrank hcard
  -- `(Ŝ_tot)²` acts as the maximal scalar on every tower member, hence on every ground state
  have htw : ∀ k, (fermionTotalSpinSquared N).mulVec (tower k) =
      ((((N + 1 : ℕ) : ℂ) / 2) * (((N + 1 : ℕ) : ℂ) / 2 + 1)) • tower k := fun k => hSq k
  intro v hvG
  have hmemv : (⟨v, hvG⟩ : G) ∈
      Submodule.span ℂ (Set.range fun k => (⟨tower k, hmem k⟩ : G)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmemv
  have hv_eq : v = ∑ k, a k • tower k := by
    have hc := congrArg Subtype.val ha
    simpa only [Submodule.coe_sum, Submodule.coe_smul] using hc.symm
  rw [hv_eq, Matrix.mulVec_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mulVec_smul, htw k, smul_comm]

end LatticeSystem.Fermion
