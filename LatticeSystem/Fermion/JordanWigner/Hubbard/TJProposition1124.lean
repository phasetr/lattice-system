import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundDegeneracyUpper
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundDegeneracyLower
import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems

/-!
# Tasaki Proposition 11.24: ferromagnetism in the d=1 ferromagnetic t-J model (E6 capstone)

The final assembly discharging `proposition_11_24` (formerly an axiom).  On the one-dimensional
periodic chain `cycleGraph (N + 1)`, at odd filling `Ne < N + 1`, the t-J ground subspace
`G = groundSubmoduleAtFilling Ĥ_tJ Ne` is the maximal-spin `(Ne+1)`-fold multiplet:

* `finrank G = Ne + 1` — `le_antisymm` of the SU(2)-tower lower bound
  (`tJ_groundSubmodule_finrank_ge`) and the `Ŝ³`-weight upper bound
  (`tJ_groundSubmodule_finrank_le`);
* every `v ∈ G` is an `(Ŝ_tot)²` eigenvector at the maximal eigenvalue `(Ne/2)(Ne/2+1)` — the
  `Ne+1` linearly independent tower states `(Ŝ⁻)^k Ω` (all maximal-spin, by
  `highestWeight_spinMultiplet_general`) span `G` (card `= finrank`), and `(Ŝ_tot)²` acts as the
  scalar `(Ne/2)(Ne/2+1)` on each, hence on every linear combination.

This is exactly `IsMaximalSpinMultipletSubmodule N G Ne`, Tasaki's Proposition 11.24.

The whole discharge rests only on Theorem A.17's single documented axiom
`exists_joint_su2_energy_eigenstate` (via the Perron–Frobenius spin-½ sector reduction); every other
layer is axiom-free.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, pp. 442-443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph Module
open scoped BigOperators

/-- **Tasaki Proposition 11.24 (ferromagnetism in the d=1 ferromagnetic t-J model).**  On the
periodic chain `cycleGraph (N + 1)`, if `Ne < N + 1` is odd then the `Ne`-electron hard-core ground
subspace is the maximal-spin `(Ne+1)`-fold multiplet: `finrank = Ne + 1` and every ground state is
an `(Ŝ_tot)²` eigenvector at `S_max(S_max+1)`, `S_max = Ne/2`.  Discharges the former axiom. -/
theorem proposition_11_24 (N : ℕ) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J)
    (Ne : ℕ) (hNe : Ne < N + 1) (hodd : Odd Ne) :
    IsMaximalSpinMultipletSubmodule N
      (groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne) Ne := by
  classical
  have hpos : 0 < N := by obtain ⟨m, hm⟩ := hodd; omega
  set G := groundSubmoduleAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne with hG
  have hfin : finrank ℂ ↥G = Ne + 1 :=
    le_antisymm (tJ_groundSubmodule_finrank_le hpos Ne hNe hodd τ J hτ hJ)
      (tJ_groundSubmodule_finrank_ge hpos Ne hNe hodd τ J hτ hJ)
  refine ⟨hfin, ?_⟩
  obtain ⟨Ω, hΩne, hΩtop, hΩsz, hΩH, hΩhc, hΩN⟩ :=
    tJ_exists_maximalSpin_highestWeight_groundState hpos Ne hNe hodd τ J hτ hJ
  obtain ⟨_, hSq⟩ := highestWeight_spinMultiplet_general N Ne Ω hΩne hΩtop hΩsz
  obtain ⟨hLI, _⟩ := highestWeight_spinMultiplet_general N Ne Ω hΩne hΩtop hΩsz
  set tower : Fin (Ne + 1) → (Fin (2 * N + 2) → Fin 2) → ℂ :=
    fun k => ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec Ω with htower
  -- every tower member is a ground state (mirror of the lower-bound construction)
  have hmem : ∀ k : Fin (Ne + 1), tower k ∈ G := by
    intro k
    have hHk : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec (tower k) =
        ((groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne : ℝ) : ℂ) •
          tower k := by
      have hcomm : Commute (tJHamiltonian N (cycleGraph (N + 1)) τ J)
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_tJHamiltonian N (cycleGraph (N + 1)) τ J).symm).pow_right _
      rw [htower, Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩH, Matrix.mulVec_smul]
    have hNk : (fermionTotalNumber (2 * N + 1)).mulVec (tower k) = (Ne : ℂ) • tower k := by
      have hcomm : Commute (fermionTotalNumber (2 * N + 1))
          ((fermionTotalSpinMinus N) ^ (k : ℕ)) :=
        ((fermionTotalSpinMinus_commute_fermionTotalNumber N).symm).pow_right _
      rw [htower, Matrix.mulVec_mulVec, hcomm.eq, ← Matrix.mulVec_mulVec, hΩN, Matrix.mulVec_smul]
    rw [hG, groundSubmoduleAtFilling, Submodule.mem_inf, Submodule.mem_inf,
      Module.End.mem_eigenspace_iff, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply]
    exact ⟨⟨hHk, hNk⟩, fermionTotalSpinMinus_pow_mulVec_mem_hardcore N (k : ℕ) hΩhc⟩
  -- the tower (Ne+1 LI states) spans G, since `card = finrank`
  have hGLI : LinearIndependent ℂ (fun k : Fin (Ne + 1) => (⟨tower k, hmem k⟩ : G)) :=
    LinearIndependent.of_comp G.subtype hLI
  have hcard : Fintype.card (Fin (Ne + 1)) = finrank ℂ ↥G := by rw [Fintype.card_fin, hfin]
  have hspan := hGLI.span_eq_top_of_card_eq_finrank hcard
  -- `(Ŝ_tot)²` acts as the maximal scalar on each tower member
  have htw : ∀ k, (fermionTotalSpinSquared N).mulVec (tower k) =
      ((Ne : ℂ) / 2 * ((Ne : ℂ) / 2 + 1)) • tower k := by
    intro k; simp only [htower]; exact hSq k
  -- spread to every ground state via the span
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
