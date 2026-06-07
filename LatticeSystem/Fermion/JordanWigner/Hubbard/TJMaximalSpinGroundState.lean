import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaisePositivity
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHighestWeight
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExpansionSpinEigen
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJGroundEnergyGe

/-!
# Tasaki 11.5: a maximal-spin highest-weight ground state (Prop 11.24 E3b/E4 PR6a)

Assembling the whole E3b chain: the d=1 ferromagnetic t-J Hamiltonian at odd filling `Ne < N+1`
has a **nonzero highest-weight ground state of maximal spin** `Ω` —
`Ŝ⁺ Ω = 0`, `Ŝ³ Ω = (Ne/2) Ω`, `Ĥ_tJ Ω = μ Ω` with `μ = groundEnergyAtFilling`.

`Ω = (Ŝ⁺_tot)^((Ne−1)/2) (tJExpansion (ℂ ∘ v))` where `v` is the strictly-positive Perron–Frobenius
eigenvector of the sector matrix.  Non-vanishing comes from the Marshall positivity
(`spinPlusPow_ne_zero_of_coeffSum_ne_zero`, since `coeffSum = Σ v_q > 0`); the highest-weight
properties from `tJ_raised_highestWeight`; and `groundEnergyAtFilling = μ` from the E2 bounds.

This `Ω` feeds `highestWeight_spinMultiplet_general` to build the `Ne+1`-fold multiplet.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **A maximal-spin highest-weight ground state of the d=1 ferromagnetic t-J model.**  For odd
`Ne < N+1` and `τ, J > 0`, there is a nonzero `Ω` with `Ŝ⁺ Ω = 0`, `Ŝ³ Ω = (Ne/2) Ω`, and
`Ĥ_tJ Ω = μ Ω` at the ground energy `μ = groundEnergyAtFilling`. -/
theorem tJ_exists_maximalSpin_highestWeight_groundState (hpos : 0 < N) (Ne : ℕ) (hNeLt : Ne < N + 1)
    (hodd : Odd Ne) (τ J : ℝ) (hτ : 0 < τ) (hJ : 0 < J) :
    ∃ (Ω : (Fin (2 * N + 2) → Fin 2) → ℂ),
      Ω ≠ 0 ∧
      (fermionTotalSpinPlus N).mulVec Ω = 0 ∧
      (fermionTotalSpinZ N).mulVec Ω = ((Ne : ℂ) / 2) • Ω ∧
      (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec Ω =
        ((groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne : ℝ) : ℂ) • Ω := by
  classical
  haveI : Fact (Ne < N + 1) := ⟨hNeLt⟩
  haveI : Fact (Odd Ne) := ⟨hodd⟩
  -- Perron–Frobenius eigenvector
  obtain ⟨c0, hc0⟩ : ∃ c : ℝ, ∀ q : TJSpinHalfFillingSector N Ne,
      tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q < c :=
    ⟨(Finset.univ.sup' Finset.univ_nonempty
        (fun q => tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q)) + 1,
      fun q => lt_of_le_of_lt
        (Finset.le_sup' (fun q => tJEffReMatrixOnSector N Ne (cycleGraph (N + 1)) τ J q q)
          (Finset.mem_univ q)) (lt_add_one _)⟩
  obtain ⟨μ, v, hvpos, hveig, hmin, _⟩ :=
    tJEffReMatrixOnSector_perronFrobenius hpos Ne hNeLt hodd τ J hτ hJ c0 hc0
  have hv0 : v ≠ 0 := fun h => by
    have := hvpos (Classical.arbitrary (TJSpinHalfFillingSector N Ne))
    rw [h] at this; simp at this
  -- ground energy equals μ
  have hgE : groundEnergyAtFilling (tJHamiltonian N (cycleGraph (N + 1)) τ J) Ne = μ :=
    le_antisymm
      (tJHamiltonian_groundEnergyAtFilling_le_of_sectorEigen hpos Ne hodd τ J hτ.le hJ.le hv0 μ
        hveig)
      (tJ_groundEnergyAtFilling_ge_of_sectorMin hpos Ne hNeLt hodd τ J hτ.le hJ.le hmin)
  -- the lifted vector and its sector eigenvalues
  set Φ₀ := tJExpansion N Ne (fun s => (v s : ℂ)) with hΦ₀
  set m := (Ne - 1) / 2 with hm
  have hΦhc : Φ₀ ∈ hubbardHardcoreSubspace N := tJExpansion_mem_hardcore Ne _
  have hΦN : (fermionTotalNumber (2 * N + 1)).mulVec Φ₀ = (Ne : ℂ) • Φ₀ :=
    fermionTotalNumber_mulVec_tJExpansion Ne _
  have hΦd : (fermionTotalDownNumber N).mulVec Φ₀ = (m : ℂ) • Φ₀ :=
    fermionTotalDownNumber_mulVec_tJExpansion N Ne _
  have hΦsz : (fermionTotalSpinZ N).mulVec Φ₀ = ((1 : ℂ) / 2) • Φ₀ := by
    have h := fermionTotalSpinZ_mulVec_tJExpansion N Ne (fun s => (v s : ℂ))
    rw [show (((1 / 2 : ℝ)) : ℂ) = (1 : ℂ) / 2 by push_cast; ring] at h
    exact h
  have hΦH : (tJHamiltonian N (cycleGraph (N + 1)) τ J).mulVec Φ₀ = (μ : ℂ) • Φ₀ :=
    tJHamiltonian_mulVec_tJExpansion_ofReal hpos Ne hodd τ J hτ.le hJ.le v μ hveig
  -- coefficient sum is nonzero (strictly positive)
  have hcs : ∑ c, Φ₀ c ≠ 0 := by
    rw [hΦ₀, coeffSum_tJExpansion]
    have hsumpos : 0 < ∑ s, v s :=
      Finset.sum_pos (fun s _ => hvpos s) ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    rw [← Complex.ofReal_sum]
    exact_mod_cast ne_of_gt hsumpos
  -- the highest weight Ω
  refine ⟨((fermionTotalSpinPlus N) ^ m).mulVec Φ₀,
    spinPlusPow_ne_zero_of_coeffSum_ne_zero Ne m Φ₀ hΦhc hΦN hΦd hcs, ?_, ?_, ?_⟩
  · exact (tJ_raised_highestWeight N (cycleGraph (N + 1)) τ J (μ : ℂ) m Φ₀ hΦsz hΦd hΦH).1
  · rw [(tJ_raised_highestWeight N (cycleGraph (N + 1)) τ J (μ : ℂ) m Φ₀ hΦsz hΦd hΦH).2.1]
    congr 1
    have : 2 * m + 1 = Ne := by obtain ⟨k, hk⟩ := hodd; omega
    push_cast [hm]
    rw [show ((Ne : ℂ)) = ((2 * m + 1 : ℕ) : ℂ) by rw [this]]
    push_cast
    ring
  · rw [(tJ_raised_highestWeight N (cycleGraph (N + 1)) τ J (μ : ℂ) m Φ₀ hΦsz hΦd hΦH).2.2, hgE]

end LatticeSystem.Fermion
