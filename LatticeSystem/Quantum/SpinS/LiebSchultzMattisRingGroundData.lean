import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingMLMUnique
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingEigenTransfer
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorMarshallCore
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.Theorem23GlobalMinimality
import LatticeSystem.Quantum.SpinS.Theorem24ZeroMagnetizationFromUniqueness
import LatticeSystem.Quantum.SpinS.AnisotropicHeisenbergReduction

/-!
# Tasaki §6.2 Theorem 6.3: ground-state data of the AFM Heisenberg ring

Combines the Marshall–Lieb–Mattis uniqueness assembly (`ringSym_ground_uniqueness`), the global
minimality lemma (`tasaki23_eigenvalue_ge_common`), and the symmetrization eigenspace transfer
(`afmHeisenberg_eigenspace_finrank_eq_ringCouplingSym`) into the complete **ground-state data** of
the physical AFM Heisenberg ring: a ground energy `E₀`, a nonzero ground eigenvector `Φ_GS` with a
one-dimensional eigenspace (uniqueness), in the `Ŝ_tot^{(3)} = 0` sector.  This is the input to
Lemmas 6.1/6.2 and the spectral-gap capstone (Theorem 6.3).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, p. 162.
-/

namespace LatticeSystem.Quantum

open Matrix Module

/-- **Ground-state data of the AFM Heisenberg ring** (`L` even ≥ 2, `N ≥ 1`): a ground energy `E₀`
and a nonzero ground eigenvector `Φ_GS` whose `E₀`-eigenspace is one-dimensional (uniqueness) and
which lies in the `Ŝ_tot^{(3)} = 0` sector. -/
theorem afm_ring_ground_state_data (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N) :
    ∃ (E₀ : ℝ) (Φ_GS : (Fin L → Fin (N + 1)) → ℂ),
      IsGroundEnergy (afmHeisenbergChainHamiltonianS L N) E₀ ∧
      Φ_GS ≠ 0 ∧
      (afmHeisenbergChainHamiltonianS L N).mulVec Φ_GS = (E₀ : ℂ) • Φ_GS ∧
      finrank ℂ (End.eigenspace (Matrix.toLin'
        (afmHeisenbergChainHamiltonianS L N)) (E₀ : ℂ)) ≤ 1 ∧
      (totalSpinSOp3 (Fin L) N).mulVec Φ_GS = 0 := by
  classical
  haveI : Nonempty (Fin L) := ⟨⟨0, by omega⟩⟩
  obtain ⟨μ, hfin, hpf, hstrict⟩ := ringSym_ground_uniqueness L N hLeven hL2 hN
  set A : Fin L → Bool := ringSublattice L with hA
  set M0 := (Finset.univ.filter (fun x : Fin L => A x = true)).card * N with hM0
  -- balanced sector is a ground sector and is nonempty
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := Fin L) A N := by
    rw [hM0, ring_tasaki23GroundStateSectors_singleton L N hLeven hL2]
    exact Finset.mem_singleton_self _
  haveI : Nonempty (magConfigS (Fin L) N M0) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  obtain ⟨v, hv_pos, hv_heis⟩ := hpf M0 hM0_mem
  -- build the full complex eigenvector Φ0 at μ
  set w : magConfigS (Fin L) N M0 → ℝ := fun σ => (marshallSignS A σ.1).re * v σ with hw
  have hw_eig : (heisenbergHamiltonianSMatrixOnMagSector (ringCouplingSym L) N M0).mulVec
      (fun σ => (w σ : ℂ)) = (μ : ℂ) • (fun σ => (w σ : ℂ)) :=
    heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal N (ringCouplingSym_im_zero L) hv_heis
  set Φ0 : (Fin L → Fin (N + 1)) → ℂ := magSectorEmbedding (fun σ => (w σ : ℂ)) with hΦ0
  have hΦ0_eig : (heisenbergHamiltonianS (ringCouplingSym L) N).mulVec Φ0 = (μ : ℂ) • Φ0 :=
    heisenbergHamiltonianS_mulVec_magSectorEmbedding_complex (ringCouplingSym L) _ hw_eig
  have hΦ0_ne : Φ0 ≠ 0 := by
    intro hzero
    let τ : magConfigS (Fin L) N M0 := Classical.arbitrary (magConfigS (Fin L) N M0)
    have hτ : (w τ : ℂ) = 0 := by
      have := congrFun hzero τ.1
      rwa [hΦ0, magSectorEmbedding_apply_subtype] at this
    have hwz : (marshallSignS A τ.1).re * v τ = 0 := by exact_mod_cast hτ
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 := marshallSignS_re_sq A τ.1
    have hvz : v τ = 0 := by
      calc v τ = (marshallSignS A τ.1).re * (marshallSignS A τ.1).re * v τ := by rw [hsq, one_mul]
        _ = (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * v τ) := by ring
        _ = 0 := by rw [hwz, mul_zero]
    exact (ne_of_gt (hv_pos τ)) hvz
  -- afm eigenvector at μ/2
  have hafm_eig : (afmHeisenbergChainHamiltonianS L N).mulVec Φ0 = ((μ / 2 : ℝ) : ℂ) • Φ0 := by
    have h2 : (2 : ℂ) • (afmHeisenbergChainHamiltonianS L N).mulVec Φ0 = (μ : ℂ) • Φ0 := by
      rw [← Matrix.smul_mulVec, ← heisenbergHamiltonianS_ringCouplingSym_eq]; exact hΦ0_eig
    have hkey : (2 : ℂ) • (afmHeisenbergChainHamiltonianS L N).mulVec Φ0 =
        (2 : ℂ) • (((μ / 2 : ℝ) : ℂ) • Φ0) := by
      rw [h2, smul_smul]; congr 1; push_cast; ring
    exact smul_right_injective _ two_ne_zero hkey
  -- global minimality: μ ≤ every eigenvalue of the symmetrized operator
  obtain ⟨c, hc⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix A (ringCouplingSym L) N
  have hmin : ∀ {μ' : ℝ} {Ψ : (Fin L → Fin (N + 1)) → ℂ}, Ψ ≠ 0 →
      (heisenbergHamiltonianS (ringCouplingSym L) N).mulVec Ψ = (μ' : ℂ) • Ψ → μ ≤ μ' := by
    intro μ' Ψ hΨ heig
    refine tasaki23_eigenvalue_ge_common A N c (ringCouplingSym_im_zero L) (ringCouplingSym_star L)
      (ringCouplingSym_re_nonneg L) (ringCouplingSym_symm L)
      (fun x y hxy => ringCouplingSym_bipartite L hLeven x y hxy) hc hpf ?_ hΨ heig
    intro M hM μM φ hφ heig2
    haveI : Nonempty (magConfigS (Fin L) N M) := by
      obtain ⟨σ, _⟩ := Function.ne_iff.mp hφ; exact ⟨σ⟩
    exact le_of_lt (hstrict hM hφ heig2)
  -- assemble IsGroundEnergy for the physical chain at E₀ = μ/2
  refine ⟨μ / 2, Φ0, ⟨⟨Φ0, hΦ0_ne, hafm_eig⟩, ?_⟩, hΦ0_ne, hafm_eig, ?_, ?_⟩
  · -- μ/2 ≤ every afm eigenvalue
    rintro E ⟨Ψ, hΨ, hΨ_eig⟩
    have h2E : (heisenbergHamiltonianS (ringCouplingSym L) N).mulVec Ψ = ((2 * E : ℝ) : ℂ) • Ψ := by
      rw [heisenbergHamiltonianS_ringCouplingSym_eq, Matrix.smul_mulVec, hΨ_eig, smul_smul]
      push_cast; ring_nf
    have := hmin hΨ h2E
    linarith
  · -- finrank ≤ 1 (transfer from the symmetrized operator)
    have htrans := afmHeisenberg_eigenspace_finrank_eq_ringCouplingSym L N ((μ / 2 : ℝ) : ℂ)
    rw [show (2 : ℂ) * ((μ / 2 : ℝ) : ℂ) = (μ : ℂ) by push_cast; ring] at htrans
    rw [← htrans]; exact hfin
  · -- Ŝ_tot^{(3)} Φ0 = 0 (uniqueness ⟹ zero magnetization), via the λ=1, D=0 reduction
    have hani_eig : (anisotropicHeisenbergS (ringCouplingSym L) 1 0 N).mulVec Φ0 =
        (μ : ℂ) • Φ0 := by
      rw [anisotropicHeisenbergS_one_zero]; exact hΦ0_eig
    have hani_fin : finrank ℂ (End.eigenspace (Matrix.toLin'
        (anisotropicHeisenbergS (ringCouplingSym L) 1 0 N)) (μ : ℂ)) ≤ 1 := by
      rw [anisotropicHeisenbergS_one_zero]; exact hfin
    exact anisotropicHeisenbergS_unique_groundState_has_zero_magnetization
      (ringCouplingSym L) 1 0 (μ : ℂ) hani_fin hΦ0_ne hani_eig

end LatticeSystem.Quantum
