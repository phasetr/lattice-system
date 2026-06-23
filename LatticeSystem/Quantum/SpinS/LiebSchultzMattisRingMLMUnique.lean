import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingUniqueness
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisRingGroundUnique
import LatticeSystem.Quantum.SpinS.StrictHOutsideFerrimagnetic
import LatticeSystem.Quantum.SpinS.ConnectedSectorFinrankLeOne
import LatticeSystem.Quantum.SpinS.Theorem24SU2GlobalUniquenessFromMLMCore
import LatticeSystem.Quantum.SpinS.FerrimagneticLROUniversal

/-!
# Tasaki §6.2 Theorem 6.3: Marshall–Lieb–Mattis uniqueness for the ring

Assembles the connected-bipartite Marshall–Lieb–Mattis machinery for the symmetrized AFM Heisenberg
ring `heisenbergHamiltonianS (ringCouplingSym L) N`, producing the **full-eigenspace finrank ≤ 1**
at the Perron–Frobenius ground energy `μ`, together with the strict outside-sector ordering.  This
is the operator-level ground-state uniqueness; the physical chain follows by the eigenspace transfer
(`LiebSchultzMattisRingEigenTransfer`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, p. 162.
-/

namespace LatticeSystem.Quantum

open Matrix SimpleGraph Module

/-- The directed ring coupling is self-conjugate (real). -/
private theorem ringCouplingSym_star (L : ℕ) (x y : Fin L) :
    star (ringCouplingSym L x y) = ringCouplingSym L x y := by
  rw [Complex.star_def, Complex.conj_eq_iff_im.mpr (ringCouplingSym_im_zero L x y)]

/-- **Sublattice classes of the even ring are each nonempty and of size `L/2`.** -/
private theorem ringSublattice_cardA_pos (L : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) :
    1 ≤ (Finset.univ.filter (fun x : Fin L => ringSublattice L x = true)).card ∧
      1 ≤ (Finset.univ.filter (fun x : Fin L => (! ringSublattice L x) = true)).card := by
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin L))) (p := fun x => ringSublattice L x = true)
  have hbal := ringSublattice_card_eq L hLeven hL2
  rw [Finset.card_univ, Fintype.card_fin] at hsum
  -- the `¬ (ringSublattice = true)` filter equals the `(! ringSublattice) = true` filter
  have hneg : (Finset.univ.filter (fun x : Fin L => ¬ (ringSublattice L x = true))).card =
      (Finset.univ.filter (fun x : Fin L => (! ringSublattice L x) = true)).card := by
    congr 1; ext x; simp
  rw [hneg, ← hbal] at hsum
  omega

/-- **Ground-state uniqueness of the symmetrized AFM Heisenberg ring** at the Perron–Frobenius
energy `μ`: assembling the connected-bipartite MLM machinery (per-sector PF simplicity + strict
outside-sector ordering) gives `finrank ≤ 1` of the full `μ`-eigenspace, together with the positive
ground eigenvector in the balanced sector and the strict outside-sector ordering. -/
theorem ringSym_ground_uniqueness (L N : ℕ) (hLeven : Even L) (hL2 : 2 ≤ L) (hN : 1 ≤ N) :
    ∃ μ : ℝ,
      finrank ℂ (End.eigenspace (Matrix.toLin'
          (heisenbergHamiltonianS (ringCouplingSym L) N)) (μ : ℂ)) ≤ 1 ∧
      (∀ {M : ℕ}, M ≠ (Finset.univ.filter (fun x : Fin L => ringSublattice L x = true)).card * N →
        [Nonempty (magConfigS (Fin L) N M)] →
        ∀ {μM : ℝ} {φ : magConfigS (Fin L) N M → ℝ}, φ ≠ 0 →
          (heisenbergHamiltonianSReMatrixOnMagSector (ringCouplingSym L) N M).mulVec φ = μM • φ →
          μ < μM) := by
  classical
  set A : Fin L → Bool := ringSublattice L with hA
  set J : Fin L → Fin L → ℂ := ringCouplingSym L with hJ
  set cardA := (Finset.univ.filter (fun x : Fin L => A x = true)).card with hcardA
  set cardB := (Finset.univ.filter (fun x : Fin L => (! A x) = true)).card with hcardB
  set M0 := cardA * N with hM0
  obtain ⟨hcardA1, hcardB1⟩ := ringSublattice_cardA_pos L hLeven hL2
  have hbal : cardA = cardB := ringSublattice_card_eq L hLeven hL2
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  obtain ⟨c, hc⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix A J N
  obtain ⟨c_toy, hc_toy⟩ :=
    exists_strict_diag_bound_dressedHeisenbergSReMatrix A (bipartiteCoupling A) N
  have hGconn : (cycleGraph (n + 1)).Connected := cycleGraph_connected
  -- instantiate the connected strict-hOutside machinery
  obtain ⟨μ, hpf, hstrict⟩ := tasaki23_strict_hOutside_of_connected A (cycleGraph (n + 1)) N c c_toy
    (ringSublattice_card_eq (n + 1) hLeven hL2).ge
    (by
      have hb : (0 : ℝ) <
          ((Finset.univ.filter (fun x : Fin (n + 1) => (! A x) = true)).card : ℝ) := by
        exact_mod_cast hcardB1
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
      positivity)
    hGconn
    (fun x y h => cycleGraph_adj_ringSublattice_ne (n + 1) hLeven h)
    (ringCouplingSym_im_zero (n + 1))
    (ringCouplingSym_star (n + 1))
    (ringCouplingSym_symm (n + 1))
    (ringCouplingSym_re_nonneg (n + 1))
    (fun x y hxy => ringCouplingSym_bipartite (n + 1) hLeven x y hxy)
    (fun x y h => cycleGraph_adj_ringCouplingSym_re_pos (n + 1) h)
    hc hc_toy hN hcardA1 hcardB1
  refine ⟨μ, ?_, ?_⟩
  · -- full-eigenspace finrank ≤ 1
    have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := Fin (n + 1)) A N := by
      rw [hM0, ring_tasaki23GroundStateSectors_singleton (n + 1) N hLeven hL2]
      exact Finset.mem_singleton_self _
    haveI : Nonempty (magConfigS (Fin (n + 1)) N M0) :=
      magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
    obtain ⟨v, hv_pos, hv_heis⟩ := hpf M0 hM0_mem
    have hsec : finrank ℂ (End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (ringCouplingSym (n + 1)) N M0)) (μ : ℂ)) ≤ 1 :=
      heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
        A c hGconn (fun x y h => cycleGraph_adj_ringSublattice_ne (n + 1) hLeven h)
        (ringCouplingSym_im_zero (n + 1))
        (fun x y h => cycleGraph_adj_ringCouplingSym_re_pos (n + 1) h)
        (ringCouplingSym_re_nonneg (n + 1)) (ringCouplingSym_symm (n + 1))
        (fun x y hxy => ringCouplingSym_bipartite (n + 1) hLeven x y hxy) hc hv_pos hv_heis
    refine heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower
      (ringCouplingSym (n + 1)) M0 (ringCouplingSym_im_zero (n + 1)) ?_ hsec
    intro M hM_ne _ μM φ hφ hφ_eig
    rw [ring_tasaki23GroundStateSectors_singleton (n + 1) N hLeven hL2] at hstrict
    exact hstrict (by rw [Finset.mem_singleton]; exact hM_ne) hφ hφ_eig
  · -- strict outside-sector ordering
    intro M hM_ne _ μM φ hφ hφ_eig
    rw [ring_tasaki23GroundStateSectors_singleton (n + 1) N hLeven hL2] at hstrict
    exact hstrict (by rw [Finset.mem_singleton]; exact hM_ne) hφ hφ_eig

end LatticeSystem.Quantum
