import LatticeSystem.Quantum.SpinS.Theorem24SU2SymmetricFinrankLeOneFromSectorPF
import LatticeSystem.Quantum.SpinS.Theorem23Sectors

/-!
# SU(2) symmetric `finrank ≤ 1` via `|A|=|¬A|` card equality

(PR #3916, Issue #3739): packaging of PR #3915 with the `|A| = |¬A|` symmetric
sublattice card equality replacing the abstract `2M = |Λ|·N` sector index
hypothesis. The sector index `M := |A|·N` automatically satisfies the
constraint via `tasaki23_card_filter_A_add_card_notA`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.4, p. 43-44.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **SU(2) symmetric `finrank ≤ 1` via `|A|=|¬A|`**: with the natural symmetric
sublattice card equality `|A| = |¬A|` and sector index `M := |A|·N`, the SU(2)
symmetric `finrank ≤ 1` conclusion holds (conditional on PR #3915's other
hypotheses). -/
theorem heisenbergHamiltonianS_finrank_le_one_at_SU2_symmetric_card_eq
    (J : Λ → Λ → ℂ) (μ : ℂ)
    (h_finrank_le_two : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ≤ 2)
    {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_admis : Φ ∈ magSubspaceS Λ N 0) (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = μ • Φ)
    (A : Λ → Bool)
    (h_card_eq : (Finset.univ.filter (fun x : Λ => A x = true)).card =
      (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N
          ((Finset.univ.filter (fun x : Λ => A x = true)).card * N))) μ) ≤ 1) :
    finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianS (Λ := Λ) J N)) μ) ≤ 1 := by
  -- Sector index M := |A|·N satisfies 2M = |Λ|·N.
  set M := (Finset.univ.filter (fun x : Λ => A x = true)).card * N with hMdef
  have hM_admis : 2 * M = Fintype.card Λ * N := by
    rw [hMdef]
    have h_sum := tasaki23_card_filter_A_add_card_notA (V := Λ) A
    rw [← h_sum]
    rw [show 2 * ((Finset.univ.filter (fun x : Λ => A x = true)).card * N) =
        (Finset.univ.filter (fun x : Λ => A x = true)).card * N +
        (Finset.univ.filter (fun x : Λ => A x = true)).card * N by ring]
    rw [Nat.add_mul, h_card_eq]
  exact heisenbergHamiltonianS_finrank_le_one_at_SU2_from_sector_pf
    J μ h_finrank_le_two hΦ_admis hΦ_ne hΦ_eig M hM_admis h_sector_pf

end LatticeSystem.Quantum
