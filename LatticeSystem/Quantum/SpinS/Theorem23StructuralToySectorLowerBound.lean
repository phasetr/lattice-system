import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyBound
import LatticeSystem.Quantum.SpinS.Theorem23ToyGroundEnergyBound
import LatticeSystem.Quantum.SpinS.Theorem23StructuralPFJointCasimir
import LatticeSystem.Quantum.SpinS.Theorem23StructuralMagSectorPF
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Structural toy sector energy lower bound (no `h_intermediate`)

(Thm23-#3887.17): structural variant of `tasaki23_toy_sector_energy_ge_predicted_legacy`
using `exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector`
(Thm23-#3887.9) and `tasaki23_toy_groundState_joint_casimir_eigenvector`
(Thm23-#3887.5).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Structural toy sector energy lower bound (every sector, no `h_intermediate`)**. -/
theorem tasaki23_toy_sector_energy_ge_predicted
    (A : V → Bool) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    {M : ℕ} [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ : V → Fin (N + 1),
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) (hN : 1 ≤ N)
    {μM : ℝ} {φ : magConfigS V N M → ℝ}
    (hφ_ne : φ ≠ 0)
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec φ =
      μM • φ) :
    (bipartiteToyMinEnergyPredicted (Λ := V) A N).re ≤ μM := by
  classical
  obtain ⟨μGS, v, _hμGS_lt, hv_pos, hReEig⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector
      (N := N) (M := M) A c (bipartiteCoupling_im A)
      (fun x y hadj => by
        rw [bipartiteCompleteGraphOf_adj_iff] at hadj
        exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict hA_ne hB_ne hN
  have hw_marshall_pos : ∀ σ,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * v σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hv_pos σ
  have hμGS_le : μGS ≤ μM :=
    tasaki23_toy_sector_groundEnergy_le_of_witness A N c hc_strict hw_marshall_pos hReEig hφ_ne hφ
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal
    (J := bipartiteCoupling A) N (bipartiteCoupling_im A) hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding (bipartiteCoupling A)
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  obtain ⟨⟨γ_tot, htot⟩, ⟨γ_A, hA⟩, ⟨γ_B, hB⟩⟩ :=
    tasaki23_toy_groundState_joint_casimir_eigenvector A c hc_strict
      hA_ne hB_ne hN hv_pos hH
  have hEnergy := heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector A htot hA hB
  have hμGS_eq : γ_tot - γ_A - γ_B = (μGS : ℂ) :=
    smul_left_injective ℂ (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)
      (hEnergy.symm.trans hH)
  have hM_le : M ≤ Fintype.card V * N := by
    obtain ⟨σ⟩ := ‹Nonempty (magConfigS V N M)›
    calc M = magSumS σ.1 := σ.2.symm
      _ ≤ Fintype.card V * N := magSumS_le σ.1
  have hw_mem :
      magSectorEmbedding (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) ∈
        magSubspaceS V N
          (((Fintype.card V * N - M : ℕ) : ℂ) - ((Fintype.card V : ℂ) * (N : ℂ) / 2)) := by
    have h := magSectorEmbedding_mem_magSubspaceS (V := V) (N := N) (M := M)
      (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))
    convert h using 2
    rw [Nat.cast_sub hM_le]
    push_cast
    ring
  have h3725 := toy_joint_eigenvector_energy_re_ge A (Fintype.card V * N - M) horient
    (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos) hw_mem htot hA hB
  have hcplx : bipartiteToyMinEnergyPredicted (Λ := V) A N =
      ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
          ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) *
          ((((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 -
              ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2) +
            1) -
          ((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : V => A x = true)).card : ℝ) * (N : ℝ) / 2 + 1) -
          ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 *
            (((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 +
              1) : ℝ) := by
    unfold bipartiteToyMinEnergyPredicted
    push_cast
    ring
  rw [hcplx, Complex.ofReal_re]
  have hμGS_re : (γ_tot - γ_A - γ_B).re = μGS := by rw [hμGS_eq, Complex.ofReal_re]
  rw [hμGS_re] at h3725
  linarith

end LatticeSystem.Quantum
