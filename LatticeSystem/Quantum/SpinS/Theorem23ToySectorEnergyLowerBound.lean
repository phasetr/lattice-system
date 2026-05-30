import LatticeSystem.Quantum.SpinS.Theorem23ToyMinEnergyBound
import LatticeSystem.Quantum.SpinS.Theorem23ToyGroundEnergyBound
import LatticeSystem.Quantum.SpinS.Theorem23PFToyJointCasimir
import LatticeSystem.Quantum.SpinS.ToyHamiltonianJointEnergy
import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergy

/-!
# Toy sector energy lower bound (Lieb–Mattis lower bound for the toy Hamiltonian)

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), option (a) — TIER 5,
the toy discharge of the non-admissible-sector bound `hOutside`.

For the bipartite toy Hamiltonian `J = bipartiteCoupling A` the predicted minimum energy
`bipartiteToyMinEnergyPredicted A N` is a lower bound for *every* eigenvalue of the dressed
sector matrix in *every* magnetisation sector — not just the admissible band.  Its
Marshall-positive Perron–Frobenius sector ground state is a joint Casimir eigenvector
(#3657), so the universal toy minimum-energy bound `toy_joint_eigenvector_energy_re_ge`
(#3725) applies; the per-sector ground state is below every other sector eigenvalue
(#3680).  Together these give the Lieb–Mattis energy lower bound, which discharges the
`hOutside` hypothesis of the global-minimality engine (#3733) for the toy coupling.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Toy sector energy lower bound (every sector).** For the bipartite toy Hamiltonian
`J = bipartiteCoupling A` (with `|¬A| ≤ |A|`), in *any* magnetisation sector `M` the
predicted minimum energy `(bipartiteToyMinEnergyPredicted A N).re` is below every
eigenvalue `μM` of the dressed sector matrix. -/
theorem tasaki23_toy_sector_energy_ge_predicted
    (A : V → Bool) (N : ℕ) (c : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    {M : ℕ} [Nonempty (magConfigS V N M)]
    (hc_strict : ∀ σ : V → Fin (N + 1),
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c)
    (h_intermediate : ∀ τ : V → Fin (N + 1), ∀ x : V,
      ∃ z, A z ≠ A x ∧ (τ z).val < N)
    {μM : ℝ} {φ : magConfigS V N M → ℝ}
    (hφ_ne : φ ≠ 0)
    (hφ : (heisenbergHamiltonianSReMatrixOnMagSector (bipartiteCoupling A) N M).mulVec φ =
      μM • φ) :
    (bipartiteToyMinEnergyPredicted (Λ := V) A N).re ≤ μM := by
  classical
  -- Marshall-positive Perron–Frobenius ground state of the toy matrix in sector M.
  obtain ⟨μGS, v, _hμGS_lt, hv_pos, hReEig⟩ :=
    exists_marshallSign_eigenvector_heisenbergHamiltonianSReMatrixOnMagSector_legacy
      (M := M) A N c (bipartiteCoupling_im A)
      (fun x y hadj => by
        rw [bipartiteCompleteGraphOf_adj_iff] at hadj
        exact bipartiteCoupling_pos_of_diff_sublattice A hadj.2)
      (fun x y => bipartiteCoupling_nonneg A x y)
      (bipartiteCoupling_symm A)
      (fun _ _ h => bipartiteCoupling_eq_zero_of_same_sublattice A h)
      hc_strict h_intermediate
  have hw_marshall_pos : ∀ σ,
      0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * v σ) := by
    intro σ
    rw [← mul_assoc, marshallSignS_re_sq, one_mul]
    exact hv_pos σ
  -- The ground state lies below the given eigenvalue.
  have hμGS_le : μGS ≤ μM :=
    tasaki23_toy_sector_groundEnergy_le_of_witness A N c hc_strict hw_marshall_pos hReEig hφ_ne hφ
  -- Lift the ground state to the full Hilbert space and split it into Casimir eigenvalues.
  have hComplex := heisenbergHamiltonianSMatrixOnMagSector_mulVec_ofReal
    (J := bipartiteCoupling A) N (bipartiteCoupling_im A) hReEig
  have hH := heisenbergHamiltonianS_mulVec_magSectorEmbedding (bipartiteCoupling A)
    (fun σ => (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) hComplex
  obtain ⟨⟨γ_tot, htot⟩, ⟨γ_A, hA⟩, ⟨γ_B, hB⟩⟩ :=
    tasaki23_toy_groundState_joint_casimir_eigenvector A N c hc_strict h_intermediate hv_pos hH
  -- The ground-state energy equals the Casimir combination `(γ_tot − γ_A − γ_B).re`.
  have hEnergy := heisenbergToyHamiltonianS_mulVec_of_joint_casimir_eigenvector A htot hA hB
  have hμGS_eq : γ_tot - γ_A - γ_B = (μGS : ℂ) :=
    smul_left_injective ℂ (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos)
      (hEnergy.symm.trans hH)
  -- Sector level `k = |V|·N − M` for the universal toy minimum-energy bound.
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
  -- Universal toy minimum-energy bound (#3725): predicted minimum ≤ `(γ_tot − γ_A − γ_B).re`.
  have h3725 := toy_joint_eigenvector_energy_re_ge A (Fintype.card V * N - M) horient
    (tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos) hw_mem htot hA hB
  -- Identify the bound's left-hand side with `(bipartiteToyMinEnergyPredicted A N).re`.
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
