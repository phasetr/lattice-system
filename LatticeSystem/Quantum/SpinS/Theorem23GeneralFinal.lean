import LatticeSystem.Quantum.SpinS.Theorem23GeneralHOutside
import LatticeSystem.Quantum.SpinS.Theorem23IntervalCommonEnergy
import LatticeSystem.Quantum.SpinS.Theorem23SectorExistence

/-!
# Tasaki §2.5 Theorem 2.3 for a general connected bipartite antiferromagnetic coupling

Issue #3542 (sound Perron–Frobenius route to Tasaki §2.5 Theorem 2.3), general-`J` capstone.

Combining the common-energy constancy (#3732), the per-sector Theorem 2.2 ground state
(#869), and the inward-ladder non-admissible lower bound (#3737) closes the full
`tasaki_2_5_theorem_2_3` statement for an ARBITRARY coupling `J` that is real, symmetric,
non-negative, bipartite, and positive on the complete bipartite graph — under the canonical
orientation `|¬A| ≤ |A|` with `s_B > 0`.  This removes the toy-coupling restriction of the
earlier capstone `tasaki_2_5_theorem_2_3_bipartiteToy` (#3735).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Springer 2020, §2.5 Theorem 2.3, p. 42; E. Lieb, D. Mattis,
J. Math. Phys. 3 (1962) 749.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A non-empty domain underlies any non-zero real sector vector. -/
private theorem nonempty_magConfigS_of_fn_ne_zero' {N M : ℕ}
    {φ : magConfigS V N M → ℝ} (hne : φ ≠ 0) : Nonempty (magConfigS V N M) := by
  by_contra h
  rw [not_nonempty_iff] at h
  exact hne (funext (fun τ => (h.false τ).elim))

/-- **Tasaki §2.5 Theorem 2.3 for a general connected bipartite antiferromagnetic coupling**
(canonical orientation `|¬A| ≤ |A|`, `s_B > 0`): the full `tasaki_2_5_theorem_2_3` statement
holds for any real symmetric non-negative bipartite coupling `J` that is positive on the
complete bipartite graph. -/
theorem tasaki_2_5_theorem_2_3_of_bipartiteCompletePositive
    (A : V → Bool) (N : ℕ) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    {J : V → V → ℂ} :
    tasaki_2_5_theorem_2_3 A N J c := by
  classical
  intro hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos hc_strict h_intermediate
    _hcardA _hcardB
  -- Common ground-state energy `μ` across all admissible sectors (TIER 4).
  obtain ⟨μ, hcommon⟩ :=
    tasaki23_common_groundEnergy A N c c_toy horient hsB hJ_real hJ_real' hJ_pos hJ_nn hJ_sym
      hJ_bipartite hc_strict hc_strict_toy h_intermediate
  refine ⟨μ, ?_, ?_⟩
  · -- Per-sector existence, Marshall expansion, and within-sector uniqueness at `μ`.
    intro M hM _hNe
    obtain ⟨μM, vM, hμM_lt, hvM_pos, hH_M, _hsupp, huniq⟩ :=
      tasaki_2_5_theorem_2_3_sector_existence (M := M) A N c hJ_real hJ_real' hJ_pos hJ_nn
        hJ_sym hJ_bipartite hc_strict h_intermediate
    -- The dressed real sector eigen-equation for the Theorem 2.2 ground state.
    have hReEig_M : (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec
        (fun σ => (marshallSignS A σ.1).re * vM σ) =
        μM • (fun σ => (marshallSignS A σ.1).re * vM σ) := by
      have hc := heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen
        J (M := M) hH_M
      rw [magSectorRestriction_magSectorEmbedding] at hc
      have hre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N
        hJ_real hc
      simpa only [Complex.ofReal_re] using hre
    have hvM_marshall_pos : ∀ σ,
        0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * vM σ) := fun σ => by
      rw [← mul_assoc, marshallSignS_re_sq, one_mul]; exact hvM_pos σ
    have hmarvM_ne : (fun σ => (marshallSignS A σ.1).re * vM σ) ≠ 0 := by
      intro h
      have h0 := congrFun h (Classical.arbitrary (magConfigS V N M))
      have hp := hvM_marshall_pos (Classical.arbitrary (magConfigS V N M))
      simp only [Pi.zero_apply] at h0
      rw [h0, mul_zero] at hp
      exact lt_irrefl 0 hp
    -- Reconcile the per-sector eigenvalue `μM` with the common energy `μ`.
    obtain ⟨wM, hwM_pos, hReEig_wM⟩ := hcommon M hM
    have hwM_marshall_pos : ∀ σ,
        0 < (marshallSignS A σ.1).re * ((marshallSignS A σ.1).re * wM σ) := fun σ => by
      rw [← mul_assoc, marshallSignS_re_sq, one_mul]; exact hwM_pos σ
    have hle₁ : μ ≤ μM :=
      heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive A N c
        hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hReEig_wM hwM_marshall_pos
        hmarvM_ne hReEig_M
    have hle₂ : μM ≤ μ :=
      heisenbergHamiltonianSReMatrixOnMagSector_eigenvalue_ge_of_marshallPositive A N c
        hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict hReEig_M hvM_marshall_pos
        (by
          intro h
          have h0 := congrFun h (Classical.arbitrary (magConfigS V N M))
          have hp := hwM_marshall_pos (Classical.arbitrary (magConfigS V N M))
          simp only [Pi.zero_apply] at h0
          rw [h0, mul_zero] at hp
          exact lt_irrefl 0 hp)
        hReEig_wM
    have hμM_eq : μM = μ := le_antisymm hle₂ hle₁
    refine ⟨vM, ?_, hvM_pos, ?_, ?_⟩
    · rw [← hμM_eq]; exact hμM_lt
    · rw [← hμM_eq]; exact hH_M
    · intro μ' Ψ' h1 h2 h3
      obtain ⟨he, hr⟩ := huniq h1 h2 h3
      exact ⟨he.trans hμM_eq, hr⟩
  · -- Global minimality via the sector min–max engine (#3733) + general-J `hOutside` (#3737).
    refine tasaki23_eigenvalue_ge_common A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite
      hc_strict hcommon (fun {M} hM_non {μM φ} hφ_ne hφ => ?_)
    haveI : Nonempty (magConfigS V N M) := nonempty_magConfigS_of_fn_ne_zero' hφ_ne
    exact tasaki23_general_hOutside A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc_strict
      hcommon hM_non hφ_ne hφ

end LatticeSystem.Quantum
