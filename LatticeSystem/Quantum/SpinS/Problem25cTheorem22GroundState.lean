import LatticeSystem.Quantum.SpinS.Theorem22Connected
import LatticeSystem.Quantum.SpinS.Problem25cAxisSwapGroundStatePhase

/-!
# Tasaki Problem 2.5.c, p. 39, eq. (2.5.6) — at the Theorem 2.2 ground state

Problem 2.5.c asks for the single-site squared spin expectation in the ground state
`|Φ_GS⟩` of Theorem 2.2: `⟨Φ_GS|(Ŝ_x^(α))²|Φ_GS⟩ = S(S+1)/3` for every axis `α = 1, 2, 3`
and every site `x ∈ Λ`.  In the repository's convention `S = N / 2`, so the printed value
`S(S+1)/3` is `N(N+2)/12`.

The book's own solution (p. 498) is the route taken here: uniqueness of the ground state
plus SU(2) invariance of the Hamiltonian force the three axis expectations to agree, and
the single-site Casimir identity `(Ŝ_x^(1))² + (Ŝ_x^(2))² + (Ŝ_x^(3))² = S(S+1)` then gives
one third of that value to each.  Both halves already exist in the library
(`Problem25cAxisSwapGroundStatePhase`, `Problem25cSingleSiteSquared`); this module supplies
the junction to Theorem 2.2, namely the rank-one input, the existence of a *normalised*
ground state, and the identification of the Theorem 2.2 energy with the Hermitian minimum.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
Problem 2.5.c, p. 39, eq. (2.5.6); solution p. 498.  The hypotheses are exactly those of
Theorem 2.2, p. 39: connectedness (Footnote 28, p. 33), bipartiteness (standing for the whole
of §2.5 from p. 37), balanced sublattices `|A| = |B|`, and `S ≥ 1/2`.

The complete bipartite graph is **not** a hypothesis here: it is only the bond graph of the
toy Hamiltonian (2.5.10), p. 41, internal to Tasaki's own proof.
-/

open LatticeSystem.Lattice

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki Problem 2.5.c, p. 39, eq. (2.5.6)** (solution p. 498), at the ground state of
Theorem 2.2, p. 39.

Under Theorem 2.2's own hypotheses — `G` connected (Footnote 28, p. 33) and bipartite for the
sublattice marker `A` (§2.5, p. 37) with balanced classes, and `J` a real symmetric
non-negative exchange vanishing within a sublattice, strictly positive on the bonds of `G` and
vanishing off `G`, at spin `S = N / 2 ≥ 1 / 2` — there is a ground energy `μ` such that

* `μ` is the Hermitian minimum eigenvalue of the Heisenberg Hamiltonian, so "the present
  ground state" of the problem is the spectral minimum;
* the eigenspace at `μ` has `finrank ℂ ≤ 1`, i.e. the ground state is unique;
* a *normalised* ground state exists, so the statement below is not vacuous;
* every normalised ground state has all three squared single-site spin expectations equal to
  `N(N+2)/12 = S(S+1)/3`, at every site `x`, which is (2.5.6).

The Marshall-signed eigenvector of Theorem 2.2 is non-zero because its coefficients are
strictly positive, which both identifies the Hermitian minimum and, after unit
normalisation, witnesses the existence clause. -/
theorem tasaki_problem_2_5_c_singleSite_spinSquare_expectation
    (A : V → Bool) (G : SimpleGraph V) (N : ℕ)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0) :
    ∃ μ : ℝ,
      μ = hermitianMinEigenvalue
          (heisenbergHamiltonianS_isHermitian_of_real (Λ := V) hJ_real' N) ∧
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ)) ≤ 1 ∧
      (∃ Φ : (V → Fin (N + 1)) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
        (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ) ∧
      (∀ {Φ : (V → Fin (N + 1)) → ℂ}, Φ ≠ 0 → star Φ ⬝ᵥ Φ = 1 →
        (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ → ∀ x : V,
          singleSiteSpinSquareExpectationS x (spinSOp1 N) Φ = (N : ℂ) * (N + 2) / 12 ∧
          singleSiteSpinSquareExpectationS x (spinSOp2 N) Φ = (N : ℂ) * (N + 2) / 12 ∧
          singleSiteSpinSquareExpectationS x (spinSOp3 N) Φ = (N : ℂ) * (N + 2) / 12) := by
  classical
  obtain ⟨μ, huniq, hlower, v, hv_pos, hEig, _hCas⟩ :=
    tasaki_2_5_theorem_2_2_of_connected A G N hGconn hGbip h_card_eq hN hJ_real hJ_real'
      hJ_sym hJ_nn hJ_bipartite hJ_pos_G hJ_off
  have hM0_mem : (Finset.univ.filter (fun x : V => A x = true)).card * N ∈
      tasaki23GroundStateSectors (V := V) A N :=
    (tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N _ h_card_eq).mpr rfl
  haveI : Nonempty (magConfigS V N
      ((Finset.univ.filter (fun x : V => A x = true)).card * N)) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  have hΦ0_ne :
      magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ)) ≠ 0 := by
    intro hzero
    let τ : magConfigS V N
        ((Finset.univ.filter (fun x : V => A x = true)).card * N) := Classical.arbitrary _
    have hτ_zero := congrFun hzero τ.1
    rw [magSectorEmbedding_apply_subtype] at hτ_zero
    have hreal_zero : (marshallSignS A τ.1).re * v τ = 0 := by
      exact_mod_cast congrArg Complex.re hτ_zero
    have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
      marshallSignS_re_sq A τ.1
    have hv_zero : v τ = 0 := by
      calc
        v τ = ((marshallSignS A τ.1).re * (marshallSignS A τ.1).re) * v τ := by
          rw [hsq, one_mul]
        _ = (marshallSignS A τ.1).re * ((marshallSignS A τ.1).re * v τ) := by ring
        _ = 0 := by rw [hreal_zero, mul_zero]
    exact (ne_of_gt (hv_pos τ)) hv_zero
  have hmin_eq : hermitianMinEigenvalue
      (heisenbergHamiltonianS_isHermitian_of_real (Λ := V) hJ_real' N) = μ :=
    hermitianMinEigenvalue_eq_common_of_eigenvector_and_global_lower
      (heisenbergHamiltonianS_isHermitian_of_real (Λ := V) hJ_real' N)
      hΦ0_ne hEig (fun hΨ_ne hΨ_eig => hlower hΨ_ne hΨ_eig)
  obtain ⟨Φ0, hΦ0_ne', hEig'⟩ :
      ∃ Φ0 : (V → Fin (N + 1)) → ℂ, Φ0 ≠ 0 ∧
        (heisenbergHamiltonianS J N).mulVec Φ0 = (μ : ℂ) • Φ0 :=
    ⟨_, hΦ0_ne, hEig⟩
  have hnormsq_pos : 0 < vecNormSqRe Φ0 := dotProduct_star_self_re_pos hΦ0_ne'
  have hnorm1 : star (unitNormalize Φ0) ⬝ᵥ unitNormalize Φ0 = 1 :=
    unitNormalize_dotProduct_self Φ0 hnormsq_pos
  have hne : unitNormalize Φ0 ≠ 0 := by
    intro h
    rw [h] at hnorm1
    simp at hnorm1
  have heig : (heisenbergHamiltonianS J N).mulVec (unitNormalize Φ0) =
      (μ : ℂ) • unitNormalize Φ0 := by
    rw [unitNormalize, Matrix.mulVec_smul, hEig', smul_comm]
  refine ⟨μ, hmin_eq.symm, huniq, ⟨unitNormalize Φ0, hne, hnorm1, heig⟩, ?_⟩
  intro Φ hΦ_ne hΦnorm hΦ x
  exact singleSiteSpinSquareExpectationS_all_axes_eq_of_zAxisRot_axisSwap_eigenphase
    J (μ : ℂ) x huniq hΦ_ne hΦnorm hΦ

end LatticeSystem.Quantum
