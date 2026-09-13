import LatticeSystem.Math.MatrixAnalysis.RankOneEigenspaceExpectation
import LatticeSystem.Quantum.SpinS.Problem25cTheorem22GroundState
import LatticeSystem.Quantum.SpinS.Problem25dPairGeneralSign

/-!
# Tasaki Problem 2.5.d, p. 40, eq. (2.5.7) — at the Theorem 2.2 ground state

Problem 2.5.d asks for the sign of the two-spin correlation in the ground state `|Φ_GS⟩` of
Theorem 2.2: `⟨Φ_GS|Ŝ_x · Ŝ_y|Φ_GS⟩` is strictly **positive** when `x` and `y` lie in the same
sublattice and strictly **negative** when they lie in different ones.

The book's own solution (p. 498) is the route taken here.  Equation (S.22) reduces the dot
product to the transverse ladder expectation by SU(2) symmetry of the unique ground state, and
(S.23) evaluates the gauge-transformed ladder expectation as a sum of manifestly positive terms.
That argument is **uniform in the pair**: the gauge factor `(−1)^x (−1)^y` is `+1` on a
same-sublattice pair and `−1` on a crossing pair, and (S.23)'s right-hand side is positive in
both cases, so the two branches of (2.5.7) are the two values of that one prefactor.  The
pair-uniform half lives in `Problem25dPairGeneralSign`; this module joins it to Theorem 2.2.

Two further inputs are supplied here rather than there.  The Perron–Frobenius vector Theorem 2.2
returns is not normalised, so the statement below is phrased for an arbitrary normalised ground
state and transported onto that vector by the rank-one eigenspace expectation bridge
(`RankOneEigenspaceExpectation`): uniqueness of the ground state makes every normalised ground
state give the same expectation.  And the third site used by the same-sublattice witness is
produced from `|A| = |B|` together with connectedness, so it is **not** a hypothesis here.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
Problem 2.5.d, p. 40, eq. (2.5.7); solution p. 498, eqs. (S.22)–(S.23).  The hypotheses are
exactly those of Theorem 2.2, p. 39: connectedness (Footnote 28, p. 33), bipartiteness (standing
for the whole of §2.5 from p. 37), balanced sublattices `|A| = |B|`, and `S ≥ 1/2`.

The complete bipartite graph is **not** a hypothesis: it is only the bond graph of the toy
Hamiltonian (2.5.10), p. 41, internal to Tasaki's own proof of Theorem 2.2.  Theorem 2.3, which
first appears on p. 42, is likewise not a hypothesis.
-/

open LatticeSystem.Lattice

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki Problem 2.5.d, p. 40, eq. (2.5.7)** (solution p. 498, eqs. (S.22)–(S.23)), at the
ground state of Theorem 2.2, p. 39.

Under Theorem 2.2's own hypotheses — `G` connected (Footnote 28, p. 33) and bipartite for the
sublattice marker `A` (§2.5, p. 37) with balanced classes, and `J` a real symmetric non-negative
exchange vanishing within a sublattice, strictly positive on the bonds of `G` and vanishing off
`G`, at spin `S = N / 2 ≥ 1 / 2` — there is a ground energy `μ` such that

* `μ` is the Hermitian minimum eigenvalue of the Heisenberg Hamiltonian, so "the ground state"
  of the problem is the spectral minimum;
* the eigenspace at `μ` has `finrank ℂ ≤ 1`, i.e. the ground state is unique;
* a *normalised* ground state exists, so the statement below is not vacuous;
* every normalised ground state has, at every pair of **distinct** sites, two-spin correlation
  with strictly positive real part when `A x = A y` and strictly negative real part when
  `A x ≠ A y`.  That is (2.5.7).

`x ≠ y` is carried because (S.22)'s reduction uses `(Ŝ_x^+ Ŝ_y^-)† = Ŝ_x^- Ŝ_y^+`, which needs
distinct sites; the diagonal case `x = y` is the single-site Casimir value `S(S+1)` of
Problem 2.5.c and is not part of (2.5.7). -/
theorem tasaki_problem_2_5_d_twoSpin_correlation_sign
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
        (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ →
        ∀ x y : V, x ≠ y →
          (A x = A y → 0 < (twoSpinCorrelationS x y Φ).re) ∧
          (A x ≠ A y → (twoSpinCorrelationS x y Φ).re < 0)) := by
  classical
  obtain ⟨μ, huniq, hlower, v, hv_pos, hEig, _hCas⟩ :=
    tasaki_2_5_theorem_2_2_of_connected A G N hGconn hGbip h_card_eq hN hJ_real hJ_real'
      hJ_sym hJ_nn hJ_bipartite hJ_pos_G hJ_off
  have hM0_mem : (Finset.univ.filter (fun z : V => A z = true)).card * N ∈
      tasaki23GroundStateSectors (V := V) A N :=
    (tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N _ h_card_eq).mpr rfl
  haveI : Nonempty (magConfigS V N
      ((Finset.univ.filter (fun z : V => A z = true)).card * N)) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  -- Theorem 2.2's real-coefficient embedding is the sector-supported Marshall form.
  have hembed :
      magSectorEmbedding (fun τ : magConfigS V N
          ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
        (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))
        = magSectorEmbedding (fun τ : magConfigS V N
            ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A τ.1 * (v τ : ℂ)) := by
    apply congrArg
    funext τ
    rw [Complex.ofReal_mul, ← marshallSignS_eq_ofReal_re]
  rw [hembed] at hEig
  set Φmar : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun τ : magConfigS V N
        ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
      marshallSignS A τ.1 * (v τ : ℂ)) with hΦmar_def
  have hΦmar_ne : Φmar ≠ 0 := by
    intro hzero
    let τ : magConfigS V N
        ((Finset.univ.filter (fun z : V => A z = true)).card * N) := Classical.arbitrary _
    have hτ : marshallSignS A τ.1 * (v τ : ℂ) = 0 := by
      have h := congrFun hzero τ.1
      rw [hΦmar_def, magSectorEmbedding_apply_subtype] at h
      simpa using h
    have hv_ne : (v τ : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt (hv_pos τ)
    exact mul_ne_zero (marshallSignS_ne_zero A τ.1) hv_ne hτ
  have hmin_eq : hermitianMinEigenvalue
      (heisenbergHamiltonianS_isHermitian_of_real (Λ := V) hJ_real' N) = μ :=
    hermitianMinEigenvalue_eq_common_of_eigenvector_and_global_lower
      (heisenbergHamiltonianS_isHermitian_of_real (Λ := V) hJ_real' N)
      hΦmar_ne hEig (fun hΨ_ne hΨ_eig => hlower hΨ_ne hΨ_eig)
  -- A normalised ground state exists, so the universal clause below is not vacuous.
  have hnormsq_pos : 0 < vecNormSqRe Φmar := dotProduct_star_self_re_pos hΦmar_ne
  have hnorm1 : star (unitNormalize Φmar) ⬝ᵥ unitNormalize Φmar = 1 :=
    unitNormalize_dotProduct_self Φmar hnormsq_pos
  have hne : unitNormalize Φmar ≠ 0 := by
    intro h
    rw [h] at hnorm1
    simp at hnorm1
  have heig : (heisenbergHamiltonianS J N).mulVec (unitNormalize Φmar) =
      (μ : ℂ) • unitNormalize Φmar := by
    rw [unitNormalize, Matrix.mulVec_smul, hEig, smul_comm]
  -- Both sublattices are inhabited: this supplies the third site of the same-sublattice
  -- witness, from `|A| = |B|` and connectedness rather than from a new hypothesis.
  have hsum : (Finset.univ.filter (fun z : V => A z = true)).card +
      (Finset.univ.filter (fun z : V => (! A z) = true)).card = Fintype.card V :=
    tasaki23_card_filter_A_add_card_notA A
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hGconn.nonempty
  have hcardA1 : 1 ≤ (Finset.univ.filter (fun z : V => A z = true)).card := by omega
  have hcardB1 : 1 ≤ (Finset.univ.filter (fun z : V => (! A z) = true)).card := by omega
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA1
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB1
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b with
    | false => exact ⟨b, hAb⟩
    | true => rw [hAb] at hbf; cases hbf
  have hself : star Φmar ⬝ᵥ Φmar = ((vecNormSqRe Φmar : ℝ) : ℂ) := by
    unfold vecNormSqRe
    rw [star_dotProduct_self_eq, Complex.ofReal_re]
  refine ⟨μ, hmin_eq.symm, huniq, ⟨unitNormalize Φmar, hne, hnorm1, heig⟩, ?_⟩
  intro Φ hΦ_ne hΦnorm hΦ_eig x y hxy
  have hpos_mar : 0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y Φmar).re :=
    twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_balanced_sector_pair
      A hxy hN hA_ne hB_ne J (μ : ℂ) v hv_pos huniq hΦmar_ne hEig
  have hbridge : (star Φmar ⬝ᵥ Φmar) * (star Φ ⬝ᵥ (spinSDot x y N).mulVec Φ)
      = star Φmar ⬝ᵥ (spinSDot x y N).mulVec Φmar :=
    LatticeSystem.Math.dotProduct_star_mulVec_eq_of_finrank_eigenspace_le_one
      huniq hΦ_ne hΦnorm hΦ_eig hEig
  have hbridge' : (star Φmar ⬝ᵥ Φmar) * twoSpinCorrelationS x y Φ
      = twoSpinCorrelationS x y Φmar := hbridge
  have hg_eq : ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinCorrelationS x y Φmar).re
      = vecNormSqRe Φmar * ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinCorrelationS x y Φ).re := by
    rw [← hbridge', hself]
    simp [Complex.mul_re]
    ring
  rw [hg_eq] at hpos_mar
  have hpos_Φ : 0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y Φ).re := by
    nlinarith [hnormsq_pos, hpos_mar]
  exact ⟨fun hsame =>
      twoSpinCorrelationS_re_pos_of_same_of_bipartite_signed_re_pos A hpos_Φ hsame,
    fun hcross =>
      twoSpinCorrelationS_re_neg_of_ne_of_bipartite_signed_re_pos A hpos_Φ hcross⟩

/-- **Tasaki Problem 2.5.d, p. 40, eq. (2.5.7), at the printed Hamiltonian (2.5.1), p. 37.**

The instance of the theorem above at the model exactly as printed at the head of §2.5,
`Ĥ = Σ_{{x,y} ∈ ℬ} Ŝ_x · Ŝ_y` — unit weight on every bond of a connected bipartite graph with
balanced sublattices.  In the ordered-pair convention of `heisenbergHamiltonianS` that
unit-weight bond sum is the coupling `couplingOf G (1/2)`, the identification being
`heisenbergHamiltonianS_couplingOf_half_eq_bondSum`.  Every hypothesis the general statement
places on the coupling is discharged here from `couplingOf` itself, so the printed model assumes
only connectedness, bipartiteness, balance and `S ≥ 1/2`. -/
theorem tasaki_problem_2_5_d_couplingOf_half
    (A : V → Bool) (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N) :
    ∃ μ : ℝ,
      μ = hermitianMinEigenvalue (heisenbergHamiltonianS_isHermitian_of_real
          (Λ := V) (couplingOf_real G (J := (1 : ℂ) / 2) (by norm_num)) N) ∧
      finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (heisenbergHamiltonianS (couplingOf G ((1 : ℂ) / 2)) N)) (μ : ℂ)) ≤ 1 ∧
      (∃ Φ : (V → Fin (N + 1)) → ℂ, Φ ≠ 0 ∧ star Φ ⬝ᵥ Φ = 1 ∧
        (heisenbergHamiltonianS (couplingOf G ((1 : ℂ) / 2)) N).mulVec Φ = (μ : ℂ) • Φ) ∧
      (∀ {Φ : (V → Fin (N + 1)) → ℂ}, Φ ≠ 0 → star Φ ⬝ᵥ Φ = 1 →
        (heisenbergHamiltonianS (couplingOf G ((1 : ℂ) / 2)) N).mulVec Φ = (μ : ℂ) • Φ →
        ∀ x y : V, x ≠ y →
          (A x = A y → 0 < (twoSpinCorrelationS x y Φ).re) ∧
          (A x ≠ A y → (twoSpinCorrelationS x y Φ).re < 0)) := by
  have hJ_real : ∀ x y : V, (couplingOf G ((1 : ℂ) / 2) x y).im = 0 := by
    intro x y
    unfold couplingOf
    by_cases h : G.Adj x y
    · rw [if_pos h]; norm_num
    · rw [if_neg h, Complex.zero_im]
  have hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (couplingOf G ((1 : ℂ) / 2) x y).re := by
    intro x y h
    unfold couplingOf
    rw [if_pos h]
    norm_num
  have hJ_off : ∀ x y : V, ¬ G.Adj x y → couplingOf G ((1 : ℂ) / 2) x y = 0 := by
    intro x y h
    unfold couplingOf
    exact if_neg h
  have hJ_nn : ∀ x y : V, 0 ≤ (couplingOf G ((1 : ℂ) / 2) x y).re := by
    intro x y
    by_cases h : G.Adj x y
    · exact (hJ_pos_G x y h).le
    · rw [hJ_off x y h, Complex.zero_re]
  have hJ_bipartite : ∀ x y : V, A x = A y → couplingOf G ((1 : ℂ) / 2) x y = 0 := by
    intro x y hxy
    unfold couplingOf
    exact if_neg fun hadj => hGbip x y hadj hxy
  exact tasaki_problem_2_5_d_twoSpin_correlation_sign A G N hGconn hGbip h_card_eq hN
    hJ_real (couplingOf_real G (by norm_num)) (couplingOf_symm G ((1 : ℂ) / 2)) hJ_nn
    hJ_bipartite hJ_pos_G hJ_off

end LatticeSystem.Quantum
