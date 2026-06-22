import LatticeSystem.Quantum.SpinS.FerrimagneticLROUniversalFinalCore

/-!
# Tasaki §4.1 Theorem 4.4 (Shen–Qiu–Tian): discharge of `shenQiuTian_ferrimagnetic_lro`

This file discharges the documented axiom `shenQiuTian_ferrimagnetic_lro`
(`FerrimagneticLRO.lean`) as a **theorem** with identical signature, for *every*
normalized ground state `Φ` of the connected bipartite antiferromagnetic spin-`S`
Heisenberg model (Issue #4604).

## Strategy (Tasaki chain (4.1.16), assembled over magnetization sectors)

The squared staggered order operator `Ô² = staggeredCasimirOpS A N` is `SU(2)`
invariant, hence commutes with `Ŝ_tot^{(3)}`, `Ŝ⁺_tot`, `Ŝ⁻_tot`.  Both the
expectation `⟨Φ, Ô² Φ⟩.re` and the squared norm `‖Φ‖²` split as finite sums over
magnetization sectors `M` of the diagonal quantities on the weight components
`Φ_M := magSectorEmbedding (magSectorRestriction Φ)`
(`weightPreserving_expectation_eq_sum_sector`, `star_dotProduct_self_eq_sum_sector`).

The per-sector bound is
`S_tot² ‖Φ_M‖² ≤ ⟨Φ_M, Ô² Φ_M⟩.re`,
proved (oriented `|¬A| ≤ |A|`) as follows.  Either `Φ_M = 0` (outside sectors,
forced by the strict outside-sector energy separation
`tasaki23_strict_hOutside_of_connected`), or `Φ_M` lies in an admissible sector
where the bare Heisenberg eigenspace is one-dimensional
(`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected`),
so `Φ_M` is proportional to the Marshall ground vector `w_M`.  The real Rayleigh
ratio `⟨w_M, Ô² w_M⟩.re / ‖w_M‖²` is `SU(2)`-ladder invariant
(`su2_expectationRatioRe_ladder_iterate_invariant`), so it agrees with the ratio
at a near-central admissible sector, where Tasaki's chain bound
`chain_bound_marshall_sector` gives `γ − m² ≥ S_tot²`.

Summing over sectors collapses `Σ_M ‖Φ_M‖² = ‖Φ‖² = 1` and rewrites `S_tot²` to
the coefficient `(N/2)² (|A| − |B|)²` (`tasaki23PredictedTotalSpin_sq_eq`).

The orientation `by_cases` reduces the general case to the oriented one, using the
sublattice-flip invariance `staggeredCasimirOpS_compl` and the symmetry of the
coefficient under `A ↦ ¬A`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4.1 Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78
(Shen, Qiu, Tian [59]); §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix Module

open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Ferrimagnetic LRO sum assembly (oriented).** Summing the per-sector bound
`staggeredCasimir_weightComponent_bound_oriented` over all magnetization sectors and
collapsing `Σ_M ‖Φ_M‖² = ‖Φ‖² = 1` (`star_dotProduct_self_eq_sum_sector`,
`weightPreserving_expectation_eq_sum_sector`) yields the normalized ferrimagnetic
bound for the oriented case `|¬A| ≤ |A|`. -/
private theorem ferrimagnetic_lro_oriented
    (A : Λ → Bool) (G : SimpleGraph Λ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {μ : ℝ} {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0) (hnorm : star Φ ⬝ᵥ Φ = 1)
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ)
    (hΦ_min : ∀ {μ' : ℝ} {Ψ' : (Λ → Fin (N + 1)) → ℂ}, Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' → μ ≤ μ') :
    tasaki23PredictedTotalSpin (V := Λ) A N ^ 2 ≤
      (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re := by
  classical
  haveI : Nonempty Λ := ⟨(Finset.card_pos.mp hcardA).choose⟩
  obtain ⟨c, hc_strict⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix A J N
  obtain ⟨c_toy, hc_strict_toy⟩ :=
    exists_strict_diag_bound_dressedHeisenbergSReMatrix A (bipartiteCoupling A) N
  set S := tasaki23PredictedTotalSpin (V := Λ) A N with hSdef
  -- Per-sector bound, summed.
  have hper : ∀ M ∈ Finset.range (Fintype.card Λ * N + 1),
      S ^ 2 * (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          magSectorEmbedding (magSectorRestriction (M := M) Φ)).re ≤
        (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          (staggeredCasimirOpS A N).mulVec
            (magSectorEmbedding (magSectorRestriction (M := M) Φ))).re := by
    intro M _
    exact staggeredCasimir_weightComponent_bound_oriented A G c c_toy horient hGconn hGbip
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G hc_strict hc_strict_toy hN hcardA hcardB
      hΦ_ne hΦ_eig (fun {μ'} {Ψ'} => hΦ_min) M
  -- Expectation sum decomposition.
  have hexp := weightPreserving_expectation_eq_sum_sector (staggeredCasimirOpS A N)
    (staggeredCasimirOpS_commute_op3' A N) Φ
  have hexpre : (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re =
      ∑ M ∈ Finset.range (Fintype.card Λ * N + 1),
        (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          (staggeredCasimirOpS A N).mulVec
            (magSectorEmbedding (magSectorRestriction (M := M) Φ))).re := by
    rw [hexp, Complex.re_sum]
  -- Norm sum decomposition: `Σ_M ‖Φ_M‖² = ‖Φ‖² = 1`.
  have hnormsum := star_dotProduct_self_eq_sum_sector Φ
  have hnorm_one : ∑ M ∈ Finset.range (Fintype.card Λ * N + 1),
      (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
        magSectorEmbedding (magSectorRestriction (M := M) Φ)).re = 1 := by
    rw [← hnormsum, hnorm, Complex.one_re]
  -- Sum the per-sector bounds.
  have hsum_le := Finset.sum_le_sum hper
  rw [← Finset.mul_sum, hnorm_one, mul_one] at hsum_le
  rw [hexpre]
  exact hsum_le

-- The `[DecidableRel G.Adj]` instance is part of the discharged axiom's signature but is
-- not used in the statement's type; the scoped linter disable keeps signature parity.
set_option linter.unusedDecidableInType false in
/-- **Tasaki Theorem 4.4 (Shen–Qiu–Tian ferrimagnetic long-range order).**  Discharge
of the documented axiom `shenQiuTian_ferrimagnetic_lro`: for the spin-`S` (`S = N/2`)
antiferromagnetic Heisenberg model on a connected bipartite lattice (modeled by a
connected bipartite graph `G`, real symmetric edge-supported strictly
antiferromagnetic coupling `J`, both sublattices nonempty), *any* normalized ground
state `Φ` obeys the ferrimagnetic bound (4.1.13)
`(N/2)² (|A| − |B|)² ≤ ⟨Φ, (Ô_Λ)² Φ⟩.re`.

The proof reduces (via the global sublattice-flip invariance `staggeredCasimirOpS_compl`
and coefficient symmetry) to the oriented assembly `ferrimagnetic_lro_oriented`, after
extracting the real ground energy `μ = E₀.re` (Hermitian eigenvalue) and handling the
trivial-spin case `N = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4.1 Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78. -/
theorem shenQiuTian_ferrimagnetic_lro (A : Λ → Bool) (J : Λ → Λ → ℂ) (N : ℕ)
    (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y) (hGconn : G.Connected)
    (hreal : ∀ x y, (J x y).im = 0) (hsym : ∀ x y, J x y = J y x)
    (hJoff : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJon : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hB : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = false)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hnorm : star Φ ⬝ᵥ Φ = 1)
    (hgs : ∃ E₀ : ℂ, (heisenbergHamiltonianS J N).mulVec Φ = E₀ • Φ ∧
      (∀ E : ℂ, ∀ Ψ : (Λ → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧ Φ ≠ 0) :
    ((N : ℝ) / 2) ^ 2 *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℤ) -
          ((Finset.univ.filter (fun x : Λ => A x = false)).card : ℤ) : ℝ) ^ 2 ≤
      (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re := by
  classical
  -- `N = 0`: both sides vanish.
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [staggeredCasimirOpS_N_zero A, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
    norm_num
  -- Real ground energy.
  obtain ⟨E₀, hE_eig, hE_min, hΦ_ne⟩ := hgs
  have hreal' : ∀ x y, star (J x y) = J x y := by
    intro x y; rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hreal x y
  have hE_im : E₀.im = 0 := by
    have hstar := isHermitian_eigenvalue_star_eq
      (heisenbergHamiltonianS_isHermitian_of_real hreal' N) hE_eig hΦ_ne
    rw [Complex.star_def, Complex.conj_eq_iff_im] at hstar; exact hstar
  set μ : ℝ := E₀.re with hμdef
  have hE_cast : E₀ = (μ : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hE_im]
  have hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ := by
    rw [← hE_cast]; exact hE_eig
  have hΦ_min : ∀ {μ' : ℝ} {Ψ' : (Λ → Fin (N + 1)) → ℂ}, Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' → μ ≤ μ' := by
    intro μ' Ψ' hΨ'_ne hΨ'
    have := hE_min (μ' : ℂ) Ψ' hΨ'_ne hΨ'
    rwa [Complex.ofReal_re] at this
  -- `J` is non-negative on the reals and vanishes within a sublattice.
  have hJ_nn : ∀ x y, 0 ≤ (J x y).re := by
    intro x y
    by_cases h : G.Adj x y
    · exact le_of_lt (hJon x y h)
    · rw [hJoff x y h, Complex.zero_re]
  have hJ_bipartite : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    apply hJoff
    intro hadj
    exact hGbip x y hadj hAxy
  -- `B`-cardinality in the `(! A x) = true` fiber form used by the oriented assembly.
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    rw [← card_filter_A_false_eq_card_filter_notA]; exact hB
  -- Orientation split.
  by_cases horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card
  · -- Oriented `|¬A| ≤ |A|`: apply the oriented assembly directly.
    have hbound := ferrimagnetic_lro_oriented A G horient hGconn hGbip hreal hreal' hsym
      hJ_nn hJ_bipartite hJon hN hA hcardB hΦ_ne hnorm hΦ_eig (fun {μ'} {Ψ'} => hΦ_min)
    rw [tasaki23PredictedTotalSpin_sq_eq A N] at hbound
    exact hbound
  · -- Reversed `|A| < |¬A|`: apply the oriented assembly to `A' := ¬A`.
    push Not at horient
    -- Cardinalities under the flip `A' = ¬A`.
    have hflip_notA : (Finset.univ.filter (fun x : Λ => (! (fun x => ! A x) x) = true)).card =
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
      congr 1
      apply Finset.filter_congr
      intro x _
      simp only [Bool.not_not]
    -- The flipped bipartite / cardinality hypotheses.
    have hGbip' : ∀ x y, G.Adj x y → (fun x => ! A x) x ≠ (fun x => ! A x) y := by
      intro x y hadj h
      simp only [Bool.not_inj_iff] at h
      exact hGbip x y hadj h
    have horient' :
        (Finset.univ.filter (fun x : Λ => (! (fun x => ! A x) x) = true)).card ≤
          (Finset.univ.filter (fun x : Λ => (fun x => ! A x) x = true)).card := by
      rw [hflip_notA]
      change (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card
      omega
    have hcardA' : 1 ≤ (Finset.univ.filter (fun x : Λ => (fun x => ! A x) x = true)).card :=
      hcardB
    have hcardB' : 1 ≤
        (Finset.univ.filter (fun x : Λ => (! (fun x => ! A x) x) = true)).card := by
      rw [hflip_notA]; exact hA
    have hJ_bipartite' : ∀ x y, (fun x => ! A x) x = (fun x => ! A x) y → J x y = 0 := by
      intro x y h
      apply hJ_bipartite
      simp only [Bool.not_inj_iff] at h
      exact h
    have hbound := ferrimagnetic_lro_oriented (fun x => ! A x) G horient' hGconn hGbip'
      hreal hreal' hsym hJ_nn hJ_bipartite' hJon hN hcardA' hcardB' hΦ_ne hnorm hΦ_eig
      (fun {μ'} {Ψ'} => hΦ_min)
    -- Transfer to `A`: `Ô²(¬A) = Ô²(A)` and the predicted spin is flip-symmetric.
    rw [staggeredCasimirOpS_compl A N] at hbound
    have hspin_eq : tasaki23PredictedTotalSpin (V := Λ) (fun x => ! A x) N =
        tasaki23PredictedTotalSpin (V := Λ) A N := by
      rw [tasaki23PredictedTotalSpin, tasaki23PredictedTotalSpin, hflip_notA]
      rw [mul_eq_mul_right_iff]
      left
      rw [abs_sub_comm]
    rw [hspin_eq, tasaki23PredictedTotalSpin_sq_eq A N] at hbound
    exact hbound

end LatticeSystem.Quantum
