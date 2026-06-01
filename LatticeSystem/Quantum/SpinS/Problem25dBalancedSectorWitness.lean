import LatticeSystem.Quantum.SpinS.MagSumStepDown
import LatticeSystem.Quantum.SpinS.Problem25dSectorSupportedWrapper
import LatticeSystem.Quantum.SpinS.SublatticeCasimirNeel

/-!
# Tasaki Problem 2.5.d: balanced-sector ladder witness

This module removes the explicit strict ladder-entry hypothesis from the
sector-supported Problem 2.5.d wrapper at the balanced sector
`M0 = |A| * N`.  For every cross-sublattice pair `A x ≠ A y`, the complement
Néel configuration gives a two-configuration witness inside this sector.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, Problem 2.5.d, p. 40, and solution pp. 498--499, equations
(S.22)--(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Strict signed ladder entries from raise/lower data -/

/-- A cross-sublattice `S_x^+ S_y^-` matrix entry is strictly positive after
the bipartite-gauge / Marshall signing whenever the two configurations agree
away from `{x, y}` and satisfy the raise/lower equalities
`σ x + 1 = τ x` and `τ y + 1 = σ y`. -/
theorem twoSpinPlusMinus_ladder_signed_entry_re_pos_of_off_two_site_raise_lower
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y)
    {σ τ : V → Fin (N + 1)}
    (hagree : ∀ k, k ≠ x → k ≠ y → σ k = τ k)
    (hxraise : (σ x).val + 1 = (τ x).val)
    (hylower : (τ y).val + 1 = (σ y).val) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      marshallSignS A σ *
      ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
      marshallSignS A τ).re := by
  classical
  let O : ℂ :=
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ)
  have hgauge : bipartiteGaugeSign A x * bipartiteGaugeSign A y = -1 :=
    bipartiteGaugeSign_mul_eq_neg_one_of_ne A hAxy
  have hxodd : Odd ((σ x).val + (τ x).val) := by
    use (σ x).val
    omega
  have hyodd : Odd ((σ y).val + (τ y).val) := by
    use (τ y).val
    omega
  have hmarshall : marshallSignS A σ * marshallSignS A τ = -1 := by
    cases hAx : A x <;> cases hAy : A y
    · exact (hAxy (by rw [hAx, hAy])).elim
    · exact marshallSignS_mul_of_agree_off_two_site_bipartite_y
        A hxy hAx hAy hagree hyodd
    · exact marshallSignS_mul_of_agree_off_two_site_bipartite_x
        A hxy hAx hAy hagree hxodd
    · exact (hAxy (by rw [hAx, hAy])).elim
  have hO_pos : 0 < O.re := by
    unfold O
    rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
      hxy hagree]
    rw [Complex.mul_re, spinSOpPlus_apply_im_zero, spinSOpMinus_apply_im_zero]
    simp only [mul_zero, sub_zero]
    exact mul_pos (spinSOpPlus_apply_re_pos_of_raise N hxraise)
      (spinSOpMinus_apply_re_pos_of_lower N hylower)
  change 0 < (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      marshallSignS A σ * O * marshallSignS A τ).re)
  calc
    (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ * O * marshallSignS A τ).re)
        = (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
            (marshallSignS A σ * marshallSignS A τ)) * O).re := by ring_nf
    _ = O.re := by rw [hgauge, hmarshall]; norm_num
    _ > 0 := hO_pos

/-! ## Balanced-sector witness -/

/-- For `N ≥ 1`, every cross-sublattice pair has a strictly positive
signed `S_x^+ S_y^-` matrix entry whose source and target configurations both
belong to the balanced sector `M0 = |A| * N`. -/
theorem exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_bipartite_ne_balanced_sector
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N) :
    ∃ σ τ : magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N),
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re := by
  classical
  let η : V → Fin (N + 1) := neelConfigOfS (fun z : V => ! A z) N
  let almostLast : Fin (N + 1) := ⟨N - 1, by omega⟩
  let oneS : Fin (N + 1) := ⟨1, by omega⟩
  have hη_sum :
      magSumS η = (Finset.univ.filter (fun z : V => A z = true)).card * N := by
    simpa [η] using magSumS_neelConfigOfS_complement A N
  cases hAx : A x <;> cases hAy : A y
  · exact (hAxy (by rw [hAx, hAy])).elim
  · let σ0 : V → Fin (N + 1) := η
    let τ0 : V → Fin (N + 1) := configUpdateTwo η x y oneS almostLast
    have hτ_sum :
        magSumS τ0 = (Finset.univ.filter (fun z : V => A z = true)).card * N := by
      change magSumS (configUpdateTwo η x y oneS almostLast) =
        (Finset.univ.filter (fun z : V => A z = true)).card * N
      have hupdate := magSumS_configUpdateTwo_eq η hxy oneS almostLast
      have hxη : (η x).val = 0 := by
        simp [η, neelConfigOfS, hAx]
      have hyη : (η y).val = N := by
        simp [η, neelConfigOfS, hAy]
      have hone : oneS.val = 1 := rfl
      have halmost : almostLast.val = N - 1 := rfl
      rw [hη_sum, hxη, hyη, hone, halmost] at hupdate
      omega
    refine ⟨⟨σ0, by simpa [σ0] using hη_sum⟩, ⟨τ0, hτ_sum⟩, ?_⟩
    have hagree : ∀ k, k ≠ x → k ≠ y → σ0 k = τ0 k := by
      intro k hkx hky
      simp [σ0, τ0, configUpdateTwo, hkx, hky]
    have hxraise : (σ0 x).val + 1 = (τ0 x).val := by
      change (η x).val + 1 = (configUpdateTwo η x y oneS almostLast x).val
      rw [configUpdateTwo_at_a]
      simp [η, neelConfigOfS, hAx, oneS]
    have hylower : (τ0 y).val + 1 = (σ0 y).val := by
      change (configUpdateTwo η x y oneS almostLast y).val + 1 = (η y).val
      rw [configUpdateTwo_at_b _ hxy]
      simp [η, neelConfigOfS, hAy, almostLast]
      omega
    exact twoSpinPlusMinus_ladder_signed_entry_re_pos_of_off_two_site_raise_lower
      A hxy hAxy hagree hxraise hylower
  · let σ0 : V → Fin (N + 1) := configUpdateTwo η x y almostLast oneS
    let τ0 : V → Fin (N + 1) := η
    have hσ_sum :
        magSumS σ0 = (Finset.univ.filter (fun z : V => A z = true)).card * N := by
      change magSumS (configUpdateTwo η x y almostLast oneS) =
        (Finset.univ.filter (fun z : V => A z = true)).card * N
      have hupdate := magSumS_configUpdateTwo_eq η hxy almostLast oneS
      have hxη : (η x).val = N := by
        simp [η, neelConfigOfS, hAx]
      have hyη : (η y).val = 0 := by
        simp [η, neelConfigOfS, hAy]
      have hone : oneS.val = 1 := rfl
      have halmost : almostLast.val = N - 1 := rfl
      rw [hη_sum, hxη, hyη, hone, halmost] at hupdate
      omega
    refine ⟨⟨σ0, hσ_sum⟩, ⟨τ0, by simpa [τ0] using hη_sum⟩, ?_⟩
    have hagree : ∀ k, k ≠ x → k ≠ y → σ0 k = τ0 k := by
      intro k hkx hky
      simp [σ0, τ0, configUpdateTwo, hkx, hky]
    have hxraise : (σ0 x).val + 1 = (τ0 x).val := by
      change (configUpdateTwo η x y almostLast oneS x).val + 1 = (η x).val
      rw [configUpdateTwo_at_a]
      simp [η, neelConfigOfS, hAx, almostLast]
      omega
    have hylower : (τ0 y).val + 1 = (σ0 y).val := by
      change (η y).val + 1 = (configUpdateTwo η x y almostLast oneS y).val
      rw [configUpdateTwo_at_b _ hxy]
      simp [η, neelConfigOfS, hAy, oneS]
    exact twoSpinPlusMinus_ladder_signed_entry_re_pos_of_off_two_site_raise_lower
      A hxy hAxy hagree hxraise hylower
  · exact (hAxy (by rw [hAx, hAy])).elim

/-! ## Balanced-sector dot-product wrapper -/

/-- Balanced-sector Problem 2.5.d ground-state phase wrapper: at
`M0 = |A| * N`, the strict ladder-entry input is supplied by the explicit
balanced-sector witness, so the sector-supported eigenspace-phase wrapper no
longer needs `hentry_pos` as an assumption. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_balanced_sector_cross_eigenphase
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hAxy : A x ≠ A y) (hN : 1 ≤ N)
    (J : V → V → ℂ) (μ : ℂ)
    (c : magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) → ℝ)
    (hc_pos : ∀ σ, 0 < c σ)
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne :
      (magSectorEmbedding (fun σ :
          magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
        marshallSignS A σ.1 * (c σ : ℂ))) ≠ 0)
    (hΦnorm :
      dotProduct
        (star (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (c σ : ℂ))))
        (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (c σ : ℂ))) = 1)
    (hΦeig :
      (heisenbergHamiltonianS J N).mulVec
          (magSectorEmbedding (fun σ :
              magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
            marshallSignS A σ.1 * (c σ : ℂ))) =
        μ • (magSectorEmbedding (fun σ :
              magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
            marshallSignS A σ.1 * (c σ : ℂ)))) :
    0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      twoSpinCorrelationS x y
        (magSectorEmbedding (fun σ :
            magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
          marshallSignS A σ.1 * (c σ : ℂ)))).re := by
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_sector_cross_eigenphase
    A hxy hAxy J μ c hc_pos
    (exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_bipartite_ne_balanced_sector
      A hxy hAxy hN)
    huniq hΦ_ne hΦnorm hΦeig

end LatticeSystem.Quantum
