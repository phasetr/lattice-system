import LatticeSystem.Quantum.SpinS.Problem25dBalancedPFEndpointCore

/-!
# Tasaki Problem 2.5.d: the correlation sign at an arbitrary pair of distinct sites

Tasaki's solution to Problem 2.5.d (p. 498, equations (S.22)–(S.23)) is uniform in the pair
`{x, y}`: it never splits into a same-sublattice and a cross-sublattice case.  The gauge factor
`(−1)^x (−1)^y` of (S.23) is `+1` on a same-sublattice pair and `−1` on a crossing pair, and the
right-hand side of (S.23) is positive in both cases; the two branches of (2.5.7) are exactly the
two values of that one prefactor.

The existing chain (`Problem25dLadderEntrySign`, `Problem25dLadderAdjointEquality`,
`Problem25dLongitudinalComponentEquality`, `Problem25dBalancedSectorWitnessCore`) carries the
crossing case only, so it reaches just the `< 0` branch of (2.5.7).  This module carries the
same steps with no hypothesis relating `A x` to `A y`, which is what both branches need:

* the gauge factor is real, and it cancels the Marshall sign product on every ladder-connected
  pair of configurations — in all four sublattice cases by the same computation;
* hence the signed `Ŝ_x^+ Ŝ_y^-` matrix entries are non-negative at every distinct pair;
* the two component equalities behind (S.22) need only that the prefactor is real;
* the strict sector-local witness of (S.23) exists at every distinct pair.  For a
  same-sublattice pair the complement Néel configuration admits neither the raise at `x` nor
  the lower at `y`, so the witness first moves one unit through a third site of the opposite
  class.  That site exists because both classes are non-empty, which under Theorem 2.2's own
  hypotheses follows from `|A| = |B|` together with connectedness; it is **not** an extra
  hypothesis on Problem 2.5.d.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
Problem 2.5.d, p. 40, equation (2.5.7); solution p. 498, equations (S.22)–(S.23).
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## The bipartite gauge factor is real -/

omit [Fintype V] [DecidableEq V] in
/-- The bipartite gauge factor `(−1)^x (−1)^y` of Tasaki's (S.23), p. 498, is real, each of its
two factors being `±1`.  Reality is the only property of the prefactor that the component
equalities behind (S.22) use, and it holds on same-sublattice and crossing pairs alike. -/
theorem bipartiteGaugeSign_mul_im_zero (A : V → Bool) (x y : V) :
    (bipartiteGaugeSign A x * bipartiteGaugeSign A y).im = 0 := by
  unfold bipartiteGaugeSign
  by_cases hx : A x <;> by_cases hy : A y <;> simp [hx, hy]

/-! ## Gauge and Marshall signs cancel on every ladder-connected pair -/

omit [DecidableEq V] in
/-- **Uniform gauge–Marshall cancellation.**  If `σ` and `τ` agree away from `{x, y}` and the
occupation sums at `x` and at `y` are both odd — exactly what a non-zero `Ŝ_x^+ Ŝ_y^-` matrix
entry forces — then the bipartite gauge factor cancels the Marshall sign product, whatever the
sublattice classes of `x` and `y` are.

The cancellation happens site by site: on an `A`-marked site the gauge contributes `+1` and the
Marshall factor is `(−1)^odd = −1`, while off `A` the gauge contributes `−1` and the Marshall
factor is `1`.  Either way that site contributes `−1`, so the two sites together give
`(−1)(−1) = 1`.  This is the reason Tasaki's (S.23) needs no case split. -/
theorem bipartiteGaugeSign_mul_marshallSignS_mul_eq_one_of_agree_off_two_site
    (A : V → Bool) {x y : V} (hxy : x ≠ y) {σ τ : V → Fin (N + 1)}
    (hagree : ∀ k, k ≠ x → k ≠ y → σ k = τ k)
    (hxodd : Odd ((σ x).val + (τ x).val))
    (hyodd : Odd ((σ y).val + (τ y).val)) :
    (bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        (marshallSignS A σ * marshallSignS A τ) = 1 := by
  rw [marshallSignS_mul_of_agree_off_two_site A hxy hagree]
  unfold bipartiteGaugeSign
  by_cases hx : A x <;> by_cases hy : A y <;>
    simp [hx, hy, Odd.neg_one_pow hxodd, Odd.neg_one_pow hyodd]

/-! ## Signed ladder matrix entries at an arbitrary distinct pair -/

/-- The bipartite-gauge / Marshall-signed `Ŝ_x^+ Ŝ_y^-` matrix entry has non-negative real part
at **every** pair of distinct sites, with no hypothesis relating `A x` to `A y`.  A non-zero
entry forces `σ` and `τ` to agree off `{x, y}` with one raise at `x` and one lower at `y`; the
gauge and Marshall signs then cancel and the bare entry that remains is non-negative.  This is
the entry input to Tasaki's (S.23), p. 498, in the form both branches of (2.5.7) need. -/
theorem twoSpinPlusMinus_ladder_signed_entry_re_nonneg_of_ne
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (σ τ : V → Fin (N + 1)) :
    0 ≤ ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      marshallSignS A σ *
      ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ) *
      marshallSignS A τ).re := by
  classical
  let O : ℂ :=
    ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N) σ τ)
  have hO_nonneg : 0 ≤ O.re :=
    onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_re_nonneg hxy σ τ
  change 0 ≤ (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
      marshallSignS A σ * O * marshallSignS A τ).re)
  by_cases hagree : ∀ k, k ≠ x → k ≠ y → σ k = τ k
  · by_cases hxraise : (σ x).val + 1 = (τ x).val
    · by_cases hylower : (τ y).val + 1 = (σ y).val
      · have hxodd : Odd ((σ x).val + (τ x).val) := ⟨(σ x).val, by omega⟩
        have hyodd : Odd ((σ y).val + (τ y).val) := ⟨(τ y).val, by omega⟩
        have hcancel :=
          bipartiteGaugeSign_mul_marshallSignS_mul_eq_one_of_agree_off_two_site
            A hxy hagree hxodd hyodd
        calc
          ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
              marshallSignS A σ * O * marshallSignS A τ).re
              = (((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
                  (marshallSignS A σ * marshallSignS A τ)) * O).re := by ring_nf
          _ = O.re := by rw [hcancel, one_mul]
          _ ≥ 0 := hO_nonneg
      · have hzero : O = 0 := by
          unfold O
          rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
            hxy hagree, spinSOpMinus_apply_other N hylower]
          ring
        rw [hzero]
        simp
    · have hzero : O = 0 := by
        unfold O
        rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree
          hxy hagree, spinSOpPlus_apply_other N hxraise]
        ring
      rw [hzero]
      simp
  · have hzero : O = 0 := by
      unfold O
      exact onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_eq_zero_of_off_two_site_diff
        hxy hagree
    rw [hzero]
    simp

/-- The signed `Ŝ_x^+ Ŝ_y^-` matrix entry is **strictly** positive at every pair of distinct
sites whenever `σ` and `τ` agree off `{x, y}` and differ by one raise at `x` and one lower at
`y`.  The strict witness required by Tasaki's (S.23), p. 498, at the level of a single matrix
entry, with no hypothesis relating `A x` to `A y`. -/
theorem twoSpinPlusMinus_ladder_signed_entry_re_pos_of_raise_lower_of_ne
    (A : V → Bool) {x y : V} (hxy : x ≠ y) {σ τ : V → Fin (N + 1)}
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
  have hxodd : Odd ((σ x).val + (τ x).val) := ⟨(σ x).val, by omega⟩
  have hyodd : Odd ((σ y).val + (τ y).val) := ⟨(τ y).val, by omega⟩
  have hcancel :=
    bipartiteGaugeSign_mul_marshallSignS_mul_eq_one_of_agree_off_two_site
      A hxy hagree hxodd hyodd
  have hO_pos : 0 < O.re := by
    unfold O
    rw [onSiteS_spinSOpPlus_mul_onSiteS_spinSOpMinus_apply_of_off_two_site_agree hxy hagree,
      Complex.mul_re, spinSOpPlus_apply_im_zero, spinSOpMinus_apply_im_zero]
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
    _ = O.re := by rw [hcancel, one_mul]
    _ > 0 := hO_pos

/-! ## The strict sector-local witness at an arbitrary distinct pair -/

/-- **Witness from a sector configuration that has room to move.**  If `σ0` lies in the
magnetization sector `M`, can be raised at `x` and lowered at `y`, then moving one unit from
`y` to `x` stays inside `M` (`magSumS_configUpdateTwo_eq` preserves the sum because the two
updated values preserve theirs), and the resulting pair realises a strictly positive signed
ladder entry.  The four sublattice cases of the theorem below differ only in how they produce
such a `σ0`. -/
private theorem exists_ladder_signed_entry_re_pos_of_sector_config
    (A : V → Bool) {x y : V} (hxy : x ≠ y) {M : ℕ}
    {σ0 : V → Fin (N + 1)} (hσ0 : magSumS σ0 = M)
    (hxroom : (σ0 x).val + 1 ≤ N) (hyroom : 1 ≤ (σ0 y).val) :
    ∃ σ τ : magConfigS V N M,
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re := by
  classical
  let vx : Fin (N + 1) := ⟨(σ0 x).val + 1, by omega⟩
  let vy : Fin (N + 1) := ⟨(σ0 y).val - 1, by have := (σ0 y).isLt; omega⟩
  have hτ0_sum : magSumS (configUpdateTwo σ0 x y vx vy) = M := by
    have hupd := magSumS_configUpdateTwo_eq σ0 hxy vx vy
    have hvx : vx.val = (σ0 x).val + 1 := rfl
    have hvy : vy.val = (σ0 y).val - 1 := rfl
    rw [hσ0, hvx, hvy] at hupd
    omega
  refine ⟨⟨σ0, hσ0⟩, ⟨configUpdateTwo σ0 x y vx vy, hτ0_sum⟩, ?_⟩
  refine twoSpinPlusMinus_ladder_signed_entry_re_pos_of_raise_lower_of_ne A hxy ?_ ?_ ?_
  · intro k hkx hky
    exact (configUpdateTwo_agree σ0 x y vx vy k hkx hky).symm
  · change (σ0 x).val + 1 = (configUpdateTwo σ0 x y vx vy x).val
    rw [configUpdateTwo_at_a]
  · change (configUpdateTwo σ0 x y vx vy y).val + 1 = (σ0 y).val
    rw [configUpdateTwo_at_b _ hxy]
    change (σ0 y).val - 1 + 1 = (σ0 y).val
    omega

/-- **Strict sector-local witness at an arbitrary distinct pair.**  For `N ≥ 1` and any two
distinct sites, the balanced sector `M0 = |A| · N` contains a pair of configurations with a
strictly positive signed `Ŝ_x^+ Ŝ_y^-` entry — the strict input to Tasaki's (S.23), p. 498.

The complement Néel configuration `η` carries `N` on the `A`-marked sites and `0` off them.  On
the crossing pair `A x = false`, `A y = true` it already has room, and on the opposite crossing
pair one move inside `{x, y}` creates it.  On a **same-sublattice** pair it has none: if both
sites are `A`-marked then both sit at `N` and neither can be raised, and if neither is marked
then both sit at `0` and neither can be lowered.  Moving one unit between `x` (respectively `y`)
and a third site `w` of the *opposite* class repairs this while staying in `M0`, because the two
updated occupations preserve their sum.  The hypotheses `hA_ne` / `hB_ne` supply that third
site; under Theorem 2.2's own hypotheses they follow from `|A| = |B|` and connectedness. -/
theorem exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_ne_balanced_sector
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hN : 1 ≤ N)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false) :
    ∃ σ τ : magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N),
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        marshallSignS A σ.1 *
        ((onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) : ManyBodyOpS V N)
          σ.1 τ.1) *
        marshallSignS A τ.1).re := by
  classical
  set M0 := (Finset.univ.filter (fun z : V => A z = true)).card * N with hM0def
  let η : V → Fin (N + 1) := neelConfigOfS (fun z : V => ! A z) N
  have hη_sum : magSumS η = M0 := by
    simpa [η, hM0def] using magSumS_neelConfigOfS_complement A N
  have hηT : ∀ z : V, A z = true → (η z).val = N := by
    intro z hz
    simp [η, neelConfigOfS, hz]
  have hηF : ∀ z : V, A z = false → (η z).val = 0 := by
    intro z hz
    simp [η, neelConfigOfS, hz]
  cases hAx : A x <;> cases hAy : A y
  · -- `A x = false`, `A y = false`: both sit at `0`; borrow one unit from an `A`-marked site.
    obtain ⟨w, hw⟩ := hA_ne
    have hyw : y ≠ w := by
      intro h
      rw [h, hw] at hAy
      exact Bool.noConfusion hAy
    have hxw : x ≠ w := by
      intro h
      rw [h, hw] at hAx
      exact Bool.noConfusion hAx
    let v1 : Fin (N + 1) := ⟨1, by omega⟩
    let vN1 : Fin (N + 1) := ⟨N - 1, by omega⟩
    have hv1 : v1.val = 1 := rfl
    have hvN1 : vN1.val = N - 1 := rfl
    have hsum : magSumS (configUpdateTwo η y w v1 vN1) = M0 := by
      have hupd := magSumS_configUpdateTwo_eq η hyw v1 vN1
      rw [hη_sum, hηF y hAy, hηT w hw, hv1, hvN1] at hupd
      omega
    have hxv : (configUpdateTwo η y w v1 vN1 x).val = 0 := by
      rw [configUpdateTwo_agree η y w v1 vN1 x hxy hxw, hηF x hAx]
    have hyv : (configUpdateTwo η y w v1 vN1 y).val = 1 := by
      rw [configUpdateTwo_at_a, hv1]
    exact exists_ladder_signed_entry_re_pos_of_sector_config A hxy hsum
      (by omega) (by omega)
  · -- `A x = false`, `A y = true`: the complement Néel configuration already has room.
    have hxv : (η x).val = 0 := hηF x hAx
    have hyv : (η y).val = N := hηT y hAy
    exact exists_ladder_signed_entry_re_pos_of_sector_config A hxy hη_sum
      (by omega) (by omega)
  · -- `A x = true`, `A y = false`: one move inside `{x, y}` creates the room.
    let vN1 : Fin (N + 1) := ⟨N - 1, by omega⟩
    let v1 : Fin (N + 1) := ⟨1, by omega⟩
    have hvN1 : vN1.val = N - 1 := rfl
    have hv1 : v1.val = 1 := rfl
    have hsum : magSumS (configUpdateTwo η x y vN1 v1) = M0 := by
      have hupd := magSumS_configUpdateTwo_eq η hxy vN1 v1
      rw [hη_sum, hηT x hAx, hηF y hAy, hvN1, hv1] at hupd
      omega
    have hxv : (configUpdateTwo η x y vN1 v1 x).val = N - 1 := by
      rw [configUpdateTwo_at_a, hvN1]
    have hyv : (configUpdateTwo η x y vN1 v1 y).val = 1 := by
      rw [configUpdateTwo_at_b _ hxy, hv1]
    exact exists_ladder_signed_entry_re_pos_of_sector_config A hxy hsum
      (by omega) (by omega)
  · -- `A x = true`, `A y = true`: both sit at `N`; lend one unit to an unmarked site.
    obtain ⟨w, hw⟩ := hB_ne
    have hxw : x ≠ w := by
      intro h
      rw [h, hw] at hAx
      exact Bool.noConfusion hAx
    have hyw : y ≠ w := by
      intro h
      rw [h, hw] at hAy
      exact Bool.noConfusion hAy
    let vN1 : Fin (N + 1) := ⟨N - 1, by omega⟩
    let v1 : Fin (N + 1) := ⟨1, by omega⟩
    have hvN1 : vN1.val = N - 1 := rfl
    have hv1 : v1.val = 1 := rfl
    have hsum : magSumS (configUpdateTwo η x w vN1 v1) = M0 := by
      have hupd := magSumS_configUpdateTwo_eq η hxw vN1 v1
      rw [hη_sum, hηT x hAx, hηF w hw, hvN1, hv1] at hupd
      omega
    have hxv : (configUpdateTwo η x w vN1 v1 x).val = N - 1 := by
      rw [configUpdateTwo_at_a, hvN1]
    have hyv : (configUpdateTwo η x w vN1 v1 y).val = N := by
      rw [configUpdateTwo_agree η x w vN1 v1 y hxy.symm hyw, hηT y hAy]
    exact exists_ladder_signed_entry_re_pos_of_sector_config A hxy hsum
      (by omega) (by omega)

/-! ## The component equalities of (S.22) need only a real prefactor -/

/-- Tasaki's first component equality behind (S.22), p. 498, at an arbitrary **real** prefactor.
On distinct sites `Ŝ_x^- Ŝ_y^+` is the adjoint of `Ŝ_x^+ Ŝ_y^-`, so the two expectations are
complex conjugates, and a real prefactor gives them equal real parts.  The crossing-pair lemma
`bipartite_signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus` is the instance at the gauge
value `−1`; the same-sublattice branch of (2.5.7) needs the value `+1`, and the bipartite gauge
factor is real in both cases (`bipartiteGaugeSign_mul_im_zero`). -/
theorem signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus_of_real
    {g : ℂ} (hg : g.im = 0) {x y : V} (hxy : x ≠ y)
    (Φ : (V → Fin (N + 1)) → ℂ) :
    (g * twoSpinMinusPlusCorrelationS x y Φ).re =
      (g * twoSpinPlusMinusCorrelationS x y Φ).re := by
  rw [twoSpinMinusPlusCorrelationS_eq_star_twoSpinPlusMinusCorrelationS hxy]
  simp [Complex.mul_re, hg]

/-- Tasaki's second component equality behind (S.22), p. 498, at an arbitrary **real**
prefactor: under axis-swap and z-axis rotation phase invariance the signed longitudinal real
part is half the signed `Ŝ_x^+ Ŝ_y^-` real part.  This is the proof of the crossing-pair lemma
`bipartite_signed_twoSpinZZCorrelationS_re_eq_half_plusMinus_of_axis_phases`, whose only use of
the sublattice hypothesis is to know that the prefactor is real. -/
theorem signed_twoSpinZZCorrelationS_re_eq_half_plusMinus_of_real_of_axis_phases
    {g : ℂ} (hg : g.im = 0) {x y : V} (hxy : x ≠ y)
    (Φ : (V → Fin (N + 1)) → ℂ) (cswap crot : ℂ)
    (hΦswap : ((axisSwapUnitarySSpinS N).tensorInv V).mulVec Φ = cswap • Φ)
    (hcswap : star cswap * cswap = 1)
    (hΦrot :
      (manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2))).mulVec Φ = crot • Φ)
    (hcrot : star crot * crot = 1) :
    (g * twoSpinZZCorrelationS x y Φ).re =
      (1 / 2 : ℝ) * (g * twoSpinPlusMinusCorrelationS x y Φ).re := by
  let C1 : ℂ := twoSpinProductCorrelationS x y (spinSOp1 N) Φ
  let C2 : ℂ := twoSpinProductCorrelationS x y (spinSOp2 N) Φ
  let C3 : ℂ := twoSpinProductCorrelationS x y (spinSOp3 N) Φ
  let P : ℂ := twoSpinPlusMinusCorrelationS x y Φ
  let M : ℂ := twoSpinMinusPlusCorrelationS x y Φ
  have h32 : C3 = C2 := by
    simpa [C2, C3] using
      (twoSpinProductCorrelationS_axis3_eq_axis2_of_axisSwap_phase
        (x := x) (y := y) (Φ := Φ) (c := cswap) hΦswap hcswap)
  have h12 : C1 = C2 := by
    simpa [C1, C2] using
      (twoSpinProductCorrelationS_axis1_eq_axis2_of_zAxisRot_phase
        (x := x) (y := y) (Φ := Φ) (c := crot) hΦrot hcrot)
  have htrans : C1 + C2 = (1 / 2 : ℂ) * (P + M) := by
    simpa [C1, C2, P, M] using
      (twoSpinProductCorrelationS_axis1_add_axis2_eq_ladder (N := N) x y Φ)
  have hsum : C2 + C2 = (1 / 2 : ℂ) * (P + M) := by
    simpa [h12] using htrans
  have hsum_re :
      (2 : ℝ) * (g * C2).re = (1 / 2 : ℝ) * ((g * P).re + (g * M).re) := by
    have h := congrArg (fun z : ℂ => (g * z).re) hsum
    calc
      (2 : ℝ) * (g * C2).re = (g * (C2 + C2)).re := by
        simp [Complex.mul_re]
        ring
      _ = (g * ((1 / 2 : ℂ) * (P + M))).re := h
      _ = (1 / 2 : ℝ) * ((g * P).re + (g * M).re) := by
        simp [Complex.mul_re]
        ring
  have hmp : (g * M).re = (g * P).re := by
    simpa [M, P] using
      (signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus_of_real hg hxy Φ)
  have htarget : (g * C2).re = (1 / 2 : ℝ) * (g * P).re := by nlinarith
  change (g * twoSpinZZCorrelationS x y Φ).re = (1 / 2 : ℝ) * (g * P).re
  rw [← twoSpinProductCorrelationS_spinSOp3_eq_twoSpinZZCorrelationS]
  change (g * C3).re = (1 / 2 : ℝ) * (g * P).re
  rw [h32]
  exact htarget

/-! ## Signed dot-product positivity at an arbitrary distinct pair -/

/-- **Signed two-spin positivity at every distinct pair**, for the sector-supported
Marshall-positive ground vector: the assembly of (S.22)–(S.23) with no hypothesis relating
`A x` to `A y`.  The signed ladder correlation is positive by the entry non-negativity and the
strict sector witness above; the two component equalities transfer that positivity to the
dot-product correlation, using only that the bipartite gauge factor is real.

The vector is not assumed normalised, so the axis-swap and z-axis rotation phases are taken
from the non-normalised eigenspace phase bridge. -/
theorem twoSpinCorrelationS_bipartite_signed_re_pos_of_marshall_balanced_sector_pair
    (A : V → Bool) {x y : V} (hxy : x ≠ y) (hN : 1 ≤ N)
    (hA_ne : ∃ a, A a = true) (hB_ne : ∃ b, A b = false)
    (J : V → V → ℂ) (μ : ℂ)
    (c : magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) → ℝ)
    (hc_pos : ∀ σ, 0 < c σ)
    (huniq : finrank ℂ ↥(End.eigenspace
      (Matrix.toLin' (heisenbergHamiltonianS J N)) μ) ≤ 1)
    (hΦ_ne :
      (magSectorEmbedding (fun σ :
          magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
        marshallSignS A σ.1 * (c σ : ℂ))) ≠ 0)
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
  classical
  set Φ : (V → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ :
        magConfigS V N ((Finset.univ.filter (fun z : V => A z = true)).card * N) =>
      marshallSignS A σ.1 * (c σ : ℂ)) with hΦ_def
  obtain ⟨cswap, hswap, hcswap⟩ :=
    exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute_of_ne_zero
      (H := heisenbergHamiltonianS J N)
      (U := (axisSwapUnitarySSpinS N).tensorInv V)
      (μ := μ) huniq hΦ_ne hΦeig
      (heisenbergHamiltonianS_commute_axisSwapUnitarySSpinS_tensorInv
        (V := V) (N := N) J).eq
      (axisSwapUnitarySSpinS_tensorInv_conjTranspose_mul_self (V := V) (N := N))
  obtain ⟨crot, hrot, hcrot⟩ :=
    exists_phase_unit_of_finrank_eigenspace_le_one_of_unitary_commute_of_ne_zero
      (H := heisenbergHamiltonianS J N)
      (U := manyBodyTensorS (fun _ : V => spinSRot3 N (Real.pi / 2)))
      (μ := μ) huniq hΦ_ne hΦeig
      (heisenbergHamiltonianS_commute_manyBodySpinSRot3 (N := N) J (Real.pi / 2)).eq
      (manyBodySpinSRot3_conjTranspose_mul_self (V := V) (N := N) (Real.pi / 2))
  have hgauge_re : (bipartiteGaugeSign A x * bipartiteGaugeSign A y).im = 0 :=
    bipartiteGaugeSign_mul_im_zero A x y
  have hpm_pos :
      0 < ((bipartiteGaugeSign A x * bipartiteGaugeSign A y) *
        twoSpinPlusMinusCorrelationS x y Φ).re :=
    twoSpinPlusMinusCorrelationS_bipartite_signed_re_pos_of_marshall_sector_coefficients
      A x y c hc_pos
      (twoSpinPlusMinus_ladder_signed_entry_re_nonneg_of_ne A hxy)
      (exists_twoSpinPlusMinus_ladder_signed_entry_re_pos_of_ne_balanced_sector
        A hxy hN hA_ne hB_ne)
  exact twoSpinCorrelationS_bipartite_signed_re_pos_of_ladder_component_equalities
    A x y Φ hpm_pos
    (signed_twoSpinMinusPlusCorrelationS_re_eq_plusMinus_of_real hgauge_re hxy Φ)
    (signed_twoSpinZZCorrelationS_re_eq_half_plusMinus_of_real_of_axis_phases
      hgauge_re hxy Φ cswap crot hswap hcswap hrot hcrot)

end LatticeSystem.Quantum
