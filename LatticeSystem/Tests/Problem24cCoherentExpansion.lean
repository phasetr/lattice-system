import LatticeSystem.Quantum.SpinS.SaturatedCoherentExpansion

/-!
# Test coverage for Tasaki Problem 2.4.c — the coherent-state / `Φ_M` expansion

TDD Red fixture for the capstone `tasaki_problem_2_4_c_coherent_expansion`
(Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 2.4.c, statement p. 34,
solution p. 497 eq. (S.19)): `Ξ_{θ,φ} = Σ_k c_k(θ, φ) • Φ_k` with
`c_k(θ, φ) = e^{-iφM(k)} · √(C(|V|N, k)) · cos(θ/2)^{|V|N-k} · sin(θ/2)^k`. The design's §0.1
corrects (S.19)'s printed `e^{-iMφ/2}` to `e^{-iMφ}` (confirmed against (S.18), (S.17), and the
already-proved `saturatedCoherentState_apply_phase`); every fixture below uses the corrected
exponent.

Fixture 1 pins the capstone's exact signature (no hypothesis beyond `[Nonempty V]`, arbitrary
`θ φ`); fixture 2 pins the corrected phase orientation at `|Λ| = 1`. Fixtures 3-6 pin the
concrete binomial/`cos`/`sin` shape of the already-existing `saturatedCoherentCoeff` and
`saturatedWeightVector` (proved directly from their definitions, independent of the capstone) at
`|Λ| = 1` and `|Λ| = 2`, guarding against a missing `√`-binomial factor, a swapped
`S_max ± M` exponent orientation, and a formula that is only correct at `N = 1`.
-/

namespace LatticeSystem.Tests.Problem24cCoherentExpansion

open LatticeSystem.Quantum
open _root_.Matrix

/-! ## Capstone signature pin (fails until the capstone is implemented) -/

/-- **Capstone signature pin.** The Problem 2.4.c capstone
(`tasaki_problem_2_4_c_coherent_expansion`) takes exactly `[Fintype V] [DecidableEq V]
[Nonempty V]` and arbitrary `θ φ : ℝ` — no `0 < θ < π` side hypothesis (the route is an exact
algebraic computation, valid for all real `θ`, `φ`; design §2 L5) and no further typeclass. This
fixture is fail-closed against a later-added angle hypothesis: adding one to the capstone's own
signature (not this fixture's) breaks the match. -/
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {N : ℕ} (θ φ : ℝ) :
    saturatedCoherentState V N θ φ
      = ∑ k : Fin (Fintype.card V * N + 1),
          (Complex.exp (-((φ : ℂ) * Complex.I) * ladderEigenvalueUp V N k)
              * ((Real.sqrt ((Fintype.card V * N).choose k.val) : ℂ)
                  * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card V * N - k.val)
                  * (Real.sin (θ / 2) : ℂ) ^ k.val))
            • saturatedWeightVector V N k :=
  tasaki_problem_2_4_c_coherent_expansion θ φ

/-! ## Phase-orientation pin (fails until the capstone is implemented) -/

/-- **Phase-orientation pin, `|Λ| = 1`, `N = 1`.** Evaluating the capstone at the single
all-up configuration exposes the `k = 0` term's phase factor `e^{-iφ·(1/2)}`
(`ladderEigenvalueUp (Fin 1) 1 0 = 1/2`), the corrected exponent of design §0.1. The printed
`e^{-iMφ/2}` of (S.19) would instead force `e^{-iφ/4}` here, so this pins the corrected
convention at the point where the `/2`-misprint is detectable. -/
example (θ φ : ℝ) :
    saturatedCoherentState (Fin 1) 1 θ φ (fun _ => 0)
      = ∑ k : Fin (Fintype.card (Fin 1) * 1 + 1),
          (Complex.exp (-((φ : ℂ) * Complex.I) * ladderEigenvalueUp (Fin 1) 1 k)
              * ((Real.sqrt ((Fintype.card (Fin 1) * 1).choose k.val) : ℂ)
                  * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card (Fin 1) * 1 - k.val)
                  * (Real.sin (θ / 2) : ℂ) ^ k.val))
            • saturatedWeightVector (Fin 1) 1 k (fun _ => 0) :=
  congrFun (tasaki_problem_2_4_c_coherent_expansion θ φ) (fun _ => 0)

/-! ## `|Λ| = 2`, `N = 1` component fixtures (already provable from existing definitions) -/

set_option linter.flexible false in
-- The broad `simp [...]` below feeds a `set`/`fin_cases` split whose branches close by a
-- further `simp`; `linter.flexible`'s narrower `simp only` suggestion does not carry through
-- those branches without per-branch adjustment. Style linter, not soundness.
/-- The `k`-th unnormalised ladder iterate at `|Λ| = 2`, `N = 1`, `k = 1` is nonzero exactly on
the two configurations with one up- and one down-spin, each with weight `1`. Component step
towards `saturatedCoherentCoeff_fin_two_one`. -/
private lemma ladderIterateUp_fin_two_one_apply (τ : Fin 2 → Fin 2) :
    ladderIterateUp (Fin 2) 1 1 τ = if magSumS τ = 1 then 1 else 0 := by
  rw [ladderIterateUp, show ((1 : Fin (Fintype.card (Fin 2) * 1 + 1)) : ℕ) = 1 from rfl, pow_one]
  rw [totalSpinSOpMinus_def, Matrix.sum_mulVec]
  simp only [Finset.sum_apply, allAlignedStateS, onSiteS_mulVec_basisVecS_apply]
  simp [Fin.sum_univ_two, onSiteS_apply, allAlignedConfigS, Fin.forall_fin_two, magSumS,
    Fin.sum_univ_two]
  set a := τ 0 with ha
  set b := τ 1 with hb
  clear_value a b
  fin_cases a <;> fin_cases b <;>
    simp [spinSOpMinus_apply_lower, spinSOpMinus_apply_diag]

/-- The `k = 1` ladder-iterate norm at `|Λ| = 2`, `N = 1` is `√2`: the fiber `magSumS = 1` has
exactly two configurations, each of unit weight. Feeds `saturatedWeightVector_fin_two_one_apply`
and `saturatedCoherentCoeff_fin_two_one`, i.e. the `√(C(2,1)) = √2` factor of (S.19). -/
private lemma saturatedLadderNorm_fin_two_one :
    saturatedLadderNorm (Fin 2) 1 1 = Real.sqrt 2 := by
  rw [saturatedLadderNorm, EuclideanSpace.norm_eq]
  congr 1
  rw [show (∑ σ, ‖(WithLp.toLp 2 (ladderIterateUp (Fin 2) 1 1) :
        EuclideanSpace ℂ (Fin 2 → Fin 2)).ofLp σ‖ ^ 2)
      = ∑ σ, ‖ladderIterateUp (Fin 2) 1 1 σ‖ ^ 2 from rfl]
  rw [show (∑ σ, ‖ladderIterateUp (Fin 2) 1 1 σ‖ ^ 2)
      = ∑ σ, (if magSumS σ = 1 then (1 : ℝ) else 0) from
      Finset.sum_congr rfl fun σ _ => by
        rw [ladderIterateUp_fin_two_one_apply]
        by_cases h : magSumS σ = 1 <;> simp [h]]
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter (fun σ : Fin 2 → Fin 2 => magSumS σ = 1)).card = 2 := by decide
  rw [hcard]
  norm_num

/-- **eq. (2.4.11) literal `S = 1/2` pin.** At `|Λ| = 2`, `N = 1`, `k = 1` the normalised sector
state `Φ_1` carries exactly the same weight `1/√2` on every configuration of its own sector, and
vanishes off it — the printed content of (2.4.11): all fiber configurations carry equal weight. A
formula that made the weight vary across the fiber (rather than being uniform) would fail this
fixture. -/
private lemma saturatedWeightVector_fin_two_one_apply (τ : Fin 2 → Fin 2) :
    saturatedWeightVector (Fin 2) 1 1 τ
      = if magSumS τ = 1 then ((Real.sqrt 2)⁻¹ : ℝ) else 0 := by
  rw [saturatedWeightVector, Pi.smul_apply, smul_eq_mul, ladderIterateUp_fin_two_one_apply,
    saturatedLadderNorm_fin_two_one]
  by_cases h : magSumS τ = 1 <;> simp [h]

/-- On the `magSumS = 1` fiber at `|Λ| = 2`, `N = 1`, the coherent-state product amplitude is
`cos(θ/2) · sin(θ/2)` regardless of which of the two configurations is chosen (both orderings of
one up- and one down-spin give the same product). Feeds `saturatedCoherentCoeff_fin_two_one`. -/
private lemma prod_saturatedCoherentAmp_fin_two_of_magSumS_eq_one (θ : ℝ) (τ : Fin 2 → Fin 2)
    (h : magSumS τ = 1) :
    ∏ x : Fin 2, saturatedCoherentAmp 1 θ (τ x) = Complex.cos (θ / 2) * Complex.sin (θ / 2) := by
  have h0 := (τ 0).isLt
  have h1 := (τ 1).isLt
  rw [Fin.prod_univ_two]
  simp only [magSumS, Fin.sum_univ_two] at h
  set a := τ 0 with ha
  set b := τ 1 with hb
  clear_value a b
  fin_cases a <;> fin_cases b <;>
    first
      | (exfalso; revert h; decide)
      | (simp only [saturatedCoherentAmp]; norm_num; try ring)

/-- **`|Λ| = 2` binomial fixture (the decisive one).** `c_1(θ) = √(C(2,1)) · cos(θ/2) sin(θ/2)
= √2 · cos(θ/2) sin(θ/2)`: a missing/erroneous binomial factor (`1` instead of `√2`, or
`C(2,1) = 2` instead of `√2`) fails here, since `N = 1` alone (`Problem24bWeightExpansion.lean`)
never exercises a nontrivial binomial coefficient. -/
private lemma saturatedCoherentCoeff_fin_two_one (θ : ℝ) :
    saturatedCoherentCoeff (Fin 2) 1 θ 1
      = (Real.sqrt 2 : ℂ) * Complex.cos (θ / 2) * Complex.sin (θ / 2) := by
  rw [saturatedCoherentCoeff, EuclideanSpace.inner_toLp_toLp]
  have hcoeff : ∀ i : Fin 2 → Fin 2, star (saturatedWeightVector (Fin 2) 1 1 i)
      = if magSumS i = 1 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0 := by
    intro i
    rw [saturatedWeightVector_fin_two_one_apply]
    by_cases h : magSumS i = 1 <;> simp [h]
  simp only [dotProduct, Pi.star_apply]
  simp_rw [hcoeff, saturatedCoherentState_zero_apply]
  have hstep : ∀ i : Fin 2 → Fin 2,
      (∏ x : Fin 2, saturatedCoherentAmp 1 θ (i x))
          * (if magSumS i = 1 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0)
        = if magSumS i = 1
            then Complex.cos (θ / 2) * Complex.sin (θ / 2) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
            else 0 := by
    intro i
    by_cases h : magSumS i = 1
    · rw [if_pos h, if_pos h, prod_saturatedCoherentAmp_fin_two_of_magSumS_eq_one θ i h]
    · rw [if_neg h, if_neg h, mul_zero]
  have hswap : ∀ i : Fin 2 → Fin 2,
      (if magSumS i = 1 then Complex.cos (θ / 2) * Complex.sin (θ / 2) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
        else (0 : ℂ))
        = (if magSumS i = 1 then (1 : ℂ) else 0)
            * (Complex.cos (θ / 2) * Complex.sin (θ / 2) * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) := by
    intro i
    by_cases h : magSumS i = 1 <;> simp [h]
  simp_rw [hstep, hswap]
  rw [← Finset.sum_mul, Finset.sum_boole]
  have hcard : (Finset.univ.filter (fun σ : Fin 2 → Fin 2 => magSumS σ = 1)).card = 2 := by decide
  rw [hcard]
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    exact_mod_cast this
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  push_cast
  field_simp
  rw [hsq]
  ring

/-! ## `|Λ| = 2`, `N = 1`, `k = 0` / `k = 2` exponent-orientation fixtures -/

/-- The `ℓ²`-norm of a standard basis vector is `1`. Reused for the `k = 0` sector state, whose
ladder iterate is exactly the all-up basis vector. -/
private lemma norm_toLp_basisVecS_eq_one {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (σ : V → Fin (N + 1)) :
    ‖(WithLp.toLp 2 (basisVecS σ) : EuclideanSpace ℂ (V → Fin (N + 1)))‖ = 1 := by
  have h := inner_self_eq_norm_sq_to_K
    (𝕜 := ℂ) (WithLp.toLp 2 (basisVecS σ) : EuclideanSpace ℂ (V → Fin (N + 1)))
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, basisVecS_inner_self] at h
  have h2 : ((‖(WithLp.toLp 2 (basisVecS σ) : EuclideanSpace ℂ (V → Fin (N + 1)))‖ ^ 2 : ℝ) : ℂ)
      = 1 := by push_cast; exact h.symm
  have h3 := Complex.ofReal_eq_one.mp h2
  nlinarith [norm_nonneg (WithLp.toLp 2 (basisVecS σ) : EuclideanSpace ℂ (V → Fin (N + 1)))]

/-- Pairing a vector with a basis vector reads off the corresponding component. -/
private lemma dotProduct_star_basisVecS {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}
    (v : (V → Fin (N + 1)) → ℂ) (σ : V → Fin (N + 1)) :
    v ⬝ᵥ star (basisVecS σ) = v σ := by
  simp [dotProduct, basisVecS_apply]

/-- The `k = 0` ladder iterate is the all-up basis vector (no lowering applied). -/
private lemma ladderIterateUp_fin_two_zero :
    ladderIterateUp (Fin 2) 1 0 = basisVecS (fun _ => (0 : Fin 2)) := by
  rw [ladderIterateUp, show ((0 : Fin (Fintype.card (Fin 2) * 1 + 1)) : ℕ) = 0 from rfl, pow_zero,
    Matrix.one_mulVec]
  rfl

set_option linter.flexible false in
-- Same rationale as `ladderIterateUp_fin_two_one_apply` above.
/-- One-step lowering action of `Ŝ^-_tot` on a basis vector at `|Λ| = 2`, `N = 1`: the two
site-lowering terms of `totalSpinSOpMinus_def` expanded and case-split into their four boolean
outcomes. Component step for the `k = 1 → k = 2` ladder step below. -/
private lemma totalSpinSOpMinus_mulVec_basisVecS_fin_two_apply
    (c τ : Fin 2 → Fin 2) :
    (totalSpinSOpMinus (Fin 2) 1 *ᵥ basisVecS c) τ
      = (if τ 1 = c 1 ∧ c 0 = 0 ∧ τ 0 = 1 then 1 else 0)
          + (if τ 0 = c 0 ∧ c 1 = 0 ∧ τ 1 = 1 then 1 else 0) := by
  rw [totalSpinSOpMinus_def, Matrix.sum_mulVec]
  simp only [Finset.sum_apply, onSiteS_mulVec_basisVecS_apply]
  simp [Fin.sum_univ_two, onSiteS_apply, Fin.forall_fin_two]
  set a := τ 0 with ha
  set b := τ 1 with hb
  set p := c 0 with hp
  set q := c 1 with hq
  clear_value a b p q
  fin_cases a <;> fin_cases b <;> fin_cases p <;> fin_cases q <;> simp [spinSOpMinus]

set_option linter.unnecessarySeqFocus false in
-- The `by_cases` case split below closes with just `simp` on some branches and needs `omega`
-- on others; the asymmetric goal counts trip `linter.unnecessarySeqFocus`. Style linter.
/-- The `k = 1` ladder iterate, rewritten as an explicit sum of the two basis vectors on its
fiber (rather than the `if`-form of `ladderIterateUp_fin_two_one_apply`), so that
`Matrix.mulVec_add` can push a further lowering through it termwise. -/
private lemma ladderIterateUp_fin_two_one_eq :
    ladderIterateUp (Fin 2) 1 1
      = basisVecS (fun i => if i = 0 then (1 : Fin 2) else 0)
        + basisVecS (fun i => if i = 0 then (0 : Fin 2) else 1) := by
  funext τ
  rw [ladderIterateUp_fin_two_one_apply, Pi.add_apply, basisVecS_apply, basisVecS_apply]
  simp only [magSumS, Fin.sum_univ_two, funext_iff, Fin.forall_fin_two, Fin.ext_iff]
  have h0 := (τ 0).isLt
  have h1 := (τ 1).isLt
  by_cases h0' : (τ 0 : ℕ) = 0 <;> by_cases h1' : (τ 1 : ℕ) = 0 <;>
      simp [h0', h1'] <;> omega

set_option linter.flexible false in
-- Same rationale as `ladderIterateUp_fin_two_one_apply` above.
/-- The `k = 2` ladder iterate at `|Λ| = 2`, `N = 1` has value `2` (not `1`) at the all-down
configuration: `k! = 2!` from the two orders in which the two sites can be lowered. Guards a
formula that dropped the `k!` factorial multiplicity. -/
private lemma ladderIterateUp_fin_two_two_apply (τ : Fin 2 → Fin 2) :
    ladderIterateUp (Fin 2) 1 2 τ = if magSumS τ = 2 then 2 else 0 := by
  rw [ladderIterateUp, show ((2 : Fin (Fintype.card (Fin 2) * 1 + 1)) : ℕ) = 2 from rfl, pow_two,
    ← Matrix.mulVec_mulVec,
    show (totalSpinSOpMinus (Fin 2) 1).mulVec (allAlignedStateS (Fin 2) 1 0)
        = ladderIterateUp (Fin 2) 1 1 from by
      rw [ladderIterateUp, show ((1 : Fin (Fintype.card (Fin 2) * 1 + 1)) : ℕ) = 1 from rfl,
        pow_one],
    ladderIterateUp_fin_two_one_eq, Matrix.mulVec_add, Pi.add_apply,
    totalSpinSOpMinus_mulVec_basisVecS_fin_two_apply,
    totalSpinSOpMinus_mulVec_basisVecS_fin_two_apply]
  simp only [magSumS, Fin.sum_univ_two, Fin.ext_iff]
  have h0 := (τ 0).isLt
  have h1 := (τ 1).isLt
  by_cases h0' : (τ 0 : ℕ) = 0 <;> by_cases h1' : (τ 1 : ℕ) = 0 <;>
    simp [h0', h1'] <;> first | omega | (split_ifs <;> first | omega | norm_num at *)

/-- The `k = 2` ladder-iterate norm at `|Λ| = 2`, `N = 1` is `2`: the fiber has one config of
value `2`, so `‖·‖ = √(2²) = 2`, normalising `Φ_2` back down to the plain all-down basis vector. -/
private lemma saturatedLadderNorm_fin_two_two :
    saturatedLadderNorm (Fin 2) 1 2 = 2 := by
  rw [saturatedLadderNorm, EuclideanSpace.norm_eq]
  rw [show (∑ σ, ‖(WithLp.toLp 2 (ladderIterateUp (Fin 2) 1 2) :
        EuclideanSpace ℂ (Fin 2 → Fin 2)).ofLp σ‖ ^ 2)
      = ∑ σ, ‖ladderIterateUp (Fin 2) 1 2 σ‖ ^ 2 from rfl]
  rw [show (∑ σ, ‖ladderIterateUp (Fin 2) 1 2 σ‖ ^ 2)
      = ∑ σ, (if magSumS σ = 2 then (4 : ℝ) else 0) from
      Finset.sum_congr rfl fun σ _ => by
        rw [ladderIterateUp_fin_two_two_apply]
        by_cases h : magSumS σ = 2
        · simp [h]; norm_num
        · simp [h]]
  rw [show (∑ σ : Fin 2 → Fin 2, (if magSumS σ = 2 then (4 : ℝ) else 0))
      = (∑ σ : Fin 2 → Fin 2, if magSumS σ = 2 then (1 : ℝ) else 0) * 4 from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : magSumS σ = 2 <;> simp [h]]
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter (fun σ : Fin 2 → Fin 2 => magSumS σ = 2)).card = 1 := by
    decide
  rw [hcard]
  rw [show ((1 : ℕ) : ℝ) * 4 = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num)]

/-- The `k = 2` sector state `Φ_2` at `|Λ| = 2`, `N = 1` is exactly the all-down basis vector
(the `2` in the iterate and the `2` in the norm cancel). -/
private lemma saturatedWeightVector_fin_two_two :
    saturatedWeightVector (Fin 2) 1 2 = basisVecS (fun _ => (1 : Fin 2)) := by
  funext τ
  rw [saturatedWeightVector, Pi.smul_apply, smul_eq_mul, ladderIterateUp_fin_two_two_apply,
    saturatedLadderNorm_fin_two_two, basisVecS_apply]
  by_cases h : magSumS τ = 2
  · have hmag : (τ 0).val + (τ 1).val = 2 := by simpa [magSumS, Fin.sum_univ_two] using h
    have h0 := (τ 0).isLt
    have h1 := (τ 1).isLt
    have e0 : (τ 0).val = 1 := by omega
    have e1 : (τ 1).val = 1 := by omega
    have hτ0 : τ 0 = 1 := Fin.ext e0
    have hτ1 : τ 1 = 1 := Fin.ext e1
    have hτ : τ = fun _ => (1 : Fin 2) := by
      funext i
      fin_cases i
      · exact hτ0
      · exact hτ1
    simp [hτ, magSumS]
  · have hτ : τ ≠ fun _ => (1 : Fin 2) := by
      intro hc
      apply h
      simp [hc, magSumS]
    simp [h, hτ]

/-- **`k = 2` orientation pin.** `c_2(θ) = sin(θ/2)²`, not `cos(θ/2)²`: pairs with the `k = 0`
fixture below to catch a swapped `S_max ± M` exponent (`cos^{|V|N-k} sin^k` vs. the reverse). -/
private lemma saturatedCoherentCoeff_fin_two_two (θ : ℝ) :
    saturatedCoherentCoeff (Fin 2) 1 θ 2 = Complex.sin (θ / 2) ^ 2 := by
  rw [saturatedCoherentCoeff, saturatedWeightVector_fin_two_two, EuclideanSpace.inner_toLp_toLp,
    dotProduct_star_basisVecS, saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-- **`k = 0` orientation pin.** `c_0(θ) = cos(θ/2)²`: the `|Λ| = 2` extension of the `|Λ| = 1`
`c_0 = cos(θ/2)` fixture (`Problem24bWeightExpansion.lean`), confirming the exponent scales with
`|V|N - k` rather than staying fixed at `1`. -/
private lemma saturatedCoherentCoeff_fin_two_zero (θ : ℝ) :
    saturatedCoherentCoeff (Fin 2) 1 θ 0 = Complex.cos (θ / 2) ^ 2 := by
  rw [saturatedCoherentCoeff, saturatedWeightVector, saturatedLadderNorm,
    ladderIterateUp_fin_two_zero, norm_toLp_basisVecS_eq_one, Complex.ofReal_one, inv_one,
    one_smul, EuclideanSpace.inner_toLp_toLp, dotProduct_star_basisVecS,
    saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-! ## `|Λ| = 1`, `N = 2` general-`S` anti-`N = 1` fixture -/

/-- The `k = 1` ladder iterate at `|Λ| = 1`, `N = 2` is nonzero only at the middle configuration,
with value `√2` — the one-site `√(C(N, j))` weight of design §0.3, invisible at every `N = 1`
fixture (`C(1, ·) = 1` there). -/
private lemma ladderIterateUp_fin_one_two_one_apply (τ : Fin 1 → Fin 3) :
    ladderIterateUp (Fin 1) 2 1 τ = if τ 0 = 1 then (Real.sqrt 2 : ℂ) else 0 := by
  rw [ladderIterateUp, show ((1 : Fin (Fintype.card (Fin 1) * 2 + 1)) : ℕ) = 1 from rfl, pow_one]
  simp only [totalSpinSOpMinus, Finset.univ_unique, Finset.sum_singleton, allAlignedStateS,
    onSiteS_mulVec_basisVecS_apply, onSiteS_apply, allAlignedConfigS]
  rw [if_pos fun k hk => absurd (Subsingleton.elim k default) hk]
  have hd : (default : Fin 1) = 0 := rfl
  rw [hd]
  by_cases h : τ 0 = 1
  · rw [if_pos h, h,
      spinSOpMinus_apply_lower 2 (show (0 : Fin 3).val + 1 = (1 : Fin 3).val from rfl)]
    norm_num
  · rw [if_neg h]
    apply spinSOpMinus_apply_other
    intro hc
    exact h (Fin.ext hc.symm)

/-- The `k = 1` ladder-iterate norm at `|Λ| = 1`, `N = 2` is `√2`: a single nonzero configuration
of magnitude `√2`. -/
private lemma saturatedLadderNorm_fin_one_two_one :
    saturatedLadderNorm (Fin 1) 2 1 = Real.sqrt 2 := by
  rw [saturatedLadderNorm, EuclideanSpace.norm_eq]
  rw [show (∑ σ, ‖(WithLp.toLp 2 (ladderIterateUp (Fin 1) 2 1) :
        EuclideanSpace ℂ (Fin 1 → Fin 3)).ofLp σ‖ ^ 2)
      = ∑ σ, ‖ladderIterateUp (Fin 1) 2 1 σ‖ ^ 2 from rfl]
  rw [show (∑ σ, ‖ladderIterateUp (Fin 1) 2 1 σ‖ ^ 2)
      = ∑ σ : Fin 1 → Fin 3, (if σ 0 = 1 then (2 : ℝ) else 0) from
      Finset.sum_congr rfl fun σ _ => by
        rw [ladderIterateUp_fin_one_two_one_apply]
        by_cases h : σ 0 = 1
        · simp [h]
        · simp [h]]
  rw [show (∑ σ : Fin 1 → Fin 3, (if σ 0 = 1 then (2 : ℝ) else 0))
      = (∑ σ : Fin 1 → Fin 3, if σ 0 = 1 then (1 : ℝ) else 0) * 2 from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases h : σ 0 = 1 <;> simp [h]]
  rw [Finset.sum_boole]
  have hcard : (Finset.univ.filter (fun σ : Fin 1 → Fin 3 => σ 0 = 1)).card = 1 := by decide
  rw [hcard]
  rw [show ((1 : ℕ) : ℝ) * 2 = 2 from by norm_num]

/-- The `k = 1` sector state at `|Λ| = 1`, `N = 2` is exactly the middle-configuration basis
vector (the `√2` in the iterate and the `√2` in the norm cancel). -/
private lemma saturatedWeightVector_fin_one_two_one :
    saturatedWeightVector (Fin 1) 2 1 = basisVecS (fun _ => (1 : Fin 3)) := by
  funext τ
  rw [saturatedWeightVector, Pi.smul_apply, smul_eq_mul, ladderIterateUp_fin_one_two_one_apply,
    saturatedLadderNorm_fin_one_two_one, basisVecS_apply]
  by_cases h : τ 0 = 1
  · have hτ : τ = fun _ => (1 : Fin 3) := by funext i; fin_cases i; exact h
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    simp [hτ, h2]
  · have hτ : τ ≠ fun _ => (1 : Fin 3) := by
      intro hc; exact h (congrFun hc 0)
    simp [h, hτ]

/-- **General-`S` anti-`N = 1` pin.** `c_1(θ) = √(C(2,1)) cos(θ/2) sin(θ/2) = √2 cos(θ/2)
sin(θ/2)` at `|Λ| = 1`, `N = 2`: a formula correct only at `N = 1` (where every one-site weight is
trivially `1`) fails here, since the per-site `√C(N, j)` weight is genuinely present. -/
private lemma saturatedCoherentCoeff_fin_one_two_one (θ : ℝ) :
    saturatedCoherentCoeff (Fin 1) 2 θ 1
      = (Real.sqrt 2 : ℂ) * Complex.cos (θ / 2) * Complex.sin (θ / 2) := by
  rw [saturatedCoherentCoeff, saturatedWeightVector_fin_one_two_one,
    EuclideanSpace.inner_toLp_toLp, dotProduct_star_basisVecS, saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

end LatticeSystem.Tests.Problem24cCoherentExpansion
