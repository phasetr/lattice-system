import LatticeSystem.Quantum.SpinS.SaturatedCoherentExpansion

/-!
# Test coverage for Tasaki Problem 2.4.c — the coherent-state / `Φ_M` expansion

Fixtures for the capstone `tasaki_problem_2_4_c_coherent_expansion` and for the closed forms it is
assembled from (Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 2.4.c,
statement p. 34, solution p. 497, eq. (S.19)): `Ξ_{θ,φ} = Σ_k c_k(θ, φ) • Φ_k` with
`c_k(θ, φ) = e^{-iφM(k)} · √(C(|V|N, k)) · cos(θ/2)^{|V|N-k} · sin(θ/2)^k`.  The azimuthal
exponent is `e^{-iMφ}` rather than the printed `e^{-iMφ/2}`; the evidence for that correction is
recorded in the module header of `SaturatedCoherentExpansion.lean`.

The fixtures come in two kinds.

* **Signature pins** for the capstone: its exact hypothesis set (nothing beyond `[Nonempty V]`,
  arbitrary `θ`, `φ`) and, at `|Λ| = 1`, the shape of the phase factor.
* **Closed-form cross-checks.**  The private lemmas below compute the ladder iterate, its norm,
  the sector state `Φ_k` and the coefficient `c_k(θ)` at `|Λ| = 2`, `N = 1` and at `|Λ| = 1`,
  `N = 2` straight from the definitions, never using the closed forms.  The final section then
  writes out the right-hand side of each closed form — `Math.sum_prod_choose_fiber`,
  `totalSpinSOpMinus_pow_allAlignedStateS_zero_apply`, `saturatedLadderNorm_eq`,
  `saturatedWeightVector_apply` (eq. (2.4.11)) and `saturatedCoherentCoeff_eq` (eq. (S.19)) — at
  those instances and equates it with the independently computed value.  A swapped
  `cos`/`sin` exponent, a dropped `√`-binomial normalisation, a dropped factorial multiplicity
  `k!`, or a formula that happens to be correct only at `N = 1` each break these fixtures.
-/

namespace LatticeSystem.Tests.Problem24cCoherentExpansion

open LatticeSystem.Quantum
open _root_.Matrix

/-! ## Capstone signature pin -/

/-- **Capstone signature pin.** The Problem 2.4.c capstone
(`tasaki_problem_2_4_c_coherent_expansion`) takes exactly `[Fintype V] [DecidableEq V]
[Nonempty V]` and arbitrary `θ φ : ℝ` — no `0 < θ < π` side hypothesis (the route is an exact
algebraic computation, valid for all real `θ`, `φ`) and no further typeclass. This
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

/-! ## Phase-orientation pin -/

/-- **Phase-orientation pin, `|Λ| = 1`, `N = 1`.** The capstone evaluated at the single all-up
configuration, where the `k = 0` phase factor is `e^{-iφ·(1/2)}`
(`ladderEigenvalueUp (Fin 1) 1 0 = 1/2`).  This is `congrFun` of the signature pin above, so it is
not an independent check of the capstone; what it adds is a concrete instance in which the
azimuthal exponent is legible, `e^{-iφM}` and not the printed `e^{-iφM/2}` (which would read
`e^{-iφ/4}` here). -/
example (θ φ : ℝ) :
    saturatedCoherentState (Fin 1) 1 θ φ (fun _ => 0)
      = ∑ k : Fin (Fintype.card (Fin 1) * 1 + 1),
          (Complex.exp (-((φ : ℂ) * Complex.I) * ladderEigenvalueUp (Fin 1) 1 k)
              * ((Real.sqrt ((Fintype.card (Fin 1) * 1).choose k.val) : ℂ)
                  * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card (Fin 1) * 1 - k.val)
                  * (Real.sin (θ / 2) : ℂ) ^ k.val))
            • saturatedWeightVector (Fin 1) 1 k (fun _ => 0) :=
  congrFun (tasaki_problem_2_4_c_coherent_expansion θ φ) (fun _ => 0)

/-! ## `|Λ| = 2`, `N = 1` components, computed from the definitions -/

/-- The `k`-th unnormalised ladder iterate at `|Λ| = 2`, `N = 1`, `k = 1` is nonzero exactly on
the two configurations with one up- and one down-spin, each with weight `1`. Component step
towards the `|Λ| = 2` sector state and coefficient below. -/
private lemma ladderIterateUp_fin_two_one_apply (τ : Fin 2 → Fin 2) :
    ladderIterateUp (Fin 2) 1 1 τ = if magSumS τ = 1 then 1 else 0 := by
  rw [ladderIterateUp, show ((1 : Fin (Fintype.card (Fin 2) * 1 + 1)) : ℕ) = 1 from rfl, pow_one]
  rw [totalSpinSOpMinus_def, Matrix.sum_mulVec]
  simp only [Finset.sum_apply, allAlignedStateS, onSiteS_mulVec_basisVecS_apply]
  simp only [Fin.isValue, onSiteS_apply, ne_eq, Nat.reduceAdd, allAlignedConfigS,
    Fin.forall_fin_two, Fin.sum_univ_two, not_true_eq_false, IsEmpty.forall_iff, one_ne_zero,
    not_false_eq_true, forall_const, true_and, zero_ne_one, and_true, magSumS]
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

/-- The normalised sector state `Φ_1` at `|Λ| = 2`, `N = 1`, computed from the definitions: it
carries the same weight `1/√2` on every configuration of its own sector and vanishes off it — the
printed content of (2.4.11) at `S = 1/2`.  Feeds the eq. (2.4.11) cross-check below. -/
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

/-- The coefficient `c_1(θ)` at `|Λ| = 2`, `N = 1`, computed from the definitions: pairing the
two-configuration sector state `Φ_1` with the coherent state gives `√2 cos(θ/2) sin(θ/2)`.  Feeds
the decisive binomial cross-check below (this is the smallest instance with a nontrivial binomial
coefficient). -/
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

/-! ## `|Λ| = 2`, `N = 1`, `k = 0` and `k = 2` components, computed from the definitions -/

/-- The `k = 0` ladder iterate is the all-up basis vector (no lowering applied). -/
private lemma ladderIterateUp_fin_two_zero :
    ladderIterateUp (Fin 2) 1 0 = basisVecS (fun _ => (0 : Fin 2)) := by
  rw [ladderIterateUp, show ((0 : Fin (Fintype.card (Fin 2) * 1 + 1)) : ℕ) = 0 from rfl, pow_zero,
    Matrix.one_mulVec]
  rfl

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
  simp only [onSiteS_apply, ne_eq, Nat.reduceAdd, Fin.forall_fin_two, Fin.isValue,
    Fin.sum_univ_two, not_true_eq_false, IsEmpty.forall_iff, one_ne_zero, not_false_eq_true,
    forall_const, true_and, zero_ne_one, and_true]
  set a := τ 0 with ha
  set b := τ 1 with hb
  set p := c 0 with hp
  set q := c 1 with hq
  clear_value a b p q
  fin_cases a <;> fin_cases b <;> fin_cases p <;> fin_cases q <;> simp [spinSOpMinus]

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
      simp [h0', h1']
  omega

/-- The `k = 2` ladder iterate at `|Λ| = 2`, `N = 1` has value `2` (not `1`) at the all-down
configuration: `k! = 2!` from the two orders in which the two sites can be lowered.  Feeds the
`k = 2` norm and the ladder-iterate cross-check below, where that factorial is compared with the
closed form. -/
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
    simp only [Fin.isValue, h0', h1', Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.zero_mod,
        one_ne_zero, ↓reduceIte, Nat.reduceAdd, zero_ne_one, and_self, and_false, true_and,
        false_and, add_zero, zero_add, right_eq_ite_iff, OfNat.zero_ne_ofNat, imp_false, ne_eq] <;>
      first | omega | (split_ifs <;> first | omega | norm_num at *)

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

/-- The coefficient `c_2(θ) = sin(θ/2)²` at `|Λ| = 2`, `N = 1`, computed from the definitions
through the all-down sector state.  Feeds the `k = 2` exponent-orientation cross-check below. -/
private lemma saturatedCoherentCoeff_fin_two_two (θ : ℝ) :
    saturatedCoherentCoeff (Fin 2) 1 θ 2 = Complex.sin (θ / 2) ^ 2 := by
  rw [saturatedCoherentCoeff, saturatedWeightVector_fin_two_two, EuclideanSpace.inner_toLp_toLp,
    dotProduct_star_basisVecS, saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-- The coefficient `c_0(θ) = cos(θ/2)²` at `|Λ| = 2`, `N = 1`, computed from the definitions
through the all-up sector state.  Feeds the `k = 0` exponent-orientation cross-check below, where
the exponent is seen to scale with `|Λ|N - k` rather than staying fixed at `1` as it does at
`|Λ| = 1` (`Problem24bWeightExpansion.lean`). -/
private lemma saturatedCoherentCoeff_fin_two_zero (θ : ℝ) :
    saturatedCoherentCoeff (Fin 2) 1 θ 0 = Complex.cos (θ / 2) ^ 2 := by
  rw [saturatedCoherentCoeff, saturatedWeightVector, saturatedLadderNorm,
    ladderIterateUp_fin_two_zero, norm_toLp_basisVecS_eq_one, Complex.ofReal_one, inv_one,
    one_smul, EuclideanSpace.inner_toLp_toLp, dotProduct_star_basisVecS,
    saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-! ## `|Λ| = 1`, `N = 2` components, computed from the definitions -/

/-- The `k = 1` ladder iterate at `|Λ| = 1`, `N = 2` is nonzero only at the middle configuration,
with value `√2` — the one-site `√(C(N, j))` weight, invisible at every `N = 1`
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

/-- The coefficient `c_1(θ) = √2 cos(θ/2) sin(θ/2)` at `|Λ| = 1`, `N = 2`, computed from the
definitions; here the per-site weight `√C(N, j)` is genuinely present, unlike at `N = 1`.  Feeds
the general-`S` cross-check below. -/
private lemma saturatedCoherentCoeff_fin_one_two_one (θ : ℝ) :
    saturatedCoherentCoeff (Fin 1) 2 θ 1
      = (Real.sqrt 2 : ℂ) * Complex.cos (θ / 2) * Complex.sin (θ / 2) := by
  rw [saturatedCoherentCoeff, saturatedWeightVector_fin_one_two_one,
    EuclideanSpace.inner_toLp_toLp, dotProduct_star_basisVecS, saturatedCoherentState_zero_apply]
  simp [saturatedCoherentAmp]

/-! ## Closed-form cross-checks

Each fixture below writes out, by hand, the right-hand side of one of the closed forms at a
concrete instance and equates it with the value computed independently above, straight from the
definitions.  The proofs are `(closed form).symm.trans (definitional computation)`: a change in
the shape of a closed form (a swapped exponent, a dropped normalisation) stops matching the
hand-written left-hand side, and a change in its value stops matching the independently computed
right-hand side. -/

/-- **Vandermonde fiber-sum cross-check, `|Λ| = 2`, `N = 2`, `k = 2`.** `Math.sum_prod_choose_fiber`
evaluates the weighted fiber sum `Σ_{Σ σ_x = 2} ∏_x C(2, σ_x)` to `C(4, 2) = 6`, against the
independent evaluation of the sum.  The site weights are nontrivial at this instance — the
balanced configuration alone contributes `C(2,1)² = 4` — so an unweighted count of the fiber
(`3` configurations) would fail here. -/
example :
    (∑ σ ∈ Finset.univ.filter (fun σ : Fin 2 → Fin 3 => ∑ x, (σ x).val = 2),
        ∏ x, (2 : ℕ).choose (σ x).val) = 6 :=
  (Math.sum_prod_choose_fiber (Fin 2) 2 2).trans (by decide)

/-- **Ladder-iterate cross-check, `|Λ| = 2`, `N = 1`, `k = 2`.**
`totalSpinSOpMinus_pow_allAlignedStateS_zero_apply` gives the value `k! · ∏_x √(C(1, σ_x))` on the
fiber, which is `2` here; `ladderIterateUp_fin_two_two_apply` computes the same `2` from the
definitions.  A closed form without the factorial multiplicity `k!` would give `1`. -/
example (σ : Fin 2 → Fin 2) :
    (if magSumS σ = 2 then
        ((((2 : ℕ).factorial : ℝ) * ∏ x : Fin 2, Real.sqrt ((1 : ℕ).choose (σ x).val) : ℝ) : ℂ)
      else 0)
      = if magSumS σ = 2 then 2 else 0 :=
  (totalSpinSOpMinus_pow_allAlignedStateS_zero_apply (V := Fin 2) (N := 1) 2 σ).symm.trans
    (ladderIterateUp_fin_two_two_apply σ)

/-- **Sector-normalisation cross-check, `|Λ| = 2`, `N = 1`, `k = 2`.** `saturatedLadderNorm_eq`
gives `k! · √(C(2,2)) = 2`; the definitional computation gives the same `2`, so both the
factorial and the binomial factor of the norm are pinned. -/
example : ((2 : ℕ).factorial : ℝ) * Real.sqrt ((Fintype.card (Fin 2) * 1).choose 2) = 2 :=
  (saturatedLadderNorm_eq (V := Fin 2) (N := 1) 2).symm.trans saturatedLadderNorm_fin_two_two

/-- **eq. (2.4.11) cross-check, `|Λ| = 2`, `N = 1`, `k = 1`.** `saturatedWeightVector_apply` gives
`(√(C(2,1)))⁻¹ ∏_x √(C(1, σ_x))` on the fiber; at `S = 1/2` every site weight is `1`, so this must
be the uniform `(√2)⁻¹` computed from the definitions — the printed content of (2.4.11). -/
example (τ : Fin 2 → Fin 2) :
    (if magSumS τ = 1 then
        (((Real.sqrt ((Fintype.card (Fin 2) * 1).choose 1))⁻¹
            * ∏ x : Fin 2, Real.sqrt ((1 : ℕ).choose (τ x).val) : ℝ) : ℂ)
      else 0)
      = if magSumS τ = 1 then ((Real.sqrt 2)⁻¹ : ℝ) else 0 :=
  (saturatedWeightVector_apply (V := Fin 2) (N := 1) 1 τ).symm.trans
    (saturatedWeightVector_fin_two_one_apply τ)

/-- **eq. (2.4.11) general-`S` cross-check, `|Λ| = 1`, `N = 2`, `k = 1`.** Here the one-site weight
`√(C(2,1)) = √2` is genuinely present and cancels the sector normalisation `√(C(2,1))`, so
`saturatedWeightVector_apply` must return the bare basis vector computed from the definitions.  A
closed form that dropped the one-site weights would give `(√2)⁻¹` instead of `1`. -/
example (τ : Fin 1 → Fin 3) :
    (if magSumS τ = 1 then
        (((Real.sqrt ((Fintype.card (Fin 1) * 2).choose 1))⁻¹
            * ∏ x : Fin 1, Real.sqrt ((2 : ℕ).choose (τ x).val) : ℝ) : ℂ)
      else 0)
      = basisVecS (fun _ => (1 : Fin 3)) τ :=
  (saturatedWeightVector_apply (V := Fin 1) (N := 2) 1 τ).symm.trans
    (congrFun saturatedWeightVector_fin_one_two_one τ)

/-- **eq. (S.19) cross-check at `k = 0`, `|Λ| = 2`, `N = 1`.** The closed-form coefficient is
`√(C(2,0)) cos(θ/2)² sin(θ/2)⁰ = cos(θ/2)²`, matching the definitional computation.  Together with
the `k = 2` fixture below this pins the exponent orientation: `cos^{|Λ|N-k} sin^k` and not the
reverse. -/
example (θ : ℝ) :
    (Real.sqrt ((Fintype.card (Fin 2) * 1).choose 0) : ℂ)
        * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card (Fin 2) * 1 - 0)
        * (Real.sin (θ / 2) : ℂ) ^ 0
      = Complex.cos (θ / 2) ^ 2 :=
  (saturatedCoherentCoeff_eq (V := Fin 2) (N := 1) θ 0).symm.trans
    (saturatedCoherentCoeff_fin_two_zero θ)

/-- **eq. (S.19) cross-check at `k = 2`, `|Λ| = 2`, `N = 1`.** The closed-form coefficient is
`√(C(2,2)) cos(θ/2)⁰ sin(θ/2)² = sin(θ/2)²`, matching the definitional computation; with the
`k = 0` fixture above, a swapped `cos`/`sin` exponent fails here. -/
example (θ : ℝ) :
    (Real.sqrt ((Fintype.card (Fin 2) * 1).choose 2) : ℂ)
        * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card (Fin 2) * 1 - 2)
        * (Real.sin (θ / 2) : ℂ) ^ 2
      = Complex.sin (θ / 2) ^ 2 :=
  (saturatedCoherentCoeff_eq (V := Fin 2) (N := 1) θ 2).symm.trans
    (saturatedCoherentCoeff_fin_two_two θ)

/-- **eq. (S.19) binomial cross-check at `k = 1`, `|Λ| = 2`, `N = 1` (the decisive one).** The
closed-form coefficient is `√(C(2,1)) cos(θ/2) sin(θ/2)`, and the definitional computation gives
`√2 cos(θ/2) sin(θ/2)`: a closed form without the `√`-binomial factor, or with `C(2,1)` in place
of `√(C(2,1))`, fails here.  The `|Λ| = 1`, `N = 1` fixtures of
`Problem24bWeightExpansion.lean` cannot catch it, since `C(1, ·) = 1` there. -/
example (θ : ℝ) :
    (Real.sqrt ((Fintype.card (Fin 2) * 1).choose 1) : ℂ)
        * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card (Fin 2) * 1 - 1)
        * (Real.sin (θ / 2) : ℂ) ^ 1
      = (Real.sqrt 2 : ℂ) * Complex.cos (θ / 2) * Complex.sin (θ / 2) :=
  (saturatedCoherentCoeff_eq (V := Fin 2) (N := 1) θ 1).symm.trans
    (saturatedCoherentCoeff_fin_two_one θ)

/-- **eq. (S.19) general-`S` cross-check at `k = 1`, `|Λ| = 1`, `N = 2`.** The binomial of the
closed form is the *global* `C(|Λ|N, k) = C(2,1) = 2`, not a per-site one: at a single site with
`N = 2` the definitional computation still gives `√2 cos(θ/2) sin(θ/2)`, so a formula correct only
for `N = 1` fails here. -/
example (θ : ℝ) :
    (Real.sqrt ((Fintype.card (Fin 1) * 2).choose 1) : ℂ)
        * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card (Fin 1) * 2 - 1)
        * (Real.sin (θ / 2) : ℂ) ^ 1
      = (Real.sqrt 2 : ℂ) * Complex.cos (θ / 2) * Complex.sin (θ / 2) :=
  (saturatedCoherentCoeff_eq (V := Fin 1) (N := 2) θ 1).symm.trans
    (saturatedCoherentCoeff_fin_one_two_one θ)

end LatticeSystem.Tests.Problem24cCoherentExpansion
