import LatticeSystem.Quantum.SpinS.SaturatedCoherentProjection
import LatticeSystem.Quantum.SpinS.SaturatedLadderComponent

/-!
# Tasaki Problem 2.4.c — closed-form expansion of the coherent state in the sector states `Φ_M`

The saturated-ferromagnet coherent state `Ξ_{θ,φ}` (Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, eq. (2.4.6), p. 33) is expanded in the magnetisation-sector ground states
`Φ_M` (eq. (2.4.9), p. 33) with explicit binomial coefficients:

  `Ξ_{θ,φ} = ∑_M e^{-iMφ} √(binom (2S_max) (S_max − M)) cos(θ/2)^{S_max+M} sin(θ/2)^{S_max−M} Φ_M`,

the solution of Problem 2.4.c (statement p. 34, solution p. 497, eq. (S.19)).  In the repo's
lowering index `k = S_max − M` this reads `cos(θ/2)^{|Λ|N − k} sin(θ/2)^k` with the binomial
`√(binom (|Λ| N) k)`, and `M = ladderEigenvalueUp V N k`.

The expansion structure `Ξ_{θ,φ} = ∑_k e^{-iφM} c_k(θ) Φ_k` is already available from
`saturatedCoherentState_eq_sum`; what this module supplies is the closed form of the coefficient
`c_k(θ) = ⟪Φ_k, Ξ_{θ,0}⟫`.  It is obtained from the component form of `Φ_k`
(`saturatedWeightVector_apply`, eq. (2.4.11)) and the site-product form of `Ξ_{θ,0}`
(`saturatedCoherentState_zero_apply`, eq. (S.18)): on the fiber `magSumS σ = k` the two
Clebsch–Gordan weight products combine into `∏_x binom N σ_x`, whose fiber sum is
`binom (|Λ| N) k` by `Math.sum_prod_choose_fiber`.  The whole computation is exact and needs no
restriction on `θ`; the result is stated for general spin `S = N/2`, whereas Tasaki states
Problem 2.4.c for `S = 1/2`.

## Phase convention

The azimuthal factor used here is `e^{-iMφ}`.  The exponent printed in (S.19) is `e^{-iMφ/2}`,
which is inconsistent with its own neighbours on p. 497 and with the definition it is derived
from:

* (S.18), displayed on the same page, carries the per-site phases `e^{-iφ/2}` on `|ψ^↑⟩` and
  `e^{+iφ/2}` on `|ψ^↓⟩`, so a configuration with `n↑` up and `n↓` down spins acquires
  `e^{-i(n↑ - n↓)φ/2} = e^{-iMφ}`, because `M = (n↑ - n↓)/2`;
* (S.17), displayed immediately above on the same page, carries `e^{i(M - M')φ}` with no `/2`;
* the phase factorisation `Ξ_{θ,φ}(σ) = e^{-iφM(σ)} Ξ_{θ,0}(σ)` is proved in this development as
  `saturatedCoherentState_apply_phase` directly from eqs. (2.4.6), p. 33 and (2.2.11), p. 22.

The capstone therefore uses `e^{-iφM}` — literally the factor produced by
`saturatedCoherentState_eq_sum` — with the `√`-binomial, `cos` and `sin` factors exactly as
printed.
-/

namespace LatticeSystem.Quantum

open _root_.Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## The closed-form sector coefficient -/

/-- **Closed form of the sector coefficient** `c_M(θ) = ⟪Φ_M, Ξ_{θ,0}⟫`, i.e. the coefficient
displayed in Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, eq. (S.19), p. 497
(solution to Problem 2.4.c):
`c_M(θ) = √(binom (2S_max) (S_max − M)) cos(θ/2)^{S_max+M} sin(θ/2)^{S_max−M}`, written here in
the lowering index `k = S_max − M`.

Both `Φ_M` and `Ξ_{θ,0}` are supported by site-product Clebsch–Gordan weights `√(binom N σ_x)`,
which multiply to `∏_x binom N σ_x` on the common fiber; summing that over the fiber gives
`binom (|Λ| N) k`, and one of the two `√(binom (|Λ| N) k)` normalisation factors survives.  The
identity is exact for every real `θ`, and holds for empty `V` as well. -/
theorem saturatedCoherentCoeff_eq (θ : ℝ) (k : Fin (Fintype.card V * N + 1)) :
    saturatedCoherentCoeff V N θ k
      = (Real.sqrt ((Fintype.card V * N).choose k.val) : ℂ)
          * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card V * N - k.val)
          * (Real.sin (θ / 2) : ℂ) ^ k.val := by
  classical
  have hkle : k.val ≤ Fintype.card V * N := Nat.lt_succ_iff.mp k.isLt
  have hchoose : (0 : ℝ) < Real.sqrt ((Fintype.card V * N).choose k.val) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.choose_pos hkle)
  have hs : Real.sqrt ((Fintype.card V * N).choose k.val) ≠ 0 := ne_of_gt hchoose
  have hampprod : ∀ σ : V → Fin (N + 1), magSumS σ = k.val →
      (∏ x : V, saturatedCoherentAmp N θ (σ x))
        = ((∏ x : V, Real.sqrt (N.choose (σ x).val) : ℝ) : ℂ)
            * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card V * N - k.val)
            * (Real.sin (θ / 2) : ℂ) ^ k.val := by
    intro σ hσ
    have hle : ∀ x ∈ (Finset.univ : Finset V), (σ x).val ≤ N := fun x _ =>
      Nat.lt_succ_iff.mp (σ x).isLt
    have hsub : ∑ x : V, (N - (σ x).val) = Fintype.card V * N - k.val := by
      rw [Finset.sum_tsub_distrib _ hle, Finset.sum_const, Finset.card_univ, smul_eq_mul,
        show (∑ x : V, (σ x).val) = k.val from hσ]
    simp only [saturatedCoherentAmp]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
      Finset.prod_pow_eq_pow_sum, hsub, show (∑ x : V, (σ x).val) = k.val from hσ,
      ← Complex.ofReal_prod]
  have hterm : ∀ σ : V → Fin (N + 1),
      saturatedCoherentState V N θ 0 σ * star (saturatedWeightVector V N k σ)
        = if magSumS σ = k.val then
            (((Real.sqrt ((Fintype.card V * N).choose k.val))⁻¹
                * ∏ x : V, ((N.choose (σ x).val : ℕ) : ℝ) : ℝ) : ℂ)
              * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card V * N - k.val)
              * (Real.sin (θ / 2) : ℂ) ^ k.val
          else 0 := by
    intro σ
    rw [saturatedWeightVector_apply]
    by_cases h : magSumS σ = k.val
    · rw [if_pos h, if_pos h, saturatedCoherentState_zero_apply, hampprod σ h]
      simp only [← starRingEnd_apply, Complex.conj_ofReal]
      have hsq : (∏ x : V, Real.sqrt (N.choose (σ x).val))
            * (∏ x : V, Real.sqrt (N.choose (σ x).val))
          = ∏ x : V, ((N.choose (σ x).val : ℕ) : ℝ) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun x _ => Real.mul_self_sqrt (Nat.cast_nonneg _)
      have hAB : ((∏ x : V, Real.sqrt (N.choose (σ x).val) : ℝ) : ℂ)
            * (((Real.sqrt ((Fintype.card V * N).choose k.val))⁻¹
                * ∏ x : V, Real.sqrt (N.choose (σ x).val) : ℝ) : ℂ)
          = (((Real.sqrt ((Fintype.card V * N).choose k.val))⁻¹
                * ∏ x : V, ((N.choose (σ x).val : ℕ) : ℝ) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        rw [← hsq]
        ring
      linear_combination ((Real.cos (θ / 2) : ℂ) ^ (Fintype.card V * N - k.val)
        * (Real.sin (θ / 2) : ℂ) ^ k.val) * hAB
    · simp only [if_neg h, star_zero, mul_zero]
  have hL0 : (∑ σ ∈ Finset.univ.filter (fun σ : V → Fin (N + 1) => magSumS σ = k.val),
      ∏ x : V, N.choose (σ x).val) = (Fintype.card V * N).choose k.val :=
    Math.sum_prod_choose_fiber V N k.val
  have hfiber : (∑ σ ∈ Finset.univ.filter (fun σ : V → Fin (N + 1) => magSumS σ = k.val),
      ∏ x : V, ((N.choose (σ x).val : ℕ) : ℝ)) = ((Fintype.card V * N).choose k.val : ℝ) := by
    rw [← hL0, Nat.cast_sum]
    exact Finset.sum_congr rfl fun σ _ => (Nat.cast_prod _ _).symm
  have hmul : Real.sqrt ((Fintype.card V * N).choose k.val)
      * Real.sqrt ((Fintype.card V * N).choose k.val)
      = ((Fintype.card V * N).choose k.val : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hinv : (Real.sqrt ((Fintype.card V * N).choose k.val))⁻¹
        * ((Fintype.card V * N).choose k.val : ℝ)
      = Real.sqrt ((Fintype.card V * N).choose k.val) := by
    calc (Real.sqrt ((Fintype.card V * N).choose k.val))⁻¹
            * ((Fintype.card V * N).choose k.val : ℝ)
        = (Real.sqrt ((Fintype.card V * N).choose k.val))⁻¹
            * (Real.sqrt ((Fintype.card V * N).choose k.val)
              * Real.sqrt ((Fintype.card V * N).choose k.val)) := by rw [hmul]
      _ = Real.sqrt ((Fintype.card V * N).choose k.val) := by
          rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]
  rw [saturatedCoherentCoeff, EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, Pi.star_apply]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ), ← Finset.sum_filter, ← Finset.sum_mul,
    ← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.mul_sum, hfiber, hinv]

/-! ## The capstone -/

/-- **Tasaki Problem 2.4.c** (statement p. 34, solution p. 497, eq. (S.19)), *Physics and
Mathematics of Quantum Many-Body Systems*: the saturated-ferromagnet coherent state `Ξ_{θ,φ}` of
eq. (2.4.6), p. 33, expands in the magnetisation-sector ground states `Φ_M` of eq. (2.4.9), p. 33,
with the closed binomial coefficients

  `e^{-iMφ} √(binom (2S_max) (S_max − M)) cos(θ/2)^{S_max+M} sin(θ/2)^{S_max−M}`,

indexed here by the lowering count `k = S_max − M`, so that `2S_max = |Λ| N`,
`S_max + M = |Λ| N − k`, `S_max − M = k` and `M = ladderEigenvalueUp V N k`.

The statement holds for arbitrary real `θ` and `φ` and for general spin `S = N/2`; Tasaki states
Problem 2.4.c for `S = 1/2`, noting that a general spin can be represented by `S = 1/2` spins.
The azimuthal factor is `e^{-iMφ}`; see this module's header for the same-page evidence
((S.18), (S.17)) and the derivation from eqs. (2.4.6)/(2.2.11) that fixes this exponent. -/
theorem tasaki_problem_2_4_c_coherent_expansion [Nonempty V] (θ φ : ℝ) :
    saturatedCoherentState V N θ φ
      = ∑ k : Fin (Fintype.card V * N + 1),
          (Complex.exp (-((φ : ℂ) * Complex.I) * ladderEigenvalueUp V N k)
              * ((Real.sqrt ((Fintype.card V * N).choose k.val) : ℂ)
                  * (Real.cos (θ / 2) : ℂ) ^ (Fintype.card V * N - k.val)
                  * (Real.sin (θ / 2) : ℂ) ^ k.val))
            • saturatedWeightVector V N k := by
  rw [saturatedCoherentState_eq_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [saturatedCoherentCoeff_eq]

end LatticeSystem.Quantum
