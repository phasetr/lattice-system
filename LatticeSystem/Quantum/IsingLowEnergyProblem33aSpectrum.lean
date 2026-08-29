import LatticeSystem.Quantum.IsingLowEnergyProblem33aEigenvectors
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The infinite-chain decay rate `κ∞` of Tasaki Problem 3.3.a

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a (statement p. 59,
solution pp. 498-501) lets `L ↑ ∞` in the root equation (S.34) of
`LatticeSystem/Quantum/IsingLowEnergyProblem33aEigenvectors.lean`: its right-hand side becomes
`λ⁻¹`, the two parity sectors share one decay rate, and that rate `κ∞` solves

* (S.35), p. 500: `e^κ∞ - e^-κ∞ = λ⁻¹`.

The left-hand side is `2 sinh κ∞`, so `kappaInf λ = arsinh (1 / (2λ))`, and the eigenvalue (S.31)
`tightBindingEnergy` evaluated at it is the source's `ε∞`:

* (S.39), p. 501: `ε∞ = -(λ/2)(e^κ∞ + e^-κ∞) + 1/2 = -√(1 + 4λ²)/2 + 1/2`.

`tightBindingEnergy_kappaInf_eq` is that middle equality, in the radical form printed on p. 501.
The trailing `≃ -λ²` of (S.39) is a small-`λ` approximation and is not asserted. `tanh_kappaInf_eq`
records `tanh κ∞ = 1/√(1 + 4λ²)`, which is the ratio `(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)` carried by
(S.40) and (S.41), and the two `Tendsto` statements record the small-`λ` replacements
`e^-κ∞ ≃ λ` (p. 500, below (S.35)) and `tanh κ∞ ≃ 1` behind the final form `≃ 2 λ^L` of (S.41).

`tightBindingEnergy λ κ` is an eigenvalue of the compression `lowEnergyMatrix N λ` only after the
shift by `E_GS^(0) = -N/4`; on its own it is an eigenvalue of the tight-binding part
`tightBindingRing N λ`. That the compression restricts `Ĥ` to an invariant subspace is not
established here, so `ε∞` is the `L ↑ ∞` value of such an eigenvalue and is not identified with a
ground-state or first-excited energy of `Ĥ`; the source's non-rigorous Taylor steps (S.36)-(S.38)
are not asserted. Tasaki notes on p. 59 that the perturbative analysis of this problem is not
mathematically rigorous.
-/

namespace LatticeSystem.Quantum

/-! ### The `L ↑ ∞` decay rate -/

/-- Tasaki eq. (S.35), p. 500: the decay rate `κ∞` of the `L ↑ ∞` limit of the root equation
(S.34), i.e. the solution of `e^κ∞ - e^-κ∞ = λ⁻¹`. The left-hand side being `2 sinh κ∞`, the
solution is `arsinh (1 / (2λ))`. -/
noncomputable def kappaInf (lam : ℝ) : ℝ := Real.arsinh (1 / (2 * lam))

/-- The radical that the `arsinh` API produces at the argument `1 / (2λ)`, rewritten as
`√(1 + 4λ²) / (2λ)`, the form in which Tasaki eq. (S.39) prints it. The hypothesis `0 < λ` is what
allows `2λ` to leave the square root with a positive sign. -/
private theorem sqrt_one_add_inv_two_mul_sq {lam : ℝ} (hlam : 0 < lam) :
    Real.sqrt (1 + (1 / (2 * lam)) ^ 2) = Real.sqrt (1 + 4 * lam ^ 2) / (2 * lam) := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hne : (2 : ℝ) * lam ≠ 0 := ne_of_gt h2
  have hx : (1 : ℝ) + (1 / (2 * lam)) ^ 2 = (1 + 4 * lam ^ 2) / (2 * lam) ^ 2 := by
    field_simp
    ring
  rw [hx, Real.sqrt_div (by positivity) ((2 * lam) ^ 2), Real.sqrt_sq (le_of_lt h2)]

/-- The decay rate is positive for a positive transverse field, matching the source's choice
`κ > 0` below eq. (S.30), p. 499. -/
theorem kappaInf_pos {lam : ℝ} (hlam : 0 < lam) : 0 < kappaInf lam := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  exact Real.arsinh_pos_iff.mpr (div_pos one_pos h2)

/-- Tasaki eq. (S.35), p. 500: `e^κ∞ - e^-κ∞ = λ⁻¹`. -/
theorem exp_kappaInf_sub_exp_neg {lam : ℝ} (hlam : 0 < lam) :
    Real.exp (kappaInf lam) - Real.exp (-(kappaInf lam)) = lam⁻¹ := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hsinh : Real.sinh (kappaInf lam) = 1 / (2 * lam) := Real.sinh_arsinh _
  have h : Real.exp (kappaInf lam) - Real.exp (-(kappaInf lam))
      = 2 * Real.sinh (kappaInf lam) := by
    rw [Real.sinh_eq]
    ring
  rw [h, hsinh]
  field_simp

/-- The closed radical form of `e^-κ∞`, namely `2λ / (1 + √(1 + 4λ²))`. It is the reciprocal of
`e^κ∞ = (1 + √(1 + 4λ²)) / (2λ)`, the value the `arsinh` API gives at `1 / (2λ)`. -/
theorem exp_neg_kappaInf_eq {lam : ℝ} (hlam : 0 < lam) :
    Real.exp (-(kappaInf lam)) = 2 * lam / (1 + Real.sqrt (1 + 4 * lam ^ 2)) := by
  have hexp : Real.exp (kappaInf lam)
      = 1 / (2 * lam) + Real.sqrt (1 + (1 / (2 * lam)) ^ 2) := Real.exp_arsinh _
  rw [Real.exp_neg, hexp, sqrt_one_add_inv_two_mul_sq hlam, ← add_div, inv_div]

/-! ### The limiting eigenvalue (S.39) -/

/-- Tasaki eq. (S.39), p. 501, middle equality: the `L ↑ ∞` value of the tight-binding eigenvalue
(S.31) — an eigenvalue of the compressed matrix only after the shift by `E_GS^(0)` — is
`ε∞ = -(λ/2)(e^κ∞ + e^-κ∞) + 1/2 = -√(1 + 4λ²)/2 + 1/2`. The trailing `≃ -λ²` of the printed
equation is a small-`λ` approximation and is not part of this statement. -/
theorem tightBindingEnergy_kappaInf_eq {lam : ℝ} (hlam : 0 < lam) :
    tightBindingEnergy lam (kappaInf lam) = (1 - Real.sqrt (1 + 4 * lam ^ 2)) / 2 := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hcosh : Real.cosh (kappaInf lam)
      = Real.sqrt (1 + (1 / (2 * lam)) ^ 2) := Real.cosh_arsinh _
  have hsum : Real.exp (kappaInf lam) + Real.exp (-(kappaInf lam))
      = Real.sqrt (1 + 4 * lam ^ 2) / lam := by
    have h : Real.exp (kappaInf lam) + Real.exp (-(kappaInf lam))
        = 2 * Real.cosh (kappaInf lam) := by
      rw [Real.cosh_eq]
      ring
    rw [h, hcosh, sqrt_one_add_inv_two_mul_sq hlam]
    field_simp
  unfold tightBindingEnergy
  rw [hsum]
  field_simp
  ring

/-- `tanh κ∞ = 1/√(1 + 4λ²)`, i.e. the ratio `(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)` that Tasaki
eqs. (S.40) and (S.41), p. 501, carry in front of `e^-κ∞L`. -/
theorem tanh_kappaInf_eq {lam : ℝ} (hlam : 0 < lam) :
    Real.tanh (kappaInf lam) = (Real.sqrt (1 + 4 * lam ^ 2))⁻¹ := by
  have h2 : (0 : ℝ) < 2 * lam := by linarith
  have hne2 : (2 : ℝ) * lam ≠ 0 := ne_of_gt h2
  have hnes : Real.sqrt (1 + 4 * lam ^ 2) ≠ 0 := by positivity
  have htanh : Real.tanh (kappaInf lam)
      = 1 / (2 * lam) / Real.sqrt (1 + (1 / (2 * lam)) ^ 2) := Real.tanh_arsinh _
  rw [htanh, sqrt_one_add_inv_two_mul_sq hlam]
  field_simp

/-! ### The two small-`λ` replacements of (S.41) -/

/-- Tasaki, p. 500, below eq. (S.35): "Because `0 < λ ≪ 1`, we have `e^κ∞ ≃ λ⁻¹`", i.e.
`e^-κ∞ / λ → 1` as `λ ↓ 0`. This is one of the two replacements behind the final form
`E_1st - E_GS ≃ 2 λ^L` of eq. (S.41), p. 501. -/
theorem tendsto_exp_neg_kappaInf_div_atZero :
    Filter.Tendsto (fun l : ℝ => Real.exp (-(kappaInf l)) / l)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hcont : Continuous (fun l : ℝ => 2 / (1 + Real.sqrt (1 + 4 * l ^ 2))) :=
    continuous_const.div
      (continuous_const.add
        ((continuous_const.add (continuous_const.mul (continuous_pow 2))).sqrt))
      (fun _ => by positivity)
  have hval : (2 : ℝ) / (1 + Real.sqrt (1 + 4 * (0 : ℝ) ^ 2)) = 1 := by norm_num
  have h : Filter.Tendsto (fun l : ℝ => 2 / (1 + Real.sqrt (1 + 4 * l ^ 2))) (nhds 0)
      (nhds ((2 : ℝ) / (1 + Real.sqrt (1 + 4 * (0 : ℝ) ^ 2)))) := hcont.tendsto 0
  rw [hval] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr'
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_)
  intro l hl
  have hl' : (0 : ℝ) < l := hl
  have hlne : l ≠ 0 := ne_of_gt hl'
  change (2 : ℝ) / (1 + Real.sqrt (1 + 4 * l ^ 2)) = Real.exp (-(kappaInf l)) / l
  rw [exp_neg_kappaInf_eq hl']
  field_simp

/-- `tanh κ∞ → 1` as `λ ↓ 0`, the second replacement behind the final form
`E_1st - E_GS ≃ 2 λ^L` of Tasaki eq. (S.41), p. 501. -/
theorem tendsto_tanh_kappaInf_atZero :
    Filter.Tendsto (fun l : ℝ => Real.tanh (kappaInf l))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsq : Continuous (fun l : ℝ => Real.sqrt (1 + 4 * l ^ 2)) :=
    (continuous_const.add (continuous_const.mul (continuous_pow 2))).sqrt
  have hne : ∀ l : ℝ, Real.sqrt (1 + 4 * l ^ 2) ≠ 0 := fun l =>
    Real.sqrt_ne_zero'.mpr (by positivity)
  have hcont : Continuous (fun l : ℝ => (Real.sqrt (1 + 4 * l ^ 2))⁻¹) := hsq.inv₀ hne
  have hval : (Real.sqrt (1 + 4 * (0 : ℝ) ^ 2))⁻¹ = 1 := by norm_num
  have h : Filter.Tendsto (fun l : ℝ => (Real.sqrt (1 + 4 * l ^ 2))⁻¹) (nhds 0)
      (nhds ((Real.sqrt (1 + 4 * (0 : ℝ) ^ 2))⁻¹)) := hcont.tendsto 0
  rw [hval] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr'
    (Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_)
  intro l hl
  have hl' : (0 : ℝ) < l := hl
  change (Real.sqrt (1 + 4 * l ^ 2))⁻¹ = Real.tanh (kappaInf l)
  exact (tanh_kappaInf_eq hl').symm

end LatticeSystem.Quantum
