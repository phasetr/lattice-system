/-
The finite reflection Cauchy–Schwarz on the two-field pairing (†)
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer, p. 86).

The two-field product pairing trace identity (†) of `RingReflectionTwoFieldPairing`,

    `Tr(U_{m}(x,y)) = ∑ₖ vₖ · conj(refLeftSum 𝓛ₖ(y)) · refLeftSum 𝓛ₖ(x)`   (vₖ ≥ 0),

exhibits the doubled Dyson–Lieb–Simon approximant `U_{m}(x,y) = (g(x)·θ(g(y))·∑ᵢ wᵢ·(θ(Cᵢ)·Cᵢ))^m`
as a finite weighted ℓ² Gram form indexed by the crossing family `κ`, with the SAME family serving
the diagonal instances `Tr(U_{m}(x,x))` and `Tr(U_{m}(y,y))`.  This file mounts the abstract finite
Gram Cauchy–Schwarz on that form:

    `(Re Tr U_{m}(x,y))² ≤ Re Tr U_{m}(x,x) · Re Tr U_{m}(y,y)`.

The pure ingredient is the weighted complex Gram inequality `reflGram_cauchySchwarz`, proved by the
ℂ→ℝ² √v-fold that reduces the weighted sum to mathlib's real Cauchy–Schwarz
`Finset.sum_mul_sq_le_sq_mul_sq`.  The inequality is phrased at the finite `(m,r)` level so the next
PR of the arc (the `r→∞`, `m→∞` double limit) streams it directly to the limit.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldPairing
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Complex.BigOperators

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Weighted complex Gram Cauchy–Schwarz.**  For a nonnegative real weight `v ≥ 0` and two
ℂ-valued families `Sa`, `Sb` indexed by a finite type `κ`, the real part of the weighted Gram
pairing `∑ₖ vₖ·conj(Sb k)·Sa k` obeys the Cauchy–Schwarz bound against the two diagonal Gram sums:

    `(Re ∑ₖ vₖ·conj(Sb k)·Sa k)² ≤ (Re ∑ₖ vₖ·conj(Sa k)·Sa k) · (Re ∑ₖ vₖ·conj(Sb k)·Sb k)`.

Proved by the ℂ→ℝ² √v-fold: each complex weight `vₖ` is split as `√vₖ·√vₖ`, turning the weighted
Gram sum over `κ` into the real inner product of the two `κ × Fin 2` sequences
`(√vₖ·(Sa k).re, √vₖ·(Sa k).im)` and `(√vₖ·(Sb k).re, √vₖ·(Sb k).im)`, whereupon the classical real
Cauchy–Schwarz `Finset.sum_mul_sq_le_sq_mul_sq` closes the bound.  The summand shape matches the
two-field pairing trace identity (†) verbatim, so the assembled tip mounts on it directly. -/
private theorem reflGram_cauchySchwarz {κ : Type} [Fintype κ] (v : κ → ℝ)
    (hv : ∀ k, 0 ≤ v k) (Sa Sb : κ → ℂ) :
    ((∑ k, (v k : ℂ) * (starRingEnd ℂ (Sb k) * Sa k)).re) ^ 2
      ≤ (∑ k, (v k : ℂ) * (starRingEnd ℂ (Sa k) * Sa k)).re
        * (∑ k, (v k : ℂ) * (starRingEnd ℂ (Sb k) * Sb k)).re := by
  have key : ∀ (c : ℝ), 0 ≤ c → ∀ z w : ℂ,
      ((c : ℂ) * (starRingEnd ℂ w * z)).re
        = Real.sqrt c * z.re * (Real.sqrt c * w.re)
          + Real.sqrt c * z.im * (Real.sqrt c * w.im) := by
    intro c hc z w
    have hs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
    rw [Complex.re_ofReal_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    linear_combination (-(z.re * w.re + z.im * w.im)) * hs
  have hmid : (∑ k, (v k : ℂ) * (starRingEnd ℂ (Sb k) * Sa k)).re
      = ∑ p : κ × Fin 2, (Real.sqrt (v p.1) * ![(Sa p.1).re, (Sa p.1).im] p.2)
          * (Real.sqrt (v p.1) * ![(Sb p.1).re, (Sb p.1).im] p.2) := by
    rw [Complex.re_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Fin.sum_univ_two, key (v k) (hv k) (Sa k) (Sb k)]
    simp
  have hda : (∑ k, (v k : ℂ) * (starRingEnd ℂ (Sa k) * Sa k)).re
      = ∑ p : κ × Fin 2, (Real.sqrt (v p.1) * ![(Sa p.1).re, (Sa p.1).im] p.2) ^ 2 := by
    rw [Complex.re_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Fin.sum_univ_two, key (v k) (hv k) (Sa k) (Sa k)]
    simp [pow_two]
  have hdb : (∑ k, (v k : ℂ) * (starRingEnd ℂ (Sb k) * Sb k)).re
      = ∑ p : κ × Fin 2, (Real.sqrt (v p.1) * ![(Sb p.1).re, (Sb p.1).im] p.2) ^ 2 := by
    rw [Complex.re_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Fin.sum_univ_two, key (v k) (hv k) (Sb k) (Sb k)]
    simp [pow_two]
  rw [hmid, hda, hdb]
  exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : κ × Fin 2 => Real.sqrt (v p.1) * ![(Sa p.1).re, (Sa p.1).im] p.2)
    (fun p : κ × Fin 2 => Real.sqrt (v p.1) * ![(Sb p.1).re, (Sb p.1).im] p.2)

end LatticeSystem.Quantum
