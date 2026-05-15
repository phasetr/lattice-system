import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmViaImbalance
import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightAbs

/-!
# Symm-energy real part via `‖bipartiteImbalanceWeight‖²`

PR #2876 established the algebraic bridge identity

  `(symm.re + min·N) · 8 + |Λ|²·N² = 4·(biw.re)²`.

Because `bipartiteImbalanceWeight A N` is real (PR #2825,
`bipartiteImbalanceWeight_im_zero`), its norm equals the absolute
value of its real part and hence

  `‖biw‖ · ‖biw‖ = biw.re · biw.re`.

Substituting yields a cleaner form using the predicted spin
magnitude `‖biw‖ = ||A| − |¬A||·N/2`:

  `(symm.re + min·N) · 8 + |Λ|²·N² = 4·‖biw‖²`.

This is the natural form for Tasaki §2.5 Theorem 2.3 (γ-4): the
predicted ground-state energy and the predicted spin magnitude
are linked by a constraint involving the lattice cardinality
alone.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Norm-squared of `bipartiteImbalanceWeight` equals real-part
squared**: since `bipartiteImbalanceWeight A N` is real (im = 0),
`‖biw‖ · ‖biw‖ = biw.re · biw.re`. -/
theorem bipartiteImbalanceWeight_norm_mul_self_eq_re_mul_self :
    ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        (bipartiteImbalanceWeight (Λ := Λ) A N).re := by
  rw [bipartiteImbalanceWeight_eq_ofReal, Complex.norm_real,
      Real.norm_eq_abs, Complex.ofReal_re, abs_mul_abs_self]

/-- **Bridge identity in `‖biw‖²` form**:
`(symm.re + min(|A|, |¬A|)·N) · 8 + |Λ|²·N² = 4·‖biw‖²`.

Substitutes `(biw.re)² = ‖biw‖²` into the PR #2876 bridge,
giving the natural form for Tasaki §2.5 Theorem 2.3 where the
predicted spin magnitude `‖biw‖ = ||A| − |¬A||·N/2` appears
directly. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_sq :
    ((bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re +
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ)) * 8 +
      (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) * ((N : ℝ) * (N : ℝ)) =
      4 *
        (‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖) := by
  rw [bipartiteImbalanceWeight_norm_mul_self_eq_re_mul_self]
  exact bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_sq A N

end LatticeSystem.Quantum
