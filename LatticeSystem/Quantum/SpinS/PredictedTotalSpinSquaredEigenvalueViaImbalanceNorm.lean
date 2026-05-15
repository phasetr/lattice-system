import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightNormEqRe

/-!
# Predicted `(Ŝ_tot)²` eigenvalue in `‖biw‖` form

The predicted ground-state `(Ŝ_tot)²` eigenvalue from
`bipartiteToyGroundStateSubspacePredicted A N` is
`(s_A − s_B)·((s_A − s_B) + 1)` where `s_A = |A|·N/2`,
`s_B = |¬A|·N/2`.

Under the orientation `|¬A| ≤ |A|`, we have `s_A − s_B = (|A|−|¬A|)·N/2
= (biw.re : ℝ) = ‖biw‖` (since `biw.re ≥ 0` under this orientation,
PR #2862). Hence the predicted eigenvalue is identified with the
imbalance norm:

  `(s_A − s_B)·((s_A − s_B) + 1) = ‖biw‖·(‖biw‖ + 1)`   (as ℝ).

Tasaki §2.5 Theorem 2.3's "predicted total spin magnitude squared
plus that magnitude" is literally the imbalance-norm squared plus
the imbalance norm, with the imbalance norm playing the role of
the predicted spin magnitude `S_tot = ||A|−|¬A||·S`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Predicted `(Ŝ_tot)²` eigenvalue real form via `‖biw‖`** at
`|¬A| ≤ |A|`: the predicted eigenvalue `(s_A − s_B)·((s_A − s_B) + 1)`
equals `‖biw‖·(‖biw‖ + 1)` as a real number. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_norm_quad
    (A : Λ → Bool) (N : ℕ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
        (Finset.univ.filter (fun x : Λ => A x = true)).card) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ +
        ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ := by
  have hbiw :=
    bipartiteImbalanceWeight_norm_eq_re_of_cardNotA_le_cardA A N horient
  rw [bipartiteImbalanceWeight_re_eq] at hbiw
  -- hbiw : ‖biw‖ = (|A| - |¬A|) · N / 2  (as a real number)
  set a : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set b : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  set Nr : ℝ := (N : ℝ)
  set biw : ℝ := ‖bipartiteImbalanceWeight (Λ := Λ) A N‖
  -- hbiw_form : biw = (a - b) * (Nr / 2)
  have hbiw_form : biw = (a - b) * (Nr / 2) := hbiw
  -- Reduce the LHS to a real expression and apply hbiw_form.
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
    Complex.one_im, Complex.natCast_re, Complex.natCast_im]
  -- All Complex.{div,mul}_im of natCast / Nat-cast pieces are 0.
  -- LHS becomes ((a - b)·(Nr/2)) · ((a - b)·(Nr/2) + 1).
  rw [hbiw_form]
  ring
end LatticeSystem.Quantum
