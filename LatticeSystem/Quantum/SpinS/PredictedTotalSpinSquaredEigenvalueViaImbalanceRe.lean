import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# Unified signed-form predicted `(Ŝ_tot)²` eigenvalue: `biw.re · (biw.re + 1)`

The predicted `(Ŝ_tot)²` eigenvalue from
`bipartiteToyGroundStateSubspacePredicted A N` is
`(s_A − s_B)·((s_A − s_B) + 1)` where `s_A = |A|·N/2`,
`s_B = |¬A|·N/2`. The signed difference

  `s_A − s_B = (|A| − |¬A|)·N/2 = (bipartiteImbalanceWeight A N).re`

(PR #2825 `bipartiteImbalanceWeight_re_eq`). Hence the predicted
eigenvalue real form is

  `((s_A − s_B)·((s_A − s_B) + 1)).re = biw.re · (biw.re + 1)`

**without any orientation hypothesis**. This is the "signed" form
of the eigenvalue, with PR #2930 (`‖biw‖·(‖biw‖+1)`) and PR #2931
(complement) being orientation-specialised consequences via
`biw.re = ±‖biw‖`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

/-- **Unified signed-form predicted `(Ŝ_tot)²` eigenvalue** without
orientation hypothesis: `((s_A − s_B)·((s_A − s_B) + 1)).re = biw.re · (biw.re + 1)`. -/
theorem bipartiteToyGroundStateSubspacePredicted_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad
    (A : Λ → Bool) (N : ℕ) :
    ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        ((bipartiteImbalanceWeight (Λ := Λ) A N).re + 1) := by
  rw [bipartiteImbalanceWeight_re_eq]
  set a : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set b : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
    Complex.one_im, Complex.natCast_re, Complex.natCast_im]
  ring

end LatticeSystem.Quantum
