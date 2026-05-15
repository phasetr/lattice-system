import LatticeSystem.Quantum.SpinS.BipartiteImbalanceWeightImZero

/-!
# Unified signed-form complement predicted `(Ŝ_tot)²` eigenvalue: `biw.re · (biw.re − 1)`

The complement-orientation predicted `(Ŝ_tot)²` eigenvalue uses
`(s_B − s_A)·((s_B − s_A) + 1)` where `s_A = |A|·N/2`,
`s_B = |¬A|·N/2`. Since `s_B − s_A = −(s_A − s_B) = −biw`, we get
`(s_B − s_A).re = −biw.re`. Hence

  `((s_B − s_A)·((s_B − s_A) + 1)).re = (−biw.re)·((−biw.re) + 1)
     = biw.re·(biw.re − 1)`

**without any orientation hypothesis**. Mirror of PR #2932 for the
complement form. PR #2931's `‖biw‖·(‖biw‖+1)` form is an
orientation-specialised consequence at `|A| ≤ |¬A|` (where
`biw.re ≤ 0` so `-biw.re = ‖biw‖`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ]

set_option linter.style.longLine false in
/-- **Unified signed-form complement predicted `(Ŝ_tot)²` eigenvalue**
without orientation hypothesis:
`((s_B − s_A)·((s_B − s_A) + 1)).re = biw.re·(biw.re − 1)`. -/
theorem bipartiteToyGroundStateSubspacePredicted_complement_totalSpinSSquared_eigenvalue_re_eq_imbalance_re_quad_signed
    (A : Λ → Bool) (N : ℕ) :
    ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
            ((N : ℂ) / 2) -
          ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
            ((N : ℂ) / 2)) *
        ((((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℂ) *
              ((N : ℂ) / 2) -
            ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℂ) *
              ((N : ℂ) / 2)) + 1)).re =
      (bipartiteImbalanceWeight (Λ := Λ) A N).re *
        ((bipartiteImbalanceWeight (Λ := Λ) A N).re - 1) := by
  rw [bipartiteImbalanceWeight_re_eq]
  set a : ℝ := ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
  set b : ℝ := ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.one_re,
    Complex.one_im, Complex.natCast_re, Complex.natCast_im]
  ring

end LatticeSystem.Quantum
