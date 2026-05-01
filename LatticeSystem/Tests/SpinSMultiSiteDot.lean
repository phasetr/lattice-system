import LatticeSystem.Quantum.SpinS.MultiSiteDot

/-!
# Test coverage for the multi-site spin-`S` two-site dot product
(Tasaki §2.5 Phase B-β β-3c)
-/

namespace LatticeSystem.Tests.SpinSMultiSiteDot

open LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- Symmetry of the two-site dot product. -/
example (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N) = spinSDot y x N :=
  spinSDot_comm x y N

/-- Same-site Casimir: `Ŝ_x · Ŝ_x = (N(N+2)/4) · 1`. -/
example (x : Λ) (N : ℕ) :
    (spinSDot x x N : ManyBodyOpS Λ N) =
      ((N : ℂ) * (N + 2) / 4) • 1 :=
  spinSDot_self x N

/-- Raising/lowering decomposition `Ŝ_x · Ŝ_y =
    (1/2)(Ŝ_x^+ Ŝ_y^- + Ŝ_x^- Ŝ_y^+) + Ŝ_x^(3) Ŝ_y^(3)`. -/
example (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N) =
      (1 / 2 : ℂ) •
        (onSiteS x (spinSOpPlus N) * onSiteS y (spinSOpMinus N) +
          onSiteS x (spinSOpMinus N) * onSiteS y (spinSOpPlus N)) +
        onSiteS x (spinSOp3 N) * onSiteS y (spinSOp3 N) :=
  spinSDot_eq_plus_minus x y N

/-- Hermiticity of `Ŝ_x · Ŝ_y`. -/
example (x y : Λ) (N : ℕ) :
    (spinSDot x y N : ManyBodyOpS Λ N).IsHermitian :=
  spinSDot_isHermitian x y N

/-- Sum of same-site Casimirs. -/
example (N : ℕ) :
    (∑ x : Λ, spinSDot x x N : ManyBodyOpS Λ N) =
      ((Fintype.card Λ : ℂ) * ((N : ℂ) * (N + 2) / 4)) • 1 :=
  sum_spinSDot_self N

end LatticeSystem.Tests.SpinSMultiSiteDot
