import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymm

/-!
# `bipartiteToyMinEnergyPredictedSymm` is real

The symmetric predicted toy-Hamiltonian minimum energy
`bipartiteToyMinEnergyPredictedSymm A N
   = -|A|·|¬A|·N²/2 - min(|A|, |¬A|)·N`
is a real number lifted to `ℂ`. This file pins down both the
imaginary-part-zero and the real-part-explicit corollaries,
mirroring the asymmetric forms in
`BipartiteImbalanceWeightImZero.lean`.

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **`bipartiteToyMinEnergyPredictedSymm` is purely real**:
`(bipartiteToyMinEnergyPredictedSymm A N).im = 0`. -/
theorem bipartiteToyMinEnergyPredictedSymm_im_zero :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).im = 0 := by
  unfold bipartiteToyMinEnergyPredictedSymm
  simp only [Complex.sub_im, Complex.neg_im, Complex.div_ofNat_im,
    Complex.mul_im, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, Nat.cast_min]
  ring

/-- **Real part of `bipartiteToyMinEnergyPredictedSymm`** as a real
expression: equals the real-axis closed form
`-|A|·|¬A|·N²/2 - min(|A|, |¬A|)·N`. -/
theorem bipartiteToyMinEnergyPredictedSymm_re_eq :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      -(((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ) *
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          ((N : ℝ) * (N : ℝ)) / 2) -
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
          ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) := by
  unfold bipartiteToyMinEnergyPredictedSymm
  simp only [Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
    Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, Nat.cast_min]
  ring

end LatticeSystem.Quantum
