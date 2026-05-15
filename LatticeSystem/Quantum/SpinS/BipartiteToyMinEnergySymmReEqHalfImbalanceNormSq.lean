import LatticeSystem.Quantum.SpinS.BipartiteToyMinEnergySymmReViaImbalanceNormSq

/-!
# Explicit form: `symm.re = ‖biw‖² / 2 − |Λ|²·N² / 8 − min·N`

PR #2877 proved the bridge identity in $\|\mathrm{biw}\|^2$ form:

  `8 · (symm.re + min·N) + |Λ|²·N² = 4 · ‖biw‖²`.

Dividing by `8` and isolating `symm.re` yields the closed form

  `(bipartiteToyMinEnergyPredictedSymm A N).re
     = ‖bipartiteImbalanceWeight A N‖² / 2 − |Λ|²·N²/8 − min(|A|, |¬A|)·N`.

This expresses the predicted symmetric ground-state energy as a
function of three quantities: the predicted spin magnitude squared
`‖biw‖²`, the lattice cardinality `|Λ|`, and the minor sublattice
count `min(|A|, |¬A|)`.

The form is convenient for Tasaki §2.5 Theorem 2.3 (γ-4): for
balanced sublattices (`‖biw‖ = 0`) the energy is
`−|Λ|²·N²/8 − |Λ|·N/4` (matching the symmetric balanced GS
prediction), while saturated edges (`‖biw‖ = |Λ|·N/2`) give
`+|Λ|²·N²/8 − |Λ|²·N²/8 = 0` (matching the saturated GS
prediction with `min = 0`).

Tracked as part of Tasaki §2.5 Theorem 2.3 / γ-4 (Issue #412).
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] (A : Λ → Bool) (N : ℕ)

/-- **Explicit closed form of `bipartiteToyMinEnergyPredictedSymm A N`
real part**:

`(symm).re = ‖biw‖² / 2 − |Λ|²·N²/8 − min(|A|, |¬A|)·N`.

Direct corollary of the bridge identity (PR #2877). -/
theorem bipartiteToyMinEnergyPredictedSymm_re_eq_half_imbalance_norm_sq_sub :
    (bipartiteToyMinEnergyPredictedSymm (Λ := Λ) A N).re =
      ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ *
          ‖bipartiteImbalanceWeight (Λ := Λ) A N‖ / 2 -
        (Fintype.card Λ : ℝ) * (Fintype.card Λ : ℝ) *
            ((N : ℝ) * (N : ℝ)) / 8 -
        min ((Finset.univ.filter (fun x : Λ => A x = true)).card : ℝ)
            ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) *
          (N : ℝ) := by
  have h := bipartiteToyMinEnergyPredictedSymm_re_via_imbalance_norm_sq
    (Λ := Λ) A N
  linarith

end LatticeSystem.Quantum
