import LatticeSystem.Quantum.SpinS.MultiSite

/-!
# Spin-`S` magnetization function on configurations
(Tasaki §2.5 Phase B-β β-4a)

For a spin parameter `N : ℕ` (with `N = 2S`) and a finite lattice `Λ`,
each configuration `σ : Λ → Fin (N + 1)` carries a **magnetization**
quantum number. We use the natural-number index sum

  `magSumS σ := Σ_{x : Λ} (σ x).val`

as the basic combinatorial quantity. The physical magnetic quantum
number is `(|Λ| · N / 2) − magSumS σ` (in units of `S`).

The magnetic-quantum-number range of `magSumS` is
`{0, 1, ..., |Λ| · N}`.

For spin-1/2 (`N = 1`), `magSumS σ = |{x : σ x = 1}|` is the
"down-spin count" and matches the existing spin-1/2 magnetization
encoding (`Quantum/MagnetizationSubspace.lean`).

Tracked in #412.
-/

namespace LatticeSystem.Quantum

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The magnetization-index sum of a spin-`S` configuration. -/
def magSumS (σ : Λ → Fin (N + 1)) : ℕ :=
  ∑ x : Λ, (σ x).val

omit [DecidableEq Λ] in
/-- `magSumS σ ≤ |Λ| · N`. -/
theorem magSumS_le (σ : Λ → Fin (N + 1)) :
    magSumS σ ≤ Fintype.card Λ * N := by
  unfold magSumS
  calc ∑ x : Λ, (σ x).val
      ≤ ∑ _ : Λ, N := by
        refine Finset.sum_le_sum ?_
        intro x _
        have := (σ x).isLt
        omega
    _ = Fintype.card Λ * N := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end LatticeSystem.Quantum
