import LatticeSystem.Math.PosSemidef.Kernel
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Connected-support dichotomy for PSD matrices (Tasaki Lemma 10.10)

Final abstract step (PIECE 3) of Tasaki Lemma 10.10. Given a positive-semidefinite `R`
whose kernel is invariant under a Hermitian `A` and is a **coordinate subspace** (the
basis-extraction property from `basis_mem_ker_of_separating_projections`), if the support
graph of `A` is connected then `R` is **positive definite or zero**.

The mechanism: a single basis vector `δ_a ∈ ker R` propagates along every edge of the
support graph (`R δ_a = 0 ⟹ R(A δ_a) = 0`, and basis extraction on `A δ_a` puts every
neighbour `δ_b` into the kernel). Connectivity then forces either *no* basis vector in the
kernel — whence `ker R` is trivial and `R` positive definite — or *all* of them, whence
`R = 0`.

## Main result

* `posDef_or_eq_zero_of_connected_support` — `R.PosDef ∨ R = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemma 10.10), pp. 363–367.
-/

namespace LatticeSystem.Math

open Matrix
open scoped BigOperators ComplexOrder

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- **Connected-support dichotomy.** Let `R` be positive semidefinite with kernel
invariant under `A` (`R v = 0 ⟹ R (A v) = 0`) and a coordinate subspace
(`R v = 0`, `v a ≠ 0 ⟹ R δ_a = 0`). If `G` is a connected graph whose every edge `b ~ a`
witnesses a nonzero entry `A b a`, then `R` is positive definite or zero. -/
theorem posDef_or_eq_zero_of_connected_support
    {R A : Matrix S S ℂ} (hR : R.PosSemidef)
    (hAinv : ∀ v : S → ℂ, R.mulVec v = 0 → R.mulVec (A.mulVec v) = 0)
    (hbasis : ∀ v : S → ℂ, R.mulVec v = 0 → ∀ a, v a ≠ 0 → R.mulVec (Pi.single a 1) = 0)
    {G : SimpleGraph S} (hGadj : ∀ b a, G.Adj b a → A b a ≠ 0) (hGconn : G.Preconnected) :
    R.PosDef ∨ R = 0 := by
  -- One-step propagation of `δ ∈ ker R` along an edge.
  have prop : ∀ a, R.mulVec (Pi.single a 1) = 0 → ∀ b, A b a ≠ 0
      → R.mulVec (Pi.single b 1) = 0 := by
    intro a ha b hba
    refine hbasis _ (hAinv _ ha) b ?_
    have hbe : A.mulVec (Pi.single a 1) b = A b a := by
      change A b ⬝ᵥ Pi.single a 1 = A b a
      rw [dotProduct_single, mul_one]
    rwa [hbe]
  -- Propagation along any walk from a kernel basis vertex.
  have walk_prop : ∀ {u w : S}, G.Walk u w → R.mulVec (Pi.single u 1) = 0
      → R.mulVec (Pi.single w 1) = 0 := by
    intro u w p
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hu => ih (prop _ hu _ (hGadj _ _ hadj.symm))
  by_cases hker : ∃ a, R.mulVec (Pi.single a 1) = 0
  · -- A basis vector lies in the kernel: connectivity spreads it to all, so `R = 0`.
    obtain ⟨a₀, ha₀⟩ := hker
    have hall : ∀ b, R.mulVec (Pi.single b 1) = 0 := fun b =>
      walk_prop (hGconn a₀ b).some ha₀
    refine Or.inr ?_
    ext i j
    have hbe : R.mulVec (Pi.single j 1) i = R i j := by
      change R i ⬝ᵥ Pi.single j 1 = R i j
      rw [dotProduct_single, mul_one]
    have hcol := congrFun (hall j) i
    rw [hbe, Pi.zero_apply] at hcol
    rw [Matrix.zero_apply]; exact hcol
  · -- No basis vector in the kernel ⟹ trivial kernel ⟹ positive definite.
    push Not at hker
    refine Or.inl (Matrix.PosDef.of_dotProduct_mulVec_pos hR.1 (fun {x} hx => ?_))
    rcases lt_or_eq_of_le (hR.dotProduct_mulVec_nonneg x) with hlt | heq
    · exact hlt
    · exfalso
      have hRx : R.mulVec x = 0 := posSemidef_mulVec_eq_zero_of_inner_zero hR heq.symm
      obtain ⟨a, hxa⟩ := Function.ne_iff.mp hx
      exact hker a (hbasis x hRx a (by simpa using hxa))

end LatticeSystem.Math
