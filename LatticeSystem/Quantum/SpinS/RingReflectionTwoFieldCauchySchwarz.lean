/-
The two-field reflection Cauchy–Schwarz on the doubled Gibbs weight `W(a,b)` via a double limit
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer; (4.1.51), pp. 89–93; DLS 1978 §2–3).

Streaming the finite `(m,r)` reflection Cauchy–Schwarz of `RingReflectionTwoFieldConeCauchySchwarz`
(`twoField_product_pairing_cauchySchwarz`) to the doubled Gibbs weight `W(a,b) =
ringTwoFieldWeight n N β a b` requires a genuinely NESTED double limit: the Dyson–Lieb–Simon Trotter
approximant `T_m(x,y) = (E_G(x)·θ(E_G(y))·exp((β/m)·D))^m` carries the crossing factor as the
exponential `exp((β/m)·D)`, which is NOT a finite cone but only the `r → ∞` limit of the cone partial
sums `S_r = ∑_{k<r}(k!)⁻¹•((β/m)·D)ᵏ`.  So one first closes `r → ∞` (exp-of-cone) to lift the finite
Cauchy–Schwarz from `U_{m,r}` to `T_m` (`twoField_pairing_cauchySchwarz_exp`), then `m → ∞` (Trotter,
`ringTwoFieldWeight_isLimit`) to reach `W`.  Both limit passages reuse the abstract limit-preserving
Cauchy–Schwarz `cauchySchwarz_of_tendsto`.  The field-free crossing interaction `D`
(`ringFieldDLSDecomposition_interaction_eq`) aligns the `(b,b)` slot, whose isLimit carries `D_b`
while the per-`m` fact produces `D_a`.  The hypothesis `0 ≤ β` is needed for cone positivity of the
crossing factor (isLimit itself needs no sign hypothesis).

This file records the capstone `ringTwoFieldWeight_reflection_cauchySchwarz`: the finite-β matrix
form of Tasaki's reflection bound (4.1.51),
`(Re Tr W(a,b))² ≤ Re Tr W(a,a) · Re Tr W(b,b)`.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldWeight
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldConeCauchySchwarz
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed

namespace LatticeSystem.Quantum

open Matrix Filter Topology

variable {n N : ℕ}

/-- **Limit-preserving Cauchy–Schwarz** (pure topology).  Along any nontrivial filter `l`, if the
three real sequences `pxy`, `pxx`, `pyy` converge to `axy`, `axx`, `ayy` and satisfy the pointwise
Cauchy–Schwarz bound `(pxy i)² ≤ pxx i · pyy i`, then the limits obey `axy² ≤ axx · ayy`.  Proved by
`le_of_tendsto_of_tendsto'` on the squared left-hand side (`Tendsto.pow`) against the product
right-hand side (`Tendsto.mul`).  Used twice in the double limit of Tasaki (4.1.51) (pp. 89–93; DLS
1978 §2–3): once for the inner `r → ∞` (exp-of-cone) passage and once for the outer `m → ∞`
(Trotter) passage. -/
private theorem cauchySchwarz_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {pxy pxx pyy : ι → ℝ} {axy axx ayy : ℝ}
    (hxy : Tendsto pxy l (𝓝 axy)) (hxx : Tendsto pxx l (𝓝 axx)) (hyy : Tendsto pyy l (𝓝 ayy))
    (hCS : ∀ i, (pxy i) ^ 2 ≤ pxx i * pyy i) : axy ^ 2 ≤ axx * ayy :=
  le_of_tendsto_of_tendsto' (hxy.pow 2) (hxx.mul hyy) hCS

/-- **Field-independence of the crossing interaction.**  The crossing interaction of the
field-augmented DLS decomposition does not depend on the field argument:
`(ringFieldDLSDecomposition a).interaction = (ringFieldDLSDecomposition b).interaction`.  Both equal
the field-free sum of the two gauged crossing-bond interactions
(`ringCrossingRPDecomposition_interaction`).  Needed to align the `(b,b)` slot of the double limit
of Tasaki (4.1.51) (pp. 89–93): `isLimit(a,b)`/`isLimit(a,a)` carry `D_a` while `isLimit(b,b)`
carries `D_b`, so the per-`m` fact's third slot is rewritten `D_a → D_b`. -/
private theorem ringFieldDLSDecomposition_interaction_eq (n N : ℕ) [NeZero n]
    (a b : Fin (2 * n) → ℝ) :
    (ringFieldDLSDecomposition n N a).interaction
      = (ringFieldDLSDecomposition n N b).interaction := by
  rw [ringFieldDLSDecomposition, ringFieldDLSDecomposition,
    ringCrossingRPDecomposition_interaction, ringCrossingRPDecomposition_interaction]

end LatticeSystem.Quantum
