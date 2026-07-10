/-
The two-field reflection Cauchy–Schwarz on the doubled Gibbs weight `W(a,b)` via a double limit
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer; (4.1.51), pp. 89–93; DLS 1978 §2–3).

Streaming the finite `(m,r)` reflection Cauchy–Schwarz of `RingReflectionTwoFieldConeCauchySchwarz`
(`twoField_product_pairing_cauchySchwarz`) to the doubled Gibbs weight `W(a,b) =
ringTwoFieldWeight n N β a b` requires a genuinely NESTED double limit: the Dyson–Lieb–Simon Trotter
approximant `T_m(x,y) = (E_G(x)·θ(E_G(y))·exp((β/m)·D))^m` carries the crossing factor as the
exponential `exp((β/m)·D)`, which is NOT a finite cone but only the `r → ∞` limit of the cone
partial sums `S_r = ∑_{k<r}(k!)⁻¹•((β/m)·D)ᵏ`.  So one first closes `r → ∞` (exp-of-cone) to lift
the finite Cauchy–Schwarz from `U_{m,r}` to `T_m` (`twoField_pairing_cauchySchwarz_exp`), then
`m → ∞` (Trotter, `ringTwoFieldWeight_isLimit`) to reach `W`.  Both passages reuse the
limit-preserving
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

open scoped Matrix.Norms.Operator

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

/-- **Per-`m` reflection Cauchy–Schwarz with an exponential crossing factor** (the `r → ∞`
passage).  For the Dyson–Lieb–Simon per-`m` approximant `T_m(x,y) = (g(x)·θ(g(y))·exp P)^m` — with
left-supported kinetic family `g` and cone-representable `P` — the real part of the trace pairing
obeys `(Re Tr T_m(x,y))² ≤ Re Tr T_m(x,x) · Re Tr T_m(y,y)`.  Obtained by closing the inner limit
`r → ∞` of the finite `(m,r)` Cauchy–Schwarz `twoField_product_pairing_cauchySchwarz`: for each `r`
the crossing partial sum `S_r = ∑_{k<r}(k!)⁻¹•Pᵏ` is a literal finite cone
(`RPTraceConeRepS.expSeriesPartialSum`), and `S_r → exp P` (`NormedSpace.exp_eq_tsum`), so
`cauchySchwarz_of_tendsto` streams the per-`r` inequality to the exponential.  This is the inner
limit of the double limit of Tasaki (4.1.51) (pp. 89–93; DLS 1978 §2–3). -/
private theorem twoField_pairing_cauchySchwarz_exp (m : ℕ)
    (g : (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N)
    (hg : ∀ z, SupportedOnLeftS n N (g z)) {P : ManyBodyOpS (Fin (2 * n)) N}
    (hP : RPTraceConeRepS n N P) (x y : Fin (2 * n) → ℝ) :
    (((g x * ringReflectionThetaS n N (g y) * NormedSpace.exp P) ^ m).trace.re) ^ 2
      ≤ ((g x * ringReflectionThetaS n N (g x) * NormedSpace.exp P) ^ m).trace.re
        * ((g y * ringReflectionThetaS n N (g y) * NormedSpace.exp P) ^ m).trace.re := by
  -- the crossing partial sums converge to `exp P` (reused clean-context lemma)
  have hexp := expSeriesPartialSum_tendsto (n := n) (N := N) P
  -- continuity of `M' ↦ Re Tr ((g u · θ(g v) · M')^m)` (matrix topology)
  have hcont : ∀ u v : Fin (2 * n) → ℝ, Continuous
      (fun M' : ManyBodyOpS (Fin (2 * n)) N =>
        ((g u * ringReflectionThetaS n N (g v) * M') ^ m).trace.re) := by
    intro u v
    haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
      FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
    exact Complex.continuous_re.comp
      (Continuous.matrix_trace ((continuous_const.mul continuous_id).pow m))
  -- the per-`r` finite Cauchy–Schwarz (crossing is the literal finite cone `S_r`)
  have hCSr : ∀ r : ℕ,
      (((g x * ringReflectionThetaS n N (g y)
          * ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • P ^ k) ^ m).trace.re) ^ 2
        ≤ ((g x * ringReflectionThetaS n N (g x)
            * ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • P ^ k) ^ m).trace.re
          * ((g y * ringReflectionThetaS n N (g y)
            * ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • P ^ k) ^ m).trace.re := by
    intro r
    obtain ⟨ι, _, C, c, hC, hc, heq⟩ := hP.expSeriesPartialSum r
    rw [heq]
    exact twoField_product_pairing_cauchySchwarz m g hg c hc C hC x y
  exact cauchySchwarz_of_tendsto
    (((hcont x y).tendsto (NormedSpace.exp P)).comp hexp)
    (((hcont x x).tendsto (NormedSpace.exp P)).comp hexp)
    (((hcont y y).tendsto (NormedSpace.exp P)).comp hexp) hCSr

/-- **Two-field reflection Cauchy–Schwarz on the doubled Gibbs weight** — the finite-β matrix form
of Tasaki's reflection bound (4.1.51), p. 86 (proof pp. 89–93; DLS 1978 §2–3).  For `0 ≤ β`, the
doubled Gibbs weight `W(a,b) = ringTwoFieldWeight n N β a b` obeys
`(Re Tr W(a,b))² ≤ Re Tr W(a,a) · Re Tr W(b,b)`.
Proved by the outer Trotter limit `m → ∞`: the isLimit approximant `T_m(x,y) → W(x,y)`
(`ringTwoFieldWeight_isLimit`); each `T_m` satisfies the per-`m` reflection Cauchy–Schwarz
(`twoField_pairing_cauchySchwarz_exp` with kinetic `g_m z = exp(-(β/m)·Lfield z)` and crossing
`P_m = (β/m)·D_a`, cone-positive because `0 ≤ β`); the field-free crossing
(`ringFieldDLSDecomposition_interaction_eq`) rewrites the `(b,b)` slot's `D_a → D_b` to match
`isLimit(b,b)`; and `cauchySchwarz_of_tendsto` streams the per-`m` bound to the limit. -/
theorem ringTwoFieldWeight_reflection_cauchySchwarz (n N : ℕ) [NeZero n] (β : ℝ) (hβ : 0 ≤ β)
    (a b : Fin (2 * n) → ℝ) :
    ((ringTwoFieldWeight n N β a b).trace.re) ^ 2
      ≤ (ringTwoFieldWeight n N β a a).trace.re * (ringTwoFieldWeight n N β b b).trace.re := by
  have htr : Continuous fun M' : ManyBodyOpS (Fin (2 * n)) N => M'.trace.re := by
    haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
      FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
    exact Complex.continuous_re.comp (Continuous.matrix_trace continuous_id)
  -- the crossing factor `P_m = (β/m)·D_a` is cone-representable because `0 ≤ β`
  have hP : ∀ m : ℕ, RPTraceConeRepS n N
      ((m : ℂ)⁻¹ • ((β : ℂ) • (ringFieldDLSDecomposition n N a).interaction)) := by
    intro m
    have hsc : (m : ℂ)⁻¹ • ((β : ℂ) • (ringFieldDLSDecomposition n N a).interaction)
        = (((m : ℝ)⁻¹ * β : ℝ) : ℂ) • (ringFieldDLSDecomposition n N a).interaction := by
      rw [smul_smul]; congr 1; push_cast; ring
    rw [hsc]
    exact (ringFieldDLSDecomposition n N a).interaction_coneRep.smul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) hβ)
  refine cauchySchwarz_of_tendsto
    ((htr.tendsto _).comp (ringTwoFieldWeight_isLimit n N β a b))
    ((htr.tendsto _).comp (ringTwoFieldWeight_isLimit n N β a a))
    ((htr.tendsto _).comp (ringTwoFieldWeight_isLimit n N β b b)) (fun m => ?_)
  have h3 := twoField_pairing_cauchySchwarz_exp m
    (fun z => NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringLeftFieldHamiltonian n N z)))
    (fun z => (((ringLeftFieldHamiltonian_supportedOnLeft n N z).smul (-(β : ℂ))).smul
      ((m : ℂ)⁻¹)).exp)
    (hP m) a b
  nth_rewrite 3 [ringFieldDLSDecomposition_interaction_eq n N a b] at h3
  exact h3

end LatticeSystem.Quantum
