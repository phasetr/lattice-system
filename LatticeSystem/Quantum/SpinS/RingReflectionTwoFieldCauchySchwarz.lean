/-
The two-field reflection Cauchy–Schwarz on the doubled bond-square Gibbs weight `W^{BS}(a,b)` via a
double limit (Tasaki §4.1 Theorem 4.2, reflection-positivity layer; (4.1.51), pp. 89–93; DLS 1978
§2–3).

Streaming the finite `(m,r)` reflection Cauchy–Schwarz of `RingReflectionTwoFieldConeCauchySchwarz`
(`twoField_product_pairing_cauchySchwarz`) to a doubled Gibbs weight requires a genuinely NESTED
double limit: the Dyson–Lieb–Simon Trotter approximant
`T_m(x,y) = (E_G(x)·θ(E_G(y))·exp((β/m)·D))^m` carries the crossing factor as the exponential
`exp((β/m)·D)`, which is NOT a finite cone but only the `r → ∞` limit of the cone partial sums
`S_r = ∑_{k<r}(k!)⁻¹•((β/m)·D)ᵏ`.  So one first closes `r → ∞` (exp-of-cone) to lift the finite
Cauchy–Schwarz from `U_{m,r}` to `T_m` (`twoField_pairing_cauchySchwarz_exp`), then `m → ∞`
(Trotter, `ringBondSquareTwoFieldWeight_isLimit`) to reach `W^{BS}`.  Both passages reuse the
limit-preserving Cauchy–Schwarz `cauchySchwarz_of_tendsto`.  The hypothesis `0 ≤ β` is needed for
cone positivity of the crossing factor (isLimit itself needs no sign hypothesis).

This file records the limit-preserving Cauchy–Schwarz `cauchySchwarz_of_tendsto`, the per-`m`
exponential-crossing Cauchy–Schwarz `twoField_pairing_cauchySchwarz_exp`, and the capstone
`ringBondSquareTwoFieldWeight_reflection_cauchySchwarz`: the finite-β matrix form of Tasaki's
reflection bound (4.1.51), `(Re Tr W^{BS}(a,b))² ≤ Re Tr W^{BS}(a,a) · Re Tr W^{BS}(b,b)`.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldWeight
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldConeCauchySchwarz
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareTwoFieldWeight
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

/-- **Per-`m` reflection Cauchy–Schwarz with a field-dependent exponential crossing factor** (the
`r → ∞` passage).  For the Dyson–Lieb–Simon per-`m` approximant
`T_m(x,y) = (g(x)·θ(g(y))·exp P(x,y))^m` — with left-supported kinetic family `g` and a
field-dependent field-crossing cone `P(u,v) = ∑ᵢ cᵢ•(θ(C i v)·C i u)` (`RPTwoFieldConeRepS`) — the
real part of the trace pairing obeys
`(Re Tr T_m(x,y))² ≤ Re Tr T_m(x,x) · Re Tr T_m(y,y)`, the three slots carrying the field-matched
crossings `exp P(x,y)`, `exp P(x,x)`, `exp P(y,y)`.  Obtained by closing the inner limit `r → ∞`
of the finite `(m,r)` Cauchy–Schwarz `twoField_product_pairing_cauchySchwarz` (already
field-dependent): for each `r` the crossing partial sum `S_r(u,v) = ∑_{k<r}(k!)⁻¹•(P u v)ᵏ` is a
single field-crossing finite cone shared across the three slots
(`RPTwoFieldConeRepS.expSeriesPartialSum`), and `S_r(u,v) → exp P(u,v)`
(`expSeriesPartialSum_tendsto`, applied separately at each slot), so `cauchySchwarz_of_tendsto`
streams the per-`r` inequality to the exponential.  This is the inner limit of the double limit of
Tasaki (4.1.51)/(4.1.69) (pp. 89–93; DLS 1978 §2–3). -/
private theorem twoField_pairing_cauchySchwarz_exp (m : ℕ)
    (g : (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N)
    (hg : ∀ z, SupportedOnLeftS n N (g z))
    {P : (Fin (2 * n) → ℝ) → (Fin (2 * n) → ℝ) → ManyBodyOpS (Fin (2 * n)) N}
    (hP : RPTwoFieldConeRepS n N P) (x y : Fin (2 * n) → ℝ) :
    (((g x * ringReflectionThetaS n N (g y) * NormedSpace.exp (P x y)) ^ m).trace.re) ^ 2
      ≤ ((g x * ringReflectionThetaS n N (g x) * NormedSpace.exp (P x x)) ^ m).trace.re
        * ((g y * ringReflectionThetaS n N (g y) * NormedSpace.exp (P y y)) ^ m).trace.re := by
  -- the crossing partial sums converge to `exp P(u,v)`, separately at each slot
  have hexpxy := expSeriesPartialSum_tendsto (n := n) (N := N) (P x y)
  have hexpxx := expSeriesPartialSum_tendsto (n := n) (N := N) (P x x)
  have hexpyy := expSeriesPartialSum_tendsto (n := n) (N := N) (P y y)
  -- continuity of `M' ↦ Re Tr ((g u · θ(g v) · M')^m)` (matrix topology)
  have hcont : ∀ u v : Fin (2 * n) → ℝ, Continuous
      (fun M' : ManyBodyOpS (Fin (2 * n)) N =>
        ((g u * ringReflectionThetaS n N (g v) * M') ^ m).trace.re) := by
    intro u v
    haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
      FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
    exact Complex.continuous_re.comp
      (Continuous.matrix_trace ((continuous_const.mul continuous_id).pow m))
  -- the per-`r` finite Cauchy–Schwarz (each slot's crossing is the shared finite cone `S_r`)
  have hCSr : ∀ r : ℕ,
      (((g x * ringReflectionThetaS n N (g y)
          * ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • (P x y) ^ k) ^ m).trace.re) ^ 2
        ≤ ((g x * ringReflectionThetaS n N (g x)
            * ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • (P x x) ^ k) ^ m).trace.re
          * ((g y * ringReflectionThetaS n N (g y)
            * ∑ k ∈ Finset.range r, ((Nat.factorial k : ℂ))⁻¹ • (P y y) ^ k) ^ m).trace.re := by
    intro r
    obtain ⟨ι, _, C, c, hC, hc, heq⟩ := hP.expSeriesPartialSum r
    simp only [heq]
    exact twoField_product_pairing_cauchySchwarz m g hg c hc C hC x y
  exact cauchySchwarz_of_tendsto
    (((hcont x y).tendsto (NormedSpace.exp (P x y))).comp hexpxy)
    (((hcont x x).tendsto (NormedSpace.exp (P x x))).comp hexpxx)
    (((hcont y y).tendsto (NormedSpace.exp (P y y))).comp hexpyy) hCSr

/-- **Two-field reflection Cauchy–Schwarz on the doubled bond-square Gibbs weight** — the finite-β
matrix form of Tasaki's reflection bound (4.1.51), p. 86 (proof pp. 89–93; DLS 1978 §2–3), in the
bond-square (field-dependent crossing) presentation of (4.1.67).  For `0 ≤ β`, the doubled
bond-square Gibbs weight `W^{BS}(a,b) = ringBondSquareTwoFieldWeight n N β a b` obeys
`(Re Tr W^{BS}(a,b))² ≤ Re Tr W^{BS}(a,a) · Re Tr W^{BS}(b,b)`.
Proved by the outer Trotter limit `m → ∞`: the isLimit approximant `T_m(x,y) → W^{BS}(x,y)`
(`ringBondSquareTwoFieldWeight_isLimit`); each `T_m` satisfies the per-`m` reflection Cauchy–Schwarz
(`twoField_pairing_cauchySchwarz_exp` with kinetic `g_m z = exp(-(β/m)·H_L(z))` and crossing
`P_m(x,y) = (β/m)·crossing(x,y)`, cone-positive because `0 ≤ β`); and `cauchySchwarz_of_tendsto`
streams the per-`m` bound to the limit.  The crossing is genuinely field-dependent
(`ringBondSquareFieldCrossing`), so its `(b,b)` slot is already native — no field-free-crossing
splice is needed. -/
theorem ringBondSquareTwoFieldWeight_reflection_cauchySchwarz (n N : ℕ) [NeZero n] (β : ℝ)
    (hβ : 0 ≤ β) (a b : Fin (2 * n) → ℝ) :
    ((ringBondSquareTwoFieldWeight n N β a b).trace.re) ^ 2
      ≤ (ringBondSquareTwoFieldWeight n N β a a).trace.re
        * (ringBondSquareTwoFieldWeight n N β b b).trace.re := by
  have htr : Continuous fun M' : ManyBodyOpS (Fin (2 * n)) N => M'.trace.re := by
    haveI : CompleteSpace (ManyBodyOpS (Fin (2 * n)) N) :=
      FiniteDimensional.complete ℂ (ManyBodyOpS (Fin (2 * n)) N)
    exact Complex.continuous_re.comp (Continuous.matrix_trace continuous_id)
  -- the field-crossing factor `P_m(x,y) = (β/m)·crossing(x,y)` is cone-representable (`0 ≤ β`)
  have hP : ∀ m : ℕ, RPTwoFieldConeRepS n N
      (fun x y => (m : ℂ)⁻¹ • ((β : ℂ) • ringBondSquareFieldCrossing n N x y)) := by
    intro m
    have hsc : (fun x y : Fin (2 * n) → ℝ =>
          (m : ℂ)⁻¹ • ((β : ℂ) • ringBondSquareFieldCrossing n N x y))
        = (fun x y => (((m : ℝ)⁻¹ * β : ℝ) : ℂ) • ringBondSquareFieldCrossing n N x y) := by
      funext x y; rw [smul_smul]; congr 1; push_cast; ring
    rw [hsc]
    exact (ringBondSquareFieldCrossing_twoFieldConeRep n N).smul_nonneg
      (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg m)) hβ)
  refine cauchySchwarz_of_tendsto
    ((htr.tendsto _).comp (ringBondSquareTwoFieldWeight_isLimit n N β a b))
    ((htr.tendsto _).comp (ringBondSquareTwoFieldWeight_isLimit n N β a a))
    ((htr.tendsto _).comp (ringBondSquareTwoFieldWeight_isLimit n N β b b)) (fun m => ?_)
  exact twoField_pairing_cauchySchwarz_exp m
    (fun z => NormedSpace.exp ((m : ℂ)⁻¹ • (-(β : ℂ) • ringBondSquareLeftFieldHamiltonian n N z)))
    (fun z => (((ringBondSquareLeftFieldHamiltonian_supportedOnLeft n N z).smul (-(β : ℂ))).smul
      ((m : ℂ)⁻¹)).exp)
    (hP m) a b

end LatticeSystem.Quantum
