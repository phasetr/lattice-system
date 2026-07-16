/-
Physical identification of the bond-square field partition function with the two-field Gibbs weight,
and the one reflection step in its sign-free classical form
(Tasaki §4.1 Theorem 4.2, reflection-positivity bond-square layer, PR-BS8b; (4.1.48)–(4.1.51),
book pp. 86–90; proof pp. 89–93; DLS 1978 §2–3).

This is the *physical identification stage* of the bond-square Dyson–Lieb–Simon reflection bound.
The gauge crux (G) `AxisTwoPiRotS.rightGauge_conj_ringBondSquareFieldHamiltonian` (BS8a-ii) turned
the physical bond-square field Hamiltonian at the staggered wrapper `physBondSquareFieldOf n a b`
into the BS6 two-field DLS operator.  Here we transport it to the partition function: since the
right-half Marshall gauge is unitary (`rightGaugeUnit`), `exp(−β·Ĥ^{BS}(physBondSquareFieldOf a b))`
conjugates to `exp(−β·Ĥ^{BS}(a,b))` (`Matrix.exp_units_conj`) and the trace is gauge-invariant
(`trace_rightGauge_conj`), giving the **identification**
`Z^{BS}(physBondSquareFieldOf a b) = Re Tr W^{BS}(a,b)`
(`ringBondSquareFieldPartitionRe_physFieldOf`).

Because the physical bond-square field carries the staggering `(−1)ˣ` internally, the wrapper is the
staggered relabel `P := ringStaggeredRelabel n` of the linear split field
(`physBondSquareFieldOf_eq_relabel`).  The two staggered relabels cancel, so the three
field-carrying slots of the reflection step collapse to Tasaki's **sign-free classical mirrors**
(4.1.50):
`physBondSquareFieldOf n (P g)(−(P g)∘r) = g` (`physBondSquareFieldOf_self`),
`physBondSquareFieldOf n (P g)(P g) = reflectLeft n g` (`physBondSquareFieldOf_diag_left`), and
`physBondSquareFieldOf n (−(P g)∘r)(−(P g)∘r) = reflectRight n g`
(`physBondSquareFieldOf_diag_right`).  Feeding these into the merged BS7 capstone
`ringBondSquareTwoFieldWeight_reflection_cauchySchwarz` yields the **one reflection step**
`Z^{BS}(g)² ≤ Z^{BS}(reflectLeft n g)·Z^{BS}(reflectRight n g)`
(`ringBondSquareFieldPartitionRe_reflection_step`), the finite-β partition-function form of Tasaki's
bond-square reflection bound (4.1.51) (of which the T = 0 bound is the `β → ∞` shadow).

See `.self-local/docs/math-tasaki-4-1-51-bond-square-physical-field-reflection-step.md`
(issue #4777, §2/§4, PR-BS8b).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareGaugeCrux
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareFieldPartition
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldCauchySchwarz
import LatticeSystem.Quantum.SpinS.RingReflectionStaggeredRelabel

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Identification of the bond-square partition function with the two-field weight trace.**  For
the staggered wrapper field `physBondSquareFieldOf n a b`, the physical bond-square partition
function equals the real trace of the doubled bond-square Gibbs weight:
`Z^{BS}(physBondSquareFieldOf a b) = Re Tr W^{BS}(a,b)`.  Since the right-half gauge is unitary
(`rightGaugeUnit`), `exp(−β·Ĥ^{BS}(physBondSquareFieldOf a b))` conjugates to
`exp(−β·Ĥ^{BS}(a,b))` (`Matrix.exp_units_conj` + the gauge crux (G)
`rightGauge_conj_ringBondSquareFieldHamiltonian`) and the trace is gauge-invariant
(`trace_rightGauge_conj`).  This transports Tasaki's bond-square reflection bound (4.1.51) to the
partition function (proof pp. 89–93; DLS 1978 §2–3). -/
theorem ringBondSquareFieldPartitionRe_physFieldOf (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n] (β : ℝ)
    (a b : Fin (2 * n) → ℝ) :
    ringBondSquareFieldPartitionRe n N β (physBondSquareFieldOf n a b)
      = (ringBondSquareTwoFieldWeight n N β a b).trace.re := by
  have hexp := Matrix.exp_units_conj (G.rightGaugeUnit n)
    (-(β : ℂ) • ringBondSquareFieldHamiltonian n N (physBondSquareFieldOf n a b))
  simp only [AxisTwoPiRotS.rightGaugeUnit_val, AxisTwoPiRotS.rightGaugeUnit_inv] at hexp
  rw [show G.rightGauge n
        * (-(β : ℂ) • ringBondSquareFieldHamiltonian n N (physBondSquareFieldOf n a b))
        * G.rightGaugeInv n
      = -(β : ℂ) • (ringBondSquareLeftFieldHamiltonian n N a
        + ringReflectionThetaS n N (ringBondSquareLeftFieldHamiltonian n N b)
        - ringBondSquareFieldCrossing n N a b) from by
    rw [mul_smul_comm, smul_mul_assoc,
      G.rightGauge_conj_ringBondSquareFieldHamiltonian n a b]] at hexp
  rw [ringBondSquareFieldPartitionRe, thermalPartitionFnS, thermalGibbsOpS,
    ringBondSquareTwoFieldWeight, hexp, G.trace_rightGauge_conj n]

/-- **Bridge to the staggered relabel** (note §4 (REL)): the staggered wrapper of the linear split
field is literally the staggered relabel `P = ringStaggeredRelabel n` of the linear split field,
`physBondSquareFieldOf n a b = ringStaggeredRelabel n (physFieldOf n a b)` (both sides
`fun z ↦ (−1)ᶻ · physFieldOf n a b z`).  This is what makes the reflection step's three field slots
collapse to the sign-free classical mirrors (4.1.50) rather than the signed linear copies. -/
private theorem physBondSquareFieldOf_eq_relabel (n : ℕ) [NeZero n] (a b : Fin (2 * n) → ℝ) :
    physBondSquareFieldOf n a b = ringStaggeredRelabel n (physFieldOf n a b) := rfl

/-- **The diagonal wrapper field is its own splitting** (note §4 L1).  With right field
`b x = −(P g)(r x)` the staggered wrapper `physBondSquareFieldOf n (P g) b` collapses to `g`:
via the bridge `(REL)` it is `P(physFieldOf n (P g)(−(P g)∘r)) = P(P g) = g` (`physFieldOf_self`
gives the inner `= P g`, `ringStaggeredRelabel_involutive` closes `P(P g) = g`).  This exhibits an
arbitrary physical field `g` as a wrapper value, the starting point of the one reflection step
(Tasaki §4.1 (4.1.50)–(4.1.51), book p. 86). -/
theorem physBondSquareFieldOf_self (n : ℕ) [NeZero n] (g : Fin (2 * n) → ℝ) :
    physBondSquareFieldOf n (ringStaggeredRelabel n g)
        (fun x => - (ringStaggeredRelabel n g) (ringReflect n x)) = g := by
  rw [physBondSquareFieldOf_eq_relabel, physFieldOf_self, ringStaggeredRelabel_involutive n g]

/-- **Diagonal-left collapse to the classical mirror** (note §4 L2).  The diagonal wrapper split at
the relabelled field is Tasaki's sign-free left reflected copy (4.1.50):
`physBondSquareFieldOf n (P g)(P g) = LatticeSystem.Math.reflectLeft n g`.  Via `(REL)` it equals
`P(physFieldOf n (P g)(P g)) = P(ringFieldReflectLeft n (P g)) = P(P(reflectLeft n g))
= reflectLeft n g`, the two staggered relabels `P` cancelling
(`ringStaggeredRelabel_reflectLeft` + `ringStaggeredRelabel_involutive`). -/
private theorem physBondSquareFieldOf_diag_left (n : ℕ) [NeZero n] (g : Fin (2 * n) → ℝ) :
    physBondSquareFieldOf n (ringStaggeredRelabel n g) (ringStaggeredRelabel n g)
      = LatticeSystem.Math.reflectLeft n g := by
  rw [physBondSquareFieldOf_eq_relabel]
  change ringStaggeredRelabel n (ringFieldReflectLeft n (ringStaggeredRelabel n g))
      = LatticeSystem.Math.reflectLeft n g
  rw [← ringStaggeredRelabel_reflectLeft n g]
  exact ringStaggeredRelabel_involutive n (LatticeSystem.Math.reflectLeft n g)

/-- **Diagonal-right collapse to the classical mirror** (note §4 L3).  Symmetric to the left case:
`physBondSquareFieldOf n (−(P g)∘r)(−(P g)∘r) = LatticeSystem.Math.reflectRight n g`, Tasaki's
sign-free right reflected copy (4.1.50), via `(REL)` and the cancellation of the two staggered
relabels (`ringStaggeredRelabel_reflectRight` + `ringStaggeredRelabel_involutive`). -/
private theorem physBondSquareFieldOf_diag_right (n : ℕ) [NeZero n] (g : Fin (2 * n) → ℝ) :
    physBondSquareFieldOf n (fun x => - (ringStaggeredRelabel n g) (ringReflect n x))
        (fun x => - (ringStaggeredRelabel n g) (ringReflect n x))
      = LatticeSystem.Math.reflectRight n g := by
  rw [physBondSquareFieldOf_eq_relabel]
  change ringStaggeredRelabel n (ringFieldReflectRight n (ringStaggeredRelabel n g))
      = LatticeSystem.Math.reflectRight n g
  rw [← ringStaggeredRelabel_reflectRight n g]
  exact ringStaggeredRelabel_involutive n (LatticeSystem.Math.reflectRight n g)

/-- **One reflection step: the finite-β partition-function form of Tasaki's bond-square reflection
bound (4.1.51), in sign-free classical form.**  For `β ≥ 0` and any physical field `g`,
`Z^{BS}(g)² ≤ Z^{BS}(reflectLeft n g)·Z^{BS}(reflectRight n g)` with `reflectLeft n g`,
`reflectRight n g` the **classical sign-free** reflected copies (4.1.50) `h^L`, `h^R` (Tasaki book
p. 86; `LatticeSystem.Math.reflectLeft/reflectRight`, no staggered relabel).  Writing `g` as the
diagonal wrapper split `physBondSquareFieldOf n (P g)(−(P g)∘r)` (`physBondSquareFieldOf_self`), the
identification `Z^{BS}(physBondSquareFieldOf a b) = Re Tr W^{BS}(a,b)`
(`ringBondSquareFieldPartitionRe_physFieldOf`) at the three field pairs, with the diagonal
collapses `physBondSquareFieldOf_diag_left/right` classicalising the two right-hand slots, reduces
the bound to the merged BS7 capstone `ringBondSquareTwoFieldWeight_reflection_cauchySchwarz` (proof
pp. 89–93; DLS 1978 §2–3).  The T = 0 ground-state bound `E_GS(g) ≥ ½{E_GS(h^L)+E_GS(h^R)}` is its
`β → ∞` limit. -/
theorem ringBondSquareFieldPartitionRe_reflection_step (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]
    {β : ℝ} (hβ : 0 ≤ β) (g : Fin (2 * n) → ℝ) :
    (ringBondSquareFieldPartitionRe n N β g) ^ 2
      ≤ ringBondSquareFieldPartitionRe n N β (LatticeSystem.Math.reflectLeft n g)
        * ringBondSquareFieldPartitionRe n N β (LatticeSystem.Math.reflectRight n g) := by
  have hself : ringBondSquareFieldPartitionRe n N β g
      = (ringBondSquareTwoFieldWeight n N β (ringStaggeredRelabel n g)
          (fun x => - (ringStaggeredRelabel n g) (ringReflect n x))).trace.re := by
    rw [← ringBondSquareFieldPartitionRe_physFieldOf G n β (ringStaggeredRelabel n g)
        (fun x => - (ringStaggeredRelabel n g) (ringReflect n x)),
      physBondSquareFieldOf_self]
  have hL : ringBondSquareFieldPartitionRe n N β (LatticeSystem.Math.reflectLeft n g)
      = (ringBondSquareTwoFieldWeight n N β (ringStaggeredRelabel n g)
          (ringStaggeredRelabel n g)).trace.re := by
    rw [← ringBondSquareFieldPartitionRe_physFieldOf G n β (ringStaggeredRelabel n g)
        (ringStaggeredRelabel n g), physBondSquareFieldOf_diag_left]
  have hR : ringBondSquareFieldPartitionRe n N β (LatticeSystem.Math.reflectRight n g)
      = (ringBondSquareTwoFieldWeight n N β
          (fun x => - (ringStaggeredRelabel n g) (ringReflect n x))
          (fun x => - (ringStaggeredRelabel n g) (ringReflect n x))).trace.re := by
    rw [← ringBondSquareFieldPartitionRe_physFieldOf G n β
        (fun x => - (ringStaggeredRelabel n g) (ringReflect n x))
        (fun x => - (ringStaggeredRelabel n g) (ringReflect n x)),
      physBondSquareFieldOf_diag_right]
  rw [hself, hL, hR]
  exact ringBondSquareTwoFieldWeight_reflection_cauchySchwarz n N β hβ (ringStaggeredRelabel n g)
    (fun x => - (ringStaggeredRelabel n g) (ringReflect n x))

end LatticeSystem.Quantum
