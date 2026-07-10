/-
Physical identification of the per-site field partition function with the two-field Gibbs weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: Gaussian domination PR7c; (4.1.47)–(4.1.51),
pp. 85–86; proof pp. 89–93, (4.1.62)–(4.1.82); DLS 1978 §2–3).

This is the *physical identification stage* of the Dyson–Lieb–Simon reflection bound.  The physical
per-site field Hamiltonian on the even ring `Fin (2n)` is `Ĥ_field(h) = Ĥ_0 + Σ_z (h z)·Ŝ_z^{(3)}`
with `Ĥ_0 = heisenbergHamiltonianS (ringCoupling (2n))` the field-free symmetric ring Hamiltonian and
`h : Fin (2n) → ℝ` an arbitrary per-site field (Tasaki (4.1.48), the `−(−1)^x` folded into `h`).  Its
physical partition function is the real part of the Gibbs trace `Z_β(h) = Re Tr exp(−β·Ĥ_field(h))`.

The **field-splitting map** `physFieldOf n a b z = if z < n then a z else −b(r z)` realizes `h` as the
physical field whose right-half Marshall gauge transform reproduces the two-field ("doubled") Gibbs
weight `W(a,b) = ringTwoFieldWeight n N β a b`.  The **sign crux** is that the two right-half minus
signs — the gauge conjugation `U·Ŝ^{(3)}·U⁻¹ = −Ŝ^{(3)}` and the `−b(r z)` slot of `physFieldOf` —
cancel, so the θ-transported right field `Σ_{x<n} (b x)·Ŝ_{r x}^{(3)}` acquires its correct positive
sign with no new sign lemma.  Gauge conjugation of `Ĥ_field(physFieldOf a b)` therefore equals the
doubled Hamiltonian `Lfield(a) + θ(Lfield(b)) − D`, and — by gauge unitarity and trace invariance —
`Z_β(physFieldOf a b) = Re Tr W(a,b)`.  Feeding this into the merged capstone
`ringTwoFieldWeight_reflection_cauchySchwarz` yields the **one reflection step**
`Z_β(h)² ≤ Z_β(h_L)·Z_β(h_R)`, the finite-β partition-function form of Tasaki's reflection bound
(4.1.51) (of which the T = 0 bound `E_GS(h) ≥ ½{E_GS(h_L)+E_GS(h_R)}` is the `β → ∞` limit).

This file records the field-splitting bookkeeping (`physFieldOf`, `physFieldOf_self`,
`sum_right_eq_sum_reflect_left`), the Ŝ^{(3)} specialisation of the gauge conjugation, the θ field-part
expansion of `Lfield(b)`, the physical field Hamiltonian (`ringFieldHamiltonian`) and the crux gauge
conjugation, the physical partition function (`ringFieldPartitionRe`) with its identification, the
diagonal nonnegativity, and the one reflection step.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionTwoFieldCauchySchwarz
import LatticeSystem.Quantum.SpinS.RingReflectionThermalTransfer

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Physical per-site field splitting.**  The field `physFieldOf n a b z = a z` on the left half
`{z < n}` and `−b(r z)` on the right half `{z ≥ n}`, with `r = ringReflect n`.  Its right-half gauge
transform reproduces the two-field doubled Gibbs weight: the left field `a` survives on the left and
(after the gauge sign `−Ŝ^{(3)}` cancels the `−b(r z)`) the field `b` transported by `θ` survives on
the right (Tasaki §4.1, reflected field copies (4.1.50), p. 86). -/
def physFieldOf (n : ℕ) (a b : Fin (2 * n) → ℝ) : Fin (2 * n) → ℝ :=
  fun z => if (z : ℕ) < n then a z else - b (ringReflect n z)

/-- **The diagonal field is its own splitting.**  With right field `b x = −h(r x)` the splitting
`physFieldOf n h b` collapses to `h`: on the right half the `if`-branch `−b(r z) = h(r(r z)) = h z`
by involutivity of `r`.  This exhibits an arbitrary physical field `h` as a `physFieldOf` value, the
starting point of the one reflection step (Tasaki §4.1 (4.1.50)–(4.1.51)). -/
theorem physFieldOf_self (n : ℕ) (h : Fin (2 * n) → ℝ) :
    physFieldOf n h (fun x => - h (ringReflect n x)) = h := by
  funext z
  rw [physFieldOf]
  split
  · rfl
  · rw [neg_neg, ringReflect_involutive n z]

/-- **Right-half sum reindexed to the reflected left half.**  Summing a family `g` over the right
half `{z ≥ n}` equals summing `g ∘ r` over the left half `{x < n}`, via the reflection bijection
`r = ringReflect n` between the two halves (`ringReflect_lt_iff`, involutivity).  Used in the crux
gauge conjugation to align the gauged right-half field term with the θ-transported field
(Tasaki §4.1, reflected field copies (4.1.50), p. 86). -/
private theorem sum_right_eq_sum_reflect_left {M : Type*} [AddCommMonoid M] (n : ℕ)
    (g : Fin (2 * n) → M) :
    ∑ z ∈ Finset.univ.filter (fun z : Fin (2 * n) => n ≤ (z : ℕ)), g z
      = ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n), g (ringReflect n x) := by
  refine Finset.sum_nbij' (fun z => ringReflect n z) (fun x => ringReflect n x) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    have hz' : n ≤ (z : ℕ) := (Finset.mem_filter.mp hz).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ringReflect_lt_iff n z).mpr hz'
  · intro x hx
    have hx' : (x : ℕ) < n := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := (ringReflect_lt_iff n (ringReflect n x)).not
    rw [ringReflect_involutive n x] at this
    omega
  · intro z _; exact ringReflect_involutive n z
  · intro x _; exact ringReflect_involutive n x
  · intro z _; rw [ringReflect_involutive n z]

namespace AxisTwoPiRotS

/-- **Ŝ^{(3)} specialisation of the right-half gauge conjugation.**  The right-half Marshall gauge
conjugates the single-site `Ŝ^{(3)}` to `−Ŝ^{(3)}` on right sites (`z ≥ n`, via
`AxisTwoPiRotS.conj_spinSOp3`, the DLS/Marshall sign) and leaves it fixed on left sites (`z < n`):
`rightGauge · onSiteS z Ŝ^{(3)} · rightGaugeInv = onSiteS z (if n ≤ z then −Ŝ^{(3)} else Ŝ^{(3)})`.
This is the sign that, combined with the `−b(r z)` slot of `physFieldOf`, transports the right field
with the correct positive sign (Tasaki §4.1 Theorem 4.2 proof, pp. 89–93). -/
theorem rightGauge_conj_onSiteS_spinSOp3 (G : AxisTwoPiRotS N) (n : ℕ) (z : Fin (2 * n)) :
    G.rightGauge n * onSiteS z (spinSOp3 N) * G.rightGaugeInv n
      = onSiteS z (if n ≤ (z : ℕ) then - spinSOp3 N else spinSOp3 N) := by
  rw [G.rightGauge_conj_onSiteS n z]
  congr 1
  split
  · rw [G.conj_spinSOp3]
  · rfl

end AxisTwoPiRotS

end LatticeSystem.Quantum
