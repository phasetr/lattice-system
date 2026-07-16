/-
Physical identification of the per-site field partition function with the two-field Gibbs weight
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: Gaussian domination PR7c; (4.1.47)–(4.1.51),
pp. 85–86; proof pp. 89–93, (4.1.62)–(4.1.82); DLS 1978 §2–3).

This is the *physical identification stage* of the Dyson–Lieb–Simon reflection bound.  The physical
per-site field Hamiltonian on the even ring `Fin (2n)` is `Ĥ_field(h) = Ĥ_0 + Σ_z (h z)·Ŝ_z^{(3)}`
with `Ĥ_0 = heisenbergHamiltonianS (ringCoupling (2n))` the field-free symmetric ring Hamiltonian
and `h : Fin (2n) → ℝ` an arbitrary per-site field (Tasaki (4.1.48), the `−(−1)^x` folded into `h`).
Its physical partition function is the real part of the Gibbs trace
`Z_β(h) = Re Tr exp(−β·Ĥ_field(h))`.

The **field-splitting map** `physFieldOf n a b z = if z < n then a z else −b(r z)` realizes `h` as
the physical field whose right-half Marshall gauge transform reproduces the two-field ("doubled")
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
`sum_right_eq_sum_reflect_left`), the Ŝ^{(3)} specialisation of the gauge conjugation, the θ
field-part expansion of `Lfield(b)`, the physical field Hamiltonian (`ringFieldHamiltonian`) and the
crux gauge
conjugation, the physical partition function (`ringFieldPartitionRe`) with its identification, and
the reflected field copies (`ringFieldReflectLeft`/`ringFieldReflectRight`).
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
(Tasaki §4.1, reflected field copies (4.1.50), p. 86).  Public (de-privatised for PR-BS8a-ii, which
reuses it from `RingReflectionBondSquareGaugeCrux` to reindex the single-ion right half — statement
and proof unchanged, visibility only, avoiding a duplicate reindex lemma). -/
theorem sum_right_eq_sum_reflect_left {M : Type*} [AddCommMonoid M] (n : ℕ)
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

/-- **θ field-part expansion of the field-augmented left Hamiltonian.**  The reflection `θ` of
`Lfield(b) = ringLeftHamiltonian + Σ_{x<n} (b x)·Ŝ_x^{(3)}` is `θ(ringLeftHamiltonian)` plus the
θ-transported field `Σ_{x<n} (b x)·Ŝ_{r x}^{(3)}`.  Since `Ŝ^{(3)}` is real, `θ` reflects the site
and leaves the operator (and the real coefficient) unchanged
(`ringReflectionThetaS_onSiteS_spinSOp3`, `Complex.conj_ofReal`).  This is the right-supported field
of the doubled weight `W(a,b)`
(Tasaki §4.1 Theorem 4.2 proof, pp. 89–93). -/
theorem ringReflectionThetaS_ringLeftFieldHamiltonian (n N : ℕ) (b : Fin (2 * n) → ℝ) :
    ringReflectionThetaS n N (ringLeftFieldHamiltonian n N b)
      = ringReflectionThetaS n N (ringLeftHamiltonian n N)
        + ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
            (b x : ℂ) • onSiteS (ringReflect n x) (spinSOp3 N) := by
  rw [ringLeftFieldHamiltonian, ringReflectionThetaS_add, ringReflectionThetaS_sum]
  refine congrArg _ (Finset.sum_congr rfl (fun x _ => ?_))
  rw [ringReflectionThetaS_smul, Complex.conj_ofReal, ringReflectionThetaS_onSiteS_spinSOp3]

/-- **Physical per-site field Hamiltonian** `Ĥ_field(h) = Ĥ_0 + Σ_z (h z)·Ŝ_z^{(3)}` on the even
ring, with `Ĥ_0 = heisenbergHamiltonianS (ringCoupling (2n))` the field-free symmetric ring
Hamiltonian and a per-site Zeeman field over all sites (Tasaki §4.1, field Hamiltonian (4.1.48),
pp. 85–86, with the `−(−1)^x` folded into the per-site field `h`). -/
noncomputable def ringFieldHamiltonian (n N : ℕ) (h : Fin (2 * n) → ℝ) :
    ManyBodyOpS (Fin (2 * n)) N :=
  heisenbergHamiltonianS (ringCoupling (2 * n)) N + ∑ z, (h z : ℂ) • onSiteS z (spinSOp3 N)

namespace AxisTwoPiRotS

/-- **Crux: the right-half gauge turns `Ĥ_field(physFieldOf a b)` into the doubled Hamiltonian.**
For the split field `physFieldOf n a b`, conjugation by the right-half Marshall gauge equals the
two-field ("doubled") Hamiltonian `Lfield(a) + θ(Lfield(b)) − D` underlying `W(a,b)`.  The
field-free part `Ĥ_0 ↦ H_L + θ(H_L) − crossing` is `rightGauge_conj_ringHamiltonian`; the field
part splits by half — on the left `a` survives directly, on the right the two minus signs (the
gauge `−Ŝ^{(3)}` and the `−b(r z)` slot) cancel and, reindexed by `r`, reproduce the θ-transported
field `Σ_{x<n} (b x)·Ŝ_{r x}^{(3)}` of `θ(Lfield(b))`.  This is the sign core of Tasaki's
reflection bound (4.1.51), proof pp. 89–93; DLS 1978 §2–3. -/
theorem rightGauge_conj_ringFieldHamiltonian (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]
    (a b : Fin (2 * n) → ℝ) :
    G.rightGauge n * ringFieldHamiltonian n N (physFieldOf n a b) * G.rightGaugeInv n
      = ringLeftFieldHamiltonian n N a
        + ringReflectionThetaS n N (ringLeftFieldHamiltonian n N b)
        - (ringFieldDLSDecomposition n N a).interaction := by
  have hfield : G.rightGauge n
        * (∑ z, (physFieldOf n a b z : ℂ) • onSiteS z (spinSOp3 N)) * G.rightGaugeInv n
      = (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
            (a x : ℂ) • onSiteS x (spinSOp3 N))
        + ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
            (b x : ℂ) • onSiteS (ringReflect n x) (spinSOp3 N) := by
    rw [rightGauge_conj_sum]
    rw [Finset.sum_congr rfl (fun z _ => by
        rw [rightGauge_conj_smul, G.rightGauge_conj_onSiteS_spinSOp3 n z] :
      ∀ z ∈ (Finset.univ : Finset (Fin (2 * n))),
        G.rightGauge n * ((physFieldOf n a b z : ℂ) • onSiteS z (spinSOp3 N)) * G.rightGaugeInv n
          = (physFieldOf n a b z : ℂ)
            • onSiteS z (if n ≤ (z : ℕ) then - spinSOp3 N else spinSOp3 N))]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun z : Fin (2 * n) => (z : ℕ) < n)]
    congr 1
    · refine Finset.sum_congr rfl (fun z hz => ?_)
      have hz' : (z : ℕ) < n := (Finset.mem_filter.mp hz).2
      simp only [physFieldOf, if_pos hz', if_neg (by omega : ¬ n ≤ (z : ℕ))]
    · rw [show (Finset.univ.filter (fun z : Fin (2 * n) => ¬ (z : ℕ) < n))
            = Finset.univ.filter (fun z : Fin (2 * n) => n ≤ (z : ℕ)) from by
          apply Finset.filter_congr; intro z _; simp only [not_lt]]
      rw [sum_right_eq_sum_reflect_left n (fun z => (physFieldOf n a b z : ℂ)
          • onSiteS z (if n ≤ (z : ℕ) then - spinSOp3 N else spinSOp3 N))]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hx' : (x : ℕ) < n := (Finset.mem_filter.mp hx).2
      have hrx : n ≤ ((ringReflect n x : Fin (2 * n)) : ℕ) := by
        have := (ringReflect_lt_iff n (ringReflect n x)).not
        rw [ringReflect_involutive n x] at this; omega
      simp only [physFieldOf, if_pos hrx,
        if_neg (by omega : ¬ ((ringReflect n x : Fin (2 * n)) : ℕ) < n),
        ringReflect_involutive n x, Complex.ofReal_neg, onSiteS_neg]
      rw [smul_neg, neg_smul]
      exact neg_neg _
  rw [ringFieldHamiltonian, rightGauge_conj_add, G.rightGauge_conj_ringHamiltonian n,
    ringDLSDecomposition_toHamiltonian, hfield, ringLeftFieldHamiltonian,
    ringReflectionThetaS_ringLeftFieldHamiltonian, ringFieldDLSDecomposition,
    ringCrossingRPDecomposition_interaction]
  abel

end AxisTwoPiRotS

/-- **Physical field partition function** `Z_β(h) = Re Tr exp(−β·Ĥ_field(h))` (Tasaki §4.1,
canonical partition function of the field Hamiltonian (4.1.48)).  We take the real part
*definitionally*: the
field Hamiltonian is Hermitian, so the Gibbs trace is real and `.re` recovers it; the genuine
nonnegativity `Z_β ≥ 0` is supplied downstream by the reflection-positivity cone, not by a
reality lemma. -/
noncomputable def ringFieldPartitionRe (n N : ℕ) (β : ℝ) (h : Fin (2 * n) → ℝ) : ℝ :=
  (thermalPartitionFnS β (ringFieldHamiltonian n N h)).re

/-- **Identification of the physical partition function with the two-field weight trace.**  For the
split field `physFieldOf n a b`, the physical partition function equals the real trace of the
doubled Gibbs weight: `Z_β(physFieldOf a b) = Re Tr W(a,b)`.  Since the right-half gauge is unitary
(`rightGaugeUnit`), `exp(−β·Ĥ_field)` conjugates to `exp(−β·(doubled Hamiltonian))`
(`Matrix.exp_units_conj` + the crux `rightGauge_conj_ringFieldHamiltonian`) and the trace is
gauge-invariant (`trace_rightGauge_conj`).  This transports Tasaki's reflection bound (4.1.51) to
the partition function (proof pp. 89–93; DLS 1978 §2–3). -/
theorem ringFieldPartitionRe_physFieldOf (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n] (β : ℝ)
    (a b : Fin (2 * n) → ℝ) :
    ringFieldPartitionRe n N β (physFieldOf n a b) = (ringTwoFieldWeight n N β a b).trace.re := by
  have hexp := Matrix.exp_units_conj (G.rightGaugeUnit n)
    (-(β : ℂ) • ringFieldHamiltonian n N (physFieldOf n a b))
  simp only [AxisTwoPiRotS.rightGaugeUnit_val, AxisTwoPiRotS.rightGaugeUnit_inv] at hexp
  rw [show G.rightGauge n * (-(β : ℂ) • ringFieldHamiltonian n N (physFieldOf n a b))
        * G.rightGaugeInv n
      = -(β : ℂ) • (ringLeftFieldHamiltonian n N a
        + ringReflectionThetaS n N (ringLeftFieldHamiltonian n N b)
        - (ringFieldDLSDecomposition n N a).interaction) from by
    rw [mul_smul_comm, smul_mul_assoc, G.rightGauge_conj_ringFieldHamiltonian n a b]] at hexp
  rw [ringFieldPartitionRe, thermalPartitionFnS, thermalGibbsOpS, ringTwoFieldWeight, hexp,
    G.trace_rightGauge_conj n]

/-- **Reflected left field copy** `h_L` (Tasaki §4.1, reflected field copies (4.1.50), p. 86): keep
the left half of `h` and reflect it onto the right, i.e. the diagonal split `physFieldOf n h h`. -/
def ringFieldReflectLeft (n : ℕ) (h : Fin (2 * n) → ℝ) : Fin (2 * n) → ℝ :=
  physFieldOf n h h

/-- **Reflected right field copy** `h_R` (Tasaki §4.1, reflected field copies (4.1.50), p. 86): keep
the right half of `h` and reflect it onto the left, i.e. the diagonal split of `−h∘r`. -/
def ringFieldReflectRight (n : ℕ) (h : Fin (2 * n) → ℝ) : Fin (2 * n) → ℝ :=
  physFieldOf n (fun x => - h (ringReflect n x)) (fun x => - h (ringReflect n x))

end LatticeSystem.Quantum
