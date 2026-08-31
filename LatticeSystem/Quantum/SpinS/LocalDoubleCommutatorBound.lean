/-
Locality of the order-operator double commutator
(Tasaki §3.4, eqs. (3.4.9)-(3.4.11), general theory of low-lying states and SSB).

For a Hamiltonian `Ĥ = Σ_{b∈B} ĥ_b` whose terms act nontrivially only inside a window `W b`, and an
order operator `Ô = Σ_{x∈Λ} ô_x` built from mutually commuting single-site operators, the
commutator `[Ĥ, Ô]` and the double commutator `[Ô, [Ĥ, Ô]]` collapse onto the windows, and the
resulting finitely many terms are bounded one by one by the commutator operator-norm inequality.
This yields the bound `⟨Φ|[Ô,[Ĥ,Ô]]|Φ⟩ ≤ ‖[Ô,[Ĥ,Ô]]‖ ≤ 16 d h₀ o₀² L^d` on a normalized state,
which is the numerator estimate feeding the Horsch-von der Linden variational argument.

The collapse is proved with **two independent windows**: an inner window `W₁ b`, off which `ĥ_b`
commutes with the order terms, and an outer window `W₂ b`, off which the order terms commute with
the inner commutators. The one-window form used by the bond-local eq. (3.4.11) is the instance
`W₁ = W₂`, and the general range-`r` estimate of Problem 3.4.a needs the two windows genuinely
unequal, since there the inner and outer ranges differ (`2r` and `4r`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §3.4, eqs. (3.4.9)-(3.4.11), pp. 66-67; Problem 3.4.a, pp. 67-68, whose solution (p. 501) is
the source of the two-window form; operator-norm properties (A.2.5)/(A.2.6), p. 463.
-/
import LatticeSystem.Math.CommutatorSum
import LatticeSystem.Quantum.SpinS.ExpectationNormBound

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Tasaki eq. (3.4.9), p. 66** — the commutator of a windowed Hamiltonian with the order
operator collapses onto the windows:
`[Σ_{b∈B} ĥ_b, Σ_{x∈Λ} ô_x] = Σ_{b∈B} Σ_{z∈W b} [ĥ_b, ô_z]`.
The hypothesis `hW` is the Lean content of "`ĥ_b` acts nontrivially only on the sites of `W b`":
it commutes with every `ô_z` seated outside `W b`. -/
theorem commutator_orderSum_eq_windowSum {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z)) :
    (∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)
      = ∑ b ∈ B, ∑ z ∈ W b, (hb b * o z - o z * hb b) := by
  rw [commutator_sum_left B (∑ x : Λ, o x) hb]
  refine Finset.sum_congr rfl fun b hbB => ?_
  rw [commutator_sum_right Finset.univ (hb b) o]
  refine (Finset.sum_subset (Finset.subset_univ (W b)) fun z _ hz => ?_).symm
  exact sub_eq_zero.mpr (hW b hbB z hz).eq

/-- Bridge from site-disjoint commutation of the order terms to the outer-window vanishing
hypothesis of the two-window collapse.  If `ĥ_b` commutes with every `ô_z` outside `W b` and
distinct sites carry commuting order operators, then for `x` outside `W b` and `z` inside it the
order term `ô_x` commutes with the inner commutator `[ĥ_b, ô_z]`.  This is exactly the content of
the single-site hypothesis `hoo` that the one-window statements below carry, and this lemma is the
only place `hoo` is used. -/
private theorem commute_order_windowCommutator {ι : Type*} {B : Finset ι}
    {hb : ι → ManyBodyOpS Λ N} {o : Λ → ManyBodyOpS Λ N} {W : ι → Finset Λ}
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z)) :
    ∀ b ∈ B, ∀ x ∉ W b, ∀ z ∈ W b, Commute (o x) (hb b * o z - o z * hb b) := by
  intro b hbB x hx z hz
  have hxz : x ≠ z := by rintro rfl; exact hx hz
  exact ((hW b hbB x hx).symm.mul_right (hoo x z hxz)).sub_right
    ((hoo x z hxz).mul_right (hW b hbB x hx).symm)

/-- **Two-window form of Tasaki eq. (3.4.10), p. 67** — the double commutator collapses onto an
*inner* window `W₁ b` and an *outer* window `W₂ b`, which need not coincide:
`[Ô, [Ĥ, Ô]] = Σ_{b∈B} Σ_{x∈W₂ b} Σ_{z∈W₁ b} [ô_x, [ĥ_b, ô_z]]`.
The inner window carries `hW`, "`ĥ_b` commutes with every `ô_z` seated outside `W₁ b`", and drives
the collapse of `[Ĥ, Ô]` exactly as in eq. (3.4.9).  The outer window carries `hWW`, "`ô_x`
commutes with `[ĥ_b, ô_z]` for `x` outside `W₂ b` and `z` inside `W₁ b`", which is what makes the
remaining site sum collapse onto `W₂ b`.
Two genuinely different windows are needed by Tasaki Problem 3.4.a (pp. 67-68, solution p. 501),
where range-`r` local terms give `W₁` the radius `2r` and `W₂` the radius `4r`; there the
single-site hypothesis `hoo` of the one-window form below need not hold. -/
theorem doubleCommutator_orderSum_eq_twoWindowSum {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W₁ W₂ : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W₁ b, Commute (hb b) (o z))
    (hWW : ∀ b ∈ B, ∀ x ∉ W₂ b, ∀ z ∈ W₁ b, Commute (o x) (hb b * o z - o z * hb b)) :
    (∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
        - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)) * (∑ x : Λ, o x)
      = ∑ b ∈ B, ∑ x ∈ W₂ b, ∑ z ∈ W₁ b,
          (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x) := by
  have hinner : ∀ x : Λ,
      o x * (∑ b ∈ B, ∑ z ∈ W₁ b, (hb b * o z - o z * hb b))
          - (∑ b ∈ B, ∑ z ∈ W₁ b, (hb b * o z - o z * hb b)) * o x
        = ∑ b ∈ B, (o x * (∑ z ∈ W₁ b, (hb b * o z - o z * hb b))
            - (∑ z ∈ W₁ b, (hb b * o z - o z * hb b)) * o x) := fun x =>
    commutator_sum_right B (o x) fun b => ∑ z ∈ W₁ b, (hb b * o z - o z * hb b)
  rw [commutator_orderSum_eq_windowSum B hb o W₁ hW,
    commutator_sum_left Finset.univ (∑ b ∈ B, ∑ z ∈ W₁ b, (hb b * o z - o z * hb b)) o]
  simp only [hinner]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hbB => ?_
  have hcollapse : ∑ x ∈ W₂ b, (o x * (∑ z ∈ W₁ b, (hb b * o z - o z * hb b))
          - (∑ z ∈ W₁ b, (hb b * o z - o z * hb b)) * o x)
      = ∑ x : Λ, (o x * (∑ z ∈ W₁ b, (hb b * o z - o z * hb b))
          - (∑ z ∈ W₁ b, (hb b * o z - o z * hb b)) * o x) := by
    refine Finset.sum_subset (Finset.subset_univ (W₂ b)) fun x _ hx => ?_
    exact sub_eq_zero.mpr (Commute.sum_right _ _ _ fun z hz => hWW b hbB x hx z hz).eq
  rw [← hcollapse]
  exact Finset.sum_congr rfl fun x _ =>
    commutator_sum_right (W₁ b) (o x) fun z => hb b * o z - o z * hb b

/-- **Tasaki eq. (3.4.10), p. 67** — the double commutator of the order operator with the windowed
Hamiltonian collapses onto the windows on *both* index positions:
`[Ô, [Ĥ, Ô]] = Σ_{b∈B} Σ_{x∈W b} Σ_{z∈W b} [ô_x, [ĥ_b, ô_z]]`.
Beyond the window hypothesis `hW` of eq. (3.4.9) this needs `hoo`, the Lean content of "`ô_x` acts
nontrivially only on the spin at `x`": distinct sites carry commuting order operators, which is what
makes the outer sum collapse onto `W b` as well.
This is the instance `W₁ = W₂ = W` of `doubleCommutator_orderSum_eq_twoWindowSum`; the collapse is
proved once, there. -/
theorem doubleCommutator_orderSum_eq_windowSum {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z)) :
    (∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
        - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b)) * (∑ x : Λ, o x)
      = ∑ b ∈ B, ∑ x ∈ W b, ∑ z ∈ W b,
          (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x) :=
  doubleCommutator_orderSum_eq_twoWindowSum B hb o W W hW
    (commute_order_windowCommutator hW hoo)

/-- **Two-window operator-norm kernel for the double commutator**
`‖[Ô, [Ĥ, Ô]]‖ ≤ 4 m₁ m₂ h₀ o₀² |B|`, where `m₁` bounds the *inner* windows `W₁ b` and `m₂` the
*outer* windows `W₂ b`, every `ĥ_b` has norm at most `h₀` and every `ô_x` norm at most `o₀`.
Each of the `|B| · m₂ · m₁` surviving terms of the two-window collapse is bounded by
`‖[ô_x, [ĥ_b, ô_z]]‖ ≤ 2 o₀ · 2 h₀ o₀ = 4 h₀ o₀²` through the commutator norm inequality
`‖[Â, B̂]‖ ≤ 2‖Â‖‖B̂‖` (Tasaki (A.2.5)/(A.2.6), p. 463) applied twice.
The two window bounds occupy fixed index positions: `m₂` counts the outer sum, over `x`, and `m₁`
the inner sum, over `z`.  Instantiating them under the range-`r` support premise of Tasaki
Problem 3.4.a (pp. 67-68) gives `m₁ = (4r+1)^d` and `m₂ = (8r+1)^d`; the printed solution (p. 501)
gives the different pair `m₁ = (2r+1)^d`, `m₂ = (4r+1)^d`, which is its own counting and does not
follow from the range-`r` premise (see `RangeLocalDoubleCommutatorBound.lean`).  Nonnegativity of
`h₀` is not a hypothesis: inside a branch
`b ∈ B` it follows from `0 ≤ ‖ĥ_b‖ ≤ h₀`.  Nonnegativity of `o₀` is one, since with `Λ` empty
nothing forces it. -/
theorem manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W₁ W₂ : ι → Finset Λ)
    (h₀ o₀ : ℝ) (m₁ m₂ : ℕ)
    (hW : ∀ b ∈ B, ∀ z ∉ W₁ b, Commute (hb b) (o z))
    (hWW : ∀ b ∈ B, ∀ x ∉ W₂ b, ∀ z ∈ W₁ b, Commute (o x) (hb b * o z - o z * hb b))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (ho₀ : 0 ≤ o₀)
    (hcard₁ : ∀ b ∈ B, (W₁ b).card ≤ m₁)
    (hcard₂ : ∀ b ∈ B, (W₂ b).card ≤ m₂) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ 4 * (m₁ : ℝ) * (m₂ : ℝ) * h₀ * o₀ ^ 2 * (B.card : ℝ) := by
  have hbound : ∀ b ∈ B, manyBodyOperatorNormS
      (∑ x ∈ W₂ b, ∑ z ∈ W₁ b,
        (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x))
      ≤ 4 * (m₁ : ℝ) * (m₂ : ℝ) * h₀ * o₀ ^ 2 := by
    intro b hbB
    have hh₀ : 0 ≤ h₀ := le_trans (manyBodyOperatorNormS_nonneg (hb b)) (hnh b hbB)
    have hK : (0 : ℝ) ≤ 4 * h₀ * o₀ ^ 2 := mul_nonneg (by linarith) (sq_nonneg o₀)
    have hterm : ∀ x z : Λ, manyBodyOperatorNormS
        (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x)
        ≤ 4 * h₀ * o₀ ^ 2 := by
      intro x z
      have hin : manyBodyOperatorNormS (hb b * o z - o z * hb b) ≤ 2 * h₀ * o₀ :=
        le_trans (manyBodyOperatorNormS_comm_le (hb b) (o z))
          (mul_le_mul (by linarith [hnh b hbB]) (hno z)
            (manyBodyOperatorNormS_nonneg _) (by linarith))
      have hout : manyBodyOperatorNormS
          (o x * (hb b * o z - o z * hb b) - (hb b * o z - o z * hb b) * o x)
          ≤ 2 * o₀ * (2 * h₀ * o₀) :=
        le_trans (manyBodyOperatorNormS_comm_le (o x) _)
          (mul_le_mul (by linarith [hno x]) hin (manyBodyOperatorNormS_nonneg _) (by linarith))
      exact le_trans hout (le_of_eq (by ring))
    refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun x _ =>
      le_trans (manyBodyOperatorNormS_sum_le _ _)
        (Finset.sum_le_sum fun z _ => hterm x z)) ?_
    rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hc₁ : ((W₁ b).card : ℝ) ≤ (m₁ : ℝ) := by exact_mod_cast hcard₁ b hbB
    have hc₂ : ((W₂ b).card : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hcard₂ b hbB
    have hc₁0 : (0 : ℝ) ≤ ((W₁ b).card : ℝ) := Nat.cast_nonneg _
    have hc₂0 : (0 : ℝ) ≤ ((W₂ b).card : ℝ) := Nat.cast_nonneg _
    refine le_trans (mul_le_mul hc₂ (mul_le_mul_of_nonneg_right hc₁ hK)
      (mul_nonneg hc₁0 hK) (le_trans hc₂0 hc₂)) ?_
    exact le_of_eq (by ring)
  rw [doubleCommutator_orderSum_eq_twoWindowSum B hb o W₁ W₂ hW hWW]
  refine le_trans (manyBodyOperatorNormS_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact le_of_eq (by ring)

/-- **Operator-norm bound for the windowed double commutator** (Tasaki §3.4, p. 67, the unnumbered
estimate preceding eq. (3.4.11)):
`‖[Ô, [Ĥ, Ô]]‖ ≤ 4 mW² h₀ o₀² |B|` whenever every `ĥ_b` has norm at most `h₀`, every `ô_x` has norm
at most `o₀`, and every window `W b` has at most `mW` sites.  Each of the `|B| · mW · mW` surviving
terms of eq. (3.4.10) is bounded by `‖[ô_x, [ĥ_b, ô_z]]‖ ≤ 2 o₀ · 2 h₀ o₀ = 4 h₀ o₀²` through the
commutator norm inequality `‖[Â, B̂]‖ ≤ 2‖Â‖‖B̂‖` (Tasaki (A.2.5)/(A.2.6), p. 463) applied twice.
The window bound `mW` is kept variable: the bond case `mW = 2` is the instance yielding the book's
constant `16`.
This is the instance `W₁ = W₂ = W`, `m₁ = m₂ = mW` of
`manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows`, where `4 m₁ m₂` collapses to `4 mW²`;
the estimate is proved once, there. -/
theorem manyBodyOperatorNormS_doubleCommutator_le_of_windows {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (h₀ o₀ : ℝ) (mW : ℕ)
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (ho₀ : 0 ≤ o₀)
    (hcard : ∀ b ∈ B, (W b).card ≤ mW) :
    manyBodyOperatorNormS
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x))
      ≤ 4 * (mW : ℝ) ^ 2 * h₀ * o₀ ^ 2 * (B.card : ℝ) :=
  le_trans (manyBodyOperatorNormS_doubleCommutator_le_of_twoWindows B hb o W W h₀ o₀ mW mW
      hW (commute_order_windowCommutator hW hoo) hnh hno ho₀ hcard hcard)
    (le_of_eq (by ring))

/-- **Tasaki eq. (3.4.11), p. 67** — the printed two-step bound
`⟨Φ_GS|[Ô,[Ĥ,Ô]]|Φ_GS⟩ ≤ ‖[Ô,[Ĥ,Ô]]‖ ≤ {16 d h₀ o₀²} L^d`
for a normalized state `Φ`, bond-local Hamiltonian terms (each window has at most the two endpoints
of a bond) and the hypercubic bond count `|B_L| = d L^d`.  The first inequality is the
operator-norm bound on the expectation in a unit vector and needs no self-adjointness, since it is
taken on the real part; the second is the norm kernel at `mW = 2`, where `4 · 2² = 16`. -/
theorem doubleCommutator_bondLocal_expectation_le {ι : Type*} (B : Finset ι)
    (hb : ι → ManyBodyOpS Λ N) (o : Λ → ManyBodyOpS Λ N) (W : ι → Finset Λ)
    (d L : ℕ) (h₀ o₀ : ℝ) {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hW : ∀ b ∈ B, ∀ z ∉ W b, Commute (hb b) (o z))
    (hoo : ∀ x z : Λ, x ≠ z → Commute (o x) (o z))
    (hnh : ∀ b ∈ B, manyBodyOperatorNormS (hb b) ≤ h₀)
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀)
    (hh₀ : 0 ≤ h₀) (ho₀ : 0 ≤ o₀)
    (hbond : ∀ b ∈ B, (W b).card ≤ 2)
    (hB : (B.card : ℝ) ≤ (d : ℝ) * (L : ℝ) ^ d)
    (hΦ : star Φ ⬝ᵥ Φ = 1) :
    rayleighOnVec
        ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
          - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            * (∑ x : Λ, o x)) Φ
      ≤ manyBodyOperatorNormS
          ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
              * (∑ x : Λ, o x))
      ∧ manyBodyOperatorNormS
          ((∑ x : Λ, o x) * ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
            - ((∑ b ∈ B, hb b) * (∑ x : Λ, o x) - (∑ x : Λ, o x) * (∑ b ∈ B, hb b))
              * (∑ x : Λ, o x))
        ≤ 16 * (d : ℝ) * h₀ * o₀ ^ 2 * (L : ℝ) ^ d := by
  refine ⟨le_trans (le_abs_self _) (expectation_abs_le_manyBodyOperatorNormS _ hΦ), ?_⟩
  refine le_trans (manyBodyOperatorNormS_doubleCommutator_le_of_windows B hb o W h₀ o₀ 2
    hW hoo hnh hno ho₀ hbond) ?_
  have hK : (0 : ℝ) ≤ 16 * h₀ * o₀ ^ 2 := mul_nonneg (by linarith) (sq_nonneg o₀)
  calc 4 * ((2 : ℕ) : ℝ) ^ 2 * h₀ * o₀ ^ 2 * (B.card : ℝ)
      = 16 * h₀ * o₀ ^ 2 * (B.card : ℝ) := by push_cast; ring
    _ ≤ 16 * h₀ * o₀ ^ 2 * ((d : ℝ) * (L : ℝ) ^ d) := mul_le_mul_of_nonneg_left hB hK
    _ = 16 * (d : ℝ) * h₀ * o₀ ^ 2 * (L : ℝ) ^ d := by ring

end LatticeSystem.Quantum
