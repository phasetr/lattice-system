/-
The right-half gauge crux of the bond-square field Hamiltonian
(Tasaki §4.1 Theorem 4.2, reflection-positivity bond-square layer, PR-BS8a-ii).

Conjugating the ungauged Dyson–Lieb–Simon split of the physical bond-square field Hamiltonian
(`ringBondSquareFieldHamiltonian_ungauged_dls`, BS8a-i) by the right-half Marshall gauge `G`
turns it
into the two-field DLS operator `H_L(a) + θ(H_L(b)) − crossing(a,b)` of BS6 (Tasaki (4.1.69), book
p.90).  Because the physical bond-square Hamiltonian staggers its field internally as
`ringBondSquareStagField h x = (−1)ˣ h_x` while the BS6 left half carries the field bare, the crux
input is the **staggered wrapper** `physBondSquareFieldOf n a b z = (−1)ᶻ · physFieldOf n a b z`
(§2.5 of the note); its internal staggering `((−1)ᶻ)² = 1` reduces the effective field to the bare
linear split `physFieldOf a b` (`ringBondSquareStagField_physBondSquareFieldOf`, (W1)).

The gauge is distributed by the algebra-homomorphism laws
(`rightGauge_conj_mul/_add/_sub/_smul/_sum`) with **no square expanded** in the bulk: intra-left
bonds are gauge-fixed (`H_L(a)` bulk via the BS8a-i bridge), intra-right bonds reindex to
`θ(H_L(b))` bulk (the right-half double-sign cancellation of the linear crux, now inside the
un-expanded square), and only the two `O(1)` crossing bonds are completed
`½(A−B)² = ½A² + ½B² − AB` into the two boundary half-squares and the field crossing
`−ringBondSquareFieldCrossing a b`.  The single-ion term splits left/right, the right half
reindexing
to `θ` of the left single-ion.  Assembling gives the gauge crux (G)
`rightGauge_conj_ringBondSquareFieldHamiltonian`, on which PR-BS8b builds the physical-field
identification and the one reflection step.

See `.self-local/docs/math-tasaki-4-1-51-bond-square-physical-field-reflection-step.md`
(issue #4777,
§2/§2.5, PR-BS8a-ii).
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareUngaugedDLS
import LatticeSystem.Quantum.SpinS.RingReflectionFieldPartition
import LatticeSystem.Quantum.SpinS.RingReflectionBondConj
import LatticeSystem.Quantum.SpinS.RingReflectionRPDecomposition
import LatticeSystem.Quantum.SpinS.RingReflectionGibbsGauge

namespace LatticeSystem.Quantum

open Matrix

variable {n N : ℕ}

/-- **Staggered wrapper of the split field** (Tasaki §4.1 (4.1.48)/(4.1.65), book pp.86,90;
note §2.5):
`physBondSquareFieldOf n a b z = (−1)ᶻ · physFieldOf n a b z`.  It is the spin-basis physical field
whose T̂-basis (bare) split field is the linear `physFieldOf a b`.  Feeding it as the physical
bond-square field cancels the physical Hamiltonian's internal `(−1)ᶻ` staggering (via
`((−1)ᶻ)² = 1`, `ringBondSquareStagField_physBondSquareFieldOf`), so the effective field inside the
square is the bare
`physFieldOf a b` and the gauge crux lands on the bare BS6 two-field weight. -/
def physBondSquareFieldOf (n : ℕ) (a b : Fin (2 * n) → ℝ) : Fin (2 * n) → ℝ :=
  fun z => (-1) ^ (z : ℕ) * physFieldOf n a b z

/-- **(W1) staggering elimination** (note §2.5): the physical staggered field of the wrapper is the
bare linear split field,
`ringBondSquareStagField (physBondSquareFieldOf n a b) = physFieldOf n a b`, since
`(−1)ᶻ · (−1)ᶻ = 1`.  This is the only new lemma the crux needs beyond the linear machinery: it
removes the `(−1)ᶻ` residue so that the intra-left/intra-right pieces land on the **bare** BS6
`H_L`/crossing fields. -/
theorem ringBondSquareStagField_physBondSquareFieldOf (n : ℕ) (a b : Fin (2 * n) → ℝ) :
    (fun z => ringBondSquareStagField (physBondSquareFieldOf n a b) z) = physFieldOf n a b := by
  funext z
  simp only [ringBondSquareStagField, physBondSquareFieldOf]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **Left value of the split field**: on the left half `(z : ℕ) < n` the split field is the left
field `a` (Tasaki §4.1 reflected copies (4.1.50), p.86). -/
private theorem physFieldOf_of_lt {n : ℕ} {a b : Fin (2 * n) → ℝ} {z : Fin (2 * n)}
    (hz : (z : ℕ) < n) : physFieldOf n a b z = a z := by
  rw [physFieldOf, if_pos hz]

/-- **Right value of the split field**: on the right half `n ≤ (z : ℕ)` the split field is the
reflected right field `−b (r z)` (Tasaki §4.1 reflected copies (4.1.50), p.86). -/
private theorem physFieldOf_of_ge {n : ℕ} {a b : Fin (2 * n) → ℝ} {z : Fin (2 * n)}
    (hz : n ≤ (z : ℕ)) : physFieldOf n a b z = - b (ringReflect n z) := by
  rw [physFieldOf, if_neg (by omega)]

/-- **Field-congruence of the per-bond term**: `ringBondSquareBondTermOf` depends on the field only
through its two endpoint values, so two fields agreeing at `x` and `x+1` give the same term. -/
private theorem ringBondSquareBondTermOf_congr (n N : ℕ) (f g : Fin (2 * n) → ℝ) (x : Fin (2 * n))
    (h1 : f x = g x) (h2 : f (ringBondSucc n x) = g (ringBondSucc n x)) :
    ringBondSquareBondTermOf n N f x = ringBondSquareBondTermOf n N g x := by
  rw [ringBondSquareBondTermOf, ringBondSquareBondTermOf, h1, h2]

namespace AxisTwoPiRotS

/-- **Conjugation by the right-half gauge distributes over differences.**  A small companion of the
`rightGauge_conj_add/_mul/_smul/_sum` laws, needed to distribute over the bond-square's longitudinal
base `Ŝ³ₓ + Ŝ³_y − f_x·1 − f_y·1`. -/
theorem rightGauge_conj_sub (G : AxisTwoPiRotS N) (n : ℕ) (P Q : ManyBodyOpS (Fin (2 * n)) N) :
    G.rightGauge n * (P - Q) * G.rightGaugeInv n
      = G.rightGauge n * P * G.rightGaugeInv n - G.rightGauge n * Q * G.rightGaugeInv n := by
  rw [mul_sub, sub_mul]

/-- **The right-half gauge fixes a fully-left per-bond term.**  For a bond `(x, x+1)` inside the
left half (`x+1 < n`), every single-site factor is left (gauge-identity) and the central scalar
shifts are
fixed, so the whole bond-square term is unchanged — **no square is expanded**. -/
theorem rightGauge_conj_ringBondSquareBondTermOf_left (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]
    (f : Fin (2 * n) → ℝ) {x : Fin (2 * n)} (hx : (x : ℕ) + 1 < n) :
    G.rightGauge n * ringBondSquareBondTermOf n N f x * G.rightGaugeInv n
      = ringBondSquareBondTermOf n N f x := by
  have hxn : (x : ℕ) < n := by omega
  have hsn : ((ringBondSucc n x : Fin (2 * n)) : ℕ) < n := by
    rw [ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]; omega
  simp only [ringBondSquareBondTermOf, pow_two, rightGauge_conj_add, G.rightGauge_conj_sub n,
    rightGauge_conj_mul, rightGauge_conj_smul, G.rightGauge_conj_onSiteS_left n hxn,
    G.rightGauge_conj_onSiteS_left n hsn, mul_one, G.rightGauge_mul_rightGaugeInv n]

/-- **The right-half gauge sends the physical intra-left bond-square sum to the left field's.**  On
the left half the split field `physFieldOf a b` restricts to `a` and the gauge is the identity, so
`G · ringBondSquareLeftBondSum(physFieldOf a b) · G⁻¹ = ringBondSquareLeftBondSum a`, the intra-left
directed bond-square sum at the left field (bridged to the `H_L(a)` bulk in the assembly). -/
theorem rightGauge_conj_ringBondSquareLeftBondSum (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]
    (a b : Fin (2 * n) → ℝ) :
    G.rightGauge n * ringBondSquareLeftBondSum n N (physFieldOf n a b) * G.rightGaugeInv n
      = ringBondSquareLeftBondSum n N a := by
  rw [ringBondSquareLeftBondSum, ringBondSquareLeftBondSum, rightGauge_conj_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : (x : ℕ) + 1 < n
  · have hxn : (x : ℕ) < n := by omega
    have hsn : ((ringBondSucc n x : Fin (2 * n)) : ℕ) < n := by
      rw [ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]; omega
    rw [if_pos hx, if_pos hx, G.rightGauge_conj_ringBondSquareBondTermOf_left n _ hx,
      ringBondSquareBondTermOf_congr n N (physFieldOf n a b) a x (physFieldOf_of_lt hxn)
        (physFieldOf_of_lt hsn)]
  · rw [if_neg hx, if_neg hx, mul_zero, zero_mul]

/-- **The right-half gauge fixes each single-ion square.**  Conjugating `(Ŝ³ₓ)²` leaves it
invariant:
on left sites the gauge is the identity, on right sites `Ŝ³ ↦ −Ŝ³` and `(−Ŝ³)² = Ŝ³²`. -/
private theorem rightGauge_conj_onSiteS_spinSOp3_sq (G : AxisTwoPiRotS N) (n : ℕ)
    (x : Fin (2 * n)) :
    G.rightGauge n * onSiteS x (spinSOp3 N) ^ 2 * G.rightGaugeInv n
      = onSiteS x (spinSOp3 N) ^ 2 := by
  rw [pow_two, rightGauge_conj_mul, G.rightGauge_conj_onSiteS n x]
  by_cases hxr : n ≤ (x : ℕ)
  · rw [if_pos hxr, G.conj_spinSOp3, onSiteS_neg, neg_mul_neg, ← pow_two]
  · rw [if_neg hxr, ← pow_two]

/-- **The right-half gauge splits the single-ion term into left and reflected-left halves.**  The
whole single-ion `∑_x (Ŝ³ₓ)²` is gauge-fixed square by square; splitting the sum into the left half
and reindexing the right half by the reflection (`sum_right_eq_sum_reflect_left`) exhibits the right
half as `θ` of the left single-ion (`θ(Ŝ³ₓ) = Ŝ³_{r x}`, `θ` multiplicative). -/
theorem rightGauge_conj_ringBondSquareSingleIon (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n] :
    G.rightGauge n * (∑ x : Fin (2 * n), onSiteS x (spinSOp3 N) ^ 2) * G.rightGaugeInv n
      = (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
            onSiteS x (spinSOp3 N) ^ 2)
        + ringReflectionThetaS n N (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
            onSiteS x (spinSOp3 N) ^ 2) := by
  rw [rightGauge_conj_sum,
    Finset.sum_congr rfl (fun x _ => G.rightGauge_conj_onSiteS_spinSOp3_sq n x),
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x : Fin (2 * n) => (x : ℕ) < n)
      (fun x => onSiteS x (spinSOp3 N) ^ 2)]
  congr 1
  rw [ringReflectionThetaS_sum,
    Finset.sum_congr rfl (fun x _ =>
      by rw [ringReflectionThetaS_pow, ringReflectionThetaS_onSiteS_spinSOp3] :
      ∀ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
        ringReflectionThetaS n N (onSiteS x (spinSOp3 N) ^ 2)
          = onSiteS (ringReflect n x) (spinSOp3 N) ^ 2),
    show (Finset.univ.filter (fun x : Fin (2 * n) => ¬ (x : ℕ) < n))
        = Finset.univ.filter (fun x : Fin (2 * n) => n ≤ (x : ℕ)) from by
      apply Finset.filter_congr; intro x _; simp only [not_lt],
    sum_right_eq_sum_reflect_left n (fun x => onSiteS x (spinSOp3 N) ^ 2)]

/-- **The right-half gauge conjugates a two-right-site longitudinal base to its negation.**  On two
right sites `x, y` (`n ≤ x, n ≤ y`), the gauge sends `Ŝ³ ↦ −Ŝ³` on both endpoints and fixes the two
central scalar shifts, so `Ŝ³ₓ + Ŝ³_y − c·1 − d·1 ↦ −(Ŝ³ₓ + Ŝ³_y + c·1 + d·1)`. -/
private theorem rightGauge_conj_base_right (G : AxisTwoPiRotS N) (n : ℕ) {x y : Fin (2 * n)}
    (hx : n ≤ (x : ℕ)) (hy : n ≤ (y : ℕ)) (c d : ℂ) :
    G.rightGauge n * (onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N) - c • 1 - d • 1)
        * G.rightGaugeInv n
      = -(onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N) + c • 1 + d • 1) := by
  rw [G.rightGauge_conj_sub n, G.rightGauge_conj_sub n, rightGauge_conj_add,
    G.rightGauge_conj_onSiteS_right n hx, G.rightGauge_conj_onSiteS_right n hy]
  simp only [G.conj_spinSOp3, onSiteS_neg, rightGauge_conj_smul, mul_one,
    G.rightGauge_mul_rightGaugeInv n]
  abel

/-- **The right-half gauge sends a physical intra-right bond term to `θ` of the reflected left bond
term.**  For a right bond `(x, x+1)` (`n ≤ x`, `x+1 < 2n`) the kinetic factors are gauge-fixed
(`(−Ŝ¹)(−Ŝ¹) = Ŝ¹Ŝ¹`, `Ŝ²` unchanged) and the longitudinal base is negated (`(−base)² = base²`); the
two right-half minus signs — the gauge `−Ŝ³` and the `−b(r·)` slot of `physFieldOf` — cancel, so
after the reflection reindex `x' = r(x+1)` the term is `θ(ringBondSquareBondTermOf b x')` (Tasaki
§4.1 sign crux, note §2, book pp.86,90). -/
private theorem rightGauge_conj_ringBondSquareBondTermOf_right (G : AxisTwoPiRotS N) (n : ℕ)
    [NeZero n] (a b : Fin (2 * n) → ℝ) {x : Fin (2 * n)} (hx : n ≤ (x : ℕ))
    (hx2 : (x : ℕ) + 1 < 2 * n) :
    G.rightGauge n * ringBondSquareBondTermOf n N (physFieldOf n a b) x * G.rightGaugeInv n
      = ringReflectionThetaS n N
          (ringBondSquareBondTermOf n N b (ringReflect n (ringBondSucc n x))) := by
  have hys : ((ringBondSucc n x : Fin (2 * n)) : ℕ) = (x : ℕ) + 1 := by
    rw [ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]
  have hyge : n ≤ ((ringBondSucc n x : Fin (2 * n)) : ℕ) := by rw [hys]; omega
  set y : Fin (2 * n) := ringBondSucc n x with hy_def
  set x' : Fin (2 * n) := ringReflect n y with hx'_def
  -- reflection site identities: r x' = y, r (succ x') = x, r x = succ x'
  have hrx' : ringReflect n x' = y := by rw [hx'_def, ringReflect_involutive]
  have hrsx' : ringReflect n (ringBondSucc n x') = x := by
    apply Fin.ext
    rw [ringReflect_val, ringBondSucc_val, hx'_def, ringReflect_val, hy_def, hys,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hrx_eq : ringReflect n x = ringBondSucc n x' := by rw [← hrsx', ringReflect_involutive]
  have hxy : x ≠ y := by
    intro h; have := congrArg Fin.val h; rw [hys] at this; omega
  -- field identities: f x = −b (succ x'), f y = −b x'
  have hfx : (physFieldOf n a b x : ℝ) = - b (ringBondSucc n x') := by
    rw [physFieldOf_of_ge hx, hrx_eq]
  have hfy : (physFieldOf n a b y : ℝ) = - b x' := by
    rw [physFieldOf_of_ge hyge, ← hx'_def]
  -- base reconciliation (fields substituted, sites reordered)
  have hbase : (onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N)
        + ((- b (ringBondSucc n x') : ℝ) : ℂ) • 1 + ((- b x' : ℝ) : ℂ) • 1)
      = (onSiteS y (spinSOp3 N) + onSiteS x (spinSOp3 N)
        - (b x' : ℂ) • 1 - (b (ringBondSucc n x') : ℂ) • 1) := by
    simp only [Complex.ofReal_neg, neg_smul]; abel
  -- gauge side
  have hL : G.rightGauge n * ringBondSquareBondTermOf n N (physFieldOf n a b) x
        * G.rightGaugeInv n
      = onSiteS x (spinSOp1 N) * onSiteS y (spinSOp1 N)
        + onSiteS x (spinSOp2 N) * onSiteS y (spinSOp2 N)
        + (1 / 2 : ℂ) • (onSiteS x (spinSOp3 N) + onSiteS y (spinSOp3 N)
            + (physFieldOf n a b x : ℂ) • 1 + (physFieldOf n a b y : ℂ) • 1) ^ 2 := by
    rw [ringBondSquareBondTermOf, ← hy_def, pow_two, rightGauge_conj_add, rightGauge_conj_add,
      rightGauge_conj_mul, rightGauge_conj_mul, rightGauge_conj_smul, rightGauge_conj_mul]
    simp only [G.rightGauge_conj_base_right n hx hyge, G.rightGauge_conj_onSiteS_right n hx,
      G.rightGauge_conj_onSiteS_right n hyge, G.conj_spinSOp1, G.conj_spinSOp2, onSiteS_neg,
      neg_mul_neg]
    rw [← pow_two]
  -- θ side
  have hR : ringReflectionThetaS n N (ringBondSquareBondTermOf n N b x')
      = onSiteS y (spinSOp1 N) * onSiteS x (spinSOp1 N)
        + onSiteS y (spinSOp2 N) * onSiteS x (spinSOp2 N)
        + (1 / 2 : ℂ) • (onSiteS y (spinSOp3 N) + onSiteS x (spinSOp3 N)
            - (b x' : ℂ) • 1 - (b (ringBondSucc n x') : ℂ) • 1) ^ 2 := by
    rw [ringBondSquareBondTermOf]
    simp only [ringReflectionThetaS_add, ringReflectionThetaS_sub, ringReflectionThetaS_mul,
      ringReflectionThetaS_smul, ringReflectionThetaS_pow, ringReflectionThetaS_one,
      ringReflectionThetaS_onSiteS_spinSOp1, ringReflectionThetaS_onSiteS_spinSOp2,
      ringReflectionThetaS_onSiteS_spinSOp3, Complex.conj_ofReal, map_div₀, map_one, map_ofNat,
      hrx', hrsx', neg_mul_neg]
  rw [hL, hR, hfx, hfy,
    onSiteS_mul_onSiteS_of_ne hxy (spinSOp1 N) (spinSOp1 N),
    onSiteS_mul_onSiteS_of_ne hxy (spinSOp2 N) (spinSOp2 N), hbase]

/-- **The right-half gauge sends the physical intra-right bond-square sum to `θ` of the left field's
bond-square sum.**  Reindexing the intra-right directed bonds by the reflection `x ↦ r(x+1)` and
applying the per-bond identity `rightGauge_conj_ringBondSquareBondTermOf_right`, the gauged
intra-right
sum equals `θ(ringBondSquareLeftBondSum b)` — the right-half double-sign cancellation of the linear
crux, threaded through the un-expanded square (Tasaki §4.1, note §2/§2.5, book pp.86,90). -/
theorem rightGauge_conj_ringBondSquareRightBondSum (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]
    (a b : Fin (2 * n) → ℝ) :
    G.rightGauge n * ringBondSquareRightBondSum n N (physFieldOf n a b) * G.rightGaugeInv n
      = ringReflectionThetaS n N (ringBondSquareLeftBondSum n N b) := by
  rw [ringBondSquareRightBondSum, rightGauge_conj_sum, ringBondSquareLeftBondSum,
    ringReflectionThetaS_sum]
  refine Fintype.sum_bijective (fun x => ringReflect n (ringBondSucc n x))
    ((ringReflect_bijective n).comp ringBondSucc_bijective) _ _ (fun x => ?_)
  by_cases hr : n ≤ (x : ℕ) ∧ (x : ℕ) + 1 < 2 * n
  · obtain ⟨hx, hx2⟩ := hr
    have heval : ((ringReflect n (ringBondSucc n x) : Fin (2 * n)) : ℕ) + 1 < n := by
      rw [ringReflect_val, ringBondSucc_val, Nat.mod_eq_of_lt (by omega)]; omega
    rw [if_pos ⟨hx, hx2⟩, if_pos heval,
      G.rightGauge_conj_ringBondSquareBondTermOf_right n a b hx hx2]
  · rw [if_neg hr, mul_zero, zero_mul]
    have hne : ¬ (((ringReflect n (ringBondSucc n x) : Fin (2 * n)) : ℕ) + 1 < n) := by
      rw [ringReflect_val, ringBondSucc_val]
      rcases Nat.lt_or_ge ((x : ℕ) + 1) (2 * n) with hc | hc
      · rw [Nat.mod_eq_of_lt hc]
        have hx := x.isLt
        rcases Nat.lt_or_ge (x : ℕ) n with hxn | hxn
        · omega
        · exact absurd ⟨hxn, by omega⟩ hr
      · have : (x : ℕ) + 1 = 2 * n := by have := x.isLt; omega
        rw [this, Nat.mod_self]; omega
    rw [if_neg hne, ringReflectionThetaS_zero]

/-- **The right-half gauge conjugates a crossing-bond longitudinal base to a signed difference.**
On a crossing bond with left site `p` (`p < n`), right site `q` (`n ≤ q`), the gauge fixes `Ŝ³_p`
and sends `Ŝ³_q ↦ −Ŝ³_q`, so `Ŝ³_p + Ŝ³_q − c·1 − d·1 ↦ Ŝ³_p − Ŝ³_q − c·1 − d·1`. -/
private theorem rightGauge_conj_base_cross (G : AxisTwoPiRotS N) (n : ℕ) {p q : Fin (2 * n)}
    (hp : (p : ℕ) < n) (hq : n ≤ (q : ℕ)) (c d : ℂ) :
    G.rightGauge n * (onSiteS p (spinSOp3 N) + onSiteS q (spinSOp3 N) - c • 1 - d • 1)
        * G.rightGaugeInv n
      = onSiteS p (spinSOp3 N) - onSiteS q (spinSOp3 N) - c • 1 - d • 1 := by
  rw [G.rightGauge_conj_sub n, G.rightGauge_conj_sub n, rightGauge_conj_add,
    G.rightGauge_conj_onSiteS_left n hp, G.rightGauge_conj_onSiteS_right n hq]
  simp only [G.conj_spinSOp3, onSiteS_neg, rightGauge_conj_smul, mul_one,
    G.rightGauge_mul_rightGaugeInv n]
  abel

/-- **The right-half gauge completes a physical crossing bond into a boundary half-square, a
`θ`-boundary half-square, and the field crossing block.**  For the crossing bond at crossing index
`i` (left site `p = ringCrossingSite n i`, right site `q = r p`), conjugation completes the square
`½(A − B)² = ½A² + ½B² − AB` with `A = Ŝ³_p − a_p·1`, `B = Ŝ³_q − b_p·1`: the two boundary
half-squares `½A²` (left) and `½B² = θ(½(Ŝ³_p − b_p·1)²)` (reflected), and the negated crossing
block `−∑_α θ(C_{i,α}(b))·C_{i,α}(a)` (kinetic `Ŝ¹`/`Ŝ²` and longitudinal `AB`), the `O(1)` end of
the DLS decomposition (Tasaki (4.1.69), book p.90, note §2). -/
private theorem rightGauge_conj_crossSym (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]
    (a b : Fin (2 * n) → ℝ) (i : Fin 2) :
    G.rightGauge n * (onSiteS (ringCrossingSite n i) (spinSOp1 N)
          * onSiteS (ringReflect n (ringCrossingSite n i)) (spinSOp1 N)
        + onSiteS (ringCrossingSite n i) (spinSOp2 N)
          * onSiteS (ringReflect n (ringCrossingSite n i)) (spinSOp2 N)
        + (1 / 2 : ℂ) • (onSiteS (ringCrossingSite n i) (spinSOp3 N)
            + onSiteS (ringReflect n (ringCrossingSite n i)) (spinSOp3 N)
            - (a (ringCrossingSite n i) : ℂ) • 1
            - (physFieldOf n a b (ringReflect n (ringCrossingSite n i)) : ℂ) • 1) ^ 2)
        * G.rightGaugeInv n
      = (1 / 2 : ℂ) • ((onSiteS (ringCrossingSite n i) (spinSOp3 N)
              + (-(a (ringCrossingSite n i) : ℂ)) • 1)
            * (onSiteS (ringCrossingSite n i) (spinSOp3 N) + (-(a (ringCrossingSite n i) : ℂ)) • 1))
        + ringReflectionThetaS n N ((1 / 2 : ℂ) • ((onSiteS (ringCrossingSite n i) (spinSOp3 N)
              + (-(b (ringCrossingSite n i) : ℂ)) • 1)
            * (onSiteS (ringCrossingSite n i) (spinSOp3 N)
              + (-(b (ringCrossingSite n i) : ℂ)) • 1)))
        - ∑ α : Fin 3, ringReflectionThetaS n N (ringBondSquareCrossingGen n N (i, α) b)
            * ringBondSquareCrossingGen n N (i, α) a := by
  have hp : (ringCrossingSite n i : ℕ) < n := by
    have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    fin_cases i
    · exact hn
    · exact Nat.sub_lt hn Nat.one_pos
  have hq : n ≤ ((ringReflect n (ringCrossingSite n i) : Fin (2 * n)) : ℕ) := by
    rw [ringReflect_val]; omega
  have hrq : ringReflect n (ringReflect n (ringCrossingSite n i)) = ringCrossingSite n i :=
    ringReflect_involutive n _
  have hpq : ringCrossingSite n i ≠ ringReflect n (ringCrossingSite n i) := by
    intro h; have := congrArg Fin.val h; omega
  have hphys : (physFieldOf n a b (ringReflect n (ringCrossingSite n i)) : ℝ)
      = - b (ringCrossingSite n i) := by rw [physFieldOf_of_ge hq, hrq]
  -- gauge the crossing bond term (kinetic fixed up to sign, base negated by `base_cross`)
  rw [pow_two, rightGauge_conj_add, rightGauge_conj_add, rightGauge_conj_mul, rightGauge_conj_mul,
    rightGauge_conj_smul, rightGauge_conj_mul]
  simp only [G.rightGauge_conj_base_cross n hp hq, G.rightGauge_conj_onSiteS_left n hp,
    G.rightGauge_conj_onSiteS_right n hq, G.conj_spinSOp1, G.conj_spinSOp2, onSiteS_neg, mul_neg]
  rw [hphys, Fin.sum_univ_three]
  -- expand the crossing block, the reflected boundary half-square, and all products; canonicalise
  -- the cross bonds to reflected-first order and close by completing the square
  -- first fully reduce the crossing generators and the reflection `θ` (before `neg_smul` can block
  -- `θ` on the field scalars)
  simp only [ringBondSquareCrossingGen, spinSOpFin3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Fin.isValue, Fin.reduceEq, if_true,
    if_false, neg_zero, zero_smul, add_zero, ringReflectionThetaS_smul, ringReflectionThetaS_mul,
    ringReflectionThetaS_add, ringReflectionThetaS_one, ringReflectionThetaS_onSiteS_spinSOp1,
    ringReflectionThetaS_onSiteS_spinSOp2, ringReflectionThetaS_onSiteS_spinSOp3,
    Complex.conj_ofReal, map_neg, map_div₀, map_one, map_ofNat]
  -- then expand every product and canonicalise the cross bonds to reflected-first order
  simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    onSiteS_mul_onSiteS_of_ne hpq (spinSOp1 N) (spinSOp1 N),
    onSiteS_mul_onSiteS_of_ne hpq (spinSOp2 N) (spinSOp2 N),
    onSiteS_mul_onSiteS_of_ne hpq (spinSOp3 N) (spinSOp3 N), neg_mul, mul_neg, neg_smul]
  push_cast
  module

set_option maxHeartbeats 1000000 in -- final DLS reassembly + one large `abel`
/-- **Gauge crux (G): the right-half gauge turns the physical bond-square field Hamiltonian into the
BS6 two-field DLS operator.**  For the staggered wrapper field `physBondSquareFieldOf a b`, whose
effective (bare) field is the linear split `physFieldOf a b` (W1), conjugating the ungauged split
(BS8a-i) by the right-half Marshall gauge lands on `H_L(a) + θ(H_L(b)) − crossing(a,b)`: the
intra-left bulk is gauge-fixed to `H_L(a)`'s bulk, the intra-right bulk reindexes to `θ(H_L(b))`'s
bulk, the two crossing bonds complete into the boundary half-squares and the field crossing, and the
single-ion term splits left/`θ`-right (Tasaki §4.1 (4.1.69), book p.90; DLS 1978 §2–3; note §2). -/
theorem rightGauge_conj_ringBondSquareFieldHamiltonian (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n]
    (a b : Fin (2 * n) → ℝ) :
    G.rightGauge n * ringBondSquareFieldHamiltonian n N (physBondSquareFieldOf n a b)
        * G.rightGaugeInv n
      = ringBondSquareLeftFieldHamiltonian n N a
        + ringReflectionThetaS n N (ringBondSquareLeftFieldHamiltonian n N b)
        - ringBondSquareFieldCrossing n N a b := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- the two crossing bond terms as the symmetric `crossSym` operands
  have hbond1 : ringBondSquareBondTermOf n N (physFieldOf n a b) ⟨n - 1, by omega⟩
      = onSiteS (ringCrossingSite n 1) (spinSOp1 N)
          * onSiteS (ringReflect n (ringCrossingSite n 1)) (spinSOp1 N)
        + onSiteS (ringCrossingSite n 1) (spinSOp2 N)
          * onSiteS (ringReflect n (ringCrossingSite n 1)) (spinSOp2 N)
        + (1 / 2 : ℂ) • (onSiteS (ringCrossingSite n 1) (spinSOp3 N)
            + onSiteS (ringReflect n (ringCrossingSite n 1)) (spinSOp3 N)
            - (a (ringCrossingSite n 1) : ℂ) • 1
            - (physFieldOf n a b (ringReflect n (ringCrossingSite n 1)) : ℂ) • 1) ^ 2 := by
    have hidx : (⟨n - 1, by omega⟩ : Fin (2 * n)) = ringCrossingSite n 1 := by
      apply Fin.ext; simp [ringCrossingSite_one_val]
    have hsucc : ringBondSucc n (ringCrossingSite n 1) = ringReflect n (ringCrossingSite n 1) := by
      apply Fin.ext
      rw [ringBondSucc_val, ringReflect_val, ringCrossingSite_one_val, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [ringBondSquareBondTermOf, hidx, hsucc,
      physFieldOf_of_lt (show ((ringCrossingSite n 1 : Fin (2 * n)) : ℕ) < n by
        rw [ringCrossingSite_one_val]; omega)]
  have hbond0 : ringBondSquareBondTermOf n N (physFieldOf n a b) ⟨2 * n - 1, by omega⟩
      = onSiteS (ringCrossingSite n 0) (spinSOp1 N)
          * onSiteS (ringReflect n (ringCrossingSite n 0)) (spinSOp1 N)
        + onSiteS (ringCrossingSite n 0) (spinSOp2 N)
          * onSiteS (ringReflect n (ringCrossingSite n 0)) (spinSOp2 N)
        + (1 / 2 : ℂ) • (onSiteS (ringCrossingSite n 0) (spinSOp3 N)
            + onSiteS (ringReflect n (ringCrossingSite n 0)) (spinSOp3 N)
            - (a (ringCrossingSite n 0) : ℂ) • 1
            - (physFieldOf n a b (ringReflect n (ringCrossingSite n 0)) : ℂ) • 1) ^ 2 := by
    have hidx0 : ringBondSucc n (⟨2 * n - 1, by omega⟩ : Fin (2 * n)) = ringCrossingSite n 0 := by
      apply Fin.ext
      rw [ringBondSucc_val, ringCrossingSite_zero_val,
        show (⟨2 * n - 1, by omega⟩ : Fin (2 * n)).val = 2 * n - 1 from rfl,
        show 2 * n - 1 + 1 = 2 * n by omega, Nat.mod_self]
    have hbidx0 : (⟨2 * n - 1, by omega⟩ : Fin (2 * n)) = ringReflect n (ringCrossingSite n 0) := by
      apply Fin.ext
      rw [ringReflect_val, ringCrossingSite_zero_val,
        show (⟨2 * n - 1, by omega⟩ : Fin (2 * n)).val = 2 * n - 1 from rfl]
      omega
    have hne : ringReflect n (ringCrossingSite n 0) ≠ ringCrossingSite n 0 := by
      intro h; have := congrArg Fin.val h
      rw [ringReflect_val, ringCrossingSite_zero_val] at this; omega
    rw [ringBondSquareBondTermOf, hidx0, hbidx0,
      physFieldOf_of_lt (show ((ringCrossingSite n 0 : Fin (2 * n)) : ℕ) < n by
        rw [ringCrossingSite_zero_val]; omega),
      onSiteS_mul_onSiteS_of_ne hne (spinSOp1 N) (spinSOp1 N),
      onSiteS_mul_onSiteS_of_ne hne (spinSOp2 N) (spinSOp2 N)]
    congr 2
    abel
  -- single-ion `(-1)•(Ŝ³Ŝ³)` sum ↔ negated `(Ŝ³)²` sum, and `θ` of the negation
  have hSI : (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
        (-1 : ℂ) • (onSiteS x (spinSOp3 N) * onSiteS x (spinSOp3 N)))
      = -∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
          onSiteS x (spinSOp3 N) ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun x _ => by rw [neg_one_smul, pow_two])
  have hThetaNeg : ringReflectionThetaS n N
        (-∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n), onSiteS x (spinSOp3 N) ^ 2)
      = -ringReflectionThetaS n N
          (∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
            onSiteS x (spinSOp3 N) ^ 2) := by
    rw [show (-∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
          onSiteS x (spinSOp3 N) ^ 2)
        = 0 - ∑ x ∈ Finset.univ.filter (fun x : Fin (2 * n) => (x : ℕ) < n),
          onSiteS x (spinSOp3 N) ^ 2 from (zero_sub _).symm,
      ringReflectionThetaS_sub, ringReflectionThetaS_zero, zero_sub]
  -- distribute the gauge over the ungauged DLS split and discharge each piece
  rw [ringBondSquareFieldHamiltonian_ungauged_dls]
  simp only [ringBondSquareStagField_physBondSquareFieldOf]
  rw [G.rightGauge_conj_sub n, rightGauge_conj_add,
    rightGauge_conj_add, rightGauge_conj_add, G.rightGauge_conj_ringBondSquareLeftBondSum n a b,
    G.rightGauge_conj_ringBondSquareRightBondSum n a b, hbond1, G.rightGauge_conj_crossSym n a b 1,
    hbond0, G.rightGauge_conj_crossSym n a b 0, G.rightGauge_conj_ringBondSquareSingleIon n]
  -- unfold the DLS targets, collapse the bulk bridge, the single-ion, boundary and crossing sums
  rw [ringBondSquareLeftFieldHamiltonian,
    ← ringBondSquareLeftBondSum_eq_leftCouplingBulk n N a, hSI,
    ringBondSquareLeftFieldHamiltonian, ← ringBondSquareLeftBondSum_eq_leftCouplingBulk n N b, hSI,
    ringReflectionThetaS_add, ringReflectionThetaS_add, hThetaNeg, Fin.sum_univ_two,
    Fin.sum_univ_two, ringReflectionThetaS_add,
    ringBondSquareFieldCrossing, Fintype.sum_prod_type, Fin.sum_univ_two]
  abel

end AxisTwoPiRotS

end LatticeSystem.Quantum
