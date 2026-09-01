import LatticeSystem.Quantum.KaplanHorschVonderLinden
import LatticeSystem.Quantum.HorschVonderLindenLowLyingState
import LatticeSystem.Quantum.SpinS.ExpectationNormBound

/-!
# Tasaki §3.4 Theorem 3.2 (Kaplan–Horsch–von der Linden): eqs. (3.4.21)-(3.4.22)

Theorem 3.2 says that an infinitesimal symmetry-breaking field triggers spontaneous symmetry
breaking: with the order operator `Ô_L`, the field-perturbed Hamiltonian `Ĥ_h = Ĥ − h Ô_L`
(eq. (3.4.19)) and a ground state `Φ_GS,h` of `Ĥ_h`, the printed conclusion is
`lim_{h↓0} lim_{L↑∞} ⟨Φ_GS,h|Ô_L/L^d|Φ_GS,h⟩ ≥ √q₀` (eq. (3.4.22), p. 70).  Footnote 24, p. 70,
records that these limits are rigorously `liminf`, and `tasaki_theorem_3_2_kaplanHorschVonderLinden`
is stated that way: the inner limit over the volume index `L` along `atTop`, the outer limit over
the field strength `h` along `𝓝[>] 0`, in the printed order.

The nesting carries content rather than presentation.  On the bounded family `min (h·L) 1` the
printed order returns `1` while the exchanged order returns `0`, which is the reason the source
gives for the order: at a fixed volume `⟨Φ_GS,h|Ô_L/L^d|Φ_GS,h⟩ → 0` as `h ↓ 0` by continuity, so
the field's effect survives only once the volume limit has been taken first.

The real-valued `liminf` forces side conditions that the physics does not.  `Filter.liminf` on `ℝ`
is the supremum of the eventual lower bounds, and a real supremum of a set unbounded above is the
junk value `0`, so an order parameter diverging with the volume would have `liminf` `0`; that is
why the statement carries an upper bound at all.  The hypothesis `hub` is that bound, and
`tasaki_orderParameter_uniformBound` produces one from a per-site operator-norm bound together with
a carrier hypothesis `#Λ ≤ L^d`.  Separately, the error term
`C/(h·L^{2d})` decays only for `1 ≤ d`; at `d = 0` it is the constant `C/h` and the volume limit
fails.  The constant that eq. (3.4.12) supplies carries a factor `d`, so it vanishes at `d = 0`,
but the abstract `C` used here cannot record that.

The finite-volume input is `kaplan_horsch_vonderLinden_order_lower_bound`
(`Quantum/KaplanHorschVonderLinden.lean`), which is eq. (3.4.21)'s first line rearranged from the
ground-state inequality eq. (3.4.20).  Two of the conjuncts that
`tasaki_eq_3_4_16_lowLyingState_ssb` (`Quantum/HorschVonderLindenLowLyingState.lean`) establishes at
`Ξ = Ξ₊` are hypotheses of the declarations below: the order-parameter bound
`⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀` of eq. (3.4.16) as `hXi`, and the halved eq. (3.4.12) bound
`⟨Ξ₊|Ĥ|Ξ₊⟩ − E_GS ≤ (C/2)L^{-d}` as `hen`.  The `L`-indexed and
`h`-indexed family is carried at the matrix level, so the §3.4 packaging meets the limits through
the instantiation of those hypotheses rather than through a declaration in this module.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §3.4, eq. (3.4.12), p. 67, eq. (3.4.16), p. 68, Theorem 3.2 with footnote 24 and
eqs. (3.4.19)-(3.4.22), pp. 69-70.
-/

namespace LatticeSystem.Quantum

open Matrix Filter Topology

/-! ### Analysis helpers for the volume limit -/

/-- The error term of the per-volume bound vanishes in the volume limit: for `1 ≤ d` and `h > 0`,
`C/(h·(L^d)^2) → 0` as `L ↑ ∞`.  The denominator diverges because `(L : ℝ) ≤ (L^d)^2` once
`1 ≤ L`, which needs `1 ≤ d`; at `d = 0` the function is the constant `C/h`. -/
private theorem kaplanHorschVonderLinden_errorTerm_tendsto_zero {C h : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hh : 0 < h) :
    Tendsto (fun L : ℕ => C / (h * ((L : ℝ) ^ d) ^ 2)) atTop (𝓝 0) := by
  refine Tendsto.div_atTop tendsto_const_nhds (Tendsto.const_mul_atTop hh ?_)
  refine tendsto_atTop_mono' atTop ?_ (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  calc (L : ℝ) = (L : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (L : ℝ) ^ (d * 2) := pow_le_pow_right₀ hL1 (by omega)
    _ = ((L : ℝ) ^ d) ^ 2 := (pow_mul _ _ _)

/-- The `liminf` kernel of the volume limit.  A real sequence `f` squeezed from below by
`m − C/(h·(L^d)^2)` and from above by `o₀`, both from `L = 1` on, has `m ≤ liminf f atTop` and
`liminf f atTop ≤ o₀`.  The lower conjunct is monotonicity of `liminf` against the convergent
minorant; the upper conjunct is what makes the lower one meaningful, since a real `liminf` is a
supremum of eventual lower bounds and takes the junk value `0` when the sequence diverges. -/
private theorem kaplanHorschVonderLinden_liminf_bounds {f : ℕ → ℝ} {m C h o₀ : ℝ} {d : ℕ}
    (hd : 1 ≤ d) (hh : 0 < h)
    (hlb : ∀ L : ℕ, 1 ≤ L → m - C / (h * ((L : ℝ) ^ d) ^ 2) ≤ f L)
    (hub : ∀ L : ℕ, 1 ≤ L → f L ≤ o₀) :
    m ≤ liminf f atTop ∧ liminf f atTop ≤ o₀ := by
  have hg : Tendsto (fun L : ℕ => m - C / (h * ((L : ℝ) ^ d) ^ 2)) atTop (𝓝 m) := by
    have := (tendsto_const_nhds (x := m) (f := atTop (α := ℕ))).sub
      (kaplanHorschVonderLinden_errorTerm_tendsto_zero (C := C) hd hh)
    simpa using this
  have hle : ∀ᶠ L : ℕ in atTop, m - C / (h * ((L : ℝ) ^ d) ^ 2) ≤ f L := by
    filter_upwards [eventually_ge_atTop 1] with L hL using hlb L hL
  have hub' : ∀ᶠ L : ℕ in atTop, f L ≤ o₀ := by
    filter_upwards [eventually_ge_atTop 1] with L hL using hub L hL
  refine ⟨?_, ?_⟩
  · calc m = liminf (fun L : ℕ => m - C / (h * ((L : ℝ) ^ d) ^ 2)) atTop := hg.liminf_eq.symm
      _ ≤ liminf f atTop :=
          Filter.liminf_le_liminf hle hg.isBoundedUnder_ge
            (isCoboundedUnder_ge_of_eventually_le atTop hub')
  · refine liminf_le_of_le ?_ ?_
    · obtain ⟨b, hb⟩ := hg.isBoundedUnder_ge
      refine ⟨b, Filter.eventually_map.mpr ?_⟩
      filter_upwards [Filter.eventually_map.mp hb, hle] with L h1 h2 using le_trans h1 h2
    · intro b hb
      obtain ⟨L, hL⟩ := (hb.and hub').exists
      exact le_trans hL.1 hL.2

/-! ### Eq. (3.4.21) at a single volume -/

/-- **Eq. (3.4.21), printed second line, per volume** (Tasaki §3.4, p. 70).  Divide
`kaplan_horsch_vonderLinden_order_lower_bound` by a volume `Ld > 0` and feed it the trial-state
order bound `hXi`, which at `Ξ = Ξ₊` and `Ld = L^d` is eq. (3.4.16)'s `⟨Ξ₊|Ô_L/L^d|Ξ₊⟩ ≥ √q₀`:
from the variational hypothesis `hvar` placing the perturbed state `Ψ` at or below the trial state
`Ξ` in the Rayleigh energy of `H − h·O` (eq. (3.4.20)) and the ground-energy bound `hE₀`, the
per-volume order parameter of `Ψ` obeys `m + (E₀ − ⟨Ξ|H|Ξ⟩)/(h·Ld) ≤ ⟨Ψ|O|Ψ⟩/Ld`.  The field `h`
enters as a divisor, so `0 < h` is what fixes the direction of the second term. -/
theorem tasaki_eq_3_4_21_perVolume {n : Type*} [Fintype n] (H O : Matrix n n ℂ) {h Ld m E₀ : ℝ}
    (hh : 0 < h) (hLd : 0 < Ld) (Ψ Ξ : n → ℂ)
    (hvar : rayleighOnVec (H - (h : ℂ) • O) Ψ ≤ rayleighOnVec (H - (h : ℂ) • O) Ξ)
    (hE₀ : E₀ ≤ rayleighOnVec H Ψ)
    (hXi : m ≤ rayleighOnVec O Ξ / Ld) :
    m + (E₀ - rayleighOnVec H Ξ) / (h * Ld) ≤ rayleighOnVec O Ψ / Ld := by
  have core := kaplan_horsch_vonderLinden_order_lower_bound H O hh Ψ Ξ hvar hE₀
  have hdiv : (rayleighOnVec O Ξ + (E₀ - rayleighOnVec H Ξ) / h) / Ld
      ≤ rayleighOnVec O Ψ / Ld := by gcongr
  have heq : (rayleighOnVec O Ξ + (E₀ - rayleighOnVec H Ξ) / h) / Ld
      = rayleighOnVec O Ξ / Ld + (E₀ - rayleighOnVec H Ξ) / (h * Ld) := by field_simp
  rw [heq] at hdiv
  linarith

/-- **Eq. (3.4.21) per volume with the trial energy bound made explicit** (Tasaki §3.4, p. 70).
Replacing the error term of `tasaki_eq_3_4_21_perVolume` by the trial-state energy bound
`hen : ⟨Ξ|H|Ξ⟩ − E₀ ≤ C/Ld` gives `m − C/(h·Ld^2) ≤ ⟨Ψ|O|Ψ⟩/Ld`.  At `Ξ = Ξ₊` and `Ld = L^d`,
`hen` is the halved eq. (3.4.12) bound `⟨Ξ₊|Ĥ|Ξ₊⟩ − E_GS ≤ (C/2)L^{-d}` with `C` standing for the
source's `C/2`, and the squared `Ld` of the conclusion is `L^{2d}`: one factor `L^{-d}` from `hen`
and one from dividing the order parameter by the volume. -/
theorem tasaki_eq_3_4_21_perVolume_energyBound {n : Type*} [Fintype n] (H O : Matrix n n ℂ)
    {h Ld m C E₀ : ℝ} (hh : 0 < h) (hLd : 0 < Ld) (Ψ Ξ : n → ℂ)
    (hvar : rayleighOnVec (H - (h : ℂ) • O) Ψ ≤ rayleighOnVec (H - (h : ℂ) • O) Ξ)
    (hE₀ : E₀ ≤ rayleighOnVec H Ψ)
    (hXi : m ≤ rayleighOnVec O Ξ / Ld)
    (hen : rayleighOnVec H Ξ - E₀ ≤ C / Ld) :
    m - C / (h * Ld ^ 2) ≤ rayleighOnVec O Ψ / Ld := by
  have h1 := tasaki_eq_3_4_21_perVolume H O hh hLd Ψ Ξ hvar hE₀ hXi
  have h2 : -(C / Ld) / (h * Ld) ≤ (E₀ - rayleighOnVec H Ξ) / (h * Ld) := by
    gcongr
    linarith
  have h3 : -(C / Ld) / (h * Ld) = -(C / (h * Ld ^ 2)) := by field_simp
  rw [h3] at h2
  linarith

/-! ### The uniform order-parameter bound -/

/-- **The order parameter per volume is bounded by the per-site operator-norm bound.**  For a
family `o : Λ → ManyBodyOpS Λ N` whose members have operator norm at most `o₀ ≥ 0`, a normalised
state `Ψ`, and a carrier satisfying `#Λ ≤ L^d` with `1 ≤ L`, the mean
`⟨Ψ|(∑ x, o x)|Ψ⟩/L^d` has absolute value at most `o₀`.  The carrier hypothesis is what converts
the extensive bound `#Λ · o₀` on the sum into an intensive one; eq. (3.4.12)'s bond-count
hypothesis bounds the number of interaction bonds and does not supply it.  The conclusion has the
shape of the uniform bound `hub` that `tasaki_theorem_3_2_kaplanHorschVonderLinden` takes
abstractly; no declaration here composes the two. -/
theorem tasaki_orderParameter_uniformBound {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (o : Λ → ManyBodyOpS Λ N) {o₀ : ℝ} {d L : ℕ}
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀) (ho₀ : 0 ≤ o₀)
    (hcard : (Fintype.card Λ : ℝ) ≤ (L : ℝ) ^ d) (hL : 1 ≤ L)
    {Ψ : (Λ → Fin (N + 1)) → ℂ} (hΨ : star Ψ ⬝ᵥ Ψ = 1) :
    |rayleighOnVec (∑ x : Λ, o x) Ψ / (L : ℝ) ^ d| ≤ o₀ := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    positivity
  have h1 : |rayleighOnVec (∑ x : Λ, o x) Ψ| ≤ manyBodyOperatorNormS (∑ x : Λ, o x) :=
    expectation_abs_le_manyBodyOperatorNormS _ hΨ
  have h2 : manyBodyOperatorNormS (∑ x : Λ, o x) ≤ ∑ x : Λ, manyBodyOperatorNormS (o x) :=
    manyBodyOperatorNormS_sum_le _ _
  have h3 : ∑ x : Λ, manyBodyOperatorNormS (o x) ≤ (Fintype.card Λ : ℝ) * o₀ := by
    calc ∑ x : Λ, manyBodyOperatorNormS (o x)
        ≤ ∑ _x : Λ, o₀ := Finset.sum_le_sum (fun x _ => hno x)
      _ = (Fintype.card Λ : ℝ) * o₀ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h4 : |rayleighOnVec (∑ x : Λ, o x) Ψ| ≤ (L : ℝ) ^ d * o₀ :=
    le_trans h1 (le_trans h2 (le_trans h3 (mul_le_mul_of_nonneg_right hcard ho₀)))
  rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
  linarith

/-! ### The volume limit and the capstone -/

/-- The family-level form of `kaplanHorschVonderLinden_liminf_bounds`.  At every `L ≥ 1` the
per-volume bound `tasaki_eq_3_4_21_perVolume_energyBound` supplies the minorant
`m − C/(h·(L^d)^2)` and `hub` supplies the majorant `o₀`, so the order mean's `liminf` lies between
`m` and `o₀`.  Both halves are produced together because the upper one is not a weakening of the
lower: the outer `liminf` of `tasaki_theorem_3_2_kaplanHorschVonderLinden` consumes it as a
coboundedness witness, while `tasaki_eq_3_4_21_volumeLiminf` exposes only the lower one. -/
private theorem kaplanHorschVonderLinden_volumeLiminf_bounds {n : ℕ → Type*} [∀ L, Fintype (n L)]
    (H O : (L : ℕ) → Matrix (n L) (n L) ℂ) (Ψ Ξ : (L : ℕ) → n L → ℂ) (E : ℕ → ℝ)
    {d : ℕ} {h m C o₀ : ℝ} (hd : 1 ≤ d) (hh : 0 < h)
    (hvar : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (H L - (h : ℂ) • O L) (Ψ L)
      ≤ rayleighOnVec (H L - (h : ℂ) • O L) (Ξ L))
    (hE : ∀ L : ℕ, 1 ≤ L → E L ≤ rayleighOnVec (H L) (Ψ L))
    (hXi : ∀ L : ℕ, 1 ≤ L → m ≤ rayleighOnVec (O L) (Ξ L) / (L : ℝ) ^ d)
    (hen : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (H L) (Ξ L) - E L ≤ C / (L : ℝ) ^ d)
    (hub : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (O L) (Ψ L) / (L : ℝ) ^ d ≤ o₀) :
    m ≤ liminf (fun L : ℕ => rayleighOnVec (O L) (Ψ L) / (L : ℝ) ^ d) atTop
      ∧ liminf (fun L : ℕ => rayleighOnVec (O L) (Ψ L) / (L : ℝ) ^ d) atTop ≤ o₀ :=
  kaplanHorschVonderLinden_liminf_bounds hd hh (fun L hL => by
    have hLpos : (0 : ℝ) < (L : ℝ) ^ d := by
      have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      positivity
    exact tasaki_eq_3_4_21_perVolume_energyBound (H L) (O L) hh hLpos (Ψ L) (Ξ L)
      (hvar L hL) (hE L hL) (hXi L hL) (hen L hL)) hub

/-- **The inner volume limit of eq. (3.4.22)** (Tasaki §3.4, p. 70).  For an `L`-indexed family of
matrices, perturbed states `Ψ L`, trial states `Ξ L` and ground energies `E L` satisfying the
hypotheses of `tasaki_eq_3_4_21_perVolume_energyBound` at every `L ≥ 1` with `Ld = L^d`, together
with the uniform upper bound `hub`, the order parameter obeys
`m ≤ liminf_{L ↑ ∞} ⟨Ψ L|O L|Ψ L⟩/L^d`.  Each hypothesis is guarded by `1 ≤ L`, and `atTop` is
insensitive to any finite set of indices, so the value of the family at `L = 0` is unconstrained.
The dimension hypothesis `1 ≤ d` is used through the error term: at `d = 0` the error is the
constant `C/h` and the conclusion fails. -/
theorem tasaki_eq_3_4_21_volumeLiminf {n : ℕ → Type*} [∀ L, Fintype (n L)]
    (H O : (L : ℕ) → Matrix (n L) (n L) ℂ) (Ψ Ξ : (L : ℕ) → n L → ℂ) (E : ℕ → ℝ)
    {d : ℕ} {h m C o₀ : ℝ} (hd : 1 ≤ d) (hh : 0 < h)
    (hvar : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (H L - (h : ℂ) • O L) (Ψ L)
      ≤ rayleighOnVec (H L - (h : ℂ) • O L) (Ξ L))
    (hE : ∀ L : ℕ, 1 ≤ L → E L ≤ rayleighOnVec (H L) (Ψ L))
    (hXi : ∀ L : ℕ, 1 ≤ L → m ≤ rayleighOnVec (O L) (Ξ L) / (L : ℝ) ^ d)
    (hen : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (H L) (Ξ L) - E L ≤ C / (L : ℝ) ^ d)
    (hub : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (O L) (Ψ L) / (L : ℝ) ^ d ≤ o₀) :
    m ≤ liminf (fun L : ℕ => rayleighOnVec (O L) (Ψ L) / (L : ℝ) ^ d) atTop :=
  (kaplanHorschVonderLinden_volumeLiminf_bounds H O Ψ Ξ E hd hh hvar hE hXi hen hub).1

/-- **Tasaki Theorem 3.2 (Kaplan–Horsch–von der Linden), eq. (3.4.22)** (§3.4, p. 70).  For an
`L`-indexed family of Hamiltonians `H L` and order operators `O L`, trial states `Ξ L`, ground
energies `E L`, and a family `Ψ h L` of ground states of the field-perturbed Hamiltonian
`H L − h·(O L)` satisfying eq. (3.4.20) at every `h > 0` and `L ≥ 1`, whose trial states obey the
eq. (3.4.16) order bound `hXi` at `√q₀` and the halved eq. (3.4.12) energy bound `hen`, and whose
order parameters obey the uniform bound `hub`, one has
`√q₀ ≤ liminf_{h ↓ 0} liminf_{L ↑ ∞} ⟨Ψ h L|O L|Ψ h L⟩/L^d`.
Both limits are `liminf` per footnote 24, the inner over `L` along `atTop` and the outer over `h`
along `𝓝[>] 0`.  The outer `liminf` takes its lower bound from the inner one at each `h > 0`, and
its coboundedness from `hub`, which bounds the inner `liminf` above by `o₀`. -/
theorem tasaki_theorem_3_2_kaplanHorschVonderLinden {n : ℕ → Type*} [∀ L, Fintype (n L)]
    (H O : (L : ℕ) → Matrix (n L) (n L) ℂ) (Ξ : (L : ℕ) → n L → ℂ)
    (Ψ : ℝ → (L : ℕ) → n L → ℂ) (E : ℕ → ℝ)
    {d : ℕ} {q₀ C o₀ : ℝ} (hd : 1 ≤ d)
    (hvar : ∀ h : ℝ, 0 < h → ∀ L : ℕ, 1 ≤ L →
      rayleighOnVec (H L - (h : ℂ) • O L) (Ψ h L)
        ≤ rayleighOnVec (H L - (h : ℂ) • O L) (Ξ L))
    (hE : ∀ h : ℝ, 0 < h → ∀ L : ℕ, 1 ≤ L → E L ≤ rayleighOnVec (H L) (Ψ h L))
    (hXi : ∀ L : ℕ, 1 ≤ L → Real.sqrt q₀ ≤ rayleighOnVec (O L) (Ξ L) / (L : ℝ) ^ d)
    (hen : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (H L) (Ξ L) - E L ≤ C / (L : ℝ) ^ d)
    (hub : ∀ h : ℝ, 0 < h → ∀ L : ℕ, 1 ≤ L →
      rayleighOnVec (O L) (Ψ h L) / (L : ℝ) ^ d ≤ o₀) :
    Real.sqrt q₀ ≤ liminf (fun h : ℝ => liminf (fun L : ℕ =>
      rayleighOnVec (O L) (Ψ h L) / (L : ℝ) ^ d) atTop) (𝓝[>] (0 : ℝ)) := by
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), 0 < h := self_mem_nhdsWithin
  have hcobound : ∀ h : ℝ, 0 < h →
      liminf (fun L : ℕ => rayleighOnVec (O L) (Ψ h L) / (L : ℝ) ^ d) atTop ≤ o₀ := fun h hh =>
    (kaplanHorschVonderLinden_volumeLiminf_bounds H O (Ψ h) Ξ E hd hh (hvar h hh) (hE h hh) hXi
      hen (hub h hh)).2
  refine le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le _ (x := o₀) ?_) ?_
  · filter_upwards [hpos] with h hh using hcobound h hh
  · filter_upwards [hpos] with h hh using
      tasaki_eq_3_4_21_volumeLiminf H O (Ψ h) Ξ E hd hh (hvar h hh) (hE h hh) hXi hen (hub h hh)

end LatticeSystem.Quantum
