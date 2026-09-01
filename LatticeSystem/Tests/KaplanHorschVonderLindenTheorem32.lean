import LatticeSystem.Quantum.KaplanHorschVonderLindenTheorem32

/-!
# Test coverage for Theorem 3.2 (Kaplan-Horsch-von der Linden), eqs. (3.4.21)-(3.4.22)

Fixtures for `LatticeSystem/Quantum/KaplanHorschVonderLindenTheorem32.lean`: signature pins for
`tasaki_eq_3_4_21_perVolume`, `tasaki_eq_3_4_21_perVolume_energyBound`,
`tasaki_eq_3_4_21_volumeLiminf`, `tasaki_orderParameter_uniformBound`, and the capstone
`tasaki_theorem_3_2_kaplanHorschVonderLinden`; a boundedness/non-vacuity witness at `q₀ = 1`; a
sharpness witness whose per-volume value is strictly below the bound at every volume; `d = 0` and
`h < 0` counterexamples; a limit-order pair on a shared bounded family; and a tight/slack pair for
the uniform bound. Also pins that `rayleighOnVec_sub_smul`
(`LatticeSystem/Quantum/KaplanHorschVonderLinden.lean`) is visible outside its defining module.

Several steps of the statement typecheck when written wrongly, which is what the counterexample
blocks are for. The `L^d` and `L^{2d}` error denominators agree at `L^d = 1`, so the sharpness
family is read at `d = 1` and pins its per-volume value exactly. The exchanged limit order also
elaborates, so both orders are computed on one shared bounded family: they come out `1` and `0`
there, which separates the two nestings without instantiating the capstone. The variational
hypothesis's direction is pinned by the four signature examples that carry it, each of which
typechecks only against the exact inequality written, and not by any numeric instance. The uniform
bound carries no variational hypothesis at all; its tight and slack instances exercise the carrier
hypothesis `hcard` at and away from equality.
-/

namespace LatticeSystem.Quantum

open Matrix Filter Topology

/-! ### Signature pins -/

/-- Pins that `rayleighOnVec_sub_smul` is exported from its defining module, hence callable from
this separate test file. -/
example {n : Type*} [Fintype n] (H O : Matrix n n ℂ) (h : ℝ) (v : n → ℂ) :
    rayleighOnVec (H - (h : ℂ) • O) v = rayleighOnVec H v - h * rayleighOnVec O v :=
  rayleighOnVec_sub_smul H O h v

/-- Pins `tasaki_eq_3_4_21_perVolume`, eq. (3.4.21)'s printed second line: the finite-volume
variational lower bound divided through by a volume `Ld > 0`, with the trial-state order mean
carried abstractly via `hXi`. -/
example {n : Type*} [Fintype n] (H O : Matrix n n ℂ) {h Ld m E₀ : ℝ}
    (hh : 0 < h) (hLd : 0 < Ld) (Ψ Ξ : n → ℂ)
    (hvar : rayleighOnVec (H - (h : ℂ) • O) Ψ ≤ rayleighOnVec (H - (h : ℂ) • O) Ξ)
    (hE₀ : E₀ ≤ rayleighOnVec H Ψ)
    (hXi : m ≤ rayleighOnVec O Ξ / Ld) :
    m + (E₀ - rayleighOnVec H Ξ) / (h * Ld) ≤ rayleighOnVec O Ψ / Ld :=
  tasaki_eq_3_4_21_perVolume H O hh hLd Ψ Ξ hvar hE₀ hXi

/-- Pins `tasaki_eq_3_4_21_perVolume_energyBound`, the same per-volume bound with the halved eq.
(3.4.12) trial-energy bound `hen` made explicit; the `Ld` appearing there squares against `h * Ld`
in the conclusion, which is where `L^{2d}` first appears once `Ld` is instantiated to `L^d`. -/
example {n : Type*} [Fintype n] (H O : Matrix n n ℂ) {h Ld m C E₀ : ℝ}
    (hh : 0 < h) (hLd : 0 < Ld) (Ψ Ξ : n → ℂ)
    (hvar : rayleighOnVec (H - (h : ℂ) • O) Ψ ≤ rayleighOnVec (H - (h : ℂ) • O) Ξ)
    (hE₀ : E₀ ≤ rayleighOnVec H Ψ)
    (hXi : m ≤ rayleighOnVec O Ξ / Ld)
    (hen : rayleighOnVec H Ξ - E₀ ≤ C / Ld) :
    m - C / (h * Ld ^ 2) ≤ rayleighOnVec O Ψ / Ld :=
  tasaki_eq_3_4_21_perVolume_energyBound H O hh hLd Ψ Ξ hvar hE₀ hXi hen

/-- Pins `tasaki_eq_3_4_21_volumeLiminf`, the inner `L ↑ ∞` step: with an `L`-indexed family
obeying the per-volume energy bound and an outer upper bound `hub` (supplying coboundedness), the
order mean's `liminf` is at least `m`. -/
example {n : ℕ → Type*} [∀ L, Fintype (n L)]
    (H O : (L : ℕ) → Matrix (n L) (n L) ℂ) (Ψ Ξ : (L : ℕ) → n L → ℂ) (E : ℕ → ℝ)
    {d : ℕ} {h m C o₀ : ℝ} (hd : 1 ≤ d) (hh : 0 < h)
    (hvar : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (H L - (h : ℂ) • O L) (Ψ L)
      ≤ rayleighOnVec (H L - (h : ℂ) • O L) (Ξ L))
    (hE : ∀ L : ℕ, 1 ≤ L → E L ≤ rayleighOnVec (H L) (Ψ L))
    (hXi : ∀ L : ℕ, 1 ≤ L → m ≤ rayleighOnVec (O L) (Ξ L) / (L : ℝ) ^ d)
    (hen : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (H L) (Ξ L) - E L ≤ C / (L : ℝ) ^ d)
    (hub : ∀ L : ℕ, 1 ≤ L → rayleighOnVec (O L) (Ψ L) / (L : ℝ) ^ d ≤ o₀) :
    m ≤ liminf (fun L : ℕ => rayleighOnVec (O L) (Ψ L) / (L : ℝ) ^ d) atTop :=
  tasaki_eq_3_4_21_volumeLiminf H O Ψ Ξ E hd hh hvar hE hXi hen hub

/-- Pins `tasaki_orderParameter_uniformBound`, whose conclusion has the shape of the uniform bound
`hub` that `tasaki_theorem_3_2_kaplanHorschVonderLinden` takes abstractly; the carrier hypothesis
`hcard : #Λ ≤ L^d` is what makes that bound intensive. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (o : Λ → ManyBodyOpS Λ N) {o₀ : ℝ} {d L : ℕ}
    (hno : ∀ x : Λ, manyBodyOperatorNormS (o x) ≤ o₀) (ho₀ : 0 ≤ o₀)
    (hcard : (Fintype.card Λ : ℝ) ≤ (L : ℝ) ^ d) (hL : 1 ≤ L)
    {Ψ : (Λ → Fin (N + 1)) → ℂ} (hΨ : star Ψ ⬝ᵥ Ψ = 1) :
    |rayleighOnVec (∑ x : Λ, o x) Ψ / (L : ℝ) ^ d| ≤ o₀ :=
  tasaki_orderParameter_uniformBound o hno ho₀ hcard hL hΨ

/-- Pins the capstone `tasaki_theorem_3_2_kaplanHorschVonderLinden` (Theorem 3.2, eq. (3.4.22)):
both limits are `Filter.liminf`, in the printed order (inner `L ↑ ∞` under `atTop`, outer
`h ↓ 0` under `𝓝[>] 0`). -/
example {n : ℕ → Type*} [∀ L, Fintype (n L)]
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
      rayleighOnVec (O L) (Ψ h L) / (L : ℝ) ^ d) atTop) (𝓝[>] (0 : ℝ)) :=
  tasaki_theorem_3_2_kaplanHorschVonderLinden H O Ξ Ψ E hd hvar hE hXi hen hub

/-! ### Boundedness / non-vacuity witness at `q₀ = 1` -/

/-- Non-vacuity witness: on `Fin 1`, `O L := L^d • 1` and `H L := 0` for every `L`, with
`Ξ L = Ψ h L := ![1]` for every `h`, every hypothesis of the capstone is discharged by proof and
the order mean is `1` at every `L ≥ 1`, so the conclusion reads `1 ≤ 1`. -/
example :
    Real.sqrt 1 ≤ liminf (fun _h : ℝ => liminf (fun L : ℕ =>
        rayleighOnVec ((((L : ℝ) ^ 1 : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) ![(1 : ℂ)]
          / (L : ℝ) ^ 1) atTop) (𝓝[>] (0 : ℝ)) := by
  have key : ∀ L : ℕ, 1 ≤ L →
      rayleighOnVec ((((L : ℝ) ^ 1 : ℝ) : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) ![(1 : ℂ)]
        / (L : ℝ) ^ 1 = 1 := by
    intro L hL
    have hL0 : (L : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      positivity
    simp only [rayleighOnVec, Matrix.mulVec, dotProduct, pow_one, Fin.sum_univ_one]
    norm_num [div_self hL0]
  refine tasaki_theorem_3_2_kaplanHorschVonderLinden (n := fun _ => Fin 1) (fun _ => 0)
    (fun L => (((L : ℝ) ^ 1 : ℝ) : ℂ) • 1) (fun _ => ![1]) (fun _ _ => ![1]) (fun _ => 0)
    (d := 1) (q₀ := 1) (C := 0) (o₀ := 1)
    le_rfl (fun h _ L _ => le_rfl) (fun h _ L _ => ?_) (fun L hL => ?_) (fun L hL => ?_)
    (fun h _ L hL => ?_)
  · simp [rayleighOnVec]
  · rw [Real.sqrt_one, key L hL]
  · simp [rayleighOnVec]
  · rw [key L hL]

/-! ### Sharpness: the two-level `1/L` family, tight at `d = 1`, `h = 1`, `C = 1`, `m = 1` -/

/-- Test-local sharpness order operator `diag(L, L - 1/L)`: at the trial vector `e₀` its Rayleigh
quotient is exactly `L` and at the perturbed vector `e₁` exactly `L - 1/L`. -/
private noncomputable def sharpnessOrderOperator (L : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((L : ℝ) : ℂ), (((L : ℝ) - 1 / (L : ℝ) : ℝ) : ℂ)]

/-- Test-local sharpness Hamiltonian `Htest L := diag(1/L, 0)`.  Against `Otest L` it makes the
field-perturbed `Htest L - Otest L` the scalar matrix `(1/L - L) • 1`, so its Rayleigh quotient
agrees at `e₀` and `e₁` and eq. (3.4.20)'s variational hypothesis holds at equality — which is what
lets the fixture below attain eq. (3.4.21)'s per-volume bound. -/
private noncomputable def sharpnessHamiltonian (L : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![((1 / (L : ℝ) : ℝ) : ℂ), 0]

/-- `sharpnessOrderOperator`'s Rayleigh quotient at the trial vector `e₀ = ![1, 0]` is `L`. -/
private theorem sharpnessOrder_atXi (L : ℕ) :
    rayleighOnVec (sharpnessOrderOperator L) ![1, 0] = (L : ℝ) := by
  simp [rayleighOnVec, sharpnessOrderOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.diagonal]

/-- `sharpnessOrderOperator`'s Rayleigh quotient at the field vector `e₁ = ![0, 1]` is
`L - 1/L`. -/
private theorem sharpnessOrder_atPsi (L : ℕ) :
    rayleighOnVec (sharpnessOrderOperator L) ![0, 1] = (L : ℝ) - 1 / (L : ℝ) := by
  simp [rayleighOnVec, sharpnessOrderOperator, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.diagonal]

/-- `sharpnessHamiltonian`'s Rayleigh quotient at `e₀ = ![1, 0]` is `1/L`. -/
private theorem sharpnessHamiltonian_atXi (L : ℕ) :
    rayleighOnVec (sharpnessHamiltonian L) ![1, 0] = 1 / (L : ℝ) := by
  simp [rayleighOnVec, sharpnessHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.diagonal]

/-- `sharpnessHamiltonian`'s Rayleigh quotient at `e₁ = ![0, 1]` is `0`. -/
private theorem sharpnessHamiltonian_atPsi (L : ℕ) :
    rayleighOnVec (sharpnessHamiltonian L) ![0, 1] = 0 := by
  simp [rayleighOnVec, sharpnessHamiltonian, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.diagonal]

/-- Sharpness fixture: at `d = 1`, `h = 1`, `C = 1`, `m = 1`, the two-level family meets
`tasaki_eq_3_4_21_perVolume_energyBound`'s `hvar`, `hE₀`, `hXi` and `hen` at equality, its
per-volume order mean is strictly below `m = 1` at every `L ≥ 1`, and that mean equals
`1 - 1/(L^1)^2`, which is `m - C/(h * (L^d)^2)` exactly, so that bound is attained here while the
finite-volume statement `m ≤ ⟨Ψ|O|Ψ⟩/L^d` is false. That the order bound `hXi` is tight too is what
makes the attainment informative: `m = 1` is the largest value it admits on this data, so the
conclusion is met with equality without any of those four inequalities being slack. The exact value
is what fixes the error term's denominator: `L^d` in place of `L^{2d}` is equally well-typed, so
elaboration alone does not choose between them. -/
example :
    (∀ L : ℕ, 1 ≤ L →
      rayleighOnVec (sharpnessHamiltonian L - ((1 : ℝ) : ℂ) • sharpnessOrderOperator L) ![0, 1]
        ≤ rayleighOnVec (sharpnessHamiltonian L - ((1 : ℝ) : ℂ) • sharpnessOrderOperator L)
            ![1, 0])
    ∧ (∀ L : ℕ, 1 ≤ L → (0 : ℝ) ≤ rayleighOnVec (sharpnessHamiltonian L) ![0, 1])
    ∧ (∀ L : ℕ, 1 ≤ L → (1 : ℝ) ≤ rayleighOnVec (sharpnessOrderOperator L) ![1, 0] / (L : ℝ) ^ 1)
    ∧ (∀ L : ℕ, 1 ≤ L →
        rayleighOnVec (sharpnessHamiltonian L) ![1, 0] - 0 ≤ (1 : ℝ) / (L : ℝ) ^ 1)
    ∧ (∀ L : ℕ, 1 ≤ L →
        rayleighOnVec (sharpnessOrderOperator L) ![0, 1] / (L : ℝ) ^ 1 < (1 : ℝ))
    ∧ (∀ L : ℕ, 1 ≤ L → rayleighOnVec (sharpnessOrderOperator L) ![0, 1] / (L : ℝ) ^ 1
        = 1 - 1 / (((L : ℝ) ^ 1) ^ 2)) := by
  have hL0 : ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≠ 0 := by
    intro L hL
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    positivity
  refine ⟨fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_,
    fun L hL => ?_⟩
  · rw [rayleighOnVec_sub_smul, rayleighOnVec_sub_smul, sharpnessOrder_atXi, sharpnessOrder_atPsi,
      sharpnessHamiltonian_atXi, sharpnessHamiltonian_atPsi]
    have := hL0 L hL
    field_simp
    ring_nf
    linarith
  · rw [sharpnessHamiltonian_atPsi]
  · rw [sharpnessOrder_atXi, pow_one, div_self (hL0 L hL)]
  · rw [sharpnessHamiltonian_atXi, pow_one]
    simp
  · rw [sharpnessOrder_atPsi, pow_one]
    have h0 := hL0 L hL
    have hLpos : (0 : ℝ) < (L : ℝ) := by
      have : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      linarith
    rw [div_lt_one hLpos]
    have : 0 < 1 / (L : ℝ) := by positivity
    linarith
  · rw [sharpnessOrder_atPsi, pow_one]
    have h0 := hL0 L hL
    field_simp

/-! ### `d = 0` counterexample -/

/-- `d = 0` makes the volume-liminf conclusion false: at `Fin 1`, `H L := 1 - 1`, `O L := 1`,
`Ψ L := ![0]`, `Ξ L := ![1]`, `E L := 0`, `m := 1`, `C := 1`, `h := 1`, `o₀ := 0`, the family
hypotheses `hvar`, `hE`, `hXi`, `hen` and `hub` of `tasaki_eq_3_4_21_volumeLiminf` are discharged
by proof and its conclusion is refuted, so `1 ≤ d` is not removable. -/
example :
    (∀ L : ℕ, 1 ≤ L →
      rayleighOnVec ((1 : Matrix (Fin 1) (Fin 1) ℂ) - ((1 : ℝ) : ℂ) • 1) ![(0 : ℂ)]
        ≤ rayleighOnVec ((1 : Matrix (Fin 1) (Fin 1) ℂ) - ((1 : ℝ) : ℂ) • 1) ![(1 : ℂ)])
    ∧ (∀ L : ℕ, 1 ≤ L → (0 : ℝ) ≤ rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(0 : ℂ)])
    ∧ (∀ L : ℕ, 1 ≤ L →
        (1 : ℝ) ≤ rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(1 : ℂ)] / (L : ℝ) ^ 0)
    ∧ (∀ L : ℕ, 1 ≤ L →
        rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(1 : ℂ)] - 0 ≤ (1 : ℝ) / (L : ℝ) ^ 0)
    ∧ (∀ L : ℕ, 1 ≤ L →
        rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(0 : ℂ)] / (L : ℝ) ^ 0 ≤ (0 : ℝ))
    ∧ ¬ ((1 : ℝ) ≤ liminf (fun L : ℕ =>
        rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(0 : ℂ)] / (L : ℝ) ^ 0) atTop) := by
  refine ⟨fun L _ => ?_, fun L _ => ?_, fun L _ => ?_, fun L _ => ?_, fun L _ => ?_, ?_⟩
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct]
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct]
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct, Matrix.one_apply]
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct, Matrix.one_apply]
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct]
  · have hzero : (fun L : ℕ =>
        rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(0 : ℂ)] / (L : ℝ) ^ 0)
        = fun _ : ℕ => (0 : ℝ) := by
      funext L
      simp [rayleighOnVec, Matrix.mulVec, dotProduct]
    rw [hzero, liminf_const]
    norm_num

/-! ### `h < 0` counterexample -/

/-- `h < 0` breaks `tasaki_eq_3_4_21_perVolume`: at `Fin 1`, `H := 0`, `O := 1`, `Ld := 1`,
`E₀ := 0`, `m := 1`, `h := -1`, `Ψ := ![0]`, `Ξ := ![1]`, the hypotheses `hvar`, `hE₀` and `hXi`
hold but the conclusion fails, so `0 < h` is not removable. -/
example :
    rayleighOnVec ((0 : Matrix (Fin 1) (Fin 1) ℂ) - ((-1 : ℝ) : ℂ) • 1) ![(0 : ℂ)]
        ≤ rayleighOnVec ((0 : Matrix (Fin 1) (Fin 1) ℂ) - ((-1 : ℝ) : ℂ) • 1) ![(1 : ℂ)]
    ∧ (0 : ℝ) ≤ rayleighOnVec (0 : Matrix (Fin 1) (Fin 1) ℂ) ![(0 : ℂ)]
    ∧ (1 : ℝ) ≤ rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(1 : ℂ)] / 1
    ∧ ¬ ((1 : ℝ) + (0 - rayleighOnVec (0 : Matrix (Fin 1) (Fin 1) ℂ) ![(1 : ℂ)]) / ((-1 : ℝ) * 1)
        ≤ rayleighOnVec (1 : Matrix (Fin 1) (Fin 1) ℂ) ![(0 : ℂ)] / 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct, Matrix.one_apply]
  · simp [rayleighOnVec]
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct, Matrix.one_apply]
  · simp [rayleighOnVec, Matrix.mulVec, dotProduct, Matrix.one_apply]

/-! ### Limit-nesting: printed order (`1`) versus exchanged order (`0`) -/

/-- The printed nesting `liminf_h (liminf_L …)` on the shared bounded family
`min (h * L) 1` gives `1`: eventually in `L`, `h * L ≥ 1` for every fixed `h > 0`. -/
example : liminf (fun h : ℝ => liminf (fun L : ℕ => min (h * L) 1) atTop) (𝓝[>] (0 : ℝ)) = 1 := by
  have hin : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), liminf (fun L : ℕ => min (h * L) 1) atTop = 1 := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hev : ∀ᶠ L : ℕ in atTop, min (h * L) 1 = 1 := by
      have hdiv : Tendsto (fun L : ℕ => h * (L : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop hh (tendsto_natCast_atTop_atTop (R := ℝ))
      filter_upwards [hdiv.eventually_ge_atTop 1] with L hL
      exact min_eq_right hL
    rw [liminf_congr hev, liminf_const]
  rw [liminf_congr hin, liminf_const]

/-- The exchanged nesting `liminf_L (liminf_h …)` on the same family gives `0`: for fixed `L`,
`min (h * L) 1 → 0` as `h ↓ 0`. This is Tasaki's own stated reason for the printed order, given in
the body text just after eq. (3.4.22) on p. 70: at any finite `L` the field-perturbed quantity
tends to `0` as `h ↓ 0` by continuity. Footnote 24 on the same page makes the different point that
the printed limits should rigorously be `liminf`. -/
example : liminf (fun L : ℕ => liminf (fun h : ℝ => min (h * L) 1) (𝓝[>] (0 : ℝ))) atTop = 0 := by
  have hin : ∀ L : ℕ, liminf (fun h : ℝ => min (h * L) 1) (𝓝[>] (0 : ℝ)) = 0 := by
    intro L
    have hcont : Tendsto (fun h : ℝ => min (h * L) 1) (𝓝[>] (0 : ℝ))
        (𝓝 (min (0 * (L : ℝ)) 1)) := by
      refine Tendsto.min ?_ tendsto_const_nhds
      exact ((continuous_id.mul continuous_const).tendsto 0).mono_left nhdsWithin_le_nhds
    simp only [zero_mul, min_eq_left (zero_le_one)] at hcont
    exact hcont.liminf_eq
  simp only [hin]
  exact liminf_const 0

/-! ### `tasaki_orderParameter_uniformBound`: a tight instance and a slack instance -/

/-- Tight instance: `Λ = Fin 1`, `N = 0`, `o x = 1`, `o₀ = 1`, `d = L = 1`. The config space
`Fin 1 → Fin 1` is `1`-dimensional, so the constant normalised vector `Ψ := fun _ => 1` has
`rayleighOnVec (∑ x, o x) Ψ = 1`, and both `hcard` (`1 ≤ 1^1`) and the conclusion (`|1 / 1^1| ≤ 1`)
sit at equality. What the fixture checks is the conclusion; the Rayleigh value is not pinned
separately here. -/
example :
    |rayleighOnVec (∑ _x : Fin 1, (1 : ManyBodyOpS (Fin 1) 0)) (fun _ => (1 : ℂ))
        / ((1 : ℕ) : ℝ) ^ 1| ≤ (1 : ℝ) := by
  have hΨ : star (fun _ : (Fin 1 → Fin 1) => (1 : ℂ)) ⬝ᵥ (fun _ => (1 : ℂ)) = 1 := by
    simp [dotProduct]
  exact tasaki_orderParameter_uniformBound (Λ := Fin 1) (N := 0)
    (fun _ : Fin 1 => (1 : ManyBodyOpS (Fin 1) 0)) (o₀ := 1) (d := 1) (L := 1)
    (fun _ => le_of_eq manyBodyOperatorNormS_one) (by norm_num) (by simp) le_rfl hΨ

/-- Slack instance: same operator and state as the tight instance but `L = 2`, so `hcard`
(`1 ≤ 2^1`) and the conclusion (`|1 / 2^1| ≤ 1`) are both strict — exercising `hcard` away from
equality. -/
example :
    |rayleighOnVec (∑ _x : Fin 1, (1 : ManyBodyOpS (Fin 1) 0)) (fun _ => (1 : ℂ))
        / ((2 : ℕ) : ℝ) ^ 1| ≤ (1 : ℝ) := by
  have hΨ : star (fun _ : (Fin 1 → Fin 1) => (1 : ℂ)) ⬝ᵥ (fun _ => (1 : ℂ)) = 1 := by
    simp [dotProduct]
  exact tasaki_orderParameter_uniformBound (Λ := Fin 1) (N := 0)
    (fun _ : Fin 1 => (1 : ManyBodyOpS (Fin 1) 0)) (o₀ := 1) (d := 1) (L := 2)
    (fun _ => le_of_eq manyBodyOperatorNormS_one) (by norm_num) (by norm_num) (by norm_num) hΨ

end LatticeSystem.Quantum
