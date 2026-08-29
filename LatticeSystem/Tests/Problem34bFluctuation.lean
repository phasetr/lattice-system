import LatticeSystem.Quantum.HorschVonderLinden

/-!
# Test coverage for Tasaki Problem 3.4.b — order fluctuation in `Ξ₊`

Fixtures for the fourth-moment identity of Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, Problem 3.4.b: statement p. 69 eq. (3.4.18), solution p. 501 eqs. (S.42)-(S.43).

`Ô_L/L^d` here denotes an abstract Hermitian observable `O L` on a per-`L` finite-dimensional
space `n L`, together with a normalized reference vector `Φ L` ("`|Φ_GS⟩`") satisfying the odd-
moment vanishing `⟨Φ_GS|Ô_L|Φ_GS⟩ = ⟨Φ_GS|Ô_L³|Φ_GS⟩ = 0` — the source's assumption (3.4.4) about
the absence of spontaneous symmetry breaking in `|Φ_GS⟩` — and an `L`-uniform long-range-order
lower bound `q₀ ≤ ⟨Φ_GS|(Ô_L/L^d)²|Φ_GS⟩` (3.4.3). From these, `hvlTrialState` constructs the
Horsch-von der Linden trial state `|Γ⟩` (3.4.7) and `hvlPlusState` the state `|Ξ₊⟩ =
(1/√2)(|Φ_GS⟩ + |Γ⟩)` (3.4.14). Neither the Hamiltonian nor locality of `Ô_L` is assumed anywhere:
the source's own derivation of (S.42)/(S.43) uses only the Hermiticity of `Ô_L`, the normalization
of `Φ_GS`, and (3.4.4); the fixtures below reflect that. Eq. (3.4.16), the Schwarz remark
(3.4.17) and the mirror state `Ξ₋` are outside the scope of this problem and are not pinned here.

## What each fixture pins

The first block pins the seven public declarations of the design in full, each restated as the
declaration's own signature and discharged only by the declaration (the
`Problem33aLowEnergy.lean` idiom): the two state constructors `hvlTrialState` / `hvlPlusState`,
the four per-`L` identities `hvlPlusState_dotProduct_self` (3.4.14 normalization),
`hvlPlusState_order_mean` (3.4.15), `hvlPlusState_order_second_moment` (S.42),
`hvlPlusState_order_variance` (S.43), and the capstone
`tasaki_problem_3_4_b_order_fluctuation` (Problem 3.4.b itself: the `L^d`-normalized fluctuation
of `Ô_L` in `Ξ₊` tends to `0` under (3.4.18)).

The second block gives three concrete numeric fixtures.

**Fixture A** (`n = Fin 2`, `O` = Pauli `X`, `Φ = e₀`) pins the normalization step of (3.4.14): a
dropped `1/√2` in `hvlPlusState` would give `⟨Ξ₊|Ô|Ξ₊⟩ = 2` instead of `1`. It **cannot** detect
any defect in the fourth-moment expansion (S.42)/(S.43): at this instance `m₂ = m₄ = 1`, so
`m₄ = m₂²` and `m₄ / m₂` coincide with every candidate expansion, i.e. the fixture is blind to
exactly the content Problem 3.4.b is about. Fixture B supplies that coverage.

**Fixture B** (`n = Fin 4`, `O = diagonal ![1,-1,2,-2]`, `Φ = (1/2,1/2,1/2,1/2)`) pins the
second-moment identity (S.42) at a point where the four wrong variants identified in the design
(dropped `1/2`, `m₄/m₂²` instead of `m₄/m₂`, `Γ` normalized by `m₂` instead of `√m₂`, an
unnormalized `Ξ₊`) all give numerically distinct wrong answers from the correct `⟨Ξ₊|Ô²|Ξ₊⟩ =
59/20` and variance `9/20`.

**Fixture C** instantiates the capstone at a concrete `L`-indexed family (`O L = L^d • X`,
`Φ L = e₀`, `q₀ = 1`) to witness that the `1 ≤ L`-guarded hypothesis bundle is satisfiable: without
such a witness, an `L = 0` slip in the capstone's `hLRO` guard could make the theorem vacuously
true for every family. The six hypotheses of the capstone (`hHerm`, `hΦ`, `hodd1`, `hodd3`,
`hLRO`, `hFourth`) are proved outright for this family (they never mention `hvlPlusState`); only
the final application to the not-yet-defined capstone is left unresolved.
-/

namespace LatticeSystem.Tests.Problem34bFluctuation

open LatticeSystem.Quantum
open Matrix

/-! ## Signature pins for the seven public declarations -/

/-- **Signature pin (D1, the trial state).** `hvlTrialState` is Tasaki's `|Γ⟩`, eq. (3.4.7):
the Hermitian image `O *ᵥ Φ` unit-normalized in the `L²` inner product. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ) : n → ℂ :=
  hvlTrialState O Φ

/-- **Signature pin (D2, the state `Ξ₊`).** `hvlPlusState` is Tasaki's `|Ξ₊⟩`, eq. (3.4.14):
`(1/√2)(Φ + Γ)` where `Γ = hvlTrialState O Φ`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ) : n → ℂ :=
  hvlPlusState O Φ

/-- **Signature pin (L6, normalization).** `hvlPlusState_dotProduct_self` gives Tasaki's remark
after (3.4.14), `⟨Ξ₊|Ξ₊⟩ = 1`, under Hermiticity of `O`, normalization and the first odd-moment
vanishing of `Φ`, and positivity of the second moment. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ)
    (hHerm : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    star (hvlPlusState O Φ) ⬝ᵥ hvlPlusState O Φ = 1 :=
  hvlPlusState_dotProduct_self O Φ hHerm hΦ hodd1 hm2

/-- **Signature pin (L8, the mean).** `hvlPlusState_order_mean` gives Tasaki eq. (3.4.15),
`⟨Ξ₊|Ô|Ξ₊⟩ = √(⟨Φ_GS|Ô²|Φ_GS⟩)`, under the same hypotheses as L6. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ)
    (hHerm : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec O (hvlPlusState O Φ) = Real.sqrt (rayleighOnVec (O ^ 2) Φ) :=
  hvlPlusState_order_mean O Φ hHerm hΦ hodd1 hm2

/-- **Signature pin (L9, the second moment).** `hvlPlusState_order_second_moment` gives Tasaki
eq. (S.42), `⟨Ξ₊|Ô²|Ξ₊⟩ = (1/2){m₂ + m₄/m₂}`, additionally under the third odd-moment vanishing of
`Φ` (needed for the `Ô⁴`-sandwiched cross terms). -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ)
    (hHerm : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) :
    rayleighOnVec (O ^ 2) (hvlPlusState O Φ)
      = 1 / 2 * (rayleighOnVec (O ^ 2) Φ + rayleighOnVec (O ^ 4) Φ / rayleighOnVec (O ^ 2) Φ) :=
  hvlPlusState_order_second_moment O Φ hHerm hΦ hodd1 hodd3 hm2

/-- **Signature pin (L10, the fluctuation identity).** `hvlPlusState_order_variance` gives Tasaki
eq. (S.43), the `L^d`-normalized fourth-moment identity for the `Ô_L`-variance in `Ξ₊`, for any
positive volume factor `V`. -/
example {n : Type*} [Fintype n] [DecidableEq n] (O : Matrix n n ℂ) (Φ : n → ℂ) (V : ℝ)
    (hHerm : O.IsHermitian) (hΦ : star Φ ⬝ᵥ Φ = 1) (hodd1 : star Φ ⬝ᵥ (O *ᵥ Φ) = 0)
    (hodd3 : star Φ ⬝ᵥ ((O ^ 3) *ᵥ Φ) = 0) (hm2 : 0 < rayleighOnVec (O ^ 2) Φ) (hV : 0 < V) :
    rayleighOnVec (O ^ 2) (hvlPlusState O Φ) / V ^ 2
        - (rayleighOnVec O (hvlPlusState O Φ) / V) ^ 2
      = 1 / 2 * (rayleighOnVec (O ^ 4) Φ / V ^ 4 - (rayleighOnVec (O ^ 2) Φ / V ^ 2) ^ 2)
          / (rayleighOnVec (O ^ 2) Φ / V ^ 2) :=
  hvlPlusState_order_variance O Φ V hHerm hΦ hodd1 hodd3 hm2 hV

/-- **Signature pin (capstone).** `tasaki_problem_3_4_b_order_fluctuation` assembles, for every
`L ≥ 1`, the four conjuncts pinned above (normalization, (3.4.15), (S.42), (S.43)) plus, as the
answer to Problem 3.4.b, the `L → ∞` vanishing of the `Ô_L/L^d`-fluctuation in `Ξ₊` under
(3.4.18). -/
example {n : ℕ → Type*} [∀ L, Fintype (n L)] [∀ L, DecidableEq (n L)]
    (d : ℕ) {q₀ : ℝ} (hq₀ : 0 < q₀)
    (O : (L : ℕ) → Matrix (n L) (n L) ℂ) (Φ : (L : ℕ) → n L → ℂ)
    (hHerm : ∀ L, (O L).IsHermitian)
    (hΦ : ∀ L, star (Φ L) ⬝ᵥ Φ L = 1)
    (hodd1 : ∀ L, star (Φ L) ⬝ᵥ (O L) *ᵥ Φ L = 0)
    (hodd3 : ∀ L, star (Φ L) ⬝ᵥ ((O L) ^ 3) *ᵥ Φ L = 0)
    (hLRO : ∀ L : ℕ, 1 ≤ L → q₀ ≤ rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2)
    (hFourth : Filter.Tendsto
      (fun L : ℕ => rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
        - (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ^ 2)
      Filter.atTop (nhds 0)) :
    (∀ L : ℕ, 1 ≤ L →
        star (hvlPlusState (O L) (Φ L)) ⬝ᵥ hvlPlusState (O L) (Φ L) = 1
      ∧ rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d
          = Real.sqrt (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2)
      ∧ rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          = 1 / 2 * (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2
              + rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
                / (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2))
      ∧ rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
          - (rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d) ^ 2
          = 1 / 2 * (rayleighOnVec ((O L) ^ 4) (Φ L) / ((L : ℝ) ^ d) ^ 4
              - (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2) ^ 2)
            / (rayleighOnVec ((O L) ^ 2) (Φ L) / ((L : ℝ) ^ d) ^ 2))
    ∧ Filter.Tendsto
        (fun L : ℕ =>
          rayleighOnVec ((O L) ^ 2) (hvlPlusState (O L) (Φ L)) / ((L : ℝ) ^ d) ^ 2
            - (rayleighOnVec (O L) (hvlPlusState (O L) (Φ L)) / (L : ℝ) ^ d) ^ 2)
        Filter.atTop (nhds 0) :=
  tasaki_problem_3_4_b_order_fluctuation d hq₀ O Φ hHerm hΦ hodd1 hodd3 hLRO hFourth

/-! ## Fixture A: Pauli `X`, normalization only -/

/-- The Fixture-A observable, Pauli `X` on `Fin 2`. -/
private def fixtureAMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Fixture-A reference vector, `e₀`. -/
private def fixtureAVector : Fin 2 → ℂ := ![1, 0]

/-- `fixtureAMatrix` is Hermitian. -/
private lemma fixtureA_herm : fixtureAMatrix.IsHermitian := by
  unfold Matrix.IsHermitian fixtureAMatrix
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- `fixtureAVector` is normalized. -/
private lemma fixtureA_norm : star fixtureAVector ⬝ᵥ fixtureAVector = 1 := by
  unfold fixtureAVector; simp [dotProduct, Fin.sum_univ_two]

/-- The first odd moment of `fixtureAMatrix` at `fixtureAVector` vanishes. -/
private lemma fixtureA_odd1 :
    star fixtureAVector ⬝ᵥ (fixtureAMatrix *ᵥ fixtureAVector) = 0 := by
  unfold fixtureAVector fixtureAMatrix; simp [dotProduct, mulVec, Fin.sum_univ_two]

/-- The third odd moment of `fixtureAMatrix` at `fixtureAVector` vanishes. -/
private lemma fixtureA_odd3 :
    star fixtureAVector ⬝ᵥ ((fixtureAMatrix ^ 3) *ᵥ fixtureAVector) = 0 := by
  unfold fixtureAVector fixtureAMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_two, pow_succ, Matrix.mul_apply]

/-- The second moment `m₂` of `fixtureAMatrix` at `fixtureAVector` is `1`. -/
private lemma fixtureA_raySq : rayleighOnVec (fixtureAMatrix ^ 2) fixtureAVector = 1 := by
  unfold rayleighOnVec fixtureAVector fixtureAMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_two, pow_succ, Matrix.mul_apply]

/-- The fourth moment `m₄` of `fixtureAMatrix` at `fixtureAVector` is `1`. -/
private lemma fixtureA_ray4 : rayleighOnVec (fixtureAMatrix ^ 4) fixtureAVector = 1 := by
  unfold rayleighOnVec fixtureAVector fixtureAMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_two, pow_succ, Matrix.mul_apply]

/-- `m₂ > 0` at Fixture A. -/
private lemma fixtureA_m2pos : (0 : ℝ) < rayleighOnVec (fixtureAMatrix ^ 2) fixtureAVector := by
  rw [fixtureA_raySq]; norm_num

/-- **Fixture A, normalization (3.4.14).** With `O` the Pauli-`X` matrix and `Φ = e₀`, `Γ = e₁`
and `Ξ₊ = (1/√2)(e₀ + e₁)`, so `⟨Ξ₊|Ξ₊⟩ = 1`. A dropped `1/√2` in `hvlPlusState` would instead give
`⟨Ξ₊|Ξ₊⟩ = 2`, so this pins the normalization constant. -/
example : star (hvlPlusState fixtureAMatrix fixtureAVector)
    ⬝ᵥ hvlPlusState fixtureAMatrix fixtureAVector = 1 :=
  hvlPlusState_dotProduct_self fixtureAMatrix fixtureAVector fixtureA_herm fixtureA_norm
    fixtureA_odd1 fixtureA_m2pos

/-- **Fixture A, order mean (3.4.15).** With the same data, `⟨Ξ₊|Ô|Ξ₊⟩ = 1`; the fourth-moment
expansion (S.42)/(S.43) is *not* exercised here since `m₂ = m₄ = 1` makes every candidate
expansion (correct or not) coincide numerically — see the module doc comment. -/
example : rayleighOnVec fixtureAMatrix (hvlPlusState fixtureAMatrix fixtureAVector) = 1 := by
  simpa [fixtureA_raySq] using
    hvlPlusState_order_mean fixtureAMatrix fixtureAVector fixtureA_herm fixtureA_norm
      fixtureA_odd1 fixtureA_m2pos

/-! ## Fixture B: `diagonal ![1,-1,2,-2]`, moment expansion -/

/-- The Fixture-B observable. -/
private def fixtureBMatrix : Matrix (Fin 4) (Fin 4) ℂ := Matrix.diagonal ![1, -1, 2, -2]

/-- The Fixture-B reference vector, the uniform superposition. -/
private noncomputable def fixtureBVector : Fin 4 → ℂ := ![1 / 2, 1 / 2, 1 / 2, 1 / 2]

/-- `fixtureBMatrix` is Hermitian. -/
private lemma fixtureB_herm : fixtureBMatrix.IsHermitian := by
  unfold Matrix.IsHermitian fixtureBMatrix
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

/-- `fixtureBVector` is normalized. -/
private lemma fixtureB_norm : star fixtureBVector ⬝ᵥ fixtureBVector = 1 := by
  unfold fixtureBVector; simp [dotProduct, Fin.sum_univ_four, map_ofNat]; norm_num

/-- The first odd moment of `fixtureBMatrix` at `fixtureBVector` vanishes. -/
private lemma fixtureB_odd1 :
    star fixtureBVector ⬝ᵥ (fixtureBMatrix *ᵥ fixtureBVector) = 0 := by
  unfold fixtureBVector fixtureBMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_four, Matrix.diagonal]

/-- The third odd moment of `fixtureBMatrix` at `fixtureBVector` vanishes. -/
private lemma fixtureB_odd3 :
    star fixtureBVector ⬝ᵥ ((fixtureBMatrix ^ 3) *ᵥ fixtureBVector) = 0 := by
  unfold fixtureBVector fixtureBMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_four, pow_succ, Matrix.mul_apply, Matrix.diagonal]

/-- The second moment `m₂` of `fixtureBMatrix` at `fixtureBVector` is `5/2`. -/
private lemma fixtureB_raySq : rayleighOnVec (fixtureBMatrix ^ 2) fixtureBVector = 5 / 2 := by
  unfold rayleighOnVec fixtureBVector fixtureBMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_four, pow_succ, Matrix.mul_apply, Matrix.diagonal]
  norm_num

/-- The fourth moment `m₄` of `fixtureBMatrix` at `fixtureBVector` is `17/2`. -/
private lemma fixtureB_ray4 : rayleighOnVec (fixtureBMatrix ^ 4) fixtureBVector = 17 / 2 := by
  unfold rayleighOnVec fixtureBVector fixtureBMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_four, pow_succ, Matrix.mul_apply, Matrix.diagonal]
  norm_num

/-- `m₂ > 0` at Fixture B. -/
private lemma fixtureB_m2pos : (0 : ℝ) < rayleighOnVec (fixtureBMatrix ^ 2) fixtureBVector := by
  rw [fixtureB_raySq]; norm_num

/-- **Fixture B, second moment (S.42).** With `O = diagonal ![1,-1,2,-2]` and `Φ` the uniform
vector `(1/2,1/2,1/2,1/2)`, `m₂ = 5/2`, `m₄ = 17/2`, and `⟨Ξ₊|Ô²|Ξ₊⟩ = 59/20`. This value is
numerically distinct from every wrong variant identified in the design (dropped `1/2` → `59/10`;
`m₄/m₂²` instead of `m₄/m₂` → `193/100`; `Γ` normalized by `m₂` instead of `√m₂` → `193/100`;
unnormalized `Ξ₊` → `59/10`). -/
example : rayleighOnVec (fixtureBMatrix ^ 2) (hvlPlusState fixtureBMatrix fixtureBVector)
    = 59 / 20 := by
  simpa [fixtureB_raySq, fixtureB_ray4] using
    hvlPlusState_order_second_moment fixtureBMatrix fixtureBVector fixtureB_herm fixtureB_norm
      fixtureB_odd1 fixtureB_odd3 fixtureB_m2pos

/-- **Fixture B, variance (S.43).** With the same data, the `Ô`-variance in `Ξ₊` is `9/20`. -/
example :
    rayleighOnVec (fixtureBMatrix ^ 2) (hvlPlusState fixtureBMatrix fixtureBVector)
      - (rayleighOnVec fixtureBMatrix (hvlPlusState fixtureBMatrix fixtureBVector)) ^ 2
        = 9 / 20 := by
  simpa [fixtureB_raySq, fixtureB_ray4, Real.sq_sqrt (show (0 : ℝ) ≤ 5 / 2 by norm_num)] using
    congrArg₂ (· - ·)
      (hvlPlusState_order_second_moment fixtureBMatrix fixtureBVector fixtureB_herm fixtureB_norm
        fixtureB_odd1 fixtureB_odd3 fixtureB_m2pos)
      (congrArg (· ^ 2)
        (hvlPlusState_order_mean fixtureBMatrix fixtureBVector fixtureB_herm fixtureB_norm
          fixtureB_odd1 fixtureB_m2pos))

/-! ## Fixture C: satisfiability of the capstone's hypothesis bundle -/

/-- The Fixture-C `L`-indexed observable, `L^d • X`. -/
private def fixtureCMatrix (d : ℕ) (L : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((L : ℂ) ^ d) • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)

/-- The Fixture-C `L`-independent reference vector, `e₀`. -/
private def fixtureCVector : Fin 2 → ℂ := ![1, 0]

/-- `fixtureCMatrix d L` squares to `(L^d)² • 1`, using `X² = 1`. -/
private lemma fixtureCMatrix_sq (d L : ℕ) :
    (fixtureCMatrix d L) ^ 2 = (((L : ℂ) ^ d) ^ 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  unfold fixtureCMatrix
  rw [smul_pow]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- `fixtureCMatrix d L` raised to the fourth power is `(L^d)⁴ • 1`. -/
private lemma fixtureCMatrix_pow4 (d L : ℕ) :
    (fixtureCMatrix d L) ^ 4 = (((L : ℂ) ^ d) ^ 4) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h2 := fixtureCMatrix_sq d L
  have heq : (fixtureCMatrix d L) ^ 4 = ((fixtureCMatrix d L) ^ 2) ^ 2 := by
    rw [← pow_mul]
  rw [heq, h2, smul_pow, one_pow]
  congr 1
  ring

/-- `fixtureCMatrix d L` is Hermitian for every `d, L`. -/
private lemma fixtureCMatrix_herm (d L : ℕ) : (fixtureCMatrix d L).IsHermitian := by
  unfold Matrix.IsHermitian fixtureCMatrix
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- `fixtureCVector` is normalized. -/
private lemma fixtureCVector_norm : star fixtureCVector ⬝ᵥ fixtureCVector = 1 := by
  unfold fixtureCVector
  simp [dotProduct, Fin.sum_univ_two]

/-- The first odd moment of `fixtureCMatrix d L` at `fixtureCVector` vanishes. -/
private lemma fixtureCVector_odd1 (d L : ℕ) :
    star fixtureCVector ⬝ᵥ (fixtureCMatrix d L) *ᵥ fixtureCVector = 0 := by
  unfold fixtureCVector fixtureCMatrix
  simp [dotProduct, mulVec, Fin.sum_univ_two]

/-- The third odd moment of `fixtureCMatrix d L` at `fixtureCVector` vanishes. -/
private lemma fixtureCVector_odd3 (d L : ℕ) :
    star fixtureCVector ⬝ᵥ ((fixtureCMatrix d L) ^ 3) *ᵥ fixtureCVector = 0 := by
  have h3 : (fixtureCMatrix d L) ^ 3 = ((L : ℂ) ^ d) ^ 3 • !![0, 1; 1, 0] := by
    unfold fixtureCMatrix
    rw [smul_pow]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h3]
  unfold fixtureCVector
  simp [dotProduct, mulVec, Fin.sum_univ_two]

/-- The second moment of `fixtureCMatrix d L` at `fixtureCVector` is `((L : ℝ)^d)²`. -/
private lemma fixtureCMatrix_rayleighSq (d L : ℕ) :
    rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector = ((L : ℝ) ^ d) ^ 2 := by
  rw [fixtureCMatrix_sq]
  unfold rayleighOnVec fixtureCVector
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  norm_cast

/-- The fourth moment of `fixtureCMatrix d L` at `fixtureCVector` is `((L : ℝ)^d)⁴`. -/
private lemma fixtureCMatrix_rayleigh4 (d L : ℕ) :
    rayleighOnVec ((fixtureCMatrix d L) ^ 4) fixtureCVector = ((L : ℝ) ^ d) ^ 4 := by
  rw [fixtureCMatrix_pow4]
  unfold rayleighOnVec fixtureCVector
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  norm_cast

/-- The Fixture-C long-range-order lower bound (3.4.3) holds with `q₀ = 1` for every `L ≥ 1`. -/
private lemma fixtureC_hLRO (d : ℕ) :
    ∀ L : ℕ, 1 ≤ L →
      (1 : ℝ) ≤ rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2 := by
  intro L hL
  rw [fixtureCMatrix_rayleighSq]
  have hLpos : (0 : ℝ) < (L : ℝ) ^ d := pow_pos (by exact_mod_cast hL) d
  rw [div_self (by positivity)]

/-- The Fixture-C fourth-moment condition (3.4.18) holds: the normalized fluctuation of the
ground state `Φ` is identically `0` (the family has no `L`-dependence to detect). -/
private lemma fixtureC_hFourth (d : ℕ) :
    Filter.Tendsto
      (fun L : ℕ => rayleighOnVec ((fixtureCMatrix d L) ^ 4) fixtureCVector / ((L : ℝ) ^ d) ^ 4
        - (rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2) ^ 2)
      Filter.atTop (nhds 0) := by
  have hzero : ∀ L : ℕ,
      rayleighOnVec ((fixtureCMatrix d L) ^ 4) fixtureCVector / ((L : ℝ) ^ d) ^ 4
        - (rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2) ^ 2
          = 0 := by
    intro L
    rw [fixtureCMatrix_rayleigh4, fixtureCMatrix_rayleighSq]
    rcases eq_or_ne ((L : ℝ) ^ d) 0 with h0 | h0
    · simp [h0]
    · rw [div_self (by positivity : ((L : ℝ) ^ d) ^ 4 ≠ 0),
        div_self (by positivity : ((L : ℝ) ^ d) ^ 2 ≠ 0)]
      ring
  simp only [hzero]
  exact tendsto_const_nhds

/-- **Fixture C, satisfiability.** Instantiating the capstone at `n L = Fin 2`, `O L = L^d •
(Pauli X)`, `Φ L = e₀` for every `L`, and `q₀ = 1` witnesses that its `1 ≤ L`-guarded hypothesis
bundle is satisfiable: `M₂ L = M₄ L = 1` for `L ≥ 1` makes `hLRO` hold at `q₀ = 1` and `hFourth` the
constant-zero sequence. Without such a witness an `L = 0` slip in `hLRO` could make the capstone
vacuously true for every family. -/
example (d : ℕ) :
    (∀ L : ℕ, 1 ≤ L →
        star (hvlPlusState (fixtureCMatrix d L) fixtureCVector)
          ⬝ᵥ hvlPlusState (fixtureCMatrix d L) fixtureCVector = 1
      ∧ rayleighOnVec (fixtureCMatrix d L) (hvlPlusState (fixtureCMatrix d L) fixtureCVector)
            / (L : ℝ) ^ d
          = Real.sqrt (rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2)
      ∧ rayleighOnVec ((fixtureCMatrix d L) ^ 2)
            (hvlPlusState (fixtureCMatrix d L) fixtureCVector) / ((L : ℝ) ^ d) ^ 2
          = 1 / 2 * (rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2
              + rayleighOnVec ((fixtureCMatrix d L) ^ 4) fixtureCVector / ((L : ℝ) ^ d) ^ 4
                / (rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2))
      ∧ rayleighOnVec ((fixtureCMatrix d L) ^ 2)
            (hvlPlusState (fixtureCMatrix d L) fixtureCVector) / ((L : ℝ) ^ d) ^ 2
          - (rayleighOnVec (fixtureCMatrix d L) (hvlPlusState (fixtureCMatrix d L) fixtureCVector)
              / (L : ℝ) ^ d) ^ 2
          = 1 / 2 * (rayleighOnVec ((fixtureCMatrix d L) ^ 4) fixtureCVector / ((L : ℝ) ^ d) ^ 4
              - (rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2) ^ 2)
            / (rayleighOnVec ((fixtureCMatrix d L) ^ 2) fixtureCVector / ((L : ℝ) ^ d) ^ 2))
    ∧ Filter.Tendsto
        (fun L : ℕ =>
          rayleighOnVec ((fixtureCMatrix d L) ^ 2)
              (hvlPlusState (fixtureCMatrix d L) fixtureCVector) / ((L : ℝ) ^ d) ^ 2
            - (rayleighOnVec (fixtureCMatrix d L) (hvlPlusState (fixtureCMatrix d L) fixtureCVector)
                / (L : ℝ) ^ d) ^ 2)
        Filter.atTop (nhds 0) :=
  tasaki_problem_3_4_b_order_fluctuation d (q₀ := 1) (by norm_num) (fixtureCMatrix d)
    (fun _ => fixtureCVector) (fixtureCMatrix_herm d) (fun _ => fixtureCVector_norm)
    (fixtureCVector_odd1 d) (fixtureCVector_odd3 d) (fixtureC_hLRO d) (fixtureC_hFourth d)

end LatticeSystem.Tests.Problem34bFluctuation
