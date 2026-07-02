import Mathlib.Analysis.Matrix.Order

/-!
# Isometry compression of a ground-state Lyapunov equation

This is the generic linear-algebra step behind Tasaki's spin-reflection-positivity proof
for the attractive Hubbard model (Tasaki §10.2.4, Lemma 10.10). A full-space
Lyapunov/Schrödinger equation for a block-supported coefficient matrix `W` compresses,
by conjugation with an isometry `J`, to an equation on the smaller sector index type.

Concretely, let `J : Matrix S T ℂ` be an isometry, i.e. `Jᴴ · J = 1` (`J` need not be
square), and suppose the coefficient `W : Matrix S S ℂ` is supported on the image of `J`
in the strong sense that it factors as `W = J · R · Jᴴ` with `R := Jᴴ · W · J` the
compressed coefficient. Then the full-space equation

  `A·W + W·Aᴴ − Σ_x U_x·(I_x·W·I_x) = E·W`

implies the compressed sector equation

  `A_k·R + R·A_kᴴ − Σ_x U_x·(I_x^k·R·I_x^k) = E·R`,

where `A_k := Jᴴ·A·J` and `I_x^k := Jᴴ·I_x·J`. The proof conjugates the full equation by
`Jᴴ · (−) · J` and repeatedly collapses the internal `Jᴴ · J = 1`; this is the same
`Jᴴ·J = 1` collapse used in `liebSRPEnergy_conj_isometry`
(`LiebAttractiveEnergyMonotone.lean`).

## Main results

* `lyapunov_conjugate_isometry` — full-space Lyapunov equation compresses to the sector one.
* `lyapunovEq_sub` — the Lyapunov/Schrödinger super-operator is linear, so the difference of
  two solutions at the same eigenvalue `E` is again a solution.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4 (Lemmas 10.9–10.10), pp. 363–367.
-/

namespace LatticeSystem.Math

open Matrix
open scoped BigOperators

variable {S T ι : Type*} [Fintype S] [Fintype T] [DecidableEq T] [Fintype ι]

/-- **Isometry compression of a ground-state Lyapunov equation** (Tasaki §10.2.4,
Lemma 10.10). For an isometry `J` (`Jᴴ · J = 1`) and a coefficient `W` factoring through
the image of `J` as `W = J · Rk · Jᴴ`, the full-space equation
`A·W + W·Aᴴ − Σ_x U_x·(I_x·W·I_x) = E·W` compresses, under `Jᴴ · (−) · J`, to
the sector equation
`(Jᴴ·A·J)·Rk + Rk·(Jᴴ·A·J)ᴴ − Σ_x U_x·((Jᴴ·I_x·J)·Rk·(Jᴴ·I_x·J)) = E·Rk`. -/
theorem lyapunov_conjugate_isometry
    {J : Matrix S T ℂ} (hJ : Jᴴ * J = 1)
    {A W : Matrix S S ℂ} {I : ι → Matrix S S ℂ} {U : ι → ℝ} {E : ℝ}
    {Rk : Matrix T T ℂ} (hemb : W = J * Rk * Jᴴ)
    (hEq : A * W + W * Aᴴ - ∑ x, (U x : ℂ) • (I x * W * I x) = (E : ℂ) • W) :
    Jᴴ * A * J * Rk + Rk * (Jᴴ * A * J)ᴴ
      - ∑ x, (U x : ℂ) • (Jᴴ * I x * J * Rk * (Jᴴ * I x * J)) = (E : ℂ) • Rk := by
  -- The compressed coefficient reads back off `W` via `Jᴴ · J = 1`.
  have hW : Jᴴ * W * J = Rk := by
    rw [hemb, show Jᴴ * (J * Rk * Jᴴ) * J = (Jᴴ * J) * Rk * (Jᴴ * J) from by
        simp only [Matrix.mul_assoc], hJ, Matrix.one_mul, Matrix.mul_one]
  -- Kinetic term: `Jᴴ · (A·W) · J = (Jᴴ·A·J)·Rk`.
  have h1 : Jᴴ * (A * W) * J = Jᴴ * A * J * Rk := by
    rw [hemb, show Jᴴ * (A * (J * Rk * Jᴴ)) * J = Jᴴ * A * J * Rk * (Jᴴ * J) from by
        simp only [Matrix.mul_assoc], hJ, Matrix.mul_one]
  -- Adjoint kinetic term: `Jᴴ · (W·Aᴴ) · J = Rk·(Jᴴ·A·J)ᴴ`.
  have h2 : Jᴴ * (W * Aᴴ) * J = Rk * (Jᴴ * A * J)ᴴ := by
    rw [hemb, show Jᴴ * (J * Rk * Jᴴ * Aᴴ) * J = (Jᴴ * J) * Rk * (Jᴴ * Aᴴ * J) from by
        simp only [Matrix.mul_assoc], hJ, Matrix.one_mul,
      show (Jᴴ * A * J)ᴴ = Jᴴ * Aᴴ * J from by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]]
  -- Interaction terms: `Jᴴ · (I_x·W·I_x) · J = (Jᴴ·I_x·J)·Rk·(Jᴴ·I_x·J)`.
  have h3 : ∀ x, Jᴴ * (I x * W * I x) * J
      = Jᴴ * I x * J * Rk * (Jᴴ * I x * J) := fun x => by
    rw [hemb, show Jᴴ * (I x * (J * Rk * Jᴴ) * I x) * J
        = Jᴴ * I x * J * Rk * (Jᴴ * I x * J) from by simp only [Matrix.mul_assoc]]
  -- Conjugating the full equation by `Jᴴ · (−) · J`.
  have key := congrArg (fun M => Jᴴ * M * J) hEq
  simp only at key
  -- Distribute the conjugation over the left-hand side.
  have hLHS : Jᴴ * (A * W + W * Aᴴ - ∑ x, (U x : ℂ) • (I x * W * I x)) * J
      = Jᴴ * A * J * Rk + Rk * (Jᴴ * A * J)ᴴ
        - ∑ x, (U x : ℂ) • (Jᴴ * I x * J * Rk * (Jᴴ * I x * J)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, h1, h2]
    congr 1
    rw [Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [Matrix.mul_smul, Matrix.smul_mul, h3 x])
  -- Collapse the right-hand side using `Jᴴ · W · J = Rk`.
  have hRHS : Jᴴ * ((E : ℂ) • W) * J = (E : ℂ) • Rk := by
    rw [show Jᴴ * ((E : ℂ) • W) * J = (E : ℂ) • (Jᴴ * W * J) from by
      simp only [Matrix.mul_smul, Matrix.smul_mul], hW]
  rw [hLHS, hRHS] at key
  exact key

/-- **Linearity of the Lyapunov/Schrödinger super-operator** (Tasaki §10.2.4, used for
Lemma 10.9). The super-operator `L(R) := A·R + R·Aᴴ − Σ_x U_x·(I_x·R·I_x)` is ℂ-linear in
`R`, so if two coefficients `R₁`, `R₂` both satisfy `L(R) = E·R` at the *same* eigenvalue
`E`, then their difference does too: `L(R₁ − R₂) = E·(R₁ − R₂)`. This is the step that lets
`|W_S| − W_S` inherit the ground-state Lyapunov equation from `|W_S|` and `W_S`. -/
theorem lyapunovEq_sub {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} {I : ι → Matrix n n ℂ} {U : ι → ℝ} {E : ℂ}
    {R1 R2 : Matrix n n ℂ}
    (h1 : A * R1 + R1 * Aᴴ - ∑ x, (U x : ℂ) • (I x * R1 * I x) = E • R1)
    (h2 : A * R2 + R2 * Aᴴ - ∑ x, (U x : ℂ) • (I x * R2 * I x) = E • R2) :
    A * (R1 - R2) + (R1 - R2) * Aᴴ - ∑ x, (U x : ℂ) • (I x * (R1 - R2) * I x)
      = E • (R1 - R2) := by
  -- The interaction sum distributes over the difference term by term.
  have hsum : ∑ x, (U x : ℂ) • (I x * (R1 - R2) * I x)
      = (∑ x, (U x : ℂ) • (I x * R1 * I x))
        - ∑ x, (U x : ℂ) • (I x * R2 * I x) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by
      rw [Matrix.mul_sub, Matrix.sub_mul, smul_sub])
  -- Distribute the remaining terms and cancel using the two hypotheses.
  rw [hsum, Matrix.mul_sub, Matrix.sub_mul, smul_sub, ← h1, ← h2]
  abel

end LatticeSystem.Math
