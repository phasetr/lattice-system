import LatticeSystem.Quantum.SpinS.SpinSPiRotation
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis3
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis1

/-!
# Signature pin: PR-A of the Problem 2.1.g exponential-identification arc, axis 3

Repository-internal regression guard for PR-A of the arc that identifies the closed-form
spin-`S` `π`-rotations `spinSPiRotationAxis` with the book's `exp(−iπ Ŝ^{(α)})` (H. Tasaki,
*Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer, 2020,
**eq. (2.1.34), p. 20**, the general-`S` closed form left to the reader as **Problem 2.1.g,
p. 20**, solution p. 495; the many-body definition **eq. (2.2.11), p. 22**). PR-A closes only
the axis-3 (diagonal) case, the third relation of (2.1.34):
`⟨ψ^σ|û₃|ψ^τ⟩ = e^{−iπσ}δ_{σ,τ}`, phrased in the integer basis index `k = S − σ` rather
than the magnetic quantum number `σ`, since `σ` itself is not an integer for
half-odd-integer `S`, so the printed exponent `e^{−iπσ}` is not a power of `−1`; this is why the
closed form carries `(−i)^N`.

Pinned:
* R0-scalar `spinSOp3Eigen_exp_neg_pi_mul_I_eq` — the scalar phase identity
  `exp(−iπ(N/2 − k)) = (−i)^N (−1)^k` carried by each diagonal entry of Tasaki (2.1.34),
  third relation, p. 20.
* R0 `spinSPiRotation3_eq_spinSRot3_pi` — the axis-3 identification
  `spinSPiRotation3 N = spinSRot3 N Real.pi` (Tasaki (2.1.34), third relation, p. 20;
  Problem 2.1.g, p. 20).
* A definitional guard that the exponential side `spinSRot3` is the genuine `NormedSpace.exp`
  of `Ŝ^{(3)}`, not a closed-form alias.
* Zero-hypothesis positive controls at `N = 1, 2, 3`, cross-checked against the existing
  `spinSRot3_eq_diagonal` closed form and the concrete diagonal entries, including the
  sign-sensitive odd case `N = 3`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.,
Springer, 2020), §2.1, Û_θ^{(α)} definition p. 15, eq. (2.1.34) p. 20, Problem 2.1.g p. 20
(solution p. 495), eq. (2.2.11) p. 22.
Refs #5455.
-/

namespace LatticeSystem.Quantum

open Matrix NormedSpace

/-! ## R0-scalar: the scalar phase identity -/

/-- R0-scalar pin: locks the exact name/signature of the scalar phase identity
`exp(−iπ(N/2 − k)) = (−i)^N (−1)^k`, the sole computation behind the axis-3
identification. -/
example (N : ℕ) (k : Fin (N + 1)) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) * spinSOp3Eigen N k) =
      ((-Complex.I) ^ N) * (-1 : ℂ) ^ (k : ℕ) :=
  spinSOp3Eigen_exp_neg_pi_mul_I_eq N k

/-! ## R0: the axis-3 exponential identification -/

/-- R0 pin: locks the exact name/signature of the axis-3 identification, Tasaki (2.1.34), third
relation, p. 20 (Problem 2.1.g, p. 20). -/
example (N : ℕ) : spinSPiRotation3 N = spinSRot3 N Real.pi :=
  spinSPiRotation3_eq_spinSRot3_pi N

/-! ## Definitional guard: the exponential side is a genuine `exp` -/

/-- Guards that the exponential object of the identification is the genuine `NormedSpace.exp` of
`Ŝ^{(3)}`: if `spinSRot3` were redefined as its own diagonal closed form, every statement below
would still hold while the content of (2.1.34) — closed form *equals* operator exponential — had
evaporated. -/
example (N : ℕ) (θ : ℝ) :
    spinSRot3 N θ = NormedSpace.exp (-(((θ : ℂ) * Complex.I)) • spinSOp3 N) := rfl

/-! ## Positive controls, zero hypotheses -/

/-- Positive control at `N = 1` (`S = 1/2`): the axis-3 identification instantiated, cross-checked
against the concrete `2 × 2` diagonal `!![-I, 0; 0, I]` via the existing `spinSRot3_eq_diagonal`
closed form. -/
example :
    spinSPiRotation3 1 = spinSRot3 1 Real.pi ∧
      spinSPiRotation3 1 = !![(-Complex.I : ℂ), 0; 0, Complex.I] := by
  refine ⟨spinSPiRotation3_eq_spinSRot3_pi 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]

/-- Positive control at `N = 2` (`S = 1`): the diagonal entries are
`(−i)^2 (−1)^k = −(−1)^k`, i.e. `!![-1, 0, 0; 0, 1, 0; 0, 0, -1]`. -/
example :
    spinSPiRotation3 2 = spinSRot3 2 Real.pi ∧
      spinSPiRotation3 2 =
        !![(-1 : ℂ), 0, 0; 0, 1, 0; 0, 0, -1] := by
  refine ⟨spinSPiRotation3_eq_spinSRot3_pi 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne]

/-- Positive control at `N = 3` (`S = 3/2`, odd `N`, the sign-sensitive case): the phase
`(−i)^3 = i` multiplies the alternating diagonal `(−1)^k`, giving
`!![i, 0, 0, 0; 0, -i, 0, 0; 0, 0, i, 0; 0, 0, 0, -i]`. -/
example :
    spinSPiRotation3 3 = spinSRot3 3 Real.pi ∧
      spinSPiRotation3 3 =
        !![Complex.I, 0, 0, 0; 0, (-Complex.I : ℂ), 0, 0; 0, 0, Complex.I, 0;
           0, 0, 0, (-Complex.I : ℂ)] := by
  refine ⟨spinSPiRotation3_eq_spinSRot3_pi 3, ?_⟩
  have hI3 : (-Complex.I : ℂ) ^ 3 = Complex.I := by
    have h2 : (-Complex.I : ℂ) ^ 2 = -1 := by
      rw [sq, neg_mul_neg, Complex.I_mul_I]
    rw [pow_succ, h2, neg_one_mul, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation3, spinSAlternating, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne,
      hI3]
  ring

/-!
# Signature pin: PR-B of the Problem 2.1.g exponential-identification arc, axis 1

PR-B closes the axis-1 (crux) case, the first relation of Tasaki (2.1.34), p. 20:
`⟨ψ^σ|û₁|ψ^τ⟩ = (−i)^{2S}δ_{σ,−τ}`, i.e. `spinSPiRotation1 N = spinSRot1 N Real.pi`, via the
Schur/commutant route of the design (`.self-local/reports/design-tsk071-exp-bridge-2026-09-09.md`
§2 Axis 1, decision recorded in
`.self-local/docs/math/pi-rotation-exponential-bridge-general-spin.tex` §"Implementation decision
of 2026-09-09"). The route conjugates the generators `Ŝ¹, Ŝ², Ŝ³` by `W := spinSRot1 N Real.pi`
at `θ = π` (Tasaki (2.1.21)/(2.1.25) p. 17–18, the `±` commutation of two `π`-rotations already
proved for arbitrary `θ` by `spinSRot1_conj_spinSLadder1Plus/Minus`) and by
`V := spinSPiRotation1 N` (via `spinReversalS_conj_spinSOp1/2/3`), concludes their quotient `Z` is
scalar by the commutant/Schur argument (`spinS_adjoin_eq_top`), and pins the scalar to `1` on the
explicit binomial highest-weight vector `u₀ = (√C(N,k))_k` (Tasaki (2.1.34) p. 20, Problem 2.1.g
p. 20, solution p. 495 — the direct route this design avoids; the top-vector pin instead).

Pinned (all new PR-B names; none exist yet):
* `spinSRot1_pi_conj_spinSOp1/2/3` — the `θ = π` conjugation of the three generators by `W`.
* `spinSPiRotation1_conj_spinSOp1/2` — the conjugation of the generators by `V`.
* `spinS_scalar_of_commute_generators` — the scalar-commutant (Schur) lemma: a matrix commuting
  with `Ŝ¹, Ŝ², Ŝ³` is a scalar multiple of `1`.
* `matrix_exp_mulVec_of_mulVec_eq_smul` — the eigenvector-exponential lemma
  `A *ᵥ v = λ • v → exp A *ᵥ v = exp λ • v`.
* `spinSTopVector` — the binomial highest-weight vector `u₀ := (√C(N,k))_k`, and its two facts
  `spinSOp1_mulVec_spinSTopVector` (`Ŝ¹u₀ = (N/2) • u₀`) and
  `spinReversalS_mulVec_spinSTopVector` (`F u₀ = u₀`).
* `spinSPiRotation1_eq_spinSRot1_pi` — the axis-1 identification, Tasaki (2.1.34), first
  relation, p. 20 (Problem 2.1.g, p. 20).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.,
Springer, 2020), (2.1.25) p. 18 (`±` commutation of two `π`-rotations), (2.1.34) p. 20,
Problem 2.1.g p. 20 (solution p. 495).
Refs #5455.
-/

/-! ## Sanity control, already valid: the concrete `N = 1` target matrix -/

/-- Already-passing sanity control (no new identifiers): confirms the concrete `2 × 2` target
matrix `(−i)^1 • [[0,1],[1,0]]` used by the `N = 1` positive controls below is exactly
`spinSPiRotation1 1` under the *existing* closed-form definition, before any exponential
identification is proved. -/
example :
    spinSPiRotation1 1 = ((-Complex.I) ^ 1 : ℂ) • (!![(0 : ℂ), 1; 1, 0]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinSPiRotation1, spinReversalS]

/-! ## R1-W: `θ = π` conjugation of the three generators by `W := spinSRot1 N Real.pi` -/

/-- R1-W pin (`Ŝ¹`): `W` commutes with `Ŝ¹` (Tasaki (2.1.25) p. 18 specialised, `α = 1`). -/
example (N : ℕ) :
    spinSRot1 N Real.pi * spinSOp1 N * spinSRot1 N (-Real.pi) = spinSOp1 N :=
  spinSRot1_pi_conj_spinSOp1 N

/-- R1-W pin (`Ŝ²`): `W Ŝ² W⁻¹ = -Ŝ²`. -/
example (N : ℕ) :
    spinSRot1 N Real.pi * spinSOp2 N * spinSRot1 N (-Real.pi) = -spinSOp2 N :=
  spinSRot1_pi_conj_spinSOp2 N

/-- R1-W pin (`Ŝ³`): `W Ŝ³ W⁻¹ = -Ŝ³`. -/
example (N : ℕ) :
    spinSRot1 N Real.pi * spinSOp3 N * spinSRot1 N (-Real.pi) = -spinSOp3 N :=
  spinSRot1_pi_conj_spinSOp3 N

/-! ## R1-V: conjugation of the generators by `V := spinSPiRotation1 N` -/

/-- R1-V pin (`Ŝ¹`): `V` fixes `Ŝ¹` (`V⁻¹ = i^N • spinReversalS N` since `F² = 1`). -/
example (N : ℕ) :
    spinSPiRotation1 N * spinSOp1 N * ((Complex.I ^ N) • spinReversalS N) = spinSOp1 N :=
  spinSPiRotation1_conj_spinSOp1 N

/-- R1-V pin (`Ŝ²`): `V Ŝ² V⁻¹ = -Ŝ²`. -/
example (N : ℕ) :
    spinSPiRotation1 N * spinSOp2 N * ((Complex.I ^ N) • spinReversalS N) = -spinSOp2 N :=
  spinSPiRotation1_conj_spinSOp2 N

/-! ## R1-Schur: the scalar-commutant lemma -/

/-- R1-Schur pin: a matrix commuting with all three spin-`S` generators is a scalar multiple of
`1` (Schur's lemma via `spinS_adjoin_eq_top`, the spanning theorem). -/
example (N : ℕ) (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (h1 : Commute Z (spinSOp1 N)) (h2 : Commute Z (spinSOp2 N)) (h3 : Commute Z (spinSOp3 N)) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :=
  spinS_scalar_of_commute_generators N Z h1 h2 h3

/-! ## R1-exp: the eigenvector-exponential lemma -/

/-- R1-exp pin: `A *ᵥ v = λ • v → exp A *ᵥ v = exp λ • v`, generic over any `Fintype`,
`DecidableEq` index (Tasaki (A.2.16)–(A.2.20) p. 465, the elementary consequence of the
power-series definition of the matrix exponential). Phrased via `Matrix.mulVec` rather than the
`*ᵥ` notation: inside `namespace LatticeSystem.Quantum` that notation fails to elaborate at all
(`elaboration function for Mathlib.Tactic.subscriptTerm has not been implemented`, independent of
any unknown identifier — the same namespace-scoped notation breakage already on record for `ᴴ`). -/
example {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (v : n → ℂ) (l : ℂ)
    (h : Matrix.mulVec A v = l • v) :
    Matrix.mulVec (NormedSpace.exp A) v = Complex.exp l • v :=
  matrix_exp_mulVec_of_mulVec_eq_smul A v l h

/-! ## R3: the binomial highest-weight vector `u₀`

Every pin below uses plain `Matrix.mulVec` rather than the `*ᵥ` notation, which does not
elaborate inside `namespace LatticeSystem.Quantum` in this file. -/

/-- R3 pin: locks the exact name/definition of the binomial top vector
`u₀ := (√C(N,k))_k` (Tasaki (2.1.34) p. 20, Problem 2.1.g p. 20, solution p. 495, (S.12)). -/
example (N : ℕ) (k : Fin (N + 1)) :
    spinSTopVector N k = (Real.sqrt (N.choose (k : ℕ)) : ℂ) := rfl

/-- R3 pin, concrete `N = 2` (`S = 1`, even): `u₀ = (1, √2, 1)`. -/
example : (spinSTopVector 2 : Fin 3 → ℂ) = ![1, (Real.sqrt 2 : ℂ), 1] := by
  funext k
  fin_cases k <;> norm_num [spinSTopVector]

/-- R3 pin, concrete `N = 3` (`S = 3/2`, odd, the sign-sensitive case): `u₀ = (1, √3, √3, 1)`. -/
example : (spinSTopVector 3 : Fin 4 → ℂ) = ![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] := by
  funext k
  fin_cases k <;> norm_num [spinSTopVector]

/-- R3 pin: `Ŝ¹ u₀ = (N/2) • u₀`, the crux computation of the whole arc (`sqrt_choose_step`,
`sqrt_raise_coeff`). -/
example (N : ℕ) :
    Matrix.mulVec (spinSOp1 N) (spinSTopVector N) = ((N : ℂ) / 2) • spinSTopVector N :=
  spinSOp1_mulVec_spinSTopVector N

/-- R3 pin, concrete `N = 2`: `Ŝ¹ u₀ = 1 • u₀` (eigenvalue `S = 1`). -/
example : Matrix.mulVec (spinSOp1 2) (spinSTopVector 2) = (1 : ℂ) • spinSTopVector 2 := by
  have h := spinSOp1_mulVec_spinSTopVector 2
  rwa [show ((2 : ℕ) : ℂ) / 2 = 1 from by norm_num] at h

/-- R3 pin, concrete `N = 3`: `Ŝ¹ u₀ = (3/2) • u₀` (eigenvalue `S = 3/2`, odd `N`). -/
example : Matrix.mulVec (spinSOp1 3) (spinSTopVector 3) = ((3 : ℂ) / 2) • spinSTopVector 3 := by
  have h := spinSOp1_mulVec_spinSTopVector 3
  rwa [show ((3 : ℕ) : ℂ) = (3 : ℂ) from by norm_num] at h

/-- R3 pin: `F u₀ = u₀`, the *only* anchor fixing the global sign for odd `N`
(`C(N,k) = C(N,N−k)`). -/
example (N : ℕ) :
    Matrix.mulVec (spinReversalS N) (spinSTopVector N) = spinSTopVector N :=
  spinReversalS_mulVec_spinSTopVector N

/-- R3 negative-control-style sign pin at the sign-sensitive odd `N = 3`: `F u₀ = u₀` on the
concrete vector `(1, √3, √3, 1)`, ruling out the `F u₀ = -u₀` alternative that would flip the
global sign of the axis-1 identification for every odd `N`. -/
example :
    Matrix.mulVec (spinReversalS 3) (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) =
      (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) := by
  have hv : (spinSTopVector 3 : Fin 4 → ℂ) =
      (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) := by
    funext k
    fin_cases k <;> norm_num [spinSTopVector]
  have h' := spinReversalS_mulVec_spinSTopVector 3
  rwa [hv] at h'

/-! ## R1: the axis-1 exponential identification, capstone of the crux -/

/-- R1 pin: locks the exact name/signature of the axis-1 identification, Tasaki (2.1.34), first
relation, p. 20 (Problem 2.1.g, p. 20; solution p. 495). -/
example (N : ℕ) : spinSPiRotation1 N = spinSRot1 N Real.pi :=
  spinSPiRotation1_eq_spinSRot1_pi N

/-- Positive control at `N = 1` (`S = 1/2`): cross-checked against the concrete `2 × 2`
`(−i)^1 • [[0,1],[1,0]] = [[0,-i],[-i,0]]`, i.e. `−iσ^x` — agrees by value with the existing
spin-`1/2` bridge `spinHalfRot1_eq_exp` (`Quantum/SpinHalfRotation/Conjugation.lean:419`); the
`Fin 2`/`Fin (1 + 1)` index types agree definitionally, so no cast is needed to compare values. -/
example :
    spinSPiRotation1 1 = spinSRot1 1 Real.pi ∧
      spinSPiRotation1 1 = !![(0 : ℂ), -Complex.I; -Complex.I, 0] := by
  refine ⟨spinSPiRotation1_eq_spinSRot1_pi 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinSPiRotation1, spinReversalS]

/-- Positive control at `N = 2` (`S = 1`, even `N`): `(−i)^2 = −1` times the unsigned
anti-diagonal, i.e. `!![0,0,-1; 0,-1,0; -1,0,0]`. -/
example :
    spinSPiRotation1 2 = spinSRot1 2 Real.pi ∧
      spinSPiRotation1 2 = !![(0 : ℂ), 0, -1; 0, -1, 0; -1, 0, 0] := by
  refine ⟨spinSPiRotation1_eq_spinSRot1_pi 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinSPiRotation1, spinReversalS]

/-- Positive control at `N = 3` (`S = 3/2`, odd `N`, the sign-sensitive case): `(−i)^3 = i` times
the unsigned anti-diagonal, i.e. `!![0,0,0,i; 0,0,i,0; 0,i,0,0; i,0,0,0]`. -/
example :
    spinSPiRotation1 3 = spinSRot1 3 Real.pi ∧
      spinSPiRotation1 3 =
        !![(0 : ℂ), 0, 0, Complex.I; 0, 0, Complex.I, 0; 0, Complex.I, 0, 0;
           Complex.I, 0, 0, 0] := by
  refine ⟨spinSPiRotation1_eq_spinSRot1_pi 3, ?_⟩
  have hI3 : (-Complex.I : ℂ) ^ 3 = Complex.I := by
    have h2 : (-Complex.I : ℂ) ^ 2 = -1 := by
      rw [sq, neg_mul_neg, Complex.I_mul_I]
    rw [pow_succ, h2, neg_one_mul, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinSPiRotation1, spinReversalS, hI3]

end LatticeSystem.Quantum
