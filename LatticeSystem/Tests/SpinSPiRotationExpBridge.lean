import LatticeSystem.Quantum.SpinS.SpinSPiRotation
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis3
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis1
import LatticeSystem.Quantum.SpinS.SpinSPiRotationExpAxis2
import LatticeSystem.Quantum.SpinHalfRotation.Conjugation

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
`⟨ψ^σ|û₁|ψ^τ⟩ = (−i)^{2S}δ_{σ,−τ}`, i.e. `spinSPiRotation1 N = spinSRot1 N Real.pi`, by a
Schur/commutant route rather than the entrywise computation that settles axis 3. The route
conjugates the generators `Ŝ¹, Ŝ², Ŝ³` by `W := spinSRot1 N Real.pi` at `θ = π` (the `π`-rotation
relation (2.1.21), p. 17, read off the `±` commutation proved for arbitrary `θ` by
`spinSRot1_conj_spinSLadder1Plus/Minus`) and by `V := spinSPiRotation1 N` (via
`spinReversalS_conj_spinSOp1/2/3`), concludes their quotient `Z` is scalar by the commutant/Schur
argument (`spinS_adjoin_eq_top`), and pins the scalar to `1` on the explicit binomial
highest-weight vector `u₀ = (√C(N,k))_k` of the first relation of (2.1.34), p. 20
(Problem 2.1.g, p. 20, solution p. 495).

Pinned:
* `spinSRot1_pi_conj_spinSOp1/2/3` — the `θ = π` conjugation of the three generators by `W`.
* A definitional guard that the exponential side `spinSRot1` is the genuine `NormedSpace.exp` of
  `Ŝ^{(1)}`, plus one concrete evaluation of that exponential at `N = 1`, `θ = π` obtained from
  the independent spin-`1/2` bridge `spinHalfRot1_eq_exp`.
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

/-! ## Definitional guard: the axis-1 exponential side is a genuine `exp` -/

/-- Guards that the exponential object of the axis-1 identification is the genuine
`NormedSpace.exp` of `Ŝ^{(1)}`: if `spinSRot1` were redefined as its own closed form, every
statement below would still hold while the content of the first relation of (2.1.34) — closed
form *equals* operator exponential — had evaporated. Companion of the axis-3 guard above. -/
example (N : ℕ) (θ : ℝ) :
    spinSRot1 N θ = NormedSpace.exp (-(((θ : ℂ) * Complex.I)) • spinSOp1 N) := rfl

/-! ## R1-W: `θ = π` conjugation of the three generators by `W := spinSRot1 N Real.pi` -/

/-- R1-W pin (`Ŝ¹`): `W` commutes with `Ŝ¹` — the `β = α` case, which lies outside the `β ≠ α`
conjugation relation (2.1.21), p. 17, and is immediate from `Û^{(1)}_π = exp(−iπ Ŝ^{(1)})`,
p. 15. -/
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
  fin_cases k <;> norm_num [spinSTopVector, Math.cgSite]

/-- R3 pin, concrete `N = 3` (`S = 3/2`, odd, the sign-sensitive case): `u₀ = (1, √3, √3, 1)`. -/
example : (spinSTopVector 3 : Fin 4 → ℂ) = ![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] := by
  funext k
  fin_cases k <;> norm_num [spinSTopVector, Math.cgSite]

/-- R3 pin: `Ŝ¹ u₀ = (N/2) • u₀`, the crux computation of the whole arc (the two ladder-step
identities `Math.sqrt_lower_coeff` for the `Ŝ^+` half and `Math.sqrt_raise_coeff` for the `Ŝ^-`
half). -/
example (N : ℕ) :
    Matrix.mulVec (spinSOp1 N) (spinSTopVector N) = ((N : ℂ) / 2) • spinSTopVector N :=
  spinSOp1_mulVec_spinSTopVector N

/-- Independent control at `N = 2`: `Ŝ¹ (1, √2, 1) = 1 • (1, √2, 1)` (eigenvalue `S = 1`),
computed entrywise from the matrix entries of `Ŝ^±` rather than by instantiating
`spinSOp1_mulVec_spinSTopVector`, so it would disagree with that lemma if the lemma were wrong. -/
example : Matrix.mulVec (spinSOp1 2) (![1, (Real.sqrt 2 : ℂ), 1] : Fin 3 → ℂ)
    = (1 : ℂ) • (![1, (Real.sqrt 2 : ℂ), 1] : Fin 3 → ℂ) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  funext k
  fin_cases k <;>
    norm_num [Matrix.mulVec, dotProduct, spinSOp1, spinSOpPlus, spinSOpMinus,
      Fin.sum_univ_succ] <;>
    ring_nf <;>
    rw [h2] <;>
    norm_num

/-- Independent control at the sign-sensitive odd `N = 3`: `Ŝ¹ (1, √3, √3, 1) =
(3/2) • (1, √3, √3, 1)` (eigenvalue `S = 3/2`), again computed entrywise. -/
example : Matrix.mulVec (spinSOp1 3)
      (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ)
    = ((3 : ℂ) / 2) • (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    norm_cast
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have h3 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
    norm_cast
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  funext k
  fin_cases k <;>
    norm_num [Matrix.mulVec, dotProduct, spinSOp1, spinSOpPlus, spinSOpMinus,
      Fin.sum_univ_succ] <;>
    ring_nf <;>
    simp only [h2, h3, h4] <;>
    push_cast <;>
    ring

/-- R3 pin: `F u₀ = u₀`, the *only* anchor fixing the global sign for odd `N`
(`C(N,k) = C(N,N−k)`). -/
example (N : ℕ) :
    Matrix.mulVec (spinReversalS N) (spinSTopVector N) = spinSTopVector N :=
  spinReversalS_mulVec_spinSTopVector N

/-- Independent sign control at the sign-sensitive odd `N = 3`: `F (1, √3, √3, 1) =
(1, √3, √3, 1)`, computed entrywise from the entries of `F` rather than by instantiating
`spinReversalS_mulVec_spinSTopVector`. -/
example :
    Matrix.mulVec (spinReversalS 3) (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) =
      (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) := by
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, spinReversalS]

/-- Negative control on the same vector: `F u₀ ≠ -u₀`, the alternative that would flip the global
sign of the axis-1 identification for every odd `N`. Refuted at the first entry, again without
appealing to `spinReversalS_mulVec_spinSTopVector`. -/
example :
    Matrix.mulVec (spinReversalS 3) (![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) ≠
      -(![1, (Real.sqrt 3 : ℂ), (Real.sqrt 3 : ℂ), 1] : Fin 4 → ℂ) := by
  intro h
  have h0 := congrFun h 0
  norm_num [Matrix.mulVec, dotProduct, spinReversalS, Fin.sum_univ_succ, Fin.last] at h0

/-! ## R1: the axis-1 exponential identification, capstone of the crux -/

/-- R1 pin: locks the exact name/signature of the axis-1 identification, Tasaki (2.1.34), first
relation, p. 20 (Problem 2.1.g, p. 20; solution p. 495). -/
example (N : ℕ) : spinSPiRotation1 N = spinSRot1 N Real.pi :=
  spinSPiRotation1_eq_spinSRot1_pi N

/-- Positive control at `N = 1` (`S = 1/2`): cross-checked against the concrete `2 × 2`
`(−i)^1 • [[0,1],[1,0]] = [[0,-i],[-i,0]]`, i.e. `−iσ^x`. The exponential side of this instance is
evaluated independently below. -/
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

/-! ## Independent evaluation of the exponential side at `N = 1`

The positive controls above evaluate the *closed-form* side; each discharges the identification
conjunct by the general theorem, so none of them observes `NormedSpace.exp`. The pin below closes
that gap at `N = 1`, where the spin-`S` operator coincides with the spin-`1/2` one and the
already-proved bridge `spinHalfRot1_eq_exp` (Tasaki Problem 2.1.b) evaluates the exponential
without using the axis-1 identification. -/

/-- The exponential side itself at `N = 1`, `θ = π`: `exp(−iπ Ŝ^{(1)}) = −i σ^x`, evaluated
through the spin-`1/2` bridge `spinHalfRot1_eq_exp` and the closed form `cos(θ/2)·1 −
2i sin(θ/2)·Ŝ^{(1)}` — independent of `spinSPiRotation1_eq_spinSRot1_pi`, and agreeing with the
value that theorem predicts.  The step `hop` is the pin that the spin-`1/2` generator is the
`N = 1` spin-`S` generator, `Ŝ^{(1)} = σ^x/2` (Tasaki eq. (2.1.7), p. 15), the `Fin 2` and
`Fin (1 + 1)` index types agreeing definitionally; it is stated here rather than as its own
`example` so that the identification is proved once. -/
example : spinSRot1 1 Real.pi = !![(0 : ℂ), -Complex.I; -Complex.I, 0] := by
  have hop : spinHalfOp1 = spinSOp1 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [spinHalfOp1, spinSOp1, spinSOpPlus, spinSOpMinus, pauliX]
  have harg : (-(Complex.I * ((Real.pi : ℝ) : ℂ))) • spinHalfOp1
      = (-((((Real.pi : ℝ) : ℂ)) * Complex.I)) • spinSOp1 1 := by
    rw [hop, mul_comm]
  have hrot : spinSRot1 1 Real.pi = spinHalfRot1 Real.pi := by
    rw [spinSRot1, spinHalfRot1_eq_exp, harg]
  rw [hrot, spinHalfRot1, rotOf, Real.cos_pi_div_two, Real.sin_pi_div_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spinHalfOp1, pauliX] <;> ring_nf

/-!
# Signature pin: PR-C of the Problem 2.1.g exponential-identification arc, axis 2

PR-C closes the axis-2 case, the second relation of Tasaki (2.1.34), p. 20:
`spinSPiRotation2 N = exp(−iπ Ŝ^{(2)})`, via the *R-conj* route: conjugating PR-B's axis-1
capstone by `spinSRot3 N (Real.pi / 2)` and its inverse, using the repository's inverse-free
intertwining bridge `matrix_exp_intertwine_of_pow_intertwine` rather than mathlib's
`Matrix.exp_conj` (which would need unit/inverse packaging for `spinSRot3` that the repository
does not have). The chain rests on the reversal `F` anti-commuting with a `z`-rotation's angle
(`F · spinSRot3 N θ = spinSRot3 N (-θ) · F`), which collapses the two half-angle conjugating
factors of the printed order `û₂ = û₃û₁` (eq. (2.1.29), p. 19) into `spinSRot3 N Real.pi` and
PR-A's capstone.

Pinned:
* `spinReversalS_mul_spinSRot3` — the angle-flip commutation of the reversal `F` past a
  `z`-rotation of any angle `θ`.
* `spinSOp1_mul_spinSRot3_neg_pi_half` — the sign-critical axis-swap commutation
  `Ŝ¹ · spinSRot3 N (-(π/2)) = spinSRot3 N (-(π/2)) · Ŝ²`, obtained from the existing
  `spinSRot3_neg_pi_half_conj_spinSOp2` (Tasaki-independent conjugation fact already in the
  repository) by right-multiplying and cancelling with `spinSRot3_mul_neg`.
* `exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_conj` — the exponential of `Ŝ²` written as the
  conjugate `spinSRot3 N (π/2) · spinSRot1 N π · spinSRot3 N (-(π/2))`, obtained from the
  axis-swap commutation above by `matrix_exp_intertwine_of_pow_intertwine`.
* A definitional guard that the closed-form side is the printed product `û₂ = û₃û₁`; the
  exponential side needs none, being written with `NormedSpace.exp` directly.
* **`spinSPiRotation2_eq_exp_spinSOp2`** — the axis-2 identification (capstone), Tasaki
  (2.1.34), second relation, p. 20 (Problem 2.1.g, p. 20).
* `exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_pi_mul_spinSRot1_pi` — the printed cyclic relation
  `û₂ = û₃û₁` (eq. (2.1.29), p. 19) restated purely in terms of the operator exponentials.
* `spinSPiRotation2_apply` — the printed entry form `⟨ψ_σ|û₂|ψ_τ⟩ = (−1)^{S+σ}δ_{σ,−τ}`
  (eq. (2.1.34), second relation, p. 20) in the integer basis index.
* `spinSPiRotationAxis_eq_exp` — the uniform statement of the closed-form family
  `spinSPiRotationAxis N α` against `exp(−iπ Ŝ^{(α)})` for all three axes `α : Fin 3`
  simultaneously (Tasaki (2.1.34), p. 20).
* Zero-hypothesis positive controls at `N = 1, 2, 3`, and a negative control separating the
  printed order `û₂ = û₃û₁` — the matrix part of the time reversal `Θ̂ = û₂K̂`, p. 278 — from
  the reversed product `û₁û₃`, which differs from it by `(−1)^{2S}`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed.,
Springer, 2020), the conjugation relations (2.1.21)/(2.1.22) p. 17, eq. (2.1.29) p. 19,
eq. (2.1.34) p. 20, Problem 2.1.g p. 20 (solution p. 495).
-/

/-! ## R2-rev: the angle-flip commutation of the reversal past a `z`-rotation -/

/-- R2-rev pin: locks the exact name/signature of the angle-flip commutation
`F · spinSRot3 N θ = spinSRot3 N (-θ) · F`, generic in `θ`. -/
example (N : ℕ) (θ : ℝ) :
    spinReversalS N * spinSRot3 N θ = spinSRot3 N (-θ) * spinReversalS N :=
  spinReversalS_mul_spinSRot3 N θ

/-! ## R2-swap: the sign-critical axis-swap commutation -/

/-- R2-swap pin: locks the exact name/signature of the axis-swap commutation
`Ŝ¹ · spinSRot3 N (-(π/2)) = spinSRot3 N (-(π/2)) · Ŝ²`, the sign-critical orientation on which
the whole conjugation chain depends. -/
example (N : ℕ) :
    spinSOp1 N * spinSRot3 N (-(Real.pi / 2)) = spinSRot3 N (-(Real.pi / 2)) * spinSOp2 N :=
  spinSOp1_mul_spinSRot3_neg_pi_half N

/-! ## R2-conj: the exponential of `Ŝ²` as a conjugate -/

/-- R2-conj pin: locks the exact name/signature of the exponential of `Ŝ²` written as the
conjugate of `spinSRot1 N Real.pi` by `spinSRot3 N (π/2)`. -/
example (N : ℕ) :
    NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) =
      spinSRot3 N (Real.pi / 2) * spinSRot1 N Real.pi * spinSRot3 N (-(Real.pi / 2)) :=
  exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_conj N

/-! ## Definitional guard: the axis-2 closed form is the printed product `û₃û₁` -/

/-- Guards the closed-form side of the axis-2 identification: `spinSPiRotation2` unfolds to the
printed product `û₂ = û₃û₁` of eq. (2.1.29), p. 19, so the statement below is about that product
and not about a separately posited matrix.  The exponential side needs no companion guard — it is
written with `NormedSpace.exp` directly, so no closed-form alias can hide in it (this is where the
axis-1 and axis-3 guards above are needed instead, their `spinSRot1`/`spinSRot3` being named
wrappers). -/
example (N : ℕ) :
    spinSPiRotation2 N = spinSPiRotation3 N * spinSPiRotation1 N := rfl

/-! ## R2: the axis-2 exponential identification, capstone -/

/-- R2 pin: locks the exact name/signature of the axis-2 identification, Tasaki (2.1.34), second
relation, p. 20 (Problem 2.1.g, p. 20; solution p. 495). -/
example (N : ℕ) :
    spinSPiRotation2 N = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) :=
  spinSPiRotation2_eq_exp_spinSOp2 N

/-! ## R2-entry: the printed entry form of (2.1.34), second relation -/

/-- R2-entry pin: locks the exact name/signature of the printed entry form
`⟨ψ_σ|û₂|ψ_τ⟩ = (−1)^{S+σ}δ_{σ,−τ}` (eq. (2.1.34), second relation, p. 20) in the integer basis
index `k`, the form in which the general-`S` phase `(−1)^{S+σ}` is actually stated. -/
example (N : ℕ) (i j : Fin (N + 1)) :
    spinSPiRotation2 N i j = if j = Fin.rev i then (-1 : ℂ) ^ (N + (i : ℕ)) else 0 :=
  spinSPiRotation2_apply N i j

/-! ## R2-129: the printed cyclic relation, purely in exponentials -/

/-- R2-129 pin: locks the exact name/signature of the printed cyclic relation `û₂ = û₃û₁`
(eq. (2.1.29), p. 19), restated purely in terms of the operator exponentials of `Ŝ²`, `Ŝ³`,
`Ŝ¹`. -/
example (N : ℕ) :
    NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 N) =
      spinSRot3 N Real.pi * spinSRot1 N Real.pi :=
  exp_neg_pi_mul_I_spinSOp2_eq_spinSRot3_pi_mul_spinSRot1_pi N

/-! ## Positive controls, zero hypotheses -/

/-- Positive control at `N = 1` (`S = 1/2`): agrees by value with the independent spin-`1/2`
bridge `spinHalfRot2_eq_exp`, since `Fin 2` and `Fin (1 + 1)` are definitionally equal. -/
example :
    spinSPiRotation2 1 = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 1) ∧
      spinSPiRotation2 1 = !![(0 : ℂ), -1; 1, 0] := by
  refine ⟨spinSPiRotation2_eq_exp_spinSOp2 1, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation2, spinSPiRotation3, spinSPiRotation1, spinSAlternating, spinReversalS,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Positive control at `N = 2` (`S = 1`, even): `spinSPiRotation2 2 =
!![0,0,1; 0,-1,0; 1,0,0]`. -/
example :
    spinSPiRotation2 2 = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 2) ∧
      spinSPiRotation2 2 = !![(0 : ℂ), 0, 1; 0, -1, 0; 1, 0, 0] := by
  refine ⟨spinSPiRotation2_eq_exp_spinSOp2 2, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation2, spinSPiRotation3, spinSPiRotation1, spinSAlternating, spinReversalS,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Positive control at `N = 3` (`S = 3/2`, odd, the sign-sensitive case):
`spinSPiRotation2 3 = !![0,0,0,-1; 0,0,1,0; 0,-1,0,0; 1,0,0,0]`. -/
example :
    spinSPiRotation2 3 = NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 3) ∧
      spinSPiRotation2 3 =
        !![(0 : ℂ), 0, 0, -1; 0, 0, 1, 0; 0, -1, 0, 0; 1, 0, 0, 0] := by
  refine ⟨spinSPiRotation2_eq_exp_spinSOp2 3, ?_⟩
  have hI3 : (-Complex.I : ℂ) ^ 3 = Complex.I := by
    have h2 : (-Complex.I : ℂ) ^ 2 = -1 := by
      rw [sq, neg_mul_neg, Complex.I_mul_I]
    rw [pow_succ, h2, neg_one_mul, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation2, spinSPiRotation3, spinSPiRotation1, spinSAlternating, spinReversalS,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, Matrix.mul_apply, Fin.sum_univ_succ,
      hI3, Complex.I_mul_I]
  norm_num [Complex.I_sq]

/-! ## R2-order: negative control on the printed order `û₂ = û₃û₁` vs `û₁û₃` -/

/-- R2-order pin: at `N = 1` the reversed product `û₁û₃` is `−exp(−iπ Ŝ^{(2)})`, differing by
`(−1)^{2S}` from the printed `û₂ = û₃û₁` that this PR identifies with that exponential (`û₂` is
the matrix part of the time reversal `Θ̂ = û₂K̂`, p. 278).  A route silently identifying `û₁û₃`
with the axis-2 exponential would make this control false; it reaches the exponential through
this PR's capstone, so it observes the route rather than the definition alone. -/
example :
    spinSPiRotation1 1 * spinSPiRotation3 1 =
      -(NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • spinSOp2 1)) := by
  rw [← spinSPiRotation2_eq_exp_spinSOp2 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation2, spinSPiRotation3, spinSPiRotation1, spinSAlternating, spinReversalS,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ## R4: the uniform axis family, at `N = 1` for all three axes -/

/-- R4 pin: locks the exact name/signature of the uniform closed-form-vs-exponential statement
`spinSPiRotationAxis N α = exp(−iπ Ŝ^{(α)})`, instantiated at `N = 1` for all three axes
`α : Fin 3` — the slot none of the sign-symmetric axis-specific statements above can observe. -/
example :
    spinSPiRotationAxis 1 0 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • (![spinSOp1 1, spinSOp2 1, spinSOp3 1] 0))
      ∧ spinSPiRotationAxis 1 1 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • (![spinSOp1 1, spinSOp2 1, spinSOp3 1] 1))
      ∧ spinSPiRotationAxis 1 2 =
        NormedSpace.exp
          (-(((Real.pi : ℂ) * Complex.I)) • (![spinSOp1 1, spinSOp2 1, spinSOp3 1] 2)) :=
  ⟨spinSPiRotationAxis_eq_exp 1 0, spinSPiRotationAxis_eq_exp 1 1, spinSPiRotationAxis_eq_exp 1 2⟩

end LatticeSystem.Quantum
