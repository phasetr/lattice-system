import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinSCore

/-!
# The axis-1 `π` rotation as an exponential

The closed-form `π` rotation `û₁` of `Quantum/SpinS/SpinSPiRotation.lean` is the exponential
`Û_π^{(1)} = exp(−iπ Ŝ^{(1)})` of the definition on p. 15, at general spin `S = N/2`: this is the
first relation of the closed form (2.1.34), p. 20, `⟨ψ^σ|û₁|ψ^τ⟩ = (−i)^{2S}δ_{σ,−τ}`, whose
general-`S` derivation is left to the reader as Problem 2.1.g, p. 20 (solution p. 495).

Unlike the axis-3 case, no closed form of `exp(−iπ Ŝ^{(1)})` is available entrywise: `Ŝ^{(1)}` is
tridiagonal in the `Ŝ^{(3)}` basis.  The route is the commutant one.  Both `W := spinSRot1 N π`
and `V := spinSPiRotation1 N` conjugate the generators the same way — fixing `Ŝ^{(1)}`, negating
`Ŝ^{(2)}` and `Ŝ^{(3)}` (the `π`-rotation relation (2.1.25), p. 18) — so `V⁻¹W` commutes with all
three; the spanning theorem `spinS_adjoin_eq_top` (Problem 2.1.a, p. 15) then makes it a scalar.
The scalar is pinned to `1` on the `x`-polarised highest-weight vector
`u₀ = (√binom(N,k))_k` built here, on which `W` acts by `exp(−iπN/2) = (−i)^N` and `V` by the same
phase.  A vector-level pin is unavoidable: for odd `N` both `tr V = tr W = 0` and the determinant
only sees the `(N+1)`-st power of the scalar, so no scalar invariant separates the two signs.

The generic ingredient is the eigenvector formula for the matrix exponential,
`A v = λ v → (exp A) v = e^λ v`, obtained from the intertwining bridge
`matrix_exp_intertwine_of_pow_intertwine` applied to the matrix whose columns are all `v`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.1: the rotation `Û_θ^{(α)} = exp(−iθ Ŝ^{(α)})`, p. 15; the `π`-rotation relation
(2.1.25), p. 18; the closed form (2.1.34) and Problem 2.1.g, p. 20 (solution p. 495); the spanning
Problem 2.1.a, p. 15 (solution p. 493).
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## The exponential on an eigenvector -/

/-- **The matrix exponential acts on an eigenvector by the exponentiated eigenvalue**:
`A v = λ v` implies `(exp A) v = e^λ v`.  Proved from the intertwining bridge
`matrix_exp_intertwine_of_pow_intertwine` for the matrix `X` all of whose columns are `v`: the
eigenvector equation says exactly `A^m X = X (λ 1)^m`, and one column of the resulting
`(exp A) X = X exp(λ 1)` is the claim.  Written with `Matrix.mulVec` rather than the `*ᵥ`
notation, which does not elaborate inside `namespace LatticeSystem.Quantum`. -/
theorem matrix_exp_mulVec_of_mulVec_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (v : n → ℂ) (l : ℂ) (h : Matrix.mulVec A v = l • v) :
    Matrix.mulVec (NormedSpace.exp A) v = Complex.exp l • v := by
  rcases isEmpty_or_nonempty n with hn | hn
  · funext i
    exact (IsEmpty.false i).elim
  obtain ⟨j₀⟩ := hn
  have hpowVec : ∀ m : ℕ, Matrix.mulVec (A ^ m) v = (l ^ m) • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul, ← pow_succ']
  let X : Matrix n n ℂ := Matrix.of fun i _ => v i
  have hXapply : ∀ i j : n, X i j = v i := fun _ _ => rfl
  have hXcol : ∀ (M : Matrix n n ℂ) (i j : n), (M * X) i j = Matrix.mulVec M v i := by
    intro M i j
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, hXapply]
  have hXrow : ∀ (c : ℂ) (i j : n), (X * (c • (1 : Matrix n n ℂ))) i j = c * v i := by
    intro c i j
    simp [Matrix.mul_apply, Matrix.one_apply, hXapply, mul_comm]
  have hpow : ∀ m : ℕ, A ^ m * X = X * (l • (1 : Matrix n n ℂ)) ^ m := by
    intro m
    ext i j
    rw [hXcol, hpowVec, smul_pow, one_pow, hXrow, Pi.smul_apply, smul_eq_mul]
  have hexpB : NormedSpace.exp (l • (1 : Matrix n n ℂ)) = Complex.exp l • 1 := by
    have hdiag : (l • (1 : Matrix n n ℂ)) = Matrix.diagonal (fun _ => l) := by
      ext i j
      by_cases hij : i = j <;> simp [hij]
    rw [hdiag, Matrix.exp_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.diagonal_apply_eq, Pi.exp_def, ← Complex.exp_eq_exp_ℂ]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hint := matrix_exp_intertwine_of_pow_intertwine hpow
  rw [hexpB] at hint
  funext i
  have hentry : (NormedSpace.exp A * X) i j₀ =
      (X * (Complex.exp l • (1 : Matrix n n ℂ))) i j₀ := by rw [hint]
  rw [hXcol, hXrow] at hentry
  rw [hentry, Pi.smul_apply, smul_eq_mul]

end LatticeSystem.Quantum
