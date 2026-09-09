import LatticeSystem.Math.Combinatorics.SqrtChooseLadder
import LatticeSystem.Quantum.SpinS.AxisSwapUnitarySSpinSCore
import LatticeSystem.Quantum.SpinS.SpinSPiRotation
import LatticeSystem.Quantum.SpinS.SpanningTheorem

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
`matrix_exp_intertwine_of_pow_intertwine` applied to the matrix whose columns are all `v`.  It
carries no spin content; it is placed next to that ingredient, which itself sits in
`Quantum/SpinS/AxisSwapUnitarySSpinSCore.lean`, so that the two generic matrix-exponential facts
move to `Math/MatrixAnalysis/` together rather than one at a time.

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

/-! ## The `x`-polarised highest-weight vector `u₀` -/

/-- **The `x`-polarised highest-weight vector** `u₀ = (√binom(N,k))_k` in the `Ŝ^{(3)}` basis of
the spin-`S` space (`N = 2S`).  It is the `Ŝ^{(1)}`-eigenvector of maximal eigenvalue `S = N/2`,
i.e. the state Tasaki writes `|ψ^S⟩` after the axis relabelling `3 ↦ 1`; the binomial weights are
the ones the `2S`-fold spin-`1/2` decomposition of Problem 2.1.g, p. 20 (solution p. 495, (S.12))
produces.  Entrywise it is the Clebsch–Gordan site weight `Math.cgSite`, the repository's single
definition of the `√binom` scalar; this is a name for that weight read as a vector, not a second
definition of it.  The two names are kept apart because they are used at different arities:
`Math.cgSite` is the scalar weight with `N` implicit, shared with the Weyl transport of `Ŝ^±`,
whereas the capstone needs the whole `Fin (N + 1) → ℂ` witness with `N` explicit at every
`Matrix.mulVec`, and it is under this name that the proof guide cites it.  The cost is that proofs
about the entries unfold both names.  Its two properties used here are
`spinSOp1_mulVec_spinSTopVector` and the binomial symmetry
`spinReversalS_mulVec_spinSTopVector`. -/
noncomputable def spinSTopVector (N : ℕ) (k : Fin (N + 1)) : ℂ :=
  Math.cgSite k

/-- Action of `Ŝ^+` on `u₀`: the single surviving raising step contributes the weight `N − i`
times the entry at `i`, by the `√binom` ladder identity `Math.sqrt_lower_coeff`.  At the top index
`i = N` there is no raising step and the coefficient `N − i` vanishes as well. -/
private lemma spinSOpPlus_mulVec_spinSTopVector (N : ℕ) (i : Fin (N + 1)) :
    Matrix.mulVec (spinSOpPlus N) (spinSTopVector N) i
      = (((N - (i : ℕ) : ℕ) : ℝ) : ℂ) * spinSTopVector N i := by
  simp only [Matrix.mulVec, dotProduct]
  rcases Nat.lt_or_ge (i : ℕ) N with hlt | hge
  · have hsucc : (i : ℕ) + 1 < N + 1 := by omega
    rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hsucc⟩ : Fin (N + 1))]
    · rw [spinSOpPlus_apply_raise N (i := i) (j := ⟨(i : ℕ) + 1, hsucc⟩) rfl]
      have hk : Real.sqrt ((((i : ℕ) + 1 : ℕ) : ℝ) * ((N : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ) + 1)) *
            Real.sqrt ((N.choose ((i : ℕ) + 1) : ℕ) : ℝ)
          = ((N - (i : ℕ) : ℕ) : ℝ) * Real.sqrt ((N.choose (i : ℕ) : ℕ) : ℝ) := by
        rw [show ((((i : ℕ) + 1 : ℕ) : ℝ) * ((N : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ) + 1))
              = ((N : ℝ) - ((i : ℕ) : ℝ)) * (((i : ℕ) : ℝ) + 1) from by push_cast; ring,
          Math.sqrt_lower_coeff hlt]
        ring
      unfold spinSTopVector Math.cgSite
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hk
    · intro b _ hb
      rw [spinSOpPlus_apply_other N (fun hval => hb (Fin.ext hval.symm)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hiEq : (i : ℕ) = N := by omega
    rw [Finset.sum_eq_zero]
    · rw [hiEq]; simp
    · intro b _
      have hb := b.isLt
      rw [spinSOpPlus_apply_other N (by omega), zero_mul]

/-- Action of `Ŝ^-` on `u₀`: the single surviving lowering step contributes the weight `i` times
the entry at `i`, by the `√binom` ladder identity `Math.sqrt_raise_coeff`.  At the bottom index
`i = 0` there is no lowering step and the coefficient `i` vanishes as well. -/
private lemma spinSOpMinus_mulVec_spinSTopVector (N : ℕ) (i : Fin (N + 1)) :
    Matrix.mulVec (spinSOpMinus N) (spinSTopVector N) i
      = (((i : ℕ) : ℝ) : ℂ) * spinSTopVector N i := by
  simp only [Matrix.mulVec, dotProduct]
  rcases Nat.eq_zero_or_pos (i : ℕ) with hzero | hpos
  · rw [Finset.sum_eq_zero]
    · rw [hzero]; simp
    · intro b _
      rw [spinSOpMinus_apply_other N (by omega), zero_mul]
  · obtain ⟨k, hk0⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨(i : ℕ) - 1, by omega⟩
    have hklt : k < N + 1 := by omega
    have hkle : k + 1 ≤ N := by have := i.isLt; omega
    rw [Finset.sum_eq_single (⟨k, hklt⟩ : Fin (N + 1))]
    · rw [spinSOpMinus_apply_lower N (i := i) (j := ⟨k, hklt⟩) (by simp [hk0])]
      have hk : Real.sqrt (((N : ℝ) - ((k : ℕ) : ℝ)) * (((k : ℕ) : ℝ) + 1)) *
            Real.sqrt ((N.choose k : ℕ) : ℝ)
          = (((k + 1 : ℕ) : ℝ)) * Real.sqrt ((N.choose (k + 1) : ℕ) : ℝ) := by
        rw [show (((N : ℝ) - ((k : ℕ) : ℝ)) * (((k : ℕ) : ℝ) + 1))
              = (((k : ℕ) : ℝ) + 1) * ((N : ℝ) - (((k : ℕ) : ℝ) + 1) + 1) from by ring,
          Math.sqrt_raise_coeff hkle]
        push_cast
        ring
      unfold spinSTopVector Math.cgSite
      rw [hk0]
      exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) hk
    · intro b _ hb
      refine mul_eq_zero_of_left (spinSOpMinus_apply_other N ?_) _
      intro hval
      exact hb (Fin.ext (show (b : ℕ) = k by omega))
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **`u₀` is the top `Ŝ^{(1)}` eigenvector**: `Ŝ^{(1)} u₀ = (N/2) u₀`, i.e. `Ŝ^{(1)} u₀ = S u₀`.
The two ladder halves of `Ŝ^{(1)} = (Ŝ^+ + Ŝ^-)/2` contribute the complementary weights `N − i`
and `i` at every index, whose half-sum is the constant `N/2`.  This is the computation that makes
the `x`-polarised state the highest-weight state of the axis-1 chain of Tasaki (2.1.34), p. 20
(Problem 2.1.g, p. 20). -/
theorem spinSOp1_mulVec_spinSTopVector (N : ℕ) :
    Matrix.mulVec (spinSOp1 N) (spinSTopVector N) = ((N : ℂ) / 2) • spinSTopVector N := by
  funext i
  have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.isLt
  rw [spinSOp1, Matrix.smul_mulVec, Matrix.add_mulVec]
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [spinSOpPlus_mulVec_spinSTopVector, spinSOpMinus_mulVec_spinSTopVector]
  rw [show (((N - (i : ℕ) : ℕ) : ℝ) : ℂ) = (N : ℂ) - ((i : ℕ) : ℂ) from by
    rw [Nat.cast_sub hi]; push_cast; ring]
  push_cast
  ring

/-- **`u₀` is invariant under the basis reversal `F`**: `F u₀ = u₀`, the binomial symmetry
`binom(N,k) = binom(N,N−k)`.  This is the *only* anchor fixing the global sign of the axis-1
identification: for half-odd-integer spin the two candidate signs are indistinguishable by any
scalar invariant. -/
theorem spinReversalS_mulVec_spinSTopVector (N : ℕ) :
    Matrix.mulVec (spinReversalS N) (spinSTopVector N) = spinSTopVector N := by
  funext i
  have hi : (i : ℕ) ≤ N := Nat.lt_succ_iff.mp i.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Fin.rev i)]
  · rw [spinReversalS_apply, if_pos rfl, one_mul, spinSTopVector, spinSTopVector, Math.cgSite,
      Math.cgSite, Fin.val_rev, Nat.add_sub_add_right, Nat.choose_symm hi]
  · intro b _ hb
    rw [spinReversalS_apply, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ## Conjugation of the generators at `θ = π`

Both `W := spinSRot1 N π` and `V := spinSPiRotation1 N` implement the same `π` rotation about
axis 1 on the generators — Tasaki (2.1.25), p. 18: axis `1` is fixed, axes `2` and `3` are
reversed.  For `W` this is the `θ = π` case of the ladder conjugation
`spinSRot1_conj_spinSLadder1Plus/Minus`, proved here for each generator; for `V` the existing
basis-reversal conjugations `spinReversalS_conj_spinSOp1/2/3` are used directly by the capstone,
the phase `(−i)^{2S}` cancelling against its inverse `i^{2S}` via
`spinSPiRotation1_inv_conj_eq_spinReversalS_conj`.
-/

/-- Conjugation of `Ŝ^{(1)}` by `W = exp(−iπ Ŝ^{(1)})` is trivial: the rotation commutes with its
own generator. -/
theorem spinSRot1_pi_conj_spinSOp1 (N : ℕ) :
    spinSRot1 N Real.pi * spinSOp1 N * spinSRot1 N (-Real.pi) = spinSOp1 N := by
  have hcomm := spinSRot1_commute_spinSOp1 N Real.pi
  rw [show spinSRot1 N Real.pi * spinSOp1 N = spinSOp1 N * spinSRot1 N Real.pi from hcomm,
    Matrix.mul_assoc, spinSRot1_mul_neg, Matrix.mul_one]

/-- **Conjugation of `Ŝ^{(2)}` by `W = exp(−iπ Ŝ^{(1)})` reverses it** — the transverse axis 2 of
Tasaki (2.1.25), p. 18.  The two axis-1 ladder operators `L^± = Ŝ^{(2)} ± i Ŝ^{(3)}` are each
scaled by `e^{∓iπ} = −1`, and their sum is `2 Ŝ^{(2)}`. -/
theorem spinSRot1_pi_conj_spinSOp2 (N : ℕ) :
    spinSRot1 N Real.pi * spinSOp2 N * spinSRot1 N (-Real.pi) = -spinSOp2 N := by
  have hneg : Complex.exp (-(((Real.pi : ℝ) : ℂ) * Complex.I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have h2 : (2 : ℂ) • spinSOp2 N = spinSLadder1Plus N + spinSLadder1Minus N :=
    (spinSLadder1Plus_add_Minus N).symm
  have hL : spinSRot1 N Real.pi * (spinSLadder1Plus N + spinSLadder1Minus N) *
      spinSRot1 N (-Real.pi) = (2 : ℂ) • (-spinSOp2 N) := by
    rw [Matrix.mul_add, Matrix.add_mul, spinSRot1_conj_spinSLadder1Plus,
      spinSRot1_conj_spinSLadder1Minus, hneg, Complex.exp_pi_mul_I, neg_one_smul, neg_one_smul,
      ← neg_add, spinSLadder1Plus_add_Minus, smul_neg]
  have hcancel : (2 : ℂ) • (spinSRot1 N Real.pi * spinSOp2 N * spinSRot1 N (-Real.pi)) =
      (2 : ℂ) • (-spinSOp2 N) := by
    rw [← hL, ← h2, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_right_injective _ (by norm_num) hcancel

/-- **Conjugation of `Ŝ^{(3)}` by `W = exp(−iπ Ŝ^{(1)})` reverses it** — the transverse axis 3 of
Tasaki (2.1.25), p. 18.  Same computation as for `Ŝ^{(2)}`, read off the difference
`L^+ − L^- = 2i Ŝ^{(3)}` instead of the sum. -/
theorem spinSRot1_pi_conj_spinSOp3 (N : ℕ) :
    spinSRot1 N Real.pi * spinSOp3 N * spinSRot1 N (-Real.pi) = -spinSOp3 N := by
  have hneg : Complex.exp (-(((Real.pi : ℝ) : ℂ) * Complex.I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have h2I : (2 * Complex.I) • spinSOp3 N = spinSLadder1Plus N - spinSLadder1Minus N :=
    (spinSLadder1Plus_sub_Minus N).symm
  have hL : spinSRot1 N Real.pi * (spinSLadder1Plus N - spinSLadder1Minus N) *
      spinSRot1 N (-Real.pi) = (2 * Complex.I) • (-spinSOp3 N) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, spinSRot1_conj_spinSLadder1Plus,
      spinSRot1_conj_spinSLadder1Minus, hneg, Complex.exp_pi_mul_I, neg_one_smul, neg_one_smul,
      neg_sub_neg, ← neg_sub, spinSLadder1Plus_sub_Minus, smul_neg]
  have hcancel : (2 * Complex.I) • (spinSRot1 N Real.pi * spinSOp3 N * spinSRot1 N (-Real.pi)) =
      (2 * Complex.I) • (-spinSOp3 N) := by
    rw [← hL, ← h2I, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_right_injective _ (by simp [Complex.I_ne_zero]) hcancel

/-- Conjugation by `V⁻¹ = i^{2S} F` is conjugation by the basis reversal `F`: the phase cancels
against the phase `(−i)^{2S}` of `V = (−i)^{2S} F`. -/
private theorem spinSPiRotation1_inv_conj_eq_spinReversalS_conj (N : ℕ)
    (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    ((Complex.I ^ N) • spinReversalS N) * M * spinSPiRotation1 N
      = spinReversalS N * M * spinReversalS N := by
  have hab : (Complex.I ^ N) * ((-Complex.I) ^ N) = 1 := by
    rw [← mul_pow, mul_neg, Complex.I_mul_I, neg_neg, one_pow]
  rw [spinSPiRotation1, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hab,
    one_smul]

/-! ## From the commutant to the axis-1 identification -/

/-- **Schur's lemma for the spin-`S` generators**: a matrix commuting with `Ŝ^{(1)}`, `Ŝ^{(2)}`
and `Ŝ^{(3)}` is a scalar multiple of the identity.  The generators adjoin to the whole matrix
algebra (`spinS_adjoin_eq_top`, Tasaki Problem 2.1.a, p. 15), so such a matrix lies in the
centralizer of everything, hence in the centre, which for matrices over a field is the range of
`Matrix.scalar`. -/
theorem spinS_scalar_of_commute_generators (N : ℕ)
    (Z : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (h1 : Commute Z (spinSOp1 N)) (h2 : Commute Z (spinSOp2 N)) (h3 : Commute Z (spinSOp3 N)) :
    ∃ c : ℂ, Z = c • (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) := by
  have hcent : ∀ M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute M Z := by
    intro M
    have hgen : ({spinSOp1 N, spinSOp2 N, spinSOp3 N} :
        Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) ⊆
        (Subalgebra.centralizer ℂ ({Z} : Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) :
          Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
      rintro g rfl
      rcases hx with rfl | rfl | rfl
      exacts [h1, h2, h3]
    have htop := Algebra.adjoin_le hgen
    rw [spinS_adjoin_eq_top] at htop
    have hM : M ∈ Subalgebra.centralizer ℂ
        ({Z} : Set (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)) := htop Algebra.mem_top
    rw [Subalgebra.mem_centralizer_iff] at hM
    exact (hM Z rfl).symm
  obtain ⟨c, hc⟩ :=
    Matrix.mem_range_scalar_iff_commute_single'.mpr fun i j => hcent (Matrix.single i j 1)
  refine ⟨c, ?_⟩
  rw [← hc, Matrix.scalar_apply]
  ext i j
  by_cases hij : i = j <;> simp [hij]

/-- **The axis-1 `π` rotation is the exponential `exp(−iπ Ŝ^{(1)})`** at every spin `S = N/2`:
the closed form `û₁ = (−i)^{2S}F` of `spinSPiRotation1` agrees with the rotation `spinSRot1 N π`
of the definition on p. 15.  This is the first relation of Tasaki (2.1.34), p. 20
(`⟨ψ^σ|û₁|ψ^τ⟩ = (−i)^{2S}δ_{σ,−τ}`), left to the reader as Problem 2.1.g, p. 20 (solution
p. 495).

Both matrices conjugate the three generators identically (Tasaki (2.1.25), p. 18), so
`Z = û₁⁻¹ exp(−iπ Ŝ^{(1)})` commutes with all of them and is therefore a scalar
(`spinS_scalar_of_commute_generators`).  The scalar is `1` because both matrices multiply the
`x`-polarised top vector `u₀` by the same phase `(−i)^{2S}`: for `exp(−iπ Ŝ^{(1)})` because `u₀` is
its eigenvector of eigenvalue `S = N/2`, for `û₁` because `F u₀ = u₀`. -/
theorem spinSPiRotation1_eq_spinSRot1_pi (N : ℕ) :
    spinSPiRotation1 N = spinSRot1 N Real.pi := by
  have hab : ((-Complex.I) ^ N) * (Complex.I ^ N) = 1 := by
    rw [← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow]
  have hVF : spinSPiRotation1 N * ((Complex.I ^ N) • spinReversalS N) = 1 := by
    rw [spinSPiRotation1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hab, one_smul,
      spinReversalS_mul_self]
  -- `Z = V⁻¹W` commutes with any generator conjugated the same way by `W` and by `F`.
  have key : ∀ (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (e : ℂ),
      spinSRot1 N Real.pi * M * spinSRot1 N (-Real.pi) = e • M →
      spinReversalS N * M * spinReversalS N = e • M → e * e = 1 →
      Commute (((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi) M := by
    intro M e hW hF he
    have hZinvZ : (spinSRot1 N (-Real.pi) * spinSPiRotation1 N) *
        (((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi) = 1 := by
      calc (spinSRot1 N (-Real.pi) * spinSPiRotation1 N) *
            (((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi)
          = spinSRot1 N (-Real.pi) * (spinSPiRotation1 N *
              ((Complex.I ^ N) • spinReversalS N)) * spinSRot1 N Real.pi := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hVF, Matrix.mul_one, spinSRot1_neg_mul]
    have hZM : ((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi * M *
        (spinSRot1 N (-Real.pi) * spinSPiRotation1 N) = M := by
      calc ((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi * M *
            (spinSRot1 N (-Real.pi) * spinSPiRotation1 N)
          = ((Complex.I ^ N) • spinReversalS N) *
              (spinSRot1 N Real.pi * M * spinSRot1 N (-Real.pi)) * spinSPiRotation1 N := by
            simp only [Matrix.mul_assoc]
        _ = ((Complex.I ^ N) • spinReversalS N) * (e • M) * spinSPiRotation1 N := by rw [hW]
        _ = e • (((Complex.I ^ N) • spinReversalS N) * M * spinSPiRotation1 N) := by
            rw [Matrix.mul_smul, Matrix.smul_mul]
        _ = e • (spinReversalS N * M * spinReversalS N) := by
            rw [spinSPiRotation1_inv_conj_eq_spinReversalS_conj]
        _ = M := by rw [hF, smul_smul, he, one_smul]
    have hmul := congrArg (fun X => X * (((Complex.I ^ N) • spinReversalS N) *
      spinSRot1 N Real.pi)) hZM
    simp only [Matrix.mul_assoc] at hmul
    rw [← Matrix.mul_assoc (spinSRot1 N (-Real.pi)), hZinvZ, Matrix.mul_one] at hmul
    have hgoal : ((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi * M =
        M * (((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi) := by
      rw [Matrix.mul_assoc]
      exact hmul
    exact hgoal
  have hcomm1 := key (spinSOp1 N) 1
    (by rw [one_smul]; exact spinSRot1_pi_conj_spinSOp1 N)
    (by rw [one_smul]; exact spinReversalS_conj_spinSOp1 N) (by norm_num)
  have hcomm2 := key (spinSOp2 N) (-1)
    (by rw [neg_one_smul]; exact spinSRot1_pi_conj_spinSOp2 N)
    (by rw [neg_one_smul]; exact spinReversalS_conj_spinSOp2 N) (by norm_num)
  have hcomm3 := key (spinSOp3 N) (-1)
    (by rw [neg_one_smul]; exact spinSRot1_pi_conj_spinSOp3 N)
    (by rw [neg_one_smul]; exact spinReversalS_conj_spinSOp3 N) (by norm_num)
  obtain ⟨c, hc⟩ := spinS_scalar_of_commute_generators N _ hcomm1 hcomm2 hcomm3
  -- The top vector pins the scalar to `1`.
  have hWu : Matrix.mulVec (spinSRot1 N Real.pi) (spinSTopVector N)
      = ((-Complex.I) ^ N) • spinSTopVector N := by
    have hA : Matrix.mulVec (-(((Real.pi : ℝ) : ℂ) * Complex.I) • spinSOp1 N)
        (spinSTopVector N)
        = (-(((Real.pi : ℝ) : ℂ) * Complex.I) * ((N : ℂ) / 2)) • spinSTopVector N := by
      rw [Matrix.smul_mulVec, spinSOp1_mulVec_spinSTopVector, smul_smul]
    have hphase : Complex.exp (-(((Real.pi : ℝ) : ℂ) * Complex.I) * ((N : ℂ) / 2))
        = (-Complex.I) ^ N := by
      have hhalf : Complex.exp (-(((Real.pi : ℝ) : ℂ) / 2 * Complex.I)) = -Complex.I := by
        simpa using cexp_neg_pi_half_mul_I
      rw [show -(((Real.pi : ℝ) : ℂ) * Complex.I) * ((N : ℂ) / 2)
            = (N : ℂ) * (-(((Real.pi : ℝ) : ℂ) / 2 * Complex.I)) from by ring,
        Complex.exp_nat_mul, hhalf]
    rw [spinSRot1, matrix_exp_mulVec_of_mulVec_eq_smul _ _ _ hA, hphase]
  have hZu : Matrix.mulVec (((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi)
      (spinSTopVector N) = spinSTopVector N := by
    rw [← Matrix.mulVec_mulVec, hWu, Matrix.mulVec_smul, Matrix.smul_mulVec,
      spinReversalS_mulVec_spinSTopVector, smul_smul, hab, one_smul]
  have hu0 : spinSTopVector N 0 = 1 := by
    rw [spinSTopVector, Math.cgSite]
    simp
  have hc1 : c = 1 := by
    rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec] at hZu
    have h0 := congrFun hZu 0
    rw [Pi.smul_apply, smul_eq_mul, hu0, mul_one] at h0
    exact h0
  have hZ1 : ((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi = 1 := by
    rw [hc, hc1, one_smul]
  calc spinSPiRotation1 N
      = spinSPiRotation1 N *
          (((Complex.I ^ N) • spinReversalS N) * spinSRot1 N Real.pi) := by
        rw [hZ1, Matrix.mul_one]
    _ = (spinSPiRotation1 N * ((Complex.I ^ N) • spinReversalS N)) * spinSRot1 N Real.pi := by
        rw [Matrix.mul_assoc]
    _ = spinSRot1 N Real.pi := by rw [hVF, Matrix.one_mul]

end LatticeSystem.Quantum
