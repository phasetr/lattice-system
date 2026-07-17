import LatticeSystem.Quantum.SpinS.LiebSchultzMattisGeneratorNorm
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Tasaki §6.2 Lemma 6.4 (CRUX B): the second-order Taylor superoperator norm bound

The generalized Lieb–Schultz–Mattis discharge (Lemma 6.4) bounds, for each local term `ĥ_x`, the
**symmetrised second difference** of the twist conjugation

`‖ Û† ĥ_x Û + Û ĥ_x Û† − 2 ĥ_x ‖ ≤ 8 ‖M̂_x‖² ‖ĥ_x‖`   (Tasaki eqs. (6.2.28)–(6.2.30)),

where (after the CRUX A global→local reduction) `Û† ĥ_x Û = exp(+i M̂_x) ĥ_x exp(−i M̂_x)` and
`Û ĥ_x Û† = exp(−i M̂_x) ĥ_x exp(+i M̂_x)`.  This replaces the book's `ad(M̂_x)` eigen-monomial
decomposition (6.2.29) by a finite-dimensional **second-order Taylor remainder** of the
matrix-conjugation superoperator, with the same `O(‖M̂_x‖²)` scaling (a sound weaker constant; the
Lemma 6.4 axiom only requires `C = C(N, r, h₀)`).  The `O(‖M̂_x‖²)` order — not `O(‖M̂_x‖)` — is
essential: the first-order term cancels in the symmetric difference, and this cancellation
turns the per-site `O(1/L²)` into the summed `O(1/L)`.

**Proof route.**  Fix a Hermitian `M` and set `A := −i M` (anti-Hermitian, `Aᴴ = −A`), so
`exp(t • A)` is unitary with adjoint `exp(−(t • A))`.  The matrix conjugation
`f(t) := exp(t • A) · X · exp(−(t • A))` (`expConjOp A X`) has derivative
`f'(t) = exp(t • A) · ⁅A, X⁆ · exp(−(t • A)) = expConjOp A ⁅A, X⁆ t`
(`hasDerivAt_expConjOp`, product rule + `hasDerivAt_exp_smul_const`), so iterating gives
`f''(t) = expConjOp A ⁅A, ⁅A, X⁆⁆ t`.  Unitary conjugation preserves the `L²` operator norm
(`manyBodyOperatorNormS_expConjOp`, consuming `manyBodyOperatorNormS_unitary_conj`), so
`‖f''(t)‖ = ‖⁅A, ⁅A, X⁆⁆‖ ≤ 4‖A‖²‖X‖ = 4‖M‖²‖X‖`.  The symmetric combination
`F(t) := f(t) + f(−t)` has `F'(0) = 0` and `‖F''‖ ≤ 2‖⁅A,⁅A,X⁆⁆‖`, so two applications of the
segment mean-value inequality `norm_image_sub_le_of_norm_deriv_le_segment'` give
`‖F(1) − F(0)‖ = ‖f(1) + f(−1) − 2 f(0)‖ ≤ 2‖⁅A,⁅A,X⁆⁆‖ ≤ 8‖M‖²‖X‖`.

The differentiation of `NormedSpace.exp` requires a `NormedRing` structure on `ManyBodyOpS`; since
`NormedSpace.exp` is norm-independent (defined from the topological ring structure), the proofs open
the scoped `L²`-operator norm instance where a norm is needed, while the statements use the ambient
`NormedSpace.exp` so they connect directly to the CRUX A reduction.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, Lemma 6.4, eqs. (6.2.28)–(6.2.30), pp. 164–165.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **matrix-conjugation superoperator** `t ↦ exp(t • A) · Y · exp(−(t • A))` evaluated at the
real parameter `s`.  With `A = −i M` (anti-Hermitian) this is the unitary conjugation
`Û_t Y Û_t†` whose second-order Taylor remainder controls the symmetrised twist difference of
Lemma 6.4. -/
noncomputable def expConjOp (A Y : ManyBodyOpS Λ N) (s : ℝ) : ManyBodyOpS Λ N :=
  NormedSpace.exp (s • A) * Y * NormedSpace.exp (-(s • A))

/-- **Derivative of the conjugation superoperator**: `d/dt [exp(t•A) Y exp(−(t•A))]
= exp(t•A) ⁅A, Y⁆ exp(−(t•A)) = expConjOp A ⁅A, Y⁆ t`.  Product rule
(`HasDerivAt.mul`) applied to the two exponential factors (`hasDerivAt_exp_smul_const` and its
mirror), pushing `A` through `exp(−(t•A))` by commutativity.  Iterating this identity yields the
first and second derivatives `f'`, `f''` of `expConjOp A X`. -/
theorem hasDerivAt_expConjOp (A Y : ManyBodyOpS Λ N) (t : ℝ) :
    HasDerivAt (expConjOp A Y) (expConjOp A (A * Y - Y * A) t) t := by
  open scoped Matrix.Norms.L2Operator in
  have hu : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • A)) (NormedSpace.exp (t • A) * A) t :=
    hasDerivAt_exp_smul_const A t
  have hv : HasDerivAt (fun s : ℝ => NormedSpace.exp (-(s • A)))
      (NormedSpace.exp (-(t • A)) * (-A)) t := by
    have h := hasDerivAt_exp_smul_const (-A) t; simp only [smul_neg] at h; exact h
  have hc : NormedSpace.exp (-(t • A)) * A = A * NormedSpace.exp (-(t • A)) :=
    ((((Commute.refl A).smul_left t).neg_left).exp_left).eq
  refine ((hu.mul_const Y).mul hv).congr_deriv ?_
  simp only [expConjOp]
  rw [show NormedSpace.exp (-(t • A)) * -A = -(A * NormedSpace.exp (-(t • A))) from by
    rw [mul_neg, hc]]
  noncomm_ring

/-- **Unitary conjugation preserves the `L²` operator norm** for an anti-Hermitian generator
(`Aᴴ = −A`): `‖exp(t•A) Y exp(−(t•A))‖ = ‖Y‖`.  Since `A` is anti-Hermitian, `exp(t•A)` is unitary
with adjoint `exp(−(t•A))` (`exp_conjTranspose` + `exp_add_of_commute`); the claim then follows from
`manyBodyOperatorNormS_unitary_conj`.  Consumes the PR-2 unitary-conjugation norm invariance. -/
theorem manyBodyOperatorNormS_expConjOp (A Y : ManyBodyOpS Λ N)
    (hA : Matrix.conjTranspose A = -A) (t : ℝ) :
    manyBodyOperatorNormS (expConjOp A Y t) = manyBodyOperatorNormS Y := by
  have hadj : (NormedSpace.exp (t • A)).conjTranspose = NormedSpace.exp (-(t • A)) := by
    rw [← Matrix.exp_conjTranspose]
    congr 1
    rw [Matrix.conjTranspose_smul, star_trivial, hA]
    exact smul_neg t A
  have hunit : (NormedSpace.exp (t • A)).conjTranspose * NormedSpace.exp (t • A) = 1 := by
    rw [hadj, ← Matrix.exp_add_of_commute]
    · rw [neg_add_cancel, NormedSpace.exp_zero]
    · exact (Commute.refl (t • A)).neg_left
  have h := manyBodyOperatorNormS_unitary_conj (U := NormedSpace.exp (t • A)) (Y := Y) hunit
  rw [hadj] at h
  exact h

/-- **Commutator norm bound** `‖⁅A, Y⁆‖ ≤ 2‖A‖‖Y‖` for the `L²` operator norm: the subtraction
triangle inequality plus submultiplicativity in both orders. -/
theorem manyBodyOperatorNormS_comm_le (A Y : ManyBodyOpS Λ N) :
    manyBodyOperatorNormS (A * Y - Y * A)
      ≤ 2 * manyBodyOperatorNormS A * manyBodyOperatorNormS Y := by
  calc manyBodyOperatorNormS (A * Y - Y * A)
      ≤ manyBodyOperatorNormS (A * Y) + manyBodyOperatorNormS (Y * A) :=
        manyBodyOperatorNormS_sub_le _ _
    _ ≤ manyBodyOperatorNormS A * manyBodyOperatorNormS Y
          + manyBodyOperatorNormS Y * manyBodyOperatorNormS A :=
        add_le_add (manyBodyOperatorNormS_mul_le _ _) (manyBodyOperatorNormS_mul_le _ _)
    _ = 2 * manyBodyOperatorNormS A * manyBodyOperatorNormS Y := by ring

/-- **Second-order symmetric-difference twist bound** (Tasaki §6.2, Lemma 6.4, eqs. (6.2.28)–
(6.2.30), pp. 164–165).  For a Hermitian `M` and arbitrary `X`,
`‖ exp(+iM) X exp(−iM) + exp(−iM) X exp(+iM) − 2X ‖ ≤ 8 ‖M‖² ‖X‖`
in the `L²` operator norm `manyBodyOperatorNormS`.  This is CRUX B of the generalized
Lieb–Schultz–Mattis Lemma 6.4: composed with the CRUX A reduction (`twistConj_eq_localGen`) at
`M = M̂_x`, `X = ĥ_x`, and the generator bound `‖M̂_x‖ ≤ B/L`, summing `8(B/L)²h₀` over
the `L` sites yields the `C/L` variational bound.

The proof sets `A := −i M` (anti-Hermitian), so `exp(±iM)` are the unitary conjugators
`exp(∓(1•A))`; the symmetric difference is `F(1) − F(0)` for `F(t) := f(t) + f(−t)`,
`f := expConjOp A X`.  Two applications of the segment mean-value inequality to `F` and `F'`, using
`F'(0) = 0` and the norm-preserving bound `‖f''(t)‖ = ‖⁅A,⁅A,X⁆⁆‖ ≤ 4‖M‖²‖X‖`, give the `≤ 8‖M‖²‖X‖`
estimate. -/
theorem symmetricDifference_conj_norm_le (M X : ManyBodyOpS Λ N) (hM : M.IsHermitian) :
    manyBodyOperatorNormS
        (NormedSpace.exp (Complex.I • M) * X * NormedSpace.exp (-Complex.I • M)
          + NormedSpace.exp (-Complex.I • M) * X * NormedSpace.exp (Complex.I • M) - 2 • X)
      ≤ 8 * manyBodyOperatorNormS M ^ 2 * manyBodyOperatorNormS X := by
  open scoped Matrix.Norms.L2Operator in
  -- The anti-Hermitian generator `A = −i M`.
  set A : ManyBodyOpS Λ N := -Complex.I • M with hAdef
  have hAanti : Matrix.conjTranspose A = -A := by
    simp only [hAdef, Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_I, hM.eq, neg_smul]
  have hnegA : -A = Complex.I • M := by rw [hAdef]; module
  have hAM : manyBodyOperatorNormS A = manyBodyOperatorNormS M := by
    rw [hAdef, manyBodyOperatorNormS_smul, norm_neg, Complex.norm_I, one_mul]
  -- The single and double commutators.
  set C : ManyBodyOpS Λ N := A * X - X * A with hCdef
  set D : ManyBodyOpS Λ N := A * C - C * A with hDdef
  -- `‖D‖ = ‖⁅A,⁅A,X⁆⁆‖ ≤ 4‖M‖²‖X‖`.
  have hKle : manyBodyOperatorNormS D
      ≤ 4 * manyBodyOperatorNormS M ^ 2 * manyBodyOperatorNormS X := by
    have h1 := manyBodyOperatorNormS_comm_le A C
    have h2 := manyBodyOperatorNormS_comm_le A X
    calc manyBodyOperatorNormS D
        ≤ 2 * manyBodyOperatorNormS A * manyBodyOperatorNormS C := h1
      _ ≤ 2 * manyBodyOperatorNormS A
            * (2 * manyBodyOperatorNormS A * manyBodyOperatorNormS X) :=
          mul_le_mul_of_nonneg_left h2 (by
            have := manyBodyOperatorNormS_nonneg A; linarith)
      _ = 4 * manyBodyOperatorNormS A ^ 2 * manyBodyOperatorNormS X := by ring
      _ = 4 * manyBodyOperatorNormS M ^ 2 * manyBodyOperatorNormS X := by rw [hAM]
  -- The conjugation curve `f` and its symmetric combination `F`, with derivatives `F'`, `F''`.
  set f : ℝ → ManyBodyOpS Λ N := expConjOp A X with hf
  set F : ℝ → ManyBodyOpS Λ N := fun s => f s + f (-s) with hF
  set F' : ℝ → ManyBodyOpS Λ N := fun s => expConjOp A C s - expConjOp A C (-s) with hF'
  set F'' : ℝ → ManyBodyOpS Λ N := fun s => expConjOp A D s + expConjOp A D (-s) with hF''
  -- `HasDerivAt F F'` and `HasDerivAt F' F''`.
  have hderivF : ∀ s : ℝ, HasDerivAt F (F' s) s := by
    intro s
    have h1 : HasDerivAt f (expConjOp A C s) s := hasDerivAt_expConjOp A X s
    have h2 : HasDerivAt (fun s : ℝ => f (-s)) (-(expConjOp A C (-s))) s := by
      have hc := (hasDerivAt_expConjOp A X (-s)).scomp s (hasDerivAt_id s).neg
      simpa using hc
    simpa [hF, hF'] using h1.add h2
  have hderivF' : ∀ s : ℝ, HasDerivAt F' (F'' s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => expConjOp A C s) (expConjOp A D s) s :=
      hasDerivAt_expConjOp A C s
    have h2 : HasDerivAt (fun s : ℝ => expConjOp A C (-s)) (-(expConjOp A D (-s))) s := by
      have hc := (hasDerivAt_expConjOp A C (-s)).scomp s (hasDerivAt_id s).neg
      simpa using hc
    simpa [hF', hF''] using h1.sub h2
  -- Uniform bound `‖F''‖ ≤ 2‖D‖` on the derivative of `F'`.
  have hboundF'' : ∀ x : ℝ, ‖F'' x‖ ≤ 2 * manyBodyOperatorNormS D := by
    intro x
    rw [← manyBodyOperatorNormS_eq_l2]
    calc manyBodyOperatorNormS (F'' x)
        ≤ manyBodyOperatorNormS (expConjOp A D x) + manyBodyOperatorNormS (expConjOp A D (-x)) :=
          manyBodyOperatorNormS_add_le _ _
      _ = 2 * manyBodyOperatorNormS D := by
          rw [manyBodyOperatorNormS_expConjOp A D hAanti,
            manyBodyOperatorNormS_expConjOp A D hAanti]; ring
  -- MVT step 1: `‖F' x‖ ≤ 2‖D‖` on `[0,1]`, using `F' 0 = 0`.
  have hF'0 : F' 0 = 0 := by simp [hF']
  have hboundF' : ∀ x ∈ Set.Ico (0 : ℝ) 1, ‖F' x‖ ≤ 2 * manyBodyOperatorNormS D := by
    have hstep := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := F') (f' := F'') (C := 2 * manyBodyOperatorNormS D) (a := 0) (b := 1)
      (fun x _ => (hderivF' x).hasDerivWithinAt) (fun x _ => hboundF'' x)
    intro x hx
    have hxi : x ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hx
    have := hstep x hxi
    rw [hF'0, sub_zero, sub_zero] at this
    refine le_trans this ?_
    have hxle : x ≤ 1 := hx.2.le
    nlinarith [manyBodyOperatorNormS_nonneg D, hx.1, hxle]
  -- MVT step 2: `‖F 1 − F 0‖ ≤ 2‖D‖`.
  have hmain : ‖F 1 - F 0‖ ≤ 2 * manyBodyOperatorNormS D := by
    have hstep := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := F) (f' := F') (C := 2 * manyBodyOperatorNormS D) (a := 0) (b := 1)
      (fun x _ => (hderivF x).hasDerivWithinAt) hboundF'
    have := hstep 1 (Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩)
    simpa using this
  -- Identify `F 1 − F 0` with the target symmetric difference.
  have hF1 : F 1 = NormedSpace.exp A * X * NormedSpace.exp (-A)
      + NormedSpace.exp (-A) * X * NormedSpace.exp A := by
    simp only [hF, hf, expConjOp]
    rw [show (1 : ℝ) • A = A from one_smul ℝ A,
      show (-1 : ℝ) • A = -A from neg_one_smul ℝ A,
      show (- -A : ManyBodyOpS Λ N) = A from neg_neg A]
  have hF0 : F 0 = X + X := by
    simp only [hF, hf, expConjOp, neg_zero]
    rw [show (0 : ℝ) • A = 0 from zero_smul ℝ A, neg_zero, NormedSpace.exp_zero, one_mul, mul_one]
  have htarget : NormedSpace.exp (Complex.I • M) * X * NormedSpace.exp (-Complex.I • M)
        + NormedSpace.exp (-Complex.I • M) * X * NormedSpace.exp (Complex.I • M) - 2 • X
      = F 1 - F 0 := by
    rw [hF1, hF0, ← hnegA, ← hAdef, two_smul]
    abel
  rw [htarget]
  calc manyBodyOperatorNormS (F 1 - F 0)
      = ‖F 1 - F 0‖ := manyBodyOperatorNormS_eq_l2 _
    _ ≤ 2 * manyBodyOperatorNormS D := hmain
    _ ≤ 2 * (4 * manyBodyOperatorNormS M ^ 2 * manyBodyOperatorNormS X) :=
        mul_le_mul_of_nonneg_left hKle (by norm_num)
    _ = 8 * manyBodyOperatorNormS M ^ 2 * manyBodyOperatorNormS X := by ring

end LatticeSystem.Quantum
