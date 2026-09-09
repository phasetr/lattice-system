import LatticeSystem.Quantum.SpinS.ManyBodyPiRotationExp
import LatticeSystem.Quantum.SpinS.TotalSpin
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Signature pin: PR-D of the Problem 2.1.g exponential-identification arc, many-body lift

Repository-internal regression guard for PR-D, the many-body lift of Tasaki
**eq. (2.2.11), p. 22** (`Û_θ^{(α)} := exp[−iθ Ŝ_tot^{(α)}] = ∏_{x∈Λ} exp[−iθ Ŝ_x^{(α)}]`),
which completes the identification of the closed-form global `π` rotation
`manyBodySPiRotation` (`Quantum/SpinS/ManyBodyPiRotation.lean`) with the book's operator
exponential, and restates **Tasaki Problem 2.2.a, p. 23** (`[solution → p. 496]`) in that
exponential notation. PR-D rests on the single-site identification of every axis already proved
on `main` (`spinSPiRotationAxis_eq_exp`, Tasaki **eq. (2.1.34), p. 20**, Problem 2.1.g p. 20).

Pinned (all new PR-D identifiers):
* `onSiteS_exp` — the site embedding commutes with the matrix exponential,
  `onSiteS i (exp A) = exp (onSiteS i A)`.
* `manyBodyTensorS_eq_noncommProd` — a many-body tensor of site operators is the (noncommutative)
  product of their site embeddings over `Finset.univ`.
* `manyBodyTensorS_const_exp` — the many-body tensor of a uniform exponential is the exponential
  of the sum of site embeddings, `⊗_x exp(A) = exp(Σ_x onSiteS x A)` (the crux of eq. (2.2.11)).
* `sum_onSiteS_smul` — scalars pull out of a sum of site embeddings.
* `manyBodySPiRotation_eq_exp` — **the capstone**: `manyBodySPiRotation Λ N α =
  exp(−iπ Ŝ_tot^{(α)})`, uniform in the axis `α : Fin 3`, Tasaki eq. (2.2.11), p. 22.
* `manyBodySPiRotationExp_commute_of_even` / `manyBodySPiRotationExp_anticommute_of_odd` /
  `tasaki_problem_2_2_a_exp_eigenvector_orthogonal` — Problem 2.2.a (a)/(b)/(c) restated with both
  global rotations replaced by their operator exponentials.

Also pinned: axis-by-axis entries of the capstone at `|Λ| = 1`, `N = 1` (must agree with the
already-proved single-site closed forms `spinSPiRotation1/2/3` on `main`); a parity pin at
`|Λ| = 2`, `N = 1` (even, commuting) and at `|Λ| = 1`, `N = 1` (odd, anticommuting +
eigenvector-orthogonality, with an explicit nonzero eigenvector); a `(−i)^{|Λ|N}` phase control at
`|Λ| = 2`, `N = 1`; and a non-identity control ruling out the degenerate "both sides collapse to
`1`" reading of the capstone.

Every entry/parity pin below is a two-part `∧`/independent-argument statement so that a failure on
a not-yet-existing PR-D identifier never masks or is masked by an unrelated tactic failure: each
conjunct/argument depends on at most one new identifier, and the concrete-value conjunct uses only
declarations already on `main`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), eq. (2.1.34) p. 20, Problem 2.1.g p. 20 (solution p. 495), eq. (2.2.11) p. 22, Problem 2.2.a
p. 23 (solution p. 496).
Refs #5455.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## Generic block: site embedding vs. the matrix exponential -/

/-- Signature pin: the site embedding `onSiteS i` commutes with the matrix exponential. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (i : Λ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    onSiteS i (NormedSpace.exp A) = NormedSpace.exp (onSiteS i A) :=
  onSiteS_exp i A

/-- Signature pin: a many-body tensor of site operators is the `Finset.univ.noncommProd` of their
site embeddings. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (W : Λ → Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (comm : (↑(Finset.univ : Finset Λ) : Set Λ).Pairwise
      (fun x y => Commute (onSiteS x (W x) : ManyBodyOpS Λ N) (onSiteS y (W y)))) :
    manyBodyTensorS W = Finset.univ.noncommProd (fun x => onSiteS x (W x)) comm :=
  manyBodyTensorS_eq_noncommProd W comm

/-- Signature pin: the many-body tensor of a uniform exponential is the exponential of the sum of
site embeddings — the crux computation of eq. (2.2.11), p. 22. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    manyBodyTensorS (fun _ : Λ => NormedSpace.exp A) =
      NormedSpace.exp (∑ x : Λ, onSiteS x A) :=
  manyBodyTensorS_const_exp A

/-- Signature pin: scalars pull out of a sum of site embeddings. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (c : ℂ)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (∑ x : Λ, onSiteS x (c • A) : ManyBodyOpS Λ N) = c • ∑ x : Λ, onSiteS x A :=
  sum_onSiteS_smul c A

/-! ## Capstone: Tasaki eq. (2.2.11), p. 22 -/

/-- Signature pin: locks the exact name/signature of the capstone, uniform in the axis
`α : Fin 3`, Tasaki eq. (2.2.11), p. 22. -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (N : ℕ) (α : Fin 3) :
    manyBodySPiRotation Λ N α =
      NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 Λ N, totalSpinSOp2 Λ N, totalSpinSOp3 Λ N] α)) :=
  manyBodySPiRotation_eq_exp Λ N α

/-! ## Axis-by-axis entry pins, `|Λ| = 1`, `N = 1`

Each pin is `capstone-at-this-axis ∧ concrete-entry-value`, split by `constructor` so the first
(new-identifier) conjunct and the second (already-`main`) conjunct are checked independently. -/

/-- Axis-`1` (`α = 0`): the capstone at this instance, and the off-diagonal entry
`spinSPiRotation1 1 0 1 = −i` it must match once combined. -/
example :
    manyBodySPiRotation (Fin 1) 1 0 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • totalSpinSOp1 (Fin 1) 1)
      ∧ manyBodySPiRotation (Fin 1) 1 0 (![0] : Fin 1 → Fin 2) (![1] : Fin 1 → Fin 2)
          = -Complex.I := by
  constructor
  · have h := manyBodySPiRotation_eq_exp (Fin 1) 1 0
    simpa using h
  · simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, spinSPiRotation1,
      spinReversalS_apply]

/-- Axis-`1` (`α = 0`) diagonal entry: `spinSPiRotation1 1 0 0 = 0`. -/
example :
    manyBodySPiRotation (Fin 1) 1 0 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • totalSpinSOp1 (Fin 1) 1)
      ∧ manyBodySPiRotation (Fin 1) 1 0 (![0] : Fin 1 → Fin 2) (![0] : Fin 1 → Fin 2) = 0 := by
  constructor
  · have h := manyBodySPiRotation_eq_exp (Fin 1) 1 0
    simpa using h
  · simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, spinSPiRotation1,
      spinReversalS_apply]

/-- Axis-`3` (`α = 2`) diagonal entry: `spinSPiRotation3 1 0 0 = −i`. -/
example :
    manyBodySPiRotation (Fin 1) 1 2 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • totalSpinSOp3 (Fin 1) 1)
      ∧ manyBodySPiRotation (Fin 1) 1 2 (![0] : Fin 1 → Fin 2) (![0] : Fin 1 → Fin 2)
          = -Complex.I := by
  constructor
  · have h := manyBodySPiRotation_eq_exp (Fin 1) 1 2
    simpa using h
  · simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, spinSPiRotation3,
      spinSAlternating]

/-- Axis-`3` (`α = 2`) off-diagonal entry: `spinSPiRotation3 1 0 1 = 0`. -/
example :
    manyBodySPiRotation (Fin 1) 1 2 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • totalSpinSOp3 (Fin 1) 1)
      ∧ manyBodySPiRotation (Fin 1) 1 2 (![0] : Fin 1 → Fin 2) (![1] : Fin 1 → Fin 2) = 0 := by
  constructor
  · have h := manyBodySPiRotation_eq_exp (Fin 1) 1 2
    simpa using h
  · simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, spinSPiRotation3,
      spinSAlternating]

/-- Axis-`2` (`α = 1`) entry: `spinSPiRotation2 1 0 1 = −1`, the sign-sensitive off-diagonal of
`û₂ = û₃û₁`. -/
example :
    manyBodySPiRotation (Fin 1) 1 1 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • totalSpinSOp2 (Fin 1) 1)
      ∧ manyBodySPiRotation (Fin 1) 1 1 (![0] : Fin 1 → Fin 2) (![1] : Fin 1 → Fin 2)
          = -1 := by
  constructor
  · have h := manyBodySPiRotation_eq_exp (Fin 1) 1 1
    simpa using h
  · simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, spinSPiRotation2,
      spinSPiRotation3, spinSPiRotation1, spinSAlternating, spinReversalS_apply,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Axis-`2` (`α = 1`) entry, the other off-diagonal: `spinSPiRotation2 1 1 0 = 1`. -/
example :
    manyBodySPiRotation (Fin 1) 1 1 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • totalSpinSOp2 (Fin 1) 1)
      ∧ manyBodySPiRotation (Fin 1) 1 1 (![1] : Fin 1 → Fin 2) (![0] : Fin 1 → Fin 2)
          = 1 := by
  constructor
  · have h := manyBodySPiRotation_eq_exp (Fin 1) 1 1
    simpa using h
  · simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, spinSPiRotation2,
      spinSPiRotation3, spinSPiRotation1, spinSAlternating, spinReversalS_apply,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-! ## Parity pins: Problem 2.2.a in the exponential notation -/

/-- Even-parity pin at `|Λ| = 2`, `N = 1` (`|Λ|N = 2` even): the two exponential global rotations
about distinct axes commute — Problem 2.2.a (a), consuming
`manyBodySPiRotationExp_commute_of_even` directly. -/
example :
    NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 (Fin 2) 1, totalSpinSOp2 (Fin 2) 1, totalSpinSOp3 (Fin 2) 1] 2)) *
      NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 (Fin 2) 1, totalSpinSOp2 (Fin 2) 1, totalSpinSOp3 (Fin 2) 1] 0)) =
      NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 (Fin 2) 1, totalSpinSOp2 (Fin 2) 1, totalSpinSOp3 (Fin 2) 1] 0)) *
      NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 (Fin 2) 1, totalSpinSOp2 (Fin 2) 1, totalSpinSOp3 (Fin 2) 1] 2)) :=
  manyBodySPiRotationExp_commute_of_even (Λ := Fin 2) (N := 1) (by decide) (by decide)

/-- Odd-parity pin at `|Λ| = 1`, `N = 1` (`|Λ|N = 1` odd): the two exponential global rotations
about distinct axes anticommute — Problem 2.2.a (b), consuming
`manyBodySPiRotationExp_anticommute_of_odd` directly. -/
example :
    NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 (Fin 1) 1, totalSpinSOp2 (Fin 1) 1, totalSpinSOp3 (Fin 1) 1] 2)) *
      NormedSpace.exp
        (-(((Real.pi : ℂ) * Complex.I)) •
          (![totalSpinSOp1 (Fin 1) 1, totalSpinSOp2 (Fin 1) 1, totalSpinSOp3 (Fin 1) 1] 0)) =
      -(NormedSpace.exp
          (-(((Real.pi : ℂ) * Complex.I)) •
            (![totalSpinSOp1 (Fin 1) 1, totalSpinSOp2 (Fin 1) 1, totalSpinSOp3 (Fin 1) 1] 0)) *
        NormedSpace.exp
          (-(((Real.pi : ℂ) * Complex.I)) •
            (![totalSpinSOp1 (Fin 1) 1, totalSpinSOp2 (Fin 1) 1, totalSpinSOp3 (Fin 1) 1] 2))) :=
  manyBodySPiRotationExp_anticommute_of_odd (Λ := Fin 1) (N := 1) (by decide) (by decide)

/-- The concrete one-site configuration-space vector `|0⟩`, used below as an explicit nonzero
eigenvector of the axis-`3` (diagonal) exponential rotation, so the eigenvector-orthogonality
capstone below is exercised non-vacuously. -/
private noncomputable def expBridgeOneSitePhi : (Fin 1 → Fin 2) → ℂ :=
  fun σ => if σ = (fun _ => (0 : Fin 2)) then 1 else 0

/-- `expBridgeOneSitePhi ≠ 0`, at `main` declarations only. -/
private lemma expBridgeOneSitePhi_ne_zero : expBridgeOneSitePhi ≠ 0 := by
  intro hzero
  have hval := congrFun hzero (fun _ => (0 : Fin 2))
  simp [expBridgeOneSitePhi] at hval

/-- `expBridgeOneSitePhi` is an eigenvector, eigenvalue `−i`, of the axis-`3` global rotation in
its `main` closed form; combined below with `manyBodySPiRotation_eq_exp` to instantiate the
exponential-side eigenvector hypothesis of the capstone. -/
private lemma expBridgeOneSitePhi_eigenvector_closedForm :
    Matrix.mulVec (manyBodySPiRotation (Fin 1) 1 2) expBridgeOneSitePhi
      = (-Complex.I) • expBridgeOneSitePhi := by
  have hop : manyBodySPiRotation (Fin 1) 1 2
      = manyBodyTensorS (fun _ : Fin 1 => spinSPiRotation3 1) := rfl
  have hsingle : expBridgeOneSitePhi = Pi.single (fun _ => (0 : Fin 2)) (1 : ℂ) := by
    funext σ
    simp [expBridgeOneSitePhi, Pi.single_apply]
  rw [hop, hsingle, Matrix.mulVec_single_one]
  funext σ
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
    manyBodyTensorS_apply, Fin.prod_univ_one, spinSPiRotation3, Matrix.smul_apply,
    spinSAlternating, pow_one]
  by_cases hσ : σ = (fun _ => (0 : Fin 2))
  · subst hσ
    simp
  · have h0 : σ 0 ≠ 0 := fun h => hσ (funext fun k => by rw [Subsingleton.elim k 0]; exact h)
    rw [Matrix.diagonal_apply_ne _ h0, if_neg hσ]

/-- Odd-parity pin at `|Λ| = 1`, `N = 1`, for Problem 2.2.a (c): the exponential eigenvector
`expBridgeOneSitePhi` of `Û_π^{(3)}` is orthogonal to `Û_π^{(1)}` applied to it — consuming
`tasaki_problem_2_2_a_exp_eigenvector_orthogonal` directly, applied to a non-vacuous, explicit
`Φ ≠ 0` and an eigenvector hypothesis carried from the closed form by
`manyBodySPiRotation_eq_exp` via `▸` (a single term, so the two new-identifier occurrences fail
independently and no unrelated tactic can mask or be masked by either). -/
example :
    star expBridgeOneSitePhi ⬝ᵥ
        Matrix.mulVec
          (NormedSpace.exp
            (-(((Real.pi : ℂ) * Complex.I)) •
              (![totalSpinSOp1 (Fin 1) 1, totalSpinSOp2 (Fin 1) 1, totalSpinSOp3 (Fin 1) 1] 0)))
          expBridgeOneSitePhi = 0 :=
  tasaki_problem_2_2_a_exp_eigenvector_orthogonal (Λ := Fin 1) (N := 1) (by decide)
    (α := 2) (β := 0) (by decide) expBridgeOneSitePhi_ne_zero
    ((manyBodySPiRotation_eq_exp (Fin 1) 1 2) ▸ expBridgeOneSitePhi_eigenvector_closedForm)

/-! ## Phase and non-identity controls, `|Λ| = 2`, `N = 1` -/

/-- `(−i)^{|Λ|N}` phase control: the diagonal entry of the axis-`3` exponential rotation at two
sites is `(−i)^2 = −1`, not the single-site phase `−i` — the entry a lift that dropped the
`|Λ|`-fold site product (or returned the single-site factor, or `1`) would fail. -/
example :
    manyBodySPiRotation (Fin 2) 1 2 =
        NormedSpace.exp (-(((Real.pi : ℂ) * Complex.I)) • totalSpinSOp3 (Fin 2) 1)
      ∧ manyBodySPiRotation (Fin 2) 1 2
          (![0, 0] : Fin 2 → Fin 2) (![0, 0] : Fin 2 → Fin 2) = -1 := by
  constructor
  · have h := manyBodySPiRotation_eq_exp (Fin 2) 1 2
    simpa using h
  · simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, spinSPiRotation3,
      spinSAlternating, Fin.prod_univ_two]

/-- Non-identity control: the closed-form axis-`3` global rotation at two sites is not the
identity, so the capstone above cannot be discharged by a degenerate proof in which both sides
collapse to `1`. No new identifier is used here — the fact holds already on `main`. -/
example : manyBodySPiRotation (Fin 2) 1 2 ≠ (1 : ManyBodyOpS (Fin 2) 1) := by
  intro h
  have h00 :=
    congrFun (congrFun h (![0, 0] : Fin 2 → Fin 2)) (![0, 0] : Fin 2 → Fin 2)
  simp [manyBodySPiRotation, manyBodyTensorS_apply, spinSPiRotationAxis, Fin.prod_univ_two,
    spinSPiRotation3, spinSAlternating] at h00
  norm_num [Matrix.one_apply] at h00

end LatticeSystem.Quantum
