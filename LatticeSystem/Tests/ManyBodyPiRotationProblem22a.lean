import LatticeSystem.Quantum.SpinS.ManyBodyPiRotation
import LatticeSystem.Quantum.Pauli

/-!
# Tests: Tasaki Problem 2.2.a many-body `π`-rotations

Pins the exact public names and signatures of the many-body
`π`-rotation layer that discharges Tasaki Problem 2.2.a (p. 23, `[solution → p. 496]`): the
`|Λ|`-fold product `Û_π^{(α)} = ∏_{x ∈ Λ} exp(−iπ Ŝ_x^{(α)})` of eq. (2.2.11) (p. 22), its master
sign identity descending from the single-site `π`-rotation anticommutation of eq. (2.1.25) (p. 18)
and the cyclic products of eq. (2.1.29) (p. 19), the commuting case (a), the anticommuting case
(b), and the eigenvector-orthogonality case (c).

* **R0** `spinSPiRotation2`: single-site convention pin at `N = 1` (`û₂ = −i σ^y`), catching a
  `û₃û₁` vs `û₁û₃` orientation slip and the book sign convention independently of the many-body
  layer.
* **R1** the master sign identity `Û^{(β)}Û^{(α)} = (−1)^{|Λ|N} Û^{(α)}Û^{(β)}`.
* **R2**/**R3** Problem 2.2.a (a)/(b): commutation for `Even (|Λ|·N)`, anticommutation for
  `Odd (|Λ|·N)`.
* **R4** unitarity of `Û_π^{(α)}`.
* **R5** Problem 2.2.a (c), the eigenvector-orthogonality capstone, `Φ ≠ 0` explicit.
* **R6** one-site (`Λ = Fin 1`, `N = 1`, `|Λ|N = 1` odd) positive control: an explicit eigenvector
  of `Û_π^{(3)}` (axis index `2`); its orthogonality to the `Û_π^{(1)}`-image (axis index `0`) is
  *computed* at the instance, and (c) is separately instantiated at the axis pair `(2, 1)`, so the
  capstone is proved non-vacuous and the conclusion is checked without going through it.
* **R7** two-site (`Λ = Fin 2`, `N = 1`, `|Λ|N = 2` even) positive control: the commuting instance
  for the same axis pair, the parity witness distinguishing (a) from (b).
* **R8** the family slot `spinSPiRotationAxis N 1 = û₂` at `N = 1`, pinned against its explicit
  `2 × 2` matrix — the slot the sign-invariant lemma statements cannot observe.
* **R9** two-site entries of `Û_π^{(3)}` at `N = 1`, pinning the tensor structure of the
  `|Λ|`-fold product at `|Λ| = 2` (both a diagonal sign and a vanishing off-diagonal entry).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.2, Problem 2.2.a, p. 23, `[solution → p. 496]`; eq. (2.2.11), p. 22; eq. (2.1.25), p. 18;
eq. (2.1.29), p. 19.
Refs #5379.
-/

namespace LatticeSystem.Tests

open LatticeSystem.Quantum

/-! ## R0: `spinSPiRotation2`, the axis-`2` single-site `π` rotation (eq. (2.1.29)) -/

/-- R0: convention pin at `S = 1/2` — `û₂ = û₃û₁ = −iσ^y`, mirroring the existing pins
`spinSPiRotation1 1 = (−i)σ^x` / `spinSPiRotation3 1 = (−i)σ^z` under the book sign convention
`e^{−iπŜ^{(α)}}`. -/
private lemma r0_spinSPiRotation2_spin_half :
    spinSPiRotation2 1 = (-Complex.I) • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotation2, spinSPiRotation1, spinSPiRotation3, spinReversalS, spinSAlternating,
      pauliY, Matrix.mul_apply, Fin.sum_univ_succ, Fin.rev]

/-! ## R1: master sign identity, Tasaki eq. (2.1.25), p. 18, lifted through eq. (2.2.11), p. 22 -/

/-- R1: locks the exact name/signature of the master sign identity
`Û^{(β)}Û^{(α)} = (−1)^{|Λ|N} Û^{(α)}Û^{(β)}` for `α ≠ β`. -/
private lemma r1_manyBodySPiRotation_swap_mul_of_ne
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} {α β : Fin 3} (h : α ≠ β) :
    manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α
      = ((-1 : ℂ) ^ (Fintype.card Λ * N)) •
          (manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β) :=
  manyBodySPiRotation_swap_mul_of_ne Λ N h

/-! ## R2: Tasaki Problem 2.2.a (a), `|Λ|S ∈ ℤ` -/

/-- R2: locks the exact name/signature of the commuting case. -/
private lemma r2_manyBodySPiRotation_commute_of_even
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (hc : Even (Fintype.card Λ * N))
    {α β : Fin 3} (h : α ≠ β) :
    manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β
      = manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α :=
  manyBodySPiRotation_commute_of_even Λ N hc h

/-! ## R3: Tasaki Problem 2.2.a (b), `|Λ|S ∈ ℤ + 1/2` -/

/-- R3: locks the exact name/signature of the anticommuting case. -/
private lemma r3_manyBodySPiRotation_anticommute_of_odd
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (hc : Odd (Fintype.card Λ * N))
    {α β : Fin 3} (h : α ≠ β) :
    manyBodySPiRotation Λ N α * manyBodySPiRotation Λ N β
      = -(manyBodySPiRotation Λ N β * manyBodySPiRotation Λ N α) :=
  manyBodySPiRotation_anticommute_of_odd Λ N hc h

/-! ## R4: unitarity of `Û_π^{(α)}` -/

/-- R4: locks the exact name/signature of many-body unitarity. -/
private lemma r4_manyBodySPiRotation_conjTranspose_mul_self
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (α : Fin 3) :
    (manyBodySPiRotation Λ N α).conjTranspose * manyBodySPiRotation Λ N α = 1 :=
  manyBodySPiRotation_conjTranspose_mul_self Λ N α

/-! ## R5: Tasaki Problem 2.2.a (c), eigenvector-orthogonality capstone -/

/-- R5: locks the exact name/signature of the capstone, with `Φ ≠ 0` an explicit hypothesis. -/
private lemma r5_tasaki_problem_2_2_a_eigenvector_orthogonal
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ} (hc : Odd (Fintype.card Λ * N))
    {α β : Fin 3} (h : α ≠ β) {Φ : (Λ → Fin (N + 1)) → ℂ} (hΦ : Φ ≠ 0) {lam : ℂ}
    (heig : (manyBodySPiRotation Λ N α).mulVec Φ = lam • Φ) :
    star Φ ⬝ᵥ (manyBodySPiRotation Λ N β).mulVec Φ = 0 :=
  tasaki_problem_2_2_a_eigenvector_orthogonal Λ N hc h hΦ heig

/-! ## R6: one-site positive control, `Λ = Fin 1`, `N = 1` (`|Λ|N = 1` odd) -/

/-- R6a: the anticommutation instance for axes `3` (index `2`) and `1` (index `0`) is genuinely
non-vacuous at one site. -/
private lemma r6a_one_site_anticommute :
    manyBodySPiRotation (Fin 1) 1 2 * manyBodySPiRotation (Fin 1) 1 0
      = -(manyBodySPiRotation (Fin 1) 1 0 * manyBodySPiRotation (Fin 1) 1 2) :=
  r3_manyBodySPiRotation_anticommute_of_odd (by decide) (by decide)

/-- The concrete one-site configuration-space vector `Φ := |0⟩`, used as an explicit eigenvector
of `Û_π^{(3)}`. -/
private def r6Phi : (Fin 1 → Fin 2) → ℂ :=
  fun σ => if σ = (fun _ => (0 : Fin 2)) then 1 else 0

/-- R6b: `r6Phi ≠ 0`, evaluated at the all-zero configuration. -/
private lemma r6b_r6Phi_ne_zero : r6Phi ≠ 0 := by
  intro hzero
  have hval := congrFun hzero (fun _ => (0 : Fin 2))
  simp [r6Phi] at hval

/-- R6c: `r6Phi` is an eigenvector of `Û_π^{(3)}` at one site, eigenvalue `−i`. -/
private lemma r6c_r6Phi_eigenvector :
    (manyBodySPiRotation (Fin 1) 1 2).mulVec r6Phi = (-Complex.I) • r6Phi := by
  have hop : manyBodySPiRotation (Fin 1) 1 2
      = manyBodyTensorS (fun _ : Fin 1 => spinSPiRotation3 1) := rfl
  have hsingle : r6Phi = Pi.single (fun _ => (0 : Fin 2)) (1 : ℂ) := by
    funext σ
    simp [r6Phi, Pi.single_apply]
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

/-- R6d: the (c) conclusion **computed** at the concrete one-site instance, independently of the
capstone: `Û_π^{(1)}` sends `|0⟩` to a multiple of `|1⟩`, whose overlap with `|0⟩` vanishes. -/
private lemma r6d_one_site_orthogonal :
    star r6Phi ⬝ᵥ (manyBodySPiRotation (Fin 1) 1 0).mulVec r6Phi = 0 := by
  have hop : manyBodySPiRotation (Fin 1) 1 0
      = manyBodyTensorS (fun _ : Fin 1 => spinSPiRotation1 1) := rfl
  have hsingle : r6Phi = Pi.single (fun _ => (0 : Fin 2)) (1 : ℂ) := by
    funext σ
    simp [r6Phi, Pi.single_apply]
  have hstar : star r6Phi = Pi.single (fun _ => (0 : Fin 2)) (1 : ℂ) := by
    funext σ
    by_cases hσ : σ = fun _ => (0 : Fin 2) <;> simp [r6Phi, Pi.single_apply, hσ]
  rw [hop, hstar, hsingle, Matrix.mulVec_single_one, single_one_dotProduct,
    Matrix.col_apply, manyBodyTensorS_apply]
  simp [spinSPiRotation1, spinReversalS_apply]

/-- R6e: the (c) capstone applied to the concrete one-site eigenvector, at the axis pair `(2, 1)`
— the control proving (c) is not vacuous, and the only place `spinSPiRotationAxis 1 1` enters the
many-body layer. -/
private lemma r6e_one_site_capstone_instance :
    star r6Phi ⬝ᵥ (manyBodySPiRotation (Fin 1) 1 1).mulVec r6Phi = 0 :=
  r5_tasaki_problem_2_2_a_eigenvector_orthogonal (by decide) (by decide) r6b_r6Phi_ne_zero
    r6c_r6Phi_eigenvector

/-! ## R7: two-site positive control, `Λ = Fin 2`, `N = 1` (`|Λ|N = 2` even) -/

/-- R7: the parity witness distinguishing (a) from (b) — the same axis pair commutes at two
sites. -/
private lemma r7_two_site_commute :
    manyBodySPiRotation (Fin 2) 1 2 * manyBodySPiRotation (Fin 2) 1 0
      = manyBodySPiRotation (Fin 2) 1 0 * manyBodySPiRotation (Fin 2) 1 2 :=
  r2_manyBodySPiRotation_commute_of_even (by decide) (by decide)

/-! ## R8: the axis-`2` slot of the family `û_α`, `N = 1` -/

/-- R8: the family slot `spinSPiRotationAxis 1 1` pinned against its explicit matrix
`û₂ = ((0, −1), (1, 0))` — the slot whose sign the axis-uniform lemma statements cannot see,
since every one of them carries exactly one `û₂` factor on each side. -/
private lemma r8_spinSPiRotationAxis_one_spin_half :
    spinSPiRotationAxis 1 1 = !![0, -1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [spinSPiRotationAxis, spinSPiRotation2, spinSPiRotation1, spinSPiRotation3,
      spinReversalS, spinSAlternating, Matrix.mul_apply, Fin.sum_univ_succ, Fin.rev]

/-! ## R9: two-site entries of `Û_π^{(3)}`, `N = 1` -/

/-- R9: the `|Λ| = 2` tensor structure of the global product, evaluated: the diagonal entry at the
aligned configuration is `(−i)² = −1`, at the anti-aligned configuration `(−i)(i) = 1`, and an
entry between configurations that differ at a site vanishes. -/
private lemma r9_two_site_axis3_values :
    manyBodySPiRotation (Fin 2) 1 2 ![0, 0] ![0, 0] = -1 ∧
      manyBodySPiRotation (Fin 2) 1 2 ![0, 1] ![0, 1] = 1 ∧
        manyBodySPiRotation (Fin 2) 1 2 ![0, 1] ![1, 1] = 0 := by
  have hop : manyBodySPiRotation (Fin 2) 1 2
      = manyBodyTensorS (fun _ : Fin 2 => spinSPiRotation3 1) := rfl
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [hop, manyBodyTensorS_apply, Fin.prod_univ_two, spinSPiRotation3, spinSAlternating,
      Matrix.diagonal_apply]

end LatticeSystem.Tests
