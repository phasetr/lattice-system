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
  of `Û_π^{(3)}` (axis index `2`) and its orthogonality to the `Û_π^{(1)}`-image (axis index `0`),
  proving (c) is not vacuously satisfied.
* **R7** two-site (`Λ = Fin 2`, `N = 1`, `|Λ|N = 2` even) positive control: the commuting instance
  for the same axis pair, the parity witness distinguishing (a) from (b).

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

/-! ## R1: master sign identity, Tasaki eq. (2.2.11) lifted through eq. (2.1.25)/(2.1.29) -/

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
      = (Finset.univ : Finset (Fin 1)).noncommProd
          (fun x => onSiteS x (spinSPiRotation3 1))
          (fun _ _ _ _ hxy => onSiteS_mul_onSiteS_of_ne hxy _ _) := rfl
  have hsite : manyBodySPiRotation (Fin 1) 1 2 = onSiteS (0 : Fin 1) (spinSPiRotation3 1) := by
    rw [hop, Finset.noncommProd_eq_pow_card _ _ _ (onSiteS (0 : Fin 1) (spinSPiRotation3 1))
      (fun a _ => by rw [Subsingleton.elim a (0 : Fin 1)])]
    simp
  have hsingle : r6Phi = Pi.single (fun _ => (0 : Fin 2)) (1 : ℂ) := by
    funext σ
    simp [r6Phi, Pi.single_apply]
  have hcond : ∀ σ : Fin 1 → Fin 2, ∀ k : Fin 1, k ≠ 0 → σ k = (fun _ => (0 : Fin 2)) k :=
    fun _ k hk => absurd (Subsingleton.elim k 0) hk
  rw [hsite, hsingle, Matrix.mulVec_single_one]
  funext σ
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, onSiteS_apply,
    if_pos (hcond σ), spinSPiRotation3, Matrix.smul_apply, spinSAlternating, pow_one]
  by_cases hσ : σ = (fun _ => (0 : Fin 2))
  · subst hσ
    simp
  · have h0 : σ 0 ≠ 0 := fun h => hσ (funext fun k => by rw [Subsingleton.elim k 0]; exact h)
    rw [Matrix.diagonal_apply_ne _ h0, if_neg hσ]

/-- R6d: the (c) capstone applied to the concrete one-site eigenvector — the control proving (c)
is not vacuous. -/
private lemma r6d_one_site_orthogonal :
    star r6Phi ⬝ᵥ (manyBodySPiRotation (Fin 1) 1 0).mulVec r6Phi = 0 :=
  r5_tasaki_problem_2_2_a_eigenvector_orthogonal (by decide) (by decide) r6b_r6Phi_ne_zero
    r6c_r6Phi_eigenvector

/-! ## R7: two-site positive control, `Λ = Fin 2`, `N = 1` (`|Λ|N = 2` even) -/

/-- R7: the parity witness distinguishing (a) from (b) — the same axis pair commutes at two
sites. -/
private lemma r7_two_site_commute :
    manyBodySPiRotation (Fin 2) 1 2 * manyBodySPiRotation (Fin 2) 1 0
      = manyBodySPiRotation (Fin 2) 1 0 * manyBodySPiRotation (Fin 2) 1 2 :=
  r2_manyBodySPiRotation_commute_of_even (by decide) (by decide)

end LatticeSystem.Tests
