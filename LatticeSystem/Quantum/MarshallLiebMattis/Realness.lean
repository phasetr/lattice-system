/-
Copyright (c) 2026 lattice-system contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LatticeSystem.Quantum.MarshallDressedBasis
import LatticeSystem.Quantum.SpinDot

/-!
# Realness of the dressed Heisenberg matrix elements
(Tasaki §2.5, p. 41, "Property (i)" in the proof of Theorem 2.2)

The first of three properties needed in Tasaki's
Perron–Frobenius proof of the Marshall–Lieb–Mattis theorem
(Theorem 2.2, §2.5 p. 39) is

  **(i)** $\langle \widetilde{\Psi}^\sigma | \hat H |
              \widetilde{\Psi}^{\sigma'}\rangle \in \mathbb{R}$

for the antiferromagnetic Heisenberg Hamiltonian $\hat H = \sum_{x,y}
J_{x,y}\,\hat S_x\cdot\hat S_y$ with **real** coupling $J : V\times V
\to \mathbb{R}$ (formalised here as `(J x y).im = 0` for all `x, y`).

The proof factors through three layers:

* `spinHalfDot_apply_im_eq_zero` — every matrix entry of the two-site
  spin product `Ŝ_x · Ŝ_y` is real (independent of any bipartite
  structure).
* `heisenbergHamiltonian_apply_im_eq_zero` — for real `J`, every
  matrix entry of `H = Σ_{x,y} J(x,y) · spinHalfDot x y` is real
  (`ℝ`-linearity of `Complex.im` together with the previous lemma).
* `marshallSignOf_im_eq_zero` — the Marshall sign
  `marshallSignOf A σ` is real (each factor is `±1 ∈ ℝ`).
* `dot_marshallDressed_heisenbergHamiltonian_marshallDressed_im_eq_zero`
  — the bilinear pairing
  `Σ_τ |Ψ̃^σ⟩ τ · (H · |Ψ̃^σ'⟩) τ` is real for real `J`.

References:

- H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
  Springer 2020, §2.5, p. 41 (Property (i) in the proof of
  Theorem 2.2).
- W. Marshall (1955); E.H. Lieb, D. Mattis (1962).
-/

namespace LatticeSystem.Quantum

open Matrix Complex

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Realness of the two-site spin-spin matrix entries -/

/-- Bridge from a matrix entry to the application of `mulVec` on the
unit basis vector at the column index:
`M σ σ' = (M.mulVec (basisVec σ')) σ`.

Proof: expand `Matrix.mulVec` (= `dotProduct`) and apply
`sum_mul_basisVec`. -/
private theorem matrix_apply_eq_mulVec_basisVec
    (M : ManyBodyOp Λ) (σ σ' : Λ → Fin 2) :
    M σ σ' = M.mulVec (basisVec σ') σ := by
  change M σ σ' = dotProduct (fun j => M σ j) (basisVec σ')
  unfold dotProduct
  rw [sum_mul_basisVec σ' (M σ)]

/-- Every matrix entry of the two-site spin product
`Ŝ_x · Ŝ_y` is **real**:
`((spinHalfDot x y) σ σ').im = 0`.

Proof by case analysis:

* `x = y`: `spinHalfDot x x = (3/4) • 1`, so the entry is
  `(3/4)` if `σ = σ'` and `0` otherwise — real.
* `x ≠ y`, `σ' x = σ' y`: action gives `(1/4) basisVec σ'`, so the
  entry is `1/4` if `σ = σ'` and `0` otherwise — real.
* `x ≠ y`, `σ' x ≠ σ' y`: action gives `(1/2) basisVec (swap σ') -
  (1/4) basisVec σ'`, so the entry takes values in `{1/2, -1/4, 0}`
  — real. -/
theorem spinHalfDot_apply_im_eq_zero (x y : Λ) (σ σ' : Λ → Fin 2) :
    ((spinHalfDot x y) σ σ').im = 0 := by
  rw [matrix_apply_eq_mulVec_basisVec (spinHalfDot x y) σ σ']
  by_cases hxy : x = y
  · subst hxy
    rw [spinHalfDot_self, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [Pi.smul_apply, smul_eq_mul, basisVec_apply]
    split_ifs <;> simp
  · by_cases hpar : σ' x = σ' y
    · rw [spinHalfDot_mulVec_basisVec_parallel hxy σ' hpar]
      simp only [Pi.smul_apply, smul_eq_mul, basisVec_apply]
      split_ifs <;> simp
    · rw [spinHalfDot_mulVec_basisVec_antiparallel hxy σ' hpar]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, basisVec_apply,
        Complex.sub_im, Complex.mul_im]
      split_ifs <;> simp

/-! ## Realness of Heisenberg-Hamiltonian matrix entries (real `J`) -/

/-- For a **real** coupling `J : Λ → Λ → ℂ` (i.e. `(J x y).im = 0`),
every matrix entry of the Heisenberg Hamiltonian
`H = Σ_{x,y} J(x,y) · spinHalfDot x y` is real:
`((heisenbergHamiltonian J) σ σ').im = 0`.

Proof: by `ℝ`-linearity of `Complex.im` and
`spinHalfDot_apply_im_eq_zero`, each summand
`(J(x,y) · (spinHalfDot x y) σ σ').im` vanishes — the product of a
real and a real is real. -/
theorem heisenbergHamiltonian_apply_im_eq_zero
    {J : Λ → Λ → ℂ} (hJ : ∀ x y, (J x y).im = 0)
    (σ σ' : Λ → Fin 2) :
    ((heisenbergHamiltonian J) σ σ').im = 0 := by
  -- Step 1: rewrite the matrix entry as a double sum of products.
  have hdecomp : (heisenbergHamiltonian J) σ σ' =
      ∑ x : Λ, ∑ y : Λ, J x y * (spinHalfDot x y) σ σ' := by
    unfold heisenbergHamiltonian
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.sum_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul]
  rw [hdecomp, Complex.im_sum]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [Complex.im_sum]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [Complex.mul_im, hJ x y, spinHalfDot_apply_im_eq_zero, zero_mul,
    mul_zero, add_zero]

/-! ## Realness of the Marshall sign -/

/-- The Marshall sign `marshallSignOf A σ` is **real**:
`(marshallSignOf A σ).im = 0`.

Each factor of the product is either `1` (if `A x = false`) or
`(-1 : ℂ)^(σ x : ℕ)` (if `A x = true`); both are real, and
products of reals are real. -/
theorem marshallSignOf_im_eq_zero {V : Type*} [Fintype V]
    (A : V → Bool) (σ : V → Fin 2) :
    (marshallSignOf A σ).im = 0 := by
  unfold marshallSignOf
  -- Each factor has zero imaginary part; products preserve this.
  refine Finset.prod_induction _ (fun z : ℂ => z.im = 0) ?_ ?_ ?_
  · -- closed under multiplication: (a * b).im = a.re * b.im + a.im * b.re
    intro a b ha hb
    rw [Complex.mul_im, ha, hb]; ring
  · -- 1 has zero imaginary part
    simp
  · -- each factor is real
    intro x _
    by_cases hA : A x = true
    · rw [if_pos hA]
      have hk : (σ x : ℕ) = 0 ∨ (σ x : ℕ) = 1 := by
        rcases (σ x) with ⟨k, hk⟩
        omega
      rcases hk with h | h
      · rw [h]; simp
      · rw [h]; simp
    · rw [if_neg hA]; simp

/-! ## Realness of the dressed bilinear form -/

/-- Push the Marshall sign factors out of `marshallDressedBasis` in
the bilinear pairing:
`Σ_τ marshallDressedBasis A σ τ · w τ
   = marshallSignOf A σ · Σ_τ basisVec σ τ · w τ`. -/
private theorem sum_marshallDressed_mul
    {V : Type*} [Fintype V] [DecidableEq V] (A : V → Bool)
    (σ : V → Fin 2) (w : (V → Fin 2) → ℂ) :
    ∑ τ : V → Fin 2, marshallDressedBasis A σ τ * w τ =
      marshallSignOf A σ * ∑ τ : V → Fin 2, basisVec σ τ * w τ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [marshallDressedBasis_apply, mul_assoc]

/-- The bilinear pairing
`Σ_τ |Ψ̃^σ⟩ τ · (H · |Ψ̃^{σ'}⟩) τ` is **real** for the spin-1/2
antiferromagnetic Heisenberg Hamiltonian with real coupling
`J : Λ → Λ → ℂ` (Tasaki §2.5, p. 41, Property (i)).

Strategy:

1. Pull out `marshallSignOf A σ` from the left dressed basis
   (`sum_marshallDressed_mul`).
2. Push `H` through the right Marshall scalar:
   `H · (marshallSignOf A σ' • basisVec σ') = marshallSignOf A σ' •
   (H · basisVec σ')` by `Matrix.mulVec_smul`.
3. Pull out `marshallSignOf A σ'` from the inner sum, leaving the
   plain matrix entry `(H σ σ')` from `sum_mul_basisVec`.
4. Conclude using realness of `marshallSignOf` and matrix entry.
-/
theorem dot_marshallDressed_heisenbergHamiltonian_marshallDressed_im_eq_zero
    (A : Λ → Bool) {J : Λ → Λ → ℂ} (hJ : ∀ x y, (J x y).im = 0)
    (σ σ' : Λ → Fin 2) :
    (∑ τ : Λ → Fin 2,
        marshallDressedBasis A σ τ *
          ((heisenbergHamiltonian J).mulVec (marshallDressedBasis A σ')) τ).im
      = 0 := by
  -- Step 1: pull out the left Marshall sign.
  rw [sum_marshallDressed_mul]
  -- Step 2 + 3: push H through and reduce inner sum to matrix entry.
  have hpush : (∑ τ : Λ → Fin 2,
        basisVec σ τ * ((heisenbergHamiltonian J).mulVec
          (marshallDressedBasis A σ')) τ) =
      marshallSignOf A σ' * (heisenbergHamiltonian J) σ σ' := by
    -- mulVec is linear in its argument: H · (s • b) = s • (H · b).
    have h1 : (heisenbergHamiltonian J).mulVec (marshallDressedBasis A σ') =
        marshallSignOf A σ' • (heisenbergHamiltonian J).mulVec (basisVec σ') := by
      unfold marshallDressedBasis
      rw [Matrix.mulVec_smul]
    rw [h1]
    -- Σ_τ b σ τ · (s • Hv) τ = s · Σ_τ b σ τ · Hv τ = s · (Hv σ).
    rw [show (∑ τ : Λ → Fin 2,
          basisVec σ τ * (marshallSignOf A σ' •
            (heisenbergHamiltonian J).mulVec (basisVec σ')) τ) =
        marshallSignOf A σ' *
          ∑ τ : Λ → Fin 2, basisVec σ τ *
            ((heisenbergHamiltonian J).mulVec (basisVec σ')) τ from ?_,
        basisVec_sum_mul σ ((heisenbergHamiltonian J).mulVec (basisVec σ')),
        ← matrix_apply_eq_mulVec_basisVec]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (basisVec σ τ) _,
      mul_assoc]
  rw [hpush, ← mul_assoc]
  -- Step 4: marshallSignOf σ * marshallSignOf σ' * H σ σ' has zero imag.
  -- All three factors are real (im = 0), and products of reals are real.
  simp only [Complex.mul_im, marshallSignOf_im_eq_zero,
    heisenbergHamiltonian_apply_im_eq_zero hJ,
    zero_mul, mul_zero, add_zero]

end LatticeSystem.Quantum
