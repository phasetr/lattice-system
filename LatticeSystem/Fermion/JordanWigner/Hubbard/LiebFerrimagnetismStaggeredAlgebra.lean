import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetism
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHermitian
import LatticeSystem.Math.MatrixAnalysis.HermitianSum

/-!
# §10.2.3 (Theorem 10.6): the staggered spin-component algebra

Operator-algebra layer of Tasaki's Theorem 10.6 (Shen–Qiu–Tian ferrimagnetism) for the
Hubbard / Jordan–Wigner fermions.  Writing `ε_x = +1` on the sublattice `A` and `ε_x = −1` on
`B = Aᶜ` (`gaugeSign`), the squared staggered order parameter of eq. (10.2.16),

  `(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y`   (`fermionStaggeredCasimirOp`),

splits into a transverse `(1,2)`-component double sum and the square of the longitudinal
staggered operator:

  `Ô^{(3)}_L = Σ_x ε_x Ŝ^z_x`,
  `(Ô_L)²_⊥ = Σ_{x,y} ε_x ε_y (Ŝ^{(1)}_x Ŝ^{(1)}_y + Ŝ^{(2)}_x Ŝ^{(2)}_y)
            = Σ_{x,y} ε_x ε_y · ½(Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y)`,
  `(Ô_L)² = (Ô_L)²_⊥ + (Ô^{(3)}_L)²`.

The split comes from the per-pair decomposition `Ŝ_x · Ŝ_y = ½(Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y)
+ Ŝ^z_x Ŝ^z_y` together with the factorization `Σ_{x,y} ε_x ε_y Ŝ^z_x Ŝ^z_y
= (Σ_x ε_x Ŝ^z_x)(Σ_y ε_y Ŝ^z_y)`.  Since `ε_x` is real, `Ô^{(3)}_L` is self-adjoint, so
`(Ô^{(3)}_L)²` is a Hermitian square: its expectation is nonnegative and dropping it from
`(Ô_L)²` can only lower an expectation,

  `⟨v| (Ô_L)²_⊥ |v⟩.re ≤ ⟨v| (Ô_L)² |v⟩.re`,

which is the positivity step feeding the ferrimagnetic bound (10.2.17).  Finally `(Ô_L)²` itself
is self-adjoint — `(Ŝ_x · Ŝ_y)ᴴ = Ŝ_y · Ŝ_x` and the staggered scalar `ε_x ε_y` is symmetric and
real, so the ordered double sum is invariant under transposing the summation order — which makes
all its expectations real.

This mirrors the spin-`S` template of §4.1 (Theorem 4.4, eq. (4.1.12),
`Quantum/SpinS/FerrimagneticLROComponentAlgebra.lean`), transplanted to the fermionic carrier
`(Fin (2N+2) → Fin 2) → ℂ`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 354, eqs. (10.2.16)/(10.2.17) (and the §4.1 template, eq. (4.1.12),
pp. 77–78); S.-Q. Shen, Z.-M. Qiu, G.-S. Tian, *Phys. Rev. Lett.* **72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

/-! ## The staggered longitudinal and transverse operators -/

/-- The **longitudinal staggered order operator** `Ô^{(3)}_L = Σ_x ε_x Ŝ^z_x`, the `z`-component
part of the staggered order parameter of Tasaki eq. (10.2.16). -/
noncomputable def fermionStaggeredSpinZ (N : ℕ) (A : Finset (Fin (N + 1))) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), gaugeSign A x • fermionSiteSpinZ N x

/-- The **transverse part of the squared staggered order parameter**,
`Σ_{x,y} ε_x ε_y (Ŝ^{(1)}_x Ŝ^{(1)}_y + Ŝ^{(2)}_x Ŝ^{(2)}_y)`, i.e. the `(1,2)`-component portion
of `(Ô_L)²` (Tasaki eq. (10.2.16)) obtained by dropping the longitudinal `Ŝ^z_x Ŝ^z_y` term from
each spin–spin dot product. -/
noncomputable def fermionStaggeredTransverse (N : ℕ) (A : Finset (Fin (N + 1))) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
    (gaugeSign A x * gaugeSign A y) • fermionSpinTransverse N x y

/-- The squared staggered order parameter written with the named sublattice gauge `gaugeSign`
instead of the inlined `if x ∈ A then 1 else -1` of its definition. -/
private theorem fermionStaggeredCasimirOp_eq_gaugeSign_sum (N : ℕ) (A : Finset (Fin (N + 1))) :
    fermionStaggeredCasimirOp N A =
      ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
        (gaugeSign A x * gaugeSign A y) • fermionSpinDot N x y := rfl

/-- The sublattice gauge factor `ε_x = ±1` is real, hence self-adjoint. -/
private theorem gaugeSign_isSelfAdjoint {N : ℕ} (A : Finset (Fin (N + 1))) (x : Fin (N + 1)) :
    IsSelfAdjoint (gaugeSign A x) := by
  rw [isSelfAdjoint_iff, gaugeSign]
  by_cases hx : x ∈ A
  · rw [if_pos hx, star_one]
  · rw [if_neg hx, star_neg, star_one]

/-! ## The transverse / longitudinal split -/

/-- **Per-pair split of `Ŝ_x · Ŝ_y`.**  The two-site spin dot product is the sum of its
transverse `(1,2)`-plane part `½(Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y)` and the longitudinal `Ŝ^z_x Ŝ^z_y`
term (Tasaki eq. (10.2.7) for the transverse piece). -/
theorem fermionSpinDot_eq_transverse_add_spinZ_mul (N : ℕ) (x y : Fin (N + 1)) :
    fermionSpinDot N x y =
      fermionSpinTransverse N x y + fermionSiteSpinZ N x * fermionSiteSpinZ N y := rfl

/-- **Transverse / longitudinal split of `(Ô_L)²`** (the fermionic form of Tasaki eq. (4.1.12)
for the staggered parameter of eq. (10.2.16)): distributing the staggered scalar `ε_x ε_y` over
the per-pair split, the `(3,3)`-component double sum `Σ_{x,y} ε_x ε_y Ŝ^z_x Ŝ^z_y` factors as
`(Σ_x ε_x Ŝ^z_x)(Σ_y ε_y Ŝ^z_y)`, the square of the longitudinal staggered operator. -/
theorem fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq (N : ℕ)
    (A : Finset (Fin (N + 1))) :
    fermionStaggeredCasimirOp N A =
      fermionStaggeredTransverse N A + fermionStaggeredSpinZ N A * fermionStaggeredSpinZ N A := by
  have hsplit : fermionStaggeredCasimirOp N A =
      fermionStaggeredTransverse N A +
        ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (gaugeSign A x * gaugeSign A y) • (fermionSiteSpinZ N x * fermionSiteSpinZ N y) := by
    rw [fermionStaggeredCasimirOp_eq_gaugeSign_sum]
    unfold fermionStaggeredTransverse
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [fermionSpinDot_eq_transverse_add_spinZ_mul, smul_add]
  rw [hsplit]
  congr 1
  unfold fermionStaggeredSpinZ
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact (smul_mul_smul_comm (gaugeSign A x) (fermionSiteSpinZ N x) (gaugeSign A y)
    (fermionSiteSpinZ N y)).symm

/-! ## Hermiticity and the transverse lower bound -/

/-- **`Ô^{(3)}_L` is self-adjoint**, being a real-linear combination of the self-adjoint per-site
operators `Ŝ^z_x`. -/
theorem fermionStaggeredSpinZ_isHermitian (N : ℕ) (A : Finset (Fin (N + 1))) :
    (fermionStaggeredSpinZ N A).IsHermitian :=
  Matrix.isHermitian_sum Finset.univ fun x _ =>
    (fermionSiteSpinZ_isHermitian N x).smul (gaugeSign_isSelfAdjoint A x)

/-- **Hermitian-square positivity.**  `(Ô^{(3)}_L)²` is the square of a self-adjoint operator,
hence positive semidefinite, so its expectation is nonnegative in every state vector. -/
theorem vectorExpectation_staggeredSpinZ_sq_nonneg (N : ℕ) (A : Finset (Fin (N + 1)))
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    0 ≤ (vectorExpectation (fermionStaggeredSpinZ N A * fermionStaggeredSpinZ N A) v).re := by
  have hps : (fermionStaggeredSpinZ N A * fermionStaggeredSpinZ N A).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (fermionStaggeredSpinZ N A)
    rwa [(fermionStaggeredSpinZ_isHermitian N A).eq] at h
  rw [vectorExpectation]
  exact (Complex.le_def.mp (hps.dotProduct_mulVec_nonneg v)).1

/-- **Transverse expectation lower bound for `(Ô_L)²`** (the positivity step feeding the
ferrimagnetic bound (10.2.17)): dropping the positive-semidefinite longitudinal square
`(Ô^{(3)}_L)²` only decreases an expectation. -/
theorem fermionStaggeredTransverse_expectation_le_staggeredCasimir_expectation (N : ℕ)
    (A : Finset (Fin (N + 1))) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (vectorExpectation (fermionStaggeredTransverse N A) v).re ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re := by
  have hnn := vectorExpectation_staggeredSpinZ_sq_nonneg N A v
  rw [vectorExpectation] at hnn ⊢
  rw [vectorExpectation, fermionStaggeredCasimirOp_eq_transverse_add_staggeredSpinZ_sq,
    Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  linarith

/-- **`(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y` is self-adjoint.**  Each summand obeys
`(ε_x ε_y Ŝ_x · Ŝ_y)ᴴ = ε_y ε_x Ŝ_y · Ŝ_x` (the gauge is real, the dot product's adjoint swaps
the two sites), so the ordered double sum is invariant under transposing the summation order.
Consequently every expectation of `(Ô_L)²` is real. -/
theorem fermionStaggeredCasimirOp_isHermitian (N : ℕ) (A : Finset (Fin (N + 1))) :
    (fermionStaggeredCasimirOp N A).IsHermitian := by
  have hterm : ∀ x y : Fin (N + 1),
      ((gaugeSign A x * gaugeSign A y) • fermionSpinDot N x y)ᴴ
        = (gaugeSign A y * gaugeSign A x) • fermionSpinDot N y x := by
    intro x y
    rw [Matrix.conjTranspose_smul, fermionSpinDot_conjTranspose, StarMul.star_mul,
      (gaugeSign_isSelfAdjoint A x).star_eq, (gaugeSign_isSelfAdjoint A y).star_eq]
  unfold Matrix.IsHermitian
  rw [fermionStaggeredCasimirOp_eq_gaugeSign_sum]
  calc (∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (gaugeSign A x * gaugeSign A y) • fermionSpinDot N x y)ᴴ
      = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (gaugeSign A y * gaugeSign A x) • fermionSpinDot N y x := by
        simp only [Matrix.conjTranspose_sum]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => hterm x y
    _ = ∑ x : Fin (N + 1), ∑ y : Fin (N + 1),
          (gaugeSign A x * gaugeSign A y) • fermionSpinDot N x y := Finset.sum_comm

end LatticeSystem.Fermion
