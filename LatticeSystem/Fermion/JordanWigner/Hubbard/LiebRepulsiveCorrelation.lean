import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsive
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin

/-!
# Spin-correlation signs in the repulsive Hubbard ground states (Tasaki §10.2.2, Theorem 10.5)

This file formalizes the statement of **Tasaki Theorem 10.5** (Shen, Qiu,
and Tian; Hal Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, 1st ed., Springer 2020, §10.2.2, p. 351, eq. (10.2.7)): under the
hypotheses of Theorem 10.4 (repulsive Hubbard at half-filling), the
transverse spin–spin correlation in any ground state is **strictly positive
for sites in the same sublattice and strictly negative for sites in
different sublattices**.

## Status

Like Theorem 10.4, this is a consequence of Lieb's spin-space
reflection-positivity method (Shen–Qiu–Tian extension); per the project
policy it is recorded as a faithful documented `axiom`, reusing the packaged
model hypotheses `IsLiebRepulsiveModel` and the ground subspace
`hubbardGroundSubmoduleAtElectronNumber` from `LiebRepulsive.lean`.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators ComplexOrder

variable {N : ℕ}

/-- The transverse spin–spin correlation operator
`Ŝ⁽¹⁾_x Ŝ⁽¹⁾_y + Ŝ⁽²⁾_x Ŝ⁽²⁾_y = ½ (Ŝ⁺_x Ŝ⁻_y + Ŝ⁻_x Ŝ⁺_y)` of Theorem 10.5
(Tasaki eq. (10.2.7)). -/
noncomputable def fermionSpinTransverse (N : ℕ) (x y : Fin (N + 1)) :
    ManyBodyOp (Fin (2 * N + 2)) :=
  (1 / 2 : ℂ) •
    (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y +
      fermionSiteSpinMinus N x * fermionSiteSpinPlus N y)

/-- The (raw) expectation `⟨v| O |v⟩` of an observable `O` in a state vector
`v`. -/
noncomputable def vectorExpectation {ι : Type*} [Fintype ι]
    (O : Matrix ι ι ℂ) (v : ι → ℂ) : ℂ :=
  dotProduct (star v) (O.mulVec v)

/-- Two sites lie in the same sublattice of the bipartition `A ⊔ Aᶜ`. -/
def SameSublattice (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) : Prop :=
  x ∈ A ↔ y ∈ A

/-- **Tasaki Theorem 10.5** (Shen–Qiu–Tian; 1st ed., Springer 2020, §10.2.2,
p. 351, eq. (10.2.7), **AXIOM**). Under the hypotheses of Theorem 10.4, for
any ground state `v` (a nonzero vector in the `(N+1)`-electron ground
subspace at the ground energy `E₀`), the transverse spin correlation
`⟨v| Ŝ⁽¹⁾_x Ŝ⁽¹⁾_y + Ŝ⁽²⁾_x Ŝ⁽²⁾_y |v⟩` is real, and is strictly positive
when `x, y` lie in the same sublattice and strictly negative otherwise.

Shen–Qiu–Tian's extension of Lieb's reflection positivity; recorded as a
faithful documented axiom. -/
axiom theorem_10_5_shen_qiu_tian_spin_correlation_sign
    (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2)))
    (hModel : IsLiebRepulsiveModel A T H)
    (E₀ : ℂ)
    (hGS_ne : hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1) ≠ ⊥)
    (hMin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber H E (N + 1) ≠ ⊥ →
      E₀.re ≤ E.re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1)) (hv0 : v ≠ 0) :
    ∀ x y : Fin (N + 1),
      (vectorExpectation (fermionSpinTransverse N x y) v).im = 0 ∧
        (SameSublattice A x y →
            0 < (vectorExpectation (fermionSpinTransverse N x y) v).re) ∧
          (¬ SameSublattice A x y →
            (vectorExpectation (fermionSpinTransverse N x y) v).re < 0)

end LatticeSystem.Fermion
