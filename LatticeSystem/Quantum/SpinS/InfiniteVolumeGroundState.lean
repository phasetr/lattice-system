import LatticeSystem.Math.CStarAlgebra.State
import Mathlib.Algebra.Star.StarAlgHom

/-!
# Tasaki §4.3.1: ground states of the infinite-volume antiferromagnetic Heisenberg model

On the infinite hypercubic lattice `ℤᵈ` the antiferromagnetic Heisenberg model is treated through its
algebra of local observables and its states (linear functionals giving expectation values), rather
than vectors in a Hilbert space.  Following Tasaki §4.3.1, we bundle the abstract data — the
`C*`-algebra of observables, the per-site spin operators `Ŝ_x^{(α)}`, and the translation
automorphisms `τ_x` — into `InfiniteSpinSystem`, and reuse the existing `C*`-algebra state machinery
(`IsState`, `WeakDual`).

**Definition 4.17**: a *translation-invariant* state `ω` is a **ground state** of the
antiferromagnetic Heisenberg model iff `ω(Ŝ_x · Ŝ_y) = ε_GS` for every nearest-neighbor bond
`{x, y} ∈ B∞` (eq. (4.3.1)), where `ε_GS` is the ground-state energy density (per bond).  This is the
infinite-volume version of the finite-volume variational characterization, restricted to
translation-invariant states (cf. Definition A.25 / Theorem A.26).

This file sets up the infinite-volume spin system and records Definition 4.17.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.3.1, Definition 4.17, eqs. (4.3.1)–(4.3.4), pp. 112–113.
-/

namespace LatticeSystem.Quantum

open scoped ComplexOrder

/-- The **infinite-volume spin system** on `ℤᵈ`: the abstract `C*`-algebra `A` of observables (the
quasi-local algebra), the per-site spin operators `spin x α = Ŝ_x^{(α)}` (`x ∈ ℤᵈ`, `α = 1, 2, 3`),
and the translation automorphisms `transl x = τ_x` (eq. (4.3.3), bundled as star-algebra
isomorphisms). -/
structure InfiniteSpinSystem (d : ℕ) (A : Type*) [CStarAlgebra A] [NormedSpace ℂ A]
    [StarModule ℂ A] where
  /-- The per-site spin operators `Ŝ_x^{(α)}`. -/
  spin : (Fin d → ℤ) → Fin 3 → A
  /-- The translation automorphisms `τ_x` (eq. (4.3.3)). -/
  transl : (Fin d → ℤ) → (A ≃⋆ₐ[ℂ] A)

namespace InfiniteSpinSystem

variable {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

/-- A site `x ∈ ℤᵈ` is **even** when its coordinate sum is even (`ℤᵈ_even`, eq. (4.3.2)); this is the
infinite-volume `A`-sublattice. -/
def evenSite (x : Fin d → ℤ) : Prop := (∑ i, x i) % 2 = 0

/-- `{x, y}` is a **nearest-neighbor bond** (`B∞`, eq. (4.3.1)) when `x` and `y` differ in exactly one
coordinate by `±1`. -/
def bond (x y : Fin d → ℤ) : Prop :=
  ∃ i : Fin d, |x i - y i| = 1 ∧ ∀ j, j ≠ i → x j = y j

/-- The **bond spin–spin operator** `Ŝ_x · Ŝ_y = Σ_α Ŝ_x^{(α)} Ŝ_y^{(α)}`. -/
noncomputable def spinDot (S : InfiniteSpinSystem d A) (x y : Fin d → ℤ) : A :=
  ∑ α : Fin 3, S.spin x α * S.spin y α

/-- A state `ρ` is **translation invariant** when `ρ(τ_x a) = ρ(a)` for every observable `a` and
every even translation `x ∈ ℤᵈ_even` (the symmetry appropriate to antiferromagnetic order). -/
def TranslationInvariant (S : InfiniteSpinSystem d A) (ρ : WeakDual ℂ A) : Prop :=
  ∀ a : A, ∀ x : Fin d → ℤ, evenSite x → ρ (S.transl x a) = ρ a

/-- **Tasaki Definition 4.17 (ground state of the infinite-volume antiferromagnetic Heisenberg
model).**  Given the ground-state energy density `εGS` (per bond, eq. (4.3.4)), a state `ρ` is a
*ground state* iff it is a state, translation invariant, and assigns every nearest-neighbor bond the
energy density: `ρ(Ŝ_x · Ŝ_y) = εGS` for all `{x, y} ∈ B∞`. -/
def IsInfiniteVolumeGroundState (S : InfiniteSpinSystem d A) (εGS : ℝ) (ρ : WeakDual ℂ A) : Prop :=
  LatticeSystem.Math.IsState ρ ∧ TranslationInvariant S ρ ∧
    ∀ x y : Fin d → ℤ, bond x y → ρ (spinDot S x y) = (εGS : ℂ)

end InfiniteSpinSystem

end LatticeSystem.Quantum
