import LatticeSystem.Math.CStarAlgebra.State
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Topology.Algebra.InfiniteSum.Basic

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
  /-- `τ_0` is the identity (the translations form an action of `ℤᵈ`). -/
  transl_zero : ∀ a : A, transl 0 a = a
  /-- The translations compose additively: `τ_x ∘ τ_y = τ_{x+y}` (action law). -/
  transl_add : ∀ (x y : Fin d → ℤ) (a : A), transl x (transl y a) = transl (x + y) a
  /-- **Spin covariance** (eq. (4.3.3)): the translation `τ_x` moves the site-`y` spin operator to
  site `y + x`, `τ_x(Ŝ_y^{(α)}) = Ŝ_{y+x}^{(α)}`. -/
  transl_spin : ∀ (x y : Fin d → ℤ) (α : Fin 3), transl x (spin y α) = spin (y + x) α

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
every **even** translation `x ∈ ℤᵈ_even`.  This is exactly Tasaki's convention for §4.3: he restricts
the translations to the even sublattice `ℤᵈ_even`, "anticipating antiferromagnetic order" (the Néel
state is invariant under even translations but *not* under odd ones), and footnote 35 explicitly
notes this is a deliberate restriction of the general (all-`x`) notion to even translations.  So the
`evenSite` quantifier is faithful to Definition 4.17, not a weakening. -/
def TranslationInvariant (S : InfiniteSpinSystem d A) (ρ : WeakDual ℂ A) : Prop :=
  ∀ a : A, ∀ x : Fin d → ℤ, evenSite x → ρ (S.transl x a) = ρ a

/-- **Tasaki Definition 4.17 (ground state of the infinite-volume antiferromagnetic Heisenberg
model).**  Given the ground-state energy density `εGS` (per bond, eq. (4.3.4)), a state `ρ` is a
*ground state* iff it is a state, translation invariant, and assigns every nearest-neighbor bond the
energy density: `ρ(Ŝ_x · Ŝ_y) = εGS` for all `{x, y} ∈ B∞`. -/
def IsInfiniteVolumeGroundState (S : InfiniteSpinSystem d A) (εGS : ℝ) (ρ : WeakDual ℂ A) : Prop :=
  LatticeSystem.Math.IsState ρ ∧ TranslationInvariant S ρ ∧
    ∀ x y : Fin d → ℤ, bond x y → ρ (spinDot S x y) = (εGS : ℂ)

instance : DecidablePred (evenSite (d := d)) := fun x => Int.decEq ((∑ i, x i) % 2) 0

/-- The finite box `Λ_L = [0, L)ᵈ ⊆ ℤᵈ` (volume `Lᵈ`), as a `Finset`. -/
noncomputable def latticeBox (d L : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Ico (0 : ℤ) (L : ℤ)

/-- The **bulk operator** `Â_L = Σ_{x ∈ Λ_L ∩ ℤᵈ_even} τ_x(Â)` (eq. (4.3.5)): the sum of the
translated observables over the even sites of the box `Λ_L`. -/
noncomputable def bulkOp (S : InfiniteSpinSystem d A) (Â : A) (L : ℕ) : A :=
  ∑ x ∈ (latticeBox d L).filter evenSite, S.transl x Â

/-- **Tasaki Definition 4.18 (ergodic state).**  A translation-invariant state `ρ` is *ergodic* iff,
for every self-adjoint observable `Â`, the fluctuation of the bulk density `Â_L / Lᵈ` vanishes in the
infinite-volume limit (eq. (4.3.6)):
`lim_{L↑∞} [ ρ(Â_L²) / (Lᵈ)² − (ρ(Â_L) / Lᵈ)² ] = 0`.
The vanishing of the fluctuation is the law of large numbers for densities — the mark of a
macroscopically "healthy" state.  (`Â` self-adjoint makes `ρ(Â_L)` and `ρ(Â_L²)` real, so the real
parts carry the content; the index is shifted by one to avoid the empty `L = 0` box.) -/
def IsErgodic (S : InfiniteSpinSystem d A) (ρ : WeakDual ℂ A) : Prop :=
  LatticeSystem.Math.IsState ρ ∧ TranslationInvariant S ρ ∧
    ∀ Â : A, IsSelfAdjoint Â →
      Filter.Tendsto
        (fun L : ℕ =>
          (ρ ((bulkOp S Â (L + 1)) ^ 2)).re / (((L : ℝ) + 1) ^ d) ^ 2
            - ((ρ (bulkOp S Â (L + 1))).re / ((L : ℝ) + 1) ^ d) ^ 2)
        Filter.atTop (nhds 0)

/-- **Tasaki Definition 4.19 (physical ground state).**  A translation-invariant ground state `ω` of
the antiferromagnetic Heisenberg model is a *physical ground state* when it is ergodic. -/
def IsPhysicalGroundState (S : InfiniteSpinSystem d A) (εGS : ℝ) (ω : WeakDual ℂ A) : Prop :=
  IsInfiniteVolumeGroundState S εGS ω ∧ IsErgodic S ω

end InfiniteSpinSystem

end LatticeSystem.Quantum
