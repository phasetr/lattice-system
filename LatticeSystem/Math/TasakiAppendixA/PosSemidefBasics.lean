import Mathlib.Analysis.Matrix.PosDef

/-!
# Tasaki Appendix A.2.3: positive-semidefinite operator basics (Lemmas A.4, A.5)

Elementary facts about nonnegative (positive-semidefinite) self-adjoint operators from
Tasaki's Mathematical Appendix, here for finite complex matrices `Matrix n n ℂ` (the operator
algebra of a finite-volume quantum system).  Unlike the Lie product formula (Theorem A.1),
these are available in mathlib, so they are **proved** (thin wrappers), not axiomatized:

* **Lemma A.4**: a Hermitian operator is positive-semidefinite iff all its eigenvalues are
  nonnegative.
* **Lemma A.5**: the sum of two positive-semidefinite operators is positive-semidefinite.

(Lemma A.6 — `B̂†B̂ ≥ 0` and the existence/uniqueness of the square root `Ĉ = √Â` — follows in a
separate PR.)

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Lemmas A.4–A.5, pp. 467–468.
-/

namespace LatticeSystem.Math

open Matrix
open scoped ComplexOrder

/-- **Tasaki Lemma A.4.**  A Hermitian matrix `A` is positive-semidefinite iff every
eigenvalue is nonnegative. -/
theorem posSemidef_iff_eigenvalues_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ i, 0 ≤ hA.eigenvalues i :=
  hA.posSemidef_iff_eigenvalues_nonneg

/-- **Tasaki Lemma A.5.**  The sum of two positive-semidefinite matrices is
positive-semidefinite (`⟨Φ|(Â+B̂)|Φ⟩ = ⟨Φ|Â|Φ⟩ + ⟨Φ|B̂|Φ⟩ ≥ 0`). -/
theorem PosSemidef.add {n : Type*} {A B : Matrix n n ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : (A + B).PosSemidef :=
  hA.add hB

end LatticeSystem.Math
