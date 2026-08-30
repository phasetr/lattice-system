import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Test coverage for the generic `IsUniqueGroundStateOn` shift/uniqueness lemmas (Theorem 10.8)

Pins the API contract of the generic `IsUniqueGroundStateOn` infrastructure that Theorem 10.8's
discharge needs, and that must live
in `Math/MatrixAnalysis/DegeneratePerturbation.lean` next to
`IsUniqueGroundStateOn.smul_of_norm_one`:

1. **S1** `IsUniqueGroundStateOn.sub_smul_one` — shifting `H` by a real scalar multiple of the
   identity shifts the unique ground energy by the same scalar and preserves the ground state.
2. **S2** `IsUniqueGroundStateOn.energy_eq` — two unique ground states on the *same* `(K, H)` have
   equal energies.
3. **S3** `IsUniqueGroundStateOn.exists_smul_eq` — two unique ground states on the same `(K, H)`
   are collinear via a unit-modulus scalar.

Each `example` fails to elaborate unless the corresponding declaration exists with exactly this
signature, so this file is the executable acceptance condition of the three lemmas.

**Not covered here**: any instantiation on a concrete Hubbard Hamiltonian — that is exercised by
`Tests/LiebShenQiuShibaBridge.lean`, which consumes the Hamiltonian-bridge identity built from
these lemmas.
-/

namespace LatticeSystem.Tests.DegeneratePerturbationShiftUniqueness

open LatticeSystem.Math Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Pins **S1**: shifting `H` by `(c : ℂ) • 1` shifts the unique ground energy by `c` and
preserves the ground state vector. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E c : ℝ}
    {φ : EuclideanSpace ℂ n} (hGS : IsUniqueGroundStateOn K H E φ) :
    IsUniqueGroundStateOn K (H - (c : ℂ) • 1) (E - c) φ :=
  hGS.sub_smul_one

/-- Pins **S2**: two unique ground states on the same `(K, H)` have equal energies. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E₁ E₂ : ℝ}
    {φ₁ φ₂ : EuclideanSpace ℂ n} (hGS₁ : IsUniqueGroundStateOn K H E₁ φ₁)
    (hGS₂ : IsUniqueGroundStateOn K H E₂ φ₂) : E₁ = E₂ :=
  hGS₁.energy_eq hGS₂

/-- Pins **S3**: two unique ground states on the same `(K, H)` are collinear via a unit-modulus
scalar `c`. -/
example {K : Submodule ℂ (EuclideanSpace ℂ n)} {H : Matrix n n ℂ} {E₁ E₂ : ℝ}
    {φ₁ φ₂ : EuclideanSpace ℂ n} (hGS₁ : IsUniqueGroundStateOn K H E₁ φ₁)
    (hGS₂ : IsUniqueGroundStateOn K H E₂ φ₂) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ φ₂ = c • φ₁ :=
  hGS₁.exists_smul_eq hGS₂

end LatticeSystem.Tests.DegeneratePerturbationShiftUniqueness
