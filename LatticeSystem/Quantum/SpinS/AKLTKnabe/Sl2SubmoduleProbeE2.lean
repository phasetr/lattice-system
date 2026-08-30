import LatticeSystem.Quantum.SpinS.TotalSpin
import LatticeSystem.Quantum.SpinS.Magnetization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Gate E2 probe: the `Matrix ↔ Submodule` round trip for the `sl₂` route

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) is the
**feasibility probe** for the passage between the
matrix world (`ManyBodyOpS Λ N = Matrix (Λ → Fin (N+1)) (Λ → Fin (N+1)) ℂ`) and the
`Submodule` / `LinearMap` world on the Euclidean space `EuclideanSpace ℂ (Λ → Fin (N+1))`.

Four things are checked, each by an actual declaration that has to type check:

1. the matrix `Ŝ⁺_tot` becomes a linear map through `Matrix.toEuclideanLin`, with the component
   description `ofLp (Ŝ⁺_tot v) = Ŝ⁺_tot *ᵥ ofLp v` (`ofLp_totalPlusLinE2`);
2. the magnetisation sector `V_m` and the highest-weight space `hw_m = V_m ∩ ker Ŝ⁺_tot` exist as
   `Submodule ℂ (EuclideanSpace ℂ (Λ → Fin (N+1)))` (`magSectorE2`, `highestWeightE2`);
3. the adjoint relation `(Ŝ⁺_tot)† = Ŝ⁻_tot` transports to the operator adjoint, which yields both
   the orthogonality statement `(range Ŝ⁻_tot)ᗮ = ker Ŝ⁺_tot` — so the `Submodule.orthogonal`
   inner-product-space instance does resolve — and the operator half of the ladder identity
   `⟪v, Ŝ⁺Ŝ⁻v⟫ − ⟪v, Ŝ⁻Ŝ⁺v⟫ = ‖Ŝ⁻v‖² − ‖Ŝ⁺v‖²` (the remaining half is the matrix
   identity `[Ŝ⁺, Ŝ⁻] = 2 Ŝ³`, which is *not* part of this probe);
4. the rank–nullity theorem applies to `Ŝ⁺_tot` restricted to `V_m`, in the exact form the
   sector dimension count needs: `dim (range) + dim hw_m = dim V_m`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.4, pp. 188–190; S. Knabe, *J. Stat. Phys.* **52**, 627–638 (1988).
-/

namespace LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2

open LatticeSystem.Quantum

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (N : ℕ)

/-- The many-body spin-`S` Hilbert space carried by the `ℓ²` inner product structure: the same
index type `Λ → Fin (N + 1)` as `ManyBodyOpS Λ N`, but with the `EuclideanSpace` instances that
`Submodule.orthogonal`, `LinearMap.adjoint` and `Module.finrank` need. -/
abbrev ManyBodyVecE2 : Type _ := EuclideanSpace ℂ (Λ → Fin (N + 1))

/-- The total raising operator `Ŝ⁺_tot` viewed as a linear endomorphism of the many-body Hilbert
space (probe item 1: the matrix-to-`LinearMap` direction of the round trip). -/
noncomputable def totalPlusLinE2 : ManyBodyVecE2 Λ N →ₗ[ℂ] ManyBodyVecE2 Λ N :=
  Matrix.toEuclideanLin (totalSpinSOpPlus Λ N)

/-- The total lowering operator `Ŝ⁻_tot` viewed as a linear endomorphism of the many-body Hilbert
space. -/
noncomputable def totalMinusLinE2 : ManyBodyVecE2 Λ N →ₗ[ℂ] ManyBodyVecE2 Λ N :=
  Matrix.toEuclideanLin (totalSpinSOpMinus Λ N)

/-- Component description of `totalPlusLinE2`: applying it and forgetting the `ℓ²` structure is
matrix–vector multiplication by `Ŝ⁺_tot`.  This is the bridge that step (F) of the design (the
explicit highest-weight vectors) will use to compute `Ŝ⁺_tot u = 0` entrywise. -/
theorem ofLp_totalPlusLinE2 (v : ManyBodyVecE2 Λ N) :
    WithLp.ofLp (totalPlusLinE2 Λ N v) = (totalSpinSOpPlus Λ N).mulVec (WithLp.ofLp v) := rfl

/-- The operator adjoint of `Ŝ⁺_tot` is `Ŝ⁻_tot`, transported from the matrix identity
`totalSpinSOpPlus_conjTranspose` through `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`. -/
theorem adjoint_totalPlusLinE2 :
    LinearMap.adjoint (totalPlusLinE2 Λ N) = totalMinusLinE2 Λ N := by
  unfold totalPlusLinE2 totalMinusLinE2
  rw [← totalSpinSOpPlus_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- The operator adjoint of `Ŝ⁻_tot` is `Ŝ⁺_tot`, transported from the matrix identity
`totalSpinSOpMinus_conjTranspose`. -/
theorem adjoint_totalMinusLinE2 :
    LinearMap.adjoint (totalMinusLinE2 Λ N) = totalPlusLinE2 Λ N := by
  unfold totalPlusLinE2 totalMinusLinE2
  rw [← totalSpinSOpMinus_conjTranspose, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

/-- **Ambient form**: the orthogonal complement of the image of the total lowering
operator is the kernel of the total raising operator, `(im Ŝ⁻_tot)ᗮ = ker Ŝ⁺_tot`.  This is the
statement whose `Submodule.orthogonal` instance was the main open risk of the route. -/
theorem orthogonal_range_totalMinusLinE2 :
    (LinearMap.range (totalMinusLinE2 Λ N))ᗮ = LinearMap.ker (totalPlusLinE2 Λ N) := by
  rw [LinearMap.orthogonal_range, adjoint_totalMinusLinE2]

/-- **Operator half of the ladder identity**: for every vector `v`,
`⟪v, Ŝ⁺Ŝ⁻v⟫ − ⟪v, Ŝ⁻Ŝ⁺v⟫ = ‖Ŝ⁻v‖² − ‖Ŝ⁺v‖²`.  Only the adjoint relations are used; combining this
with the matrix commutator identity `[Ŝ⁺_tot, Ŝ⁻_tot] = 2 Ŝ³_tot` and `Ŝ³_tot v = m v` on the
magnetisation sector `V_m` gives `‖Ŝ⁻v‖² = ‖Ŝ⁺v‖² + 2m‖v‖²`. -/
theorem ladderInnerNormSqE2 (v : ManyBodyVecE2 Λ N) :
    inner ℂ v (totalPlusLinE2 Λ N (totalMinusLinE2 Λ N v))
        - inner ℂ v (totalMinusLinE2 Λ N (totalPlusLinE2 Λ N v))
      = (‖totalMinusLinE2 Λ N v‖ : ℂ) ^ 2 - (‖totalPlusLinE2 Λ N v‖ : ℂ) ^ 2 := by
  have h1 : inner ℂ v (totalPlusLinE2 Λ N (totalMinusLinE2 Λ N v))
      = (‖totalMinusLinE2 Λ N v‖ : ℂ) ^ 2 := by
    rw [← adjoint_totalMinusLinE2 Λ N, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    rfl
  have h2 : inner ℂ v (totalMinusLinE2 Λ N (totalPlusLinE2 Λ N v))
      = (‖totalPlusLinE2 Λ N v‖ : ℂ) ^ 2 := by
    rw [← adjoint_totalPlusLinE2 Λ N, LinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K]
    rfl
  rw [h1, h2]

/-- The magnetisation sector `V_m`, i.e. the subspace of vectors supported on the configurations
`σ` with `magSumS σ = m` (probe item 2: a genuine `Submodule` of the Euclidean space). -/
noncomputable def magSectorE2 (m : ℕ) : Submodule ℂ (ManyBodyVecE2 Λ N) where
  carrier := {v | ∀ σ : Λ → Fin (N + 1), magSumS σ ≠ m → WithLp.ofLp v σ = 0}
  add_mem' := by
    intro a b ha hb σ hσ
    have hab : WithLp.ofLp (a + b) σ = WithLp.ofLp a σ + WithLp.ofLp b σ := rfl
    rw [hab, ha σ hσ, hb σ hσ, add_zero]
  zero_mem' := by
    intro σ _
    rfl
  smul_mem' := by
    intro c a ha σ hσ
    have hca : WithLp.ofLp (c • a) σ = c * WithLp.ofLp a σ := rfl
    rw [hca, ha σ hσ, mul_zero]

/-- The highest-weight space `hw_m = V_m ∩ ker Ŝ⁺_tot`. -/
noncomputable def highestWeightE2 (m : ℕ) : Submodule ℂ (ManyBodyVecE2 Λ N) :=
  magSectorE2 Λ N m ⊓ LinearMap.ker (totalPlusLinE2 Λ N)

/-- Rank–nullity for `Ŝ⁺_tot` restricted to the magnetisation sector `V_m`,
`dim (Ŝ⁺_tot V_m) + dim hw_m = dim V_m`.  Together with the surjectivity of `Ŝ⁺_tot : V_m → V_{m+1}`
(which is the content of (B), not proved here) this gives `dim hw_m = dim V_m − dim V_{m+1}`. -/
theorem finrank_range_add_finrank_highestWeightE2 (m : ℕ) :
    Module.finrank ℂ ↥(LinearMap.range ((totalPlusLinE2 Λ N).domRestrict (magSectorE2 Λ N m)))
        + Module.finrank ℂ ↥(highestWeightE2 Λ N m)
      = Module.finrank ℂ ↥(magSectorE2 Λ N m) := by
  have hmap : Submodule.map (magSectorE2 Λ N m).subtype
      (LinearMap.ker ((totalPlusLinE2 Λ N).domRestrict (magSectorE2 Λ N m)))
      = highestWeightE2 Λ N m := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype, highestWeightE2]
  have hker : Module.finrank ℂ
      ↥(LinearMap.ker ((totalPlusLinE2 Λ N).domRestrict (magSectorE2 Λ N m)))
      = Module.finrank ℂ ↥(highestWeightE2 Λ N m) := by
    have hequiv := (Submodule.equivMapOfInjective (magSectorE2 Λ N m).subtype
      (Submodule.injective_subtype _)
      (LinearMap.ker ((totalPlusLinE2 Λ N).domRestrict (magSectorE2 Λ N m)))).finrank_eq
    rw [hequiv, hmap]
  rw [← hker]
  exact LinearMap.finrank_range_add_finrank_ker _

end LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2
