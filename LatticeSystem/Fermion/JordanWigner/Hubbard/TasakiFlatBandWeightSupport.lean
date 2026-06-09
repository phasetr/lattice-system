import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandWeightStructure
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandUniqueness
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiFlatBandTheorem11_11

/-!
# Tasaki §11.3.1: occupation-basis support of a fixed-weight ground vector (toward block ≤ 1)

The rotated occupation basis diagonalises both `N̂` and `Ŝ^z`
(`fermionTotalNumber_mulVec_occMonomial`, `fermionTotalSpinZ_mulVec_occMonomial`).  Hence a vector
that is an `N̂`/`Ŝ^z` eigenvector has occupation-basis coordinates supported only on the matching
weight: expanding `v` in the basis and applying the diagonal operator equates the per-monomial
coefficients, so an off-weight coordinate vanishes by basis independence.

For the `Ŝ^z`-weight block `G ⊓ eigenspace(Ŝ^z, μ)` of the half-filled ground subspace this pins the
support to occupation configs with exactly `K+1` occupied modes (`N̂ = K+1`), `Ŝ^z` weight `μ`, and
(from `BKernel ⊆ AlphaFock`) no `β`-occupation — i.e. the `α`-Slater states `|Φ_S⟩`, on which the
no-double-occupancy condition will force the symmetric (Dicke) combination.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.1.  Tracked in Issue #4346.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {K : ℕ} {ν : ℝ}

/-- **Off-eigenvalue occupation coordinates vanish.**  If an operator `T` is diagonal on the
occupation basis with eigenvalue `d f` on `occMonomial f`, and `v` is a `T`-eigenvector with
eigenvalue `μ`, then the occupation coordinate of `v` at any config `g` with `d g ≠ μ` is zero. -/
theorem flatBandOccBasis_repr_eq_zero_of_eigenvalue_ne
    (T : Matrix (Fin (2 * (2 * K + 1) + 2) → Fin 2) (Fin (2 * (2 * K + 1) + 2) → Fin 2) ℂ)
    (d : ((Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2) → ℂ)
    (hdiag : ∀ f, T.mulVec (occMonomial K ν f) = d f • occMonomial K ν f)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ} (μ : ℂ) (hv : T.mulVec v = μ • v)
    {g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2} (hg : d g ≠ μ) :
    (flatBandOccBasis K ν).repr v g = 0 := by
  have hLIfam : LinearIndependent ℂ (occMonomial K ν) := by
    have h := (flatBandOccBasis K ν).linearIndependent
    rwa [show occMonomial K ν = ⇑(flatBandOccBasis K ν) from
      funext (fun f => (flatBandOccBasis_apply f).symm)]
  have hLI : ∑ f, (d f * (flatBandOccBasis K ν).repr v f - μ * (flatBandOccBasis K ν).repr v f) •
      occMonomial K ν f = 0 := by
    have e1 : T.mulVec v
        = ∑ f, (d f * (flatBandOccBasis K ν).repr v f) • occMonomial K ν f := by
      conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [flatBandOccBasis_apply f, Matrix.mulVec_smul, hdiag f, smul_smul,
        mul_comm ((flatBandOccBasis K ν).repr v f) (d f)]
    have e2 : μ • v = ∑ f, (μ * (flatBandOccBasis K ν).repr v f) • occMonomial K ν f := by
      conv_lhs => rw [← (flatBandOccBasis K ν).sum_repr v, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun f _ => ?_)
      rw [flatBandOccBasis_apply f, smul_smul]
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, ← e1, ← e2, hv, sub_self]
  have hcoeff := Fintype.linearIndependent_iff.mp hLIfam _ hLI g
  have hfact : (d g - μ) * (flatBandOccBasis K ν).repr v g = 0 := by rw [sub_mul]; exact hcoeff
  exact (mul_eq_zero.mp hfact).resolve_left (sub_ne_zero.mpr hg)

/-- **A half-filled ground vector's occupation support has exactly `K+1` occupied modes.**  Off the
`N̂ = K+1` shell the occupation coordinate vanishes. -/
theorem flatBandOccBasis_repr_eq_zero_of_card_ne (t U : ℝ)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U)
    {g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2} (hg : (occFinset g).card ≠ K + 1) :
    (flatBandOccBasis K ν).repr v g = 0 := by
  rw [flatBandHalfFilledGroundSubmodule, Submodule.mem_inf, Module.End.mem_eigenspace_iff,
    Matrix.mulVecLin_apply] at hv
  refine flatBandOccBasis_repr_eq_zero_of_eigenvalue_ne (fermionTotalNumber (2 * (2 * K + 1) + 1))
    (fun f => ((occFinset f).card : ℂ)) (fun f => fermionTotalNumber_mulVec_occMonomial K ν f)
    ((K + 1 : ℕ) : ℂ) hv.2 ?_
  change ((occFinset g).card : ℂ) ≠ ((K + 1 : ℕ) : ℂ)
  exact_mod_cast hg

/-- **A fixed-`Ŝ^z`-weight ground vector's occupation support has the matching `Ŝ^z` weight.**  Off
the weight `μ` the occupation coordinate vanishes. -/
theorem flatBandOccBasis_repr_eq_zero_of_spinZ_ne (t U : ℝ) (μ : ℂ)
    {v : (Fin (2 * (2 * K + 1) + 2) → Fin 2) → ℂ}
    (hv : v ∈ flatBandHalfFilledGroundSubmodule K ν t U ⊓
      Module.End.eigenspace (fermionTotalSpinZ (2 * K + 1)).mulVecLin μ)
    {g : (Fin (K + 1) ⊕ Fin (K + 1)) × Fin 2 → Fin 2}
    (hg : (∑ q ∈ occFinset g, flatBandSpinCharge q.2) ≠ μ) :
    (flatBandOccBasis K ν).repr v g = 0 := by
  rw [Submodule.mem_inf, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv
  exact flatBandOccBasis_repr_eq_zero_of_eigenvalue_ne (fermionTotalSpinZ (2 * K + 1))
    (fun f => ∑ q ∈ occFinset f, flatBandSpinCharge q.2)
    (fun f => fermionTotalSpinZ_mulVec_occMonomial K ν f) μ hv.2 hg

end LatticeSystem.Fermion
