import LatticeSystem.Math.MatrixAnalysis.DegeneratePerturbation

/-!
# Unitary conjugation transports a unique ground state between sectors

Generic (model-independent) linear-algebra layer complementing the reindexing and constant-shift
transports of `Math/MatrixAnalysis/SubmatrixGroundState.lean`: a unitary `U` intertwining two
Hamiltonians, `Uᴴ H' U = H`, carries the unique normalized ground state of `H` on a subspace `K`
to the unique normalized ground state of `H'` on a subspace `K'`, at the **same** energy.

Both sector-mapping directions are hypotheses and both are genuinely used: the forward one places
the transported vector in `K'`, the backward one pulls a competing `K'`-eigenvector back into `K`,
where the minimality and uniqueness clauses of `IsUniqueGroundStateOn` live.  Likewise both
unitarity identities are used: `UᴴU = 1` for norm preservation, `UUᴴ = 1` for the round trip that
recovers a competitor from its pullback.

A constant energy offset between the two Hamiltonians is deliberately **not** absorbed here; apply
`IsUniqueGroundStateOn.sub_smul_one` (`Math/MatrixAnalysis/DegeneratePerturbation.lean`) on the
source side first, so that this file states the transport at a single energy.

## Main result

* `IsUniqueGroundStateOn.conj_unitary` — the unitary sector transport of a unique ground state.
-/

namespace LatticeSystem.Math

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The identity matrix acts as the identity map on `EuclideanSpace ℂ n`. -/
private theorem toEuclideanLin_one_apply (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (1 : Matrix n n ℂ) v = v := by
  apply WithLp.ofLp_injective 2
  simp

/-- **A matrix `U` with `Uᴴ U = 1` acts isometrically.**  The associated linear map has
`toEuclideanLin Uᴴ` as its adjoint, so `⟪U v, U v⟫ = ⟪v, (UᴴU) v⟫ = ⟪v, v⟫`. -/
private theorem norm_toEuclideanLin_of_conjTranspose_mul_self {U : Matrix n n ℂ}
    (hUU : Matrix.conjTranspose U * U = 1) (v : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanLin U v‖ = ‖v‖ := by
  have hinner : inner ℂ (Matrix.toEuclideanLin U v) (Matrix.toEuclideanLin U v)
      = (inner ℂ v v : ℂ) := by
    rw [← LinearMap.adjoint_inner_right, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      ← toEuclideanLin_mul_apply, hUU, toEuclideanLin_one_apply]
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ), inner_self_eq_norm_sq_to_K (𝕜 := ℂ)] at hinner
  have hsq : ‖Matrix.toEuclideanLin U v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast hinner
  rw [← Real.sqrt_sq (norm_nonneg (Matrix.toEuclideanLin U v)), hsq,
    Real.sqrt_sq (norm_nonneg v)]

/-- **Unitary conjugation transports a unique ground state at unchanged energy.**  Let `U` be
unitary (`UᴴU = UUᴴ = 1`) and intertwine two Hamiltonians, `Uᴴ H' U = H`.  If `U` maps a subspace
`K` into `K'` and `Uᴴ` maps `K'` back into `K`, then the unique normalized ground state `φ` of `H`
on `K` is carried by `U` to the unique normalized ground state of `H'` on `K'`, with the same
energy `E`.

The intertwiner rearranges (using `UUᴴ = 1`) into `H' U = U H` and `H Uᴴ = Uᴴ H'`, which transport
eigenvectors in either direction at unchanged eigenvalue; the two sector-mapping hypotheses then
keep both transports inside the relevant subspaces, so minimality of `E` on `K` and uniqueness of
`φ` there transfer verbatim to `K'`.  Any constant energy shift between two Hamiltonians must be
removed beforehand with `IsUniqueGroundStateOn.sub_smul_one`. -/
theorem IsUniqueGroundStateOn.conj_unitary {K K' : Submodule ℂ (EuclideanSpace ℂ n)}
    {U H H' : Matrix n n ℂ} {E : ℝ} {φ : EuclideanSpace ℂ n}
    (hUU : Matrix.conjTranspose U * U = 1)
    (hUUc : U * Matrix.conjTranspose U = 1)
    (hconj : Matrix.conjTranspose U * H' * U = H)
    (hfwd : ∀ v ∈ K, Matrix.toEuclideanLin U v ∈ K')
    (hbwd : ∀ v ∈ K', Matrix.toEuclideanLin (Matrix.conjTranspose U) v ∈ K)
    (hGS : IsUniqueGroundStateOn K H E φ) :
    IsUniqueGroundStateOn K' H' E (Matrix.toEuclideanLin U φ) := by
  obtain ⟨hmem, hnorm, heig, hground, huniq⟩ := hGS
  have hH'U : H' * U = U * H := by
    rw [← hconj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUUc, Matrix.one_mul]
  have hHUc : H * Matrix.conjTranspose U = Matrix.conjTranspose U * H' := by
    rw [← hconj, Matrix.mul_assoc, Matrix.mul_assoc, hUUc, Matrix.mul_one]
  have hUcU : ∀ v : EuclideanSpace ℂ n,
      Matrix.toEuclideanLin U (Matrix.toEuclideanLin (Matrix.conjTranspose U) v) = v := by
    intro v
    rw [← toEuclideanLin_mul_apply, hUUc, toEuclideanLin_one_apply]
  -- Pull a `K'`-eigenvector of `H'` back to a `K`-eigenvector of `H` at the same eigenvalue.
  have hpull : ∀ (μ : ℝ) (ψ : EuclideanSpace ℂ n), ψ ∈ K' →
      Matrix.toEuclideanLin H' ψ = (μ : ℂ) • ψ →
      Matrix.toEuclideanLin (Matrix.conjTranspose U) ψ ∈ K ∧
        Matrix.toEuclideanLin H (Matrix.toEuclideanLin (Matrix.conjTranspose U) ψ)
          = (μ : ℂ) • Matrix.toEuclideanLin (Matrix.conjTranspose U) ψ := by
    intro μ ψ hψmem hψeig
    refine ⟨hbwd ψ hψmem, ?_⟩
    rw [← toEuclideanLin_mul_apply, hHUc, toEuclideanLin_mul_apply, hψeig, map_smul]
  have hpush : Matrix.toEuclideanLin H' (Matrix.toEuclideanLin U φ)
      = (E : ℂ) • Matrix.toEuclideanLin U φ := by
    rw [← toEuclideanLin_mul_apply, hH'U, toEuclideanLin_mul_apply, heig, map_smul]
  have hnormU : ‖Matrix.toEuclideanLin U φ‖ = 1 := by
    rw [norm_toEuclideanLin_of_conjTranspose_mul_self hUU, hnorm]
  have hne : Matrix.toEuclideanLin U φ ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnormU
    exact one_ne_zero hnormU.symm
  refine ⟨hfwd φ hmem, hnormU, hpush, ⟨⟨_, hfwd φ hmem, hne, hpush⟩, ?_⟩, ?_⟩
  · rintro μ ⟨ψ, hψmem, hψne, hψeig⟩
    obtain ⟨hgmem, hgeig⟩ := hpull μ ψ hψmem hψeig
    refine hground.2 μ ⟨_, hgmem, ?_, hgeig⟩
    intro hz
    refine hψne ?_
    calc ψ = Matrix.toEuclideanLin U (Matrix.toEuclideanLin (Matrix.conjTranspose U) ψ) :=
          (hUcU ψ).symm
      _ = Matrix.toEuclideanLin U 0 := by rw [hz]
      _ = 0 := map_zero _
  · intro ψ hψmem hψeig
    obtain ⟨hgmem, hgeig⟩ := hpull E ψ hψmem hψeig
    obtain ⟨c, hc⟩ := huniq _ hgmem hgeig
    refine ⟨c, ?_⟩
    calc ψ = Matrix.toEuclideanLin U (Matrix.toEuclideanLin (Matrix.conjTranspose U) ψ) :=
          (hUcU ψ).symm
      _ = Matrix.toEuclideanLin U (c • φ) := by rw [hc]
      _ = c • Matrix.toEuclideanLin U φ := map_smul _ _ _

end LatticeSystem.Math
