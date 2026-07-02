import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# The spectral absolute value of a Hermitian matrix (Tasaki §10.2.4)

Thirtieth layer (PR30) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model), in the **corrected Hermitian-`W` endgame**.

Lieb's spin-space reflection-positivity inequality `E(W) ≥ E(|W|)` replaces the
Hermitian coefficient matrix `W = Σ_j λ_j v_j v_j†` by its **spectral absolute value**
`|W| = Σ_j |λ_j| v_j v_j†`. This file constructs `|W|` (as `hermitianAbs`) via the
spectral diagonalization `W = U·D·Uᴴ` (`U = eigenvectorUnitary`,
`D = diagonal eigenvalues`), setting `|W| = U·|D|·Uᴴ`, and establishes its three
structural properties: it is positive-semidefinite (hence Hermitian) and squares to
`W²` (so the kinetic term `Tr(W²·T)` is invariant under `W ↦ |W|`).

## Main definitions

* `hermitianAbs` — the spectral absolute value `|W| = U·|D|·Uᴴ` of a Hermitian `W`.

## Main results

* `hermitianAbs_posSemidef` — `|W|` is positive-semidefinite.
* `hermitianAbs_isHermitian` — `|W|` is Hermitian.
* `hermitianAbs_mul_self` — `|W|² = W²` (kinetic invariance).
* `hermitianAbs_sub_posSemidef` — `|W| − W` is positive-semidefinite
  (eigenvalues `|λᵢ| − λᵢ ≥ 0`).
* `hermitianAbs_commute` — `|W|` commutes with `W` (both diagonalize in the same
  eigenbasis).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.4, eq. (10.2.42); E. H. Lieb,
*Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectral absolute value `|W| = U·|D|·Uᴴ` of a Hermitian matrix `W = U·D·Uᴴ`
(`U = eigenvectorUnitary`, `D = diagonal eigenvalues`, `|D| = diagonal |eigenvalues|`). -/
noncomputable def hermitianAbs {W : Matrix n n ℂ} (hW : W.IsHermitian) : Matrix n n ℂ :=
  (hW.eigenvectorUnitary : Matrix n n ℂ) *
    Matrix.diagonal (RCLike.ofReal ∘ fun i => |hW.eigenvalues i|) *
    (hW.eigenvectorUnitary : Matrix n n ℂ)ᴴ

/-- `Uᴴ·U = 1` for the eigenvector unitary. -/
private theorem eigenvectorUnitary_conjTranspose_mul {W : Matrix n n ℂ}
    (hW : W.IsHermitian) :
    (hW.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hW.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
  have h := Matrix.mem_unitaryGroup_iff'.mp (SetLike.coe_mem hW.eigenvectorUnitary)
  rwa [Matrix.star_eq_conjTranspose] at h

/-- The spectral absolute value is positive-semidefinite. -/
theorem hermitianAbs_posSemidef {W : Matrix n n ℂ} (hW : W.IsHermitian) :
    (hermitianAbs hW).PosSemidef := by
  have hD : (Matrix.diagonal (RCLike.ofReal ∘ fun i => |hW.eigenvalues i|) :
      Matrix n n ℂ).PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    simp only [Function.comp_apply]
    exact RCLike.ofReal_nonneg.mpr (abs_nonneg (hW.eigenvalues i))
  simpa [hermitianAbs] using hD.mul_mul_conjTranspose_same (hW.eigenvectorUnitary : Matrix n n ℂ)

/-- The spectral absolute value is Hermitian. -/
theorem hermitianAbs_isHermitian {W : Matrix n n ℂ} (hW : W.IsHermitian) :
    (hermitianAbs hW).IsHermitian :=
  (hermitianAbs_posSemidef hW).isHermitian

/-- **The spectral absolute value squares to `W²`** (so the kinetic energy `Tr(W²T)`
is invariant under `W ↦ |W|`). -/
theorem hermitianAbs_mul_self {W : Matrix n n ℂ} (hW : W.IsHermitian) :
    hermitianAbs hW * hermitianAbs hW = W * W := by
  set U := (hW.eigenvectorUnitary : Matrix n n ℂ) with hU
  set absD : Matrix n n ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ fun i => |hW.eigenvalues i|) with hAbsD
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) with hD
  have hUU : Uᴴ * U = 1 := eigenvectorUnitary_conjTranspose_mul hW
  have hsq : absD * absD = D * D := by
    rw [hAbsD, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    exact_mod_cast abs_mul_abs_self (hW.eigenvalues i)
  have hWspec : W = U * D * Uᴴ := by
    conv_lhs => rw [hW.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hU, ← hD]
  have key : ∀ E : Matrix n n ℂ, U * E * Uᴴ * (U * E * Uᴴ) = U * (E * E) * Uᴴ := by
    intro E
    have h1 : U * E * Uᴴ * (U * E * Uᴴ) = U * E * (Uᴴ * U) * E * Uᴴ := by noncomm_ring
    rw [h1, hUU, Matrix.mul_one]
    noncomm_ring
  rw [hermitianAbs, ← hU, ← hAbsD, key, hsq, hWspec, key]

/-- **`|W| − W` is positive-semidefinite**: in the eigenbasis `W = U·D·Uᴴ` the
difference is `U·(|D|−D)·Uᴴ`, a unitary conjugate of the nonnegative diagonal `|D|−D`
(entries `|λᵢ| − λᵢ ≥ 0`). -/
theorem hermitianAbs_sub_posSemidef {W : Matrix n n ℂ} (hW : W.IsHermitian) :
    (hermitianAbs hW - W).PosSemidef := by
  set U := (hW.eigenvectorUnitary : Matrix n n ℂ) with hU
  set absD : Matrix n n ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ fun i => |hW.eigenvalues i|) with hAbsD
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) with hD
  have hWspec : W = U * D * Uᴴ := by
    conv_lhs => rw [hW.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hU, ← hD]
  have hdiff : hermitianAbs hW - W = U * (absD - D) * Uᴴ := by
    rw [hermitianAbs, ← hU, ← hAbsD, hWspec, Matrix.mul_sub, Matrix.sub_mul]
  have hPSD : (absD - D).PosSemidef := by
    rw [hAbsD, hD, Matrix.diagonal_sub]
    refine Matrix.PosSemidef.diagonal ?_
    intro i
    simp only [Function.comp_apply, ← RCLike.ofReal_sub]
    exact RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (le_abs_self (hW.eigenvalues i)))
  rw [hdiff]
  exact hPSD.mul_mul_conjTranspose_same U

/-- **`|W|` commutes with `W`**: both are functions of the same eigenbasis
(`|W| = U·|D|·Uᴴ`, `W = U·D·Uᴴ`) and the diagonal matrices `|D|`, `D` commute. -/
theorem hermitianAbs_commute {W : Matrix n n ℂ} (hW : W.IsHermitian) :
    hermitianAbs hW * W = W * hermitianAbs hW := by
  set U := (hW.eigenvectorUnitary : Matrix n n ℂ) with hU
  set absD : Matrix n n ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ fun i => |hW.eigenvalues i|) with hAbsD
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hW.eigenvalues) with hD
  have hUU : Uᴴ * U = 1 := eigenvectorUnitary_conjTranspose_mul hW
  have hWspec : W = U * D * Uᴴ := by
    conv_lhs => rw [hW.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hU, ← hD]
  have hcomm : absD * D = D * absD := by
    rw [hAbsD, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply]
    ring
  rw [hermitianAbs, ← hU, ← hAbsD, hWspec]
  have hL : U * absD * Uᴴ * (U * D * Uᴴ) = U * (absD * D) * Uᴴ := by
    have h1 : U * absD * Uᴴ * (U * D * Uᴴ) = U * absD * (Uᴴ * U) * D * Uᴴ := by noncomm_ring
    rw [h1, hUU, Matrix.mul_one]
    noncomm_ring
  have hR : U * D * Uᴴ * (U * absD * Uᴴ) = U * (D * absD) * Uᴴ := by
    have h1 : U * D * Uᴴ * (U * absD * Uᴴ) = U * D * (Uᴴ * U) * absD * Uᴴ := by noncomm_ring
    rw [h1, hUU, Matrix.mul_one]
    noncomm_ring
  rw [hL, hR, hcomm]

end LatticeSystem.Fermion
