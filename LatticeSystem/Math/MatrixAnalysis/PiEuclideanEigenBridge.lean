import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The Pi ⇄ `EuclideanSpace` matrix eigen-equation bridge (Theorem 10.4 arc, PR-14a)

Generic layer item for the Theorem 10.4 (Lieb repulsive Hubbard half-filling) discharge arc
(issue #5320, PR-14a). `hubbardGroundSubmoduleAtElectronNumber`
(`LatticeSystem/Fermion/JordanWigner/Hubbard/LiebRepulsive.lean`) lives on the plain function
carrier (Pi type, `Matrix.mulVecLin`), while every sector-machinery asset built for the arc so far
(`numberSpinZCasimirSectorEuclidean`, `exists_unique_casimir_sector_strict_min`,
`ham_su2_multiplet_companion`) is stated on `EuclideanSpace ℂ n` via `Matrix.toEuclideanLin`. This
file crosses that boundary **once**, as a single iff lemma, so PR-14a/14b need not repeat the
crossing at every use site.

## Main result

* `mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul` — `M.mulVec v = a • v` on the Pi carrier iff
  `Matrix.toEuclideanLin M (WithLp.toLp 2 v) = a • WithLp.toLp 2 v` on the `EuclideanSpace` carrier.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2 (Theorem 10.4), pp. 350–353.
-/

namespace LatticeSystem.Math

open Matrix

/-- **The Pi ⇄ `EuclideanSpace` eigen-equation bridge.** A matrix eigen-equation on the plain
function carrier `n → ℂ` (`Matrix.mulVec`) holds iff the corresponding eigen-equation holds on the
`EuclideanSpace ℂ n` carrier (`Matrix.toEuclideanLin`) after transporting the vector along
`WithLp.toLp 2`. Built from `Matrix.toLpLin_toLp` / `Matrix.toLin'_apply`
(`Mathlib/Analysis/InnerProductSpace/PiL2.lean`), the same identity already used inline in
`isHermitian_mulVec_eigenvalue_eq_ofReal` (`Math/CommutingHermitianEigenvector.lean:130`). -/
theorem mulVec_eq_smul_iff_toEuclideanLin_toLp_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (v : n → ℂ) (a : ℂ) :
    M.mulVec v = a • v ↔
      Matrix.toEuclideanLin M (WithLp.toLp 2 v) = a • (WithLp.toLp 2 v) := by
  have happ : Matrix.toEuclideanLin M (WithLp.toLp 2 v) = WithLp.toLp 2 (M.mulVec v) := by
    rw [show Matrix.toEuclideanLin M = Matrix.toLpLin 2 2 M from rfl, Matrix.toLpLin_toLp,
      Matrix.toLin'_apply]
  rw [happ, ← WithLp.toLp_smul]
  exact ((WithLp.toLp_injective 2).eq_iff).symm

end LatticeSystem.Math
