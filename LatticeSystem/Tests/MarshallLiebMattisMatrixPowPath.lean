import LatticeSystem.Quantum.MarshallLiebMattis.MatrixPowPath

/-!
# Test coverage for matrix-power positivity from a positive path
-/

namespace LatticeSystem.Tests.MarshallLiebMattisMatrixPowPath

open LatticeSystem.Math

/-- The main theorem signature exposes correctly. -/
example {B : Matrix (Fin 2) (Fin 2) ℝ}
    (hB_nn : ∀ i j, 0 ≤ B i j) (k : ℕ) (p : ℕ → Fin 2)
    (hpos : ∀ i ≤ k, 0 < B (p i) (p (i + 1))) :
    0 < (B ^ (k + 1)) (p 0) (p (k + 1)) :=
  matrix_pow_succ_pos_of_path hB_nn k p hpos

end LatticeSystem.Tests.MarshallLiebMattisMatrixPowPath
