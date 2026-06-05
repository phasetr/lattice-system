import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHermitian
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorBasis

/-!
# Tasaki 11.5: the t-J effective matrix in the site-state basis (Prop 11.24 PR-A)

The compression `M = Tᴴ Ĥ_tJ T` of the t-J Hamiltonian to the spin-charge-separated site-state
basis `|Φ_s⟩ = basisVec (tJConfigOf s)`, indexed by site-states `s : Fin (N+1) → Fin 3`
(`0 = empty`, `1 = ↑`, `2 = ↓`).  This is the finite real-symmetric matrix to which the
Perron–Frobenius theorem (A.18) is applied in the discharge of Proposition 11.24, mirroring the
Nagaoka §11.2 construction (`tasakiEffMatrix`).

`M` is Hermitian (the compression of the Hermitian `Ĥ_tJ`), and its entries are the matrix elements
`M_{s',s} = ⟨Φ_{s'} | Ĥ_tJ | Φ_s⟩`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The embedding `T` of the site-state basis into the many-body space: its column at the site-state
`s` is the computational basis vector `|Φ_s⟩ = basisVec (tJConfigOf s)`. -/
noncomputable def tJEmbedding (N : ℕ) :
    Matrix (Fin (2 * N + 2) → Fin 2) (Fin (N + 1) → Fin 3) ℂ :=
  Matrix.of (fun w s => basisVec (tJConfigOf N s) w)

/-- The site-state basis vectors are real-valued, so the embedding's conjugate-transpose entry
equals the embedding entry. -/
theorem tJEmbedding_star (N : ℕ) (s : Fin (N + 1) → Fin 3) (w : Fin (2 * N + 2) → Fin 2) :
    star (basisVec (tJConfigOf N s) w) = basisVec (tJConfigOf N s) w := by
  rw [basisVec_apply]; split <;> simp

/-- The **t-J effective matrix** `M = Tᴴ Ĥ_tJ T`: the finite matrix of `Ĥ_tJ` in the site-state
basis, indexed by `s : Fin (N+1) → Fin 3`. -/
noncomputable def tJEffMatrix (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) :
    Matrix (Fin (N + 1) → Fin 3) (Fin (N + 1) → Fin 3) ℂ :=
  (tJEmbedding N)ᴴ * tJHamiltonian N G τ J * tJEmbedding N

/-- `M` is Hermitian, being the compression `Tᴴ Ĥ_tJ T` of the Hermitian `Ĥ_tJ`. -/
theorem tJEffMatrix_isHermitian (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) : (tJEffMatrix N G τ J).IsHermitian := by
  change (tJEffMatrix N G τ J)ᴴ = tJEffMatrix N G τ J
  unfold tJEffMatrix
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, (tJHamiltonian_isHermitian N G τ J).eq, Matrix.mul_assoc]

/-- The entries of `M` are the matrix elements of `Ĥ_tJ`:
`M_{s',s} = ⟨Φ_{s'} | Ĥ_tJ | Φ_s⟩ = Σ_w Φ_{s'}(w) (Ĥ_tJ Φ_s)(w)` (real-bilinear pairing, using that
the basis states are real-valued). -/
theorem tJEffMatrix_apply (N : ℕ) (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (s' s : Fin (N + 1) → Fin 3) :
    tJEffMatrix N G τ J s' s =
      ∑ w, basisVec (tJConfigOf N s') w *
        ((tJHamiltonian N G τ J).mulVec (basisVec (tJConfigOf N s))) w := by
  unfold tJEffMatrix tJEmbedding
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Matrix.conjTranspose_apply, Matrix.of_apply, tJEmbedding_star]
  rfl

end LatticeSystem.Fermion
