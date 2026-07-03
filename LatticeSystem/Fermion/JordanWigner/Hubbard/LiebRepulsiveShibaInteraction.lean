import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaUnitary
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsive
import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheoremCore
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePHConjDiag

/-!
# The Shiba particle-hole flip of the symmetric interaction (Tasaki §9.3.3, eq. (9.3.54))

Interaction layer (c5) of the axiom-free portion of **Tasaki Theorem 10.4** (Lieb's
theorem for the repulsive Hubbard model at half-filling), Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §9.3.3, p. 336.

The symmetric repulsive interaction
`Ĥint' = Σ_x U_x (n̂_{x↑} − ½)(n̂_{x↓} − ½)` (eq. (9.3.47)/(10.2.6)) is **diagonal**
in the Fock occupation basis, and the Shiba particle-hole flip on the down species
(`n̂_{x↓} ↦ 1 − n̂_{x↓}`, `shibaConfig`) sends `(n̂_{x↓} − ½) ↦ −(n̂_{x↓} − ½)`, so it
negates every summand:
`Ĥint'` conjugated by the Shiba permutation `P = shibaPermMatrix` equals `−Ĥint'`
(Tasaki eq. (9.3.54), interaction part, p. 336).

This is exactly the interaction half of the Shiba mapping `Û(Ĥhop + Ĥint')Û = Ĥhop − Ĥint'`.
The full Shiba unitary `Û = diagonal(sign)·P` (with the sublattice gauge and the
Jordan–Wigner down-flip parity in `sign`) has `Û(Ĥint')Û = −Ĥint'` too, because the
diagonal `sign` commutes with the diagonal `Ĥint'` and has modulus one; that
sign-dressed version is added in the kinetic layer (c4), where the sign is needed to
also fix the kinetic term.  This file supplies the sign-independent core.

## Main definitions

* `symmetricRepulsiveInteractionDiag` — the diagonal entry function of `Ĥint'`.
* `shibaSignedUnitary` — the sign-dressed Shiba unitary `Û = diagonal(s)·P`
  (Tasaki eq. (9.3.50)).

## Main results

* `fermionMultiNumber_eq_diagonal` — a site-occupation number operator is diagonal.
* `symmetricRepulsiveHubbardInteraction_eq_diagonal` — `Ĥint'` is a diagonal matrix.
* `symmetricRepulsiveInteractionDiag_shibaConfig` — the diagonal entries negate under
  the Shiba flip.
* `shibaPermMatrix_conj_symmetricInteraction` — `P·Ĥint'·P = −Ĥint'`
  (Tasaki eq. (9.3.54), interaction part).
* `shibaSignedUnitary_conjTranspose_mul_self` — `Ûᴴ·Û = 1` (unitarity).
* `shibaSignedUnitary_self_mul_conjTranspose` — `Û·Ûᴴ = 1` (unitarity).
* `shibaSignedUnitary_conj_symmetricInteraction` — `Ûᴴ·Ĥint'·Û = −Ĥint'`
  (Tasaki eq. (9.3.54), interaction part, sign-dressed form).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §9.3.3, eqs. (9.3.47)/(9.3.54), pp. 334–336;
E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## The number operators and the symmetric interaction are diagonal -/

/-- A site-occupation number operator is diagonal in the Fock occupation basis, with
entry the occupation of the corresponding mode:
`n̂_j = diagonal (c ↦ c j)`. -/
theorem fermionMultiNumber_eq_diagonal (M : ℕ) (j : Fin (M + 1)) :
    fermionMultiNumber M j = Matrix.diagonal (fun c => ((c j).val : ℂ)) := by
  funext τ ρ
  have h1 : (fermionMultiNumber M j).mulVec (basisVec ρ) τ = fermionMultiNumber M j τ ρ := by
    simp only [Matrix.mulVec, dotProduct]
    exact sum_mul_basisVec ρ (fun k => fermionMultiNumber M j τ k)
  rw [← h1, fermionMultiNumber_mulVec_basisVec, Pi.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply]
  by_cases h : τ = ρ
  · subst h; rw [basisVec_self, mul_one, if_pos rfl]
  · rw [basisVec_of_ne h, mul_zero, if_neg h]

/-- The diagonal entry function of the symmetric repulsive interaction `Ĥint'`
(Tasaki eq. (9.3.47)/(10.2.6)):
`c ↦ Σ_x U_x (c(2x) − ½)(c(2x+1) − ½)`. -/
noncomputable def symmetricRepulsiveInteractionDiag (N : ℕ) (U : Fin (N + 1) → ℝ)
    (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  ∑ x : Fin (N + 1), (U x : ℂ) *
    ((((c (spinfulIndex N x 0)).val : ℂ) - 1 / 2) *
      (((c (spinfulIndex N x 1)).val : ℂ) - 1 / 2))

/-- The symmetric repulsive interaction is diagonal in the Fock occupation basis:
`Ĥint' = diagonal (symmetricRepulsiveInteractionDiag)`. -/
theorem symmetricRepulsiveHubbardInteraction_eq_diagonal (U : Fin (N + 1) → ℝ) :
    symmetricRepulsiveHubbardInteraction N U
      = Matrix.diagonal (symmetricRepulsiveInteractionDiag N U) := by
  have hcentered : ∀ (j : Fin (2 * N + 1 + 1)),
      fermionMultiNumber (2 * N + 1) j - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2)))
        = Matrix.diagonal (fun c => ((c j).val : ℂ) - 1 / 2) := by
    intro j
    rw [fermionMultiNumber_eq_diagonal]
    ext τ ρ
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
      smul_eq_mul]
    by_cases h : τ = ρ
    · subst h; simp
    · simp [h]
  have hterm : ∀ x : Fin (N + 1),
      (U x : ℂ) • ((fermionUpNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2)))) *
          (fermionDownNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2)))))
        = Matrix.diagonal (fun c => (U x : ℂ) *
            ((((c (spinfulIndex N x 0)).val : ℂ) - 1 / 2) *
              (((c (spinfulIndex N x 1)).val : ℂ) - 1 / 2))) := by
    intro x
    rw [fermionUpNumber, fermionDownNumber, hcentered, hcentered, diagonal_mul_diagonal,
      ← diagonal_smul]
    congr 1
  funext τ ρ
  rw [symmetricRepulsiveHubbardInteraction, Matrix.sum_apply]
  simp only [hterm, Matrix.diagonal_apply]
  by_cases h : τ = ρ
  · simp only [if_pos h, symmetricRepulsiveInteractionDiag]
  · simp only [if_neg h, Finset.sum_const_zero]

/-! ## The Shiba flip negates the diagonal entries -/

/-- The Shiba flip fixes the up-mode occupation: `shibaConfig c (2x) = c (2x)`. -/
theorem shibaConfig_apply_up (c : Fin (2 * N + 2) → Fin 2) (x : Fin (N + 1)) :
    shibaConfig N c (spinfulIndex N x 0) = c (spinfulIndex N x 0) := by
  simp only [shibaConfig, hubbardMergeConfig_spinfulIndex_zero, hubbardUpConfig]

/-- The Shiba flip flips the down-mode occupation:
`shibaConfig c (2x+1) = flip (c (2x+1))`. -/
theorem shibaConfig_apply_down (c : Fin (2 * N + 2) → Fin 2) (x : Fin (N + 1)) :
    shibaConfig N c (spinfulIndex N x 1) = flipOccupation (c (spinfulIndex N x 1)) := by
  simp only [shibaConfig, hubbardMergeConfig_spinfulIndex_one, particleHoleConfig,
    hubbardDownConfig]

/-- **The Shiba flip negates the interaction diagonal** (Tasaki eq. (9.3.54),
interaction part, p. 336): under `n̂_{x↓} ↦ 1 − n̂_{x↓}` each factor `(n̂_{x↓} − ½)`
flips sign while `(n̂_{x↑} − ½)` is untouched, so every summand is negated. -/
theorem symmetricRepulsiveInteractionDiag_shibaConfig (U : Fin (N + 1) → ℝ)
    (c : Fin (2 * N + 2) → Fin 2) :
    symmetricRepulsiveInteractionDiag N U (shibaConfig N c)
      = -symmetricRepulsiveInteractionDiag N U c := by
  rw [symmetricRepulsiveInteractionDiag, symmetricRepulsiveInteractionDiag,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [shibaConfig_apply_up, shibaConfig_apply_down, flipOccupation_val_complex]
  ring

/-! ## The interaction sign flip via the Shiba permutation -/

/-- **The Shiba permutation flips the sign of the symmetric interaction**
(Tasaki eq. (9.3.54), interaction part, p. 336):
`P·Ĥint'·P = −Ĥint'`.  Since `Ĥint'` is diagonal, conjugating by the Shiba
permutation reindexes its diagonal by the flip, which negates every entry. -/
theorem shibaPermMatrix_conj_symmetricInteraction (U : Fin (N + 1) → ℝ) :
    shibaPermMatrix N * symmetricRepulsiveHubbardInteraction N U * shibaPermMatrix N
      = -symmetricRepulsiveHubbardInteraction N U := by
  rw [symmetricRepulsiveHubbardInteraction_eq_diagonal, shibaPermMatrix_conj_diagonal,
    diagonal_neg]
  congr 1
  funext k
  exact symmetricRepulsiveInteractionDiag_shibaConfig U k

/-! ## The sign-dressed Shiba unitary and the interaction conjugation -/

/-- The **sign-dressed Shiba unitary** `Û = diagonal(s)·P` (Tasaki eq. (9.3.50)):
the Shiba permutation `P = shibaPermMatrix` dressed by a diagonal sign function `s`.
The full Shiba transformation takes `s` to be the sublattice gauge times the
Jordan–Wigner down-flip parity (that specific value is fixed in the kinetic layer,
c4); the results here hold for **any** modulus-one `s`, since the interaction
conjugation only uses `|s| = 1`. -/
noncomputable def shibaSignedUnitary (N : ℕ) (s : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ :=
  Matrix.diagonal s * shibaPermMatrix N

/-- The conjugate transpose of the sign-dressed Shiba unitary:
`Ûᴴ = P·diagonal(s̄)` (using `Pᴴ = P`). -/
theorem shibaSignedUnitary_conjTranspose (s : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    Matrix.conjTranspose (shibaSignedUnitary N s)
      = shibaPermMatrix N * Matrix.diagonal (star s) := by
  rw [shibaSignedUnitary, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose,
    shibaPermMatrix_isHermitian.eq]

/-- **The sign-dressed Shiba unitary is unitary** when `s` has modulus one
(`s̄·s = 1`): `Ûᴴ·Û = 1` (Tasaki eq. (9.3.50)).  The signs cancel
(`diagonal (s̄)·diagonal s = 1`) and the permutation part squares to the identity. -/
theorem shibaSignedUnitary_conjTranspose_mul_self
    (s : (Fin (2 * N + 2) → Fin 2) → ℂ) (hs : ∀ c, star (s c) * s c = 1) :
    Matrix.conjTranspose (shibaSignedUnitary N s) * shibaSignedUnitary N s = 1 := by
  rw [shibaSignedUnitary_conjTranspose, shibaSignedUnitary,
    show shibaPermMatrix N * Matrix.diagonal (star s) * (Matrix.diagonal s * shibaPermMatrix N)
        = shibaPermMatrix N * (Matrix.diagonal (star s) * Matrix.diagonal s) * shibaPermMatrix N
      from by simp only [Matrix.mul_assoc],
    diagonal_mul_diagonal,
    show (fun c => (star s) c * s c) = (fun _ => (1 : ℂ)) from by
      funext c; simp only [Pi.star_apply]; exact hs c,
    diagonal_one, Matrix.mul_one, shibaPermMatrix_mul_self]

/-- **The sign-dressed Shiba unitary is unitary on the other side** when `s` has
modulus one (`s̄·s = 1`): `Û·Ûᴴ = 1` (Tasaki eq. (9.3.50)).  Symmetric to
`shibaSignedUnitary_conjTranspose_mul_self`: the permutation part squares to the
identity and the signs `s·s̄ = 1` cancel. -/
theorem shibaSignedUnitary_self_mul_conjTranspose
    (s : (Fin (2 * N + 2) → Fin 2) → ℂ) (hs : ∀ c, star (s c) * s c = 1) :
    shibaSignedUnitary N s * Matrix.conjTranspose (shibaSignedUnitary N s) = 1 := by
  rw [shibaSignedUnitary_conjTranspose, shibaSignedUnitary,
    show Matrix.diagonal s * shibaPermMatrix N * (shibaPermMatrix N * Matrix.diagonal (star s))
        = Matrix.diagonal s * (shibaPermMatrix N * shibaPermMatrix N) * Matrix.diagonal (star s)
      from by simp only [Matrix.mul_assoc],
    shibaPermMatrix_mul_self, Matrix.mul_one, diagonal_mul_diagonal,
    show (fun c => s c * (star s) c) = (fun _ => (1 : ℂ)) from by
      funext c; simp only [Pi.star_apply]
      rw [mul_comm]; exact hs c,
    diagonal_one]

/-- **The sign-dressed Shiba unitary flips the sign of the symmetric interaction**
(Tasaki eq. (9.3.54), interaction part, p. 336): `Ûᴴ·Ĥint'·Û = −Ĥint'`.  The
diagonal sign `s` and the diagonal `Ĥint'` commute and `|s| = 1`, so the sign
cancels and the statement reduces to the bare-permutation version. -/
theorem shibaSignedUnitary_conj_symmetricInteraction
    (s : (Fin (2 * N + 2) → Fin 2) → ℂ) (hs : ∀ c, star (s c) * s c = 1)
    (U : Fin (N + 1) → ℝ) :
    Matrix.conjTranspose (shibaSignedUnitary N s)
        * symmetricRepulsiveHubbardInteraction N U * shibaSignedUnitary N s
      = -symmetricRepulsiveHubbardInteraction N U := by
  rw [symmetricRepulsiveHubbardInteraction_eq_diagonal, shibaSignedUnitary_conjTranspose,
    shibaSignedUnitary,
    show shibaPermMatrix N * Matrix.diagonal (star s)
          * Matrix.diagonal (symmetricRepulsiveInteractionDiag N U)
          * (Matrix.diagonal s * shibaPermMatrix N)
        = shibaPermMatrix N
          * (Matrix.diagonal (star s)
              * Matrix.diagonal (symmetricRepulsiveInteractionDiag N U) * Matrix.diagonal s)
          * shibaPermMatrix N from by simp only [Matrix.mul_assoc],
    diagonal_mul_diagonal, diagonal_mul_diagonal,
    show (fun c => (star s) c * symmetricRepulsiveInteractionDiag N U c * s c)
          = symmetricRepulsiveInteractionDiag N U from by
      funext c
      simp only [Pi.star_apply]
      rw [show star (s c) * symmetricRepulsiveInteractionDiag N U c * s c
            = symmetricRepulsiveInteractionDiag N U c * (star (s c) * s c) from by ring,
        hs c, mul_one],
    ← symmetricRepulsiveHubbardInteraction_eq_diagonal,
    shibaPermMatrix_conj_symmetricInteraction]

end LatticeSystem.Fermion
