import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticConj
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveGammaReflection
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockCoeffDown
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveKineticReal
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractivePHConjDiag

/-!
# The pair-transfer operator as a hop product / block transfer matrix (Tasaki §10.2.4)

First implementation layer toward discharging
`theorem_10_3_tian_pair_correlation_positive` (Tian's pair-correlation positivity for the
attractive Hubbard model, Tasaki Theorem 10.3).

The on-site pair-transfer operator `P_{x,y} = ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑}` is rewritten,
by pure Jordan–Wigner anticommutation in the **interleaved** (spinful) ordering, as a product of a
single up-spin hop and a single down-spin hop:
`P_{x,y} = (ĉ†_{x,↑} ĉ_{y,↑}) · (ĉ†_{x,↓} ĉ_{y,↓})` (`hubbardPairCorrelationOp_eq_hop_product`).
Moving the up annihilation `ĉ_{y,↑}` two anticommutations to the left crosses two strictly distinct
Jordan–Wigner modes (`(−1)² = +1`), so the sign is `+1` and the identity holds even for `x = y`.

The identification of this interleaved hop product with the **block-ordered** single-species
kinetic operators `hubbardBlockKineticUp` / `hubbardBlockKineticDown` (which the Theorem 10.2
coefficient machinery uses) is the subject of the companion conjugation lemma in this file
(`hubbardBlockToSpinful_conj_pairCorrelation`), obtained via the block ↔ interleaved permutation
operator `U = hubbardBlockToSpinfulPermutationOperator` and the single-hop conjugation identity
`permutationOperator_hop_conj_eq` (exactly analogous to `hubbardBlockKinetic_conj_eq`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.4, p. 372 (eq. (10.2.50)/(10.2.51)); E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201;
G.-S. Tian, *J. Phys. A* **27** (1994).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The pair-transfer operator is a product of a single up hop and a single down hop.**
In the interleaved (spinful) Jordan–Wigner ordering,
`ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑} = (ĉ†_{x,↑} ĉ_{y,↑}) · (ĉ†_{x,↓} ĉ_{y,↓})`.  The proof moves the
up annihilation `ĉ_{y,↑}` (mode `spinfulIndex y 0`) leftward past `ĉ_{y,↓}`
(mode `spinfulIndex y 1`) and `ĉ†_{x,↓}` (mode `spinfulIndex x 1`); both crossings are strictly
distinct modes (the spin labels `0` and `1` differ, so the indices differ even when `x = y`),
giving sign `(−1)² = +1`.
This is the interleaved-ordering step (L2a) toward the block transfer-matrix identity of
Tasaki §10.2.4 (Theorem 10.3). -/
theorem hubbardPairCorrelationOp_eq_hop_product (N : ℕ) (x y : Fin (N + 1)) :
    hubbardPairCorrelationOp N x y
      = (fermionUpCreation N x * fermionUpAnnihilation N y)
        * (fermionDownCreation N x * fermionDownAnnihilation N y) := by
  simp only [hubbardPairCorrelationOp, fermionUpCreation, fermionDownCreation,
    fermionUpAnnihilation, fermionDownAnnihilation]
  -- Abbreviations: `a = ĉ†_{x,↑}`, `b = ĉ†_{x,↓}`, `c = ĉ_{y,↓}`, `d = ĉ_{y,↑}`.
  set a := fermionMultiCreation (2 * N + 1) (spinfulIndex N x 0) with ha
  set b := fermionMultiCreation (2 * N + 1) (spinfulIndex N x 1) with hb
  set c := fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 1) with hc
  set d := fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 0) with hd
  -- `{ĉ_{y,↓}, ĉ_{y,↑}} = 0`: distinct modes `spinfulIndex y 1 ≠ spinfulIndex y 0`.
  have hne1 : spinfulIndex N y 1 ≠ spinfulIndex N y 0 := by
    rw [Ne, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)
  -- `{ĉ†_{x,↓}, ĉ_{y,↑}} = 0`: distinct modes `spinfulIndex x 1 ≠ spinfulIndex y 0`.
  have hne2 : spinfulIndex N x 1 ≠ spinfulIndex N y 0 := by
    rw [Ne, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)
  have hcd : c * d = -(d * c) := by
    rw [eq_neg_iff_add_eq_zero]; exact fermionMultiAnnihilation_anticomm_of_ne hne1
  have hbd : b * d = -(d * b) := by
    rw [eq_neg_iff_add_eq_zero]; exact fermionMultiCreation_annihilation_anticomm_of_ne hne2
  have h1 : b * (c * d) = -(b * (d * c)) := by rw [hcd, mul_neg]
  have h2 : b * (d * c) = -(d * (b * c)) := by
    rw [← mul_assoc, hbd, neg_mul, mul_assoc]
  have hmid : b * (c * d) = d * (b * c) := by rw [h1, h2]; exact neg_neg _
  rw [mul_assoc (a * b) c d, mul_assoc a b (c * d), hmid]
  exact (mul_assoc a d (b * c)).symm

/-- A single-entry up block kinetic operator collapses to one hop:
`hubbardBlockKineticUp N (single x y 1) = ĉ†_{block x,↑} ĉ_{block y,↑}`.  The double sum over the
single-entry matrix `Matrix.single x y 1` keeps only the `(i, j) = (x, y)` term. -/
private theorem hubbardBlockKineticUp_single (N : ℕ) (x y : Fin (N + 1)) :
    hubbardBlockKineticUp N (Matrix.single x y 1)
      = fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N x 0)
        * fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N y 0) := by
  rw [hubbardBlockKineticUp,
    Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
      (fun i _ hix => Finset.sum_eq_zero (fun j _ => by
        rw [Matrix.single_apply, if_neg (fun h => hix h.1.symm), zero_smul])),
    Finset.sum_eq_single_of_mem y (Finset.mem_univ y)
      (fun j _ hjy => by rw [Matrix.single_apply, if_neg (fun h => hjy h.2.symm), zero_smul]),
    Matrix.single_apply_same, one_smul]

/-- A single-entry down block kinetic operator collapses to one hop:
`hubbardBlockKineticDown N (single x y 1) = ĉ†_{block x,↓} ĉ_{block y,↓}`. -/
private theorem hubbardBlockKineticDown_single (N : ℕ) (x y : Fin (N + 1)) :
    hubbardBlockKineticDown N (Matrix.single x y 1)
      = fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N x 1)
        * fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N y 1) := by
  rw [hubbardBlockKineticDown,
    Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
      (fun i _ hix => Finset.sum_eq_zero (fun j _ => by
        rw [Matrix.single_apply, if_neg (fun h => hix h.1.symm), zero_smul])),
    Finset.sum_eq_single_of_mem y (Finset.mem_univ y)
      (fun j _ hjy => by rw [Matrix.single_apply, if_neg (fun h => hjy h.2.symm), zero_smul]),
    Matrix.single_apply_same, one_smul]

/-- **The block ↔ interleaved conjugate of the pair-transfer operator is the single-hop block
transfer product.**  Conjugating the pair-transfer operator by the block ↔ interleaved permutation
operator `U = hubbardBlockToSpinfulPermutationOperator N` (as in `hubbardBlockKinetic_conj_eq`)
sends the block-ordered product of a single up hop and a single down hop, at the single-entry
hopping `Matrix.single x y 1`, to the interleaved pair-transfer operator:
`U · (hubbardBlockKineticUp (single x y 1) · hubbardBlockKineticDown (single x y 1)) · Uᴴ
  = ĉ†_{x,↑} ĉ†_{x,↓} ĉ_{y,↓} ĉ_{y,↑}`.  Each hop is transported by the single-hop conjugation
identity `permutationOperator_hop_conj_eq` (with `π` sending `block i s ↦ spinful i s`), and the two
interleaved hops recombine into the pair-transfer operator by
`hubbardPairCorrelationOp_eq_hop_product`.  This is the index-matching step (L2b) of
Tasaki §10.2.4 (Theorem 10.3): it lets the Theorem 10.2 coefficient machinery (whose `blockWCoeff`
already carries the `Uᴴ` back-rotation) act on the pair-transfer operator through the block-ordered
single-species kinetic operators. -/
theorem hubbardBlockToSpinful_conj_pairCorrelation (N : ℕ) (x y : Fin (N + 1)) :
    hubbardBlockToSpinfulPermutationOperator N
        * (hubbardBlockKineticUp N (Matrix.single x y 1)
            * hubbardBlockKineticDown N (Matrix.single x y 1))
        * (hubbardBlockToSpinfulPermutationOperator N)ᴴ
      = hubbardPairCorrelationOp N x y := by
  set U := hubbardBlockToSpinfulPermutationOperator N with hU
  set P1 := fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N x 0)
    * fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N y 0) with hP1
  set P2 := fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N x 1)
    * fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N y 1) with hP2
  rw [hubbardBlockKineticUp_single, hubbardBlockKineticDown_single, ← hP1, ← hP2]
  have hUU : Uᴴ * U = 1 := hubbardBlockToSpinfulPermutationOperator_conjTranspose_mul N
  -- Split the conjugation across the product, inserting `Uᴴ · U = 1`.
  have key : P1 * P2 = P1 * Uᴴ * (U * P2) := by
    rw [Matrix.mul_assoc P1, ← Matrix.mul_assoc Uᴴ U P2, hUU, Matrix.one_mul]
  have hsplit : U * (P1 * P2) * Uᴴ = (U * P1 * Uᴴ) * (U * P2 * Uᴴ) := by
    rw [key]; simp only [Matrix.mul_assoc]
  -- Conjugate each single hop by `U = permutationOperator π` (`π : block i s ↦ spinful i s`).
  have hc1 : U * P1 * Uᴴ
      = fermionMultiCreation (2 * N + 1) (spinfulIndex N x 0)
        * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 0) := by
    rw [hU, hP1, hubbardBlockToSpinfulPermutationOperator, permutationOperator_hop_conj_eq,
      hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex,
      hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex]
  have hc2 : U * P2 * Uᴴ
      = fermionMultiCreation (2 * N + 1) (spinfulIndex N x 1)
        * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N y 1) := by
    rw [hU, hP2, hubbardBlockToSpinfulPermutationOperator, permutationOperator_hop_conj_eq,
      hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex,
      hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex]
  rw [hsplit, hc1, hc2, hubbardPairCorrelationOp_eq_hop_product]
  rfl

/-- **The pair-transfer operator acts on the reconciliation coefficient matrix as
`W ↦ S · W · Sᵀ`.**  With `S := hubbardBlockKineticUpFixedMatrix N (single x y 1)` the fixed
single-hop up-kinetic matrix and `W := blockWCoeff N ψ`,
`blockWCoeff N ((hubbardPairCorrelationOp N x y).mulVec ψ) = S · W · Sᵀ`.  The interleaved
pair-transfer operator is back-rotated by `Uᴴ` (absorbed in `blockWCoeff`) to the block-ordered hop
product `hubbardBlockKineticUp (single x y 1) · hubbardBlockKineticDown (single x y 1)`
(`hubbardBlockToSpinful_conj_pairCorrelation`); the up hop acts by left multiplication by `S`
(`hubbardBlockKineticUpCoeffAction_eq_mul_fixed`) and the down hop by right multiplication by the
fixed-right matrix `Bᵣ = Pₚₕ · Sᴴ · Pₚₕ`
(`hubbardBlockKineticDownFixedRightMatrix_eq_permConj_conjTranspose`); collapsing the
particle-hole gauge `Pₚₕ² = 1` and using `Sᴴ = Sᵀ` for the real single-entry hopping yields
`S · W · Sᵀ`.  This is step L3 of Tasaki §10.2.4 (Theorem 10.3). -/
theorem blockWCoeff_pairCorrelation_mulVec (N : ℕ) (x y : Fin (N + 1))
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    blockWCoeff N ((hubbardPairCorrelationOp N x y).mulVec ψ)
      = hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1) * blockWCoeff N ψ
        * (hubbardBlockKineticUpFixedMatrix N (Matrix.single x y 1))ᵀ := by
  have hSEreal : ∀ i j, star ((Matrix.single x y (1 : ℂ)) i j) = (Matrix.single x y 1) i j := by
    intro i j; rw [Matrix.single_apply]; split <;> simp
  -- Back-rotate `Uᴴ · P = (block up-hop · block down-hop) · Uᴴ` (from L2b).
  have hconj : (hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec
        ((hubbardPairCorrelationOp N x y).mulVec ψ)
      = (hubbardBlockKineticUp N (Matrix.single x y 1)
          * hubbardBlockKineticDown N (Matrix.single x y 1)).mulVec
          ((hubbardBlockToSpinfulPermutationOperator N)ᴴ.mulVec ψ) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [← hubbardBlockToSpinful_conj_pairCorrelation, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hubbardBlockToSpinfulPermutationOperator_conjTranspose_mul, Matrix.one_mul]
  rw [blockWCoeff, blockWCoeff, hconj, ← Matrix.mulVec_mulVec,
    hubbardBlockCoeff_hubbardBlockKineticUp_mulVec, hubbardBlockKineticUpCoeffAction_eq_mul_fixed,
    hubbardBlockCoeff_hubbardBlockKineticDown_mulVec,
    hubbardBlockKineticDownCoeffAction_eq_mul_fixedRight,
    hubbardBlockKineticDownFixedRightMatrix_eq_permConj_conjTranspose N hSEreal,
    hubbardBlockKineticUpFixedMatrix_conjTranspose_eq_transpose N hSEreal]
  simp only [Matrix.mul_assoc]
  rw [particleHoleConfigPermMatrix_mul_self, Matrix.mul_one]

end LatticeSystem.Fermion
