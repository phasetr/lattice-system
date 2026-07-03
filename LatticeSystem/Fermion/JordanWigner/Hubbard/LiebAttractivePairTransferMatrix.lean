import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive
import LatticeSystem.Fermion.JordanWigner.CAR.CrossSiteOfNe

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

end LatticeSystem.Fermion
