import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaKinetic
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive

/-!
# The full Shiba conjugation repulsive → attractive (Tasaki §10.2.2, eq. (10.2.10))

Conjugation layer (c6) of the axiom-free portion of **Tasaki Theorem 10.4** (Lieb's
theorem for the repulsive Hubbard model at half-filling), Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.2, pp. 350–352.

Combining the kinetic invariance (c4, `shibaSignedUnitary_conj_symmetricKinetic`,
eq. (9.3.52)) and the interaction sign flip (c5,
`shibaSignedUnitary_conj_symmetricInteraction`, eq. (9.3.54)), the Shiba unitary sends
the symmetric **repulsive** Hubbard Hamiltonian to an **attractive** one:
`Ûᴴ (Ĥhop + Ĥint') Û = Ĥhop − Ĥint'` (Tasaki eq. (10.2.10), p. 352).

The chemical shift produced when `−Ĥint'` is re-expressed through the attractive
interaction is absorbed into the hopping diagonal (Tasaki eq. (10.2.11), p. 352):
`−Ĥint' = Ĥatt-int + Σ_x (U_x/2)(n̂_{x↑}+n̂_{x↓}) − ¼ Σ_x U_x`,
so the conjugate equals `attractiveHubbardHamiltonian (T + diag(U/2)) U` minus the
scalar `¼ Σ_x U_x`.  (The constant is **negative**: expanding
`(n̂↑−½)(n̂↓−½) = n̂↑n̂↓ − ½(n̂↑+n̂↓) + ¼` gives `−¼` in `−Ĥint'`.)

## Main results

* `symmetricHubbardOnSite_expand` — the per-site expansion
  `(n̂↑−½)(n̂↓−½) = n̂↑n̂↓ − ½n̂↑ − ½n̂↓ + ¼`.
* `hubbardKinetic_add` — additivity of the kinetic operator in the hopping matrix.
* `hubbardKinetic_diagonal` — the kinetic operator of a diagonal hopping is the
  weighted sum of on-site number operators.
* `neg_symmetricRepulsiveInteraction_eq` — `−Ĥint'` re-expressed as attractive
  interaction plus chemical potential minus a constant (Tasaki eq. (10.2.11)).
* `shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive` — the full conjugation
  `Ûᴴ Ĥ^rep Û = attractive (T + diag(U/2)) U − ¼Σ U` (Tasaki eq. (10.2.10)).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §§9.3.3/10.2.2, eqs. (9.3.52)/(9.3.54)/(10.2.10)/(10.2.11),
pp. 336, 350–352; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## Algebraic helpers -/

/-- **The symmetric on-site expansion** (Tasaki eq. (10.2.11), per site): centring the
number operators and multiplying,
`(n̂_{x↑}−½)(n̂_{x↓}−½) = n̂_{x↑}n̂_{x↓} − ½n̂_{x↑} − ½n̂_{x↓} + ¼`.  The identity `1` is
central, so this is a plain distributive expansion. -/
theorem symmetricHubbardOnSite_expand (x : Fin (N + 1)) :
    (fermionUpNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2))))
        * (fermionDownNumber N x - (1 / 2 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2))))
      = fermionUpNumber N x * fermionDownNumber N x
        - (1 / 2 : ℂ) • fermionUpNumber N x - (1 / 2 : ℂ) • fermionDownNumber N x
        + (1 / 4 : ℂ) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
  rw [sub_mul, mul_sub, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one,
    mul_smul_comm, mul_one, smul_smul]
  norm_num
  abel

/-- **Additivity of the kinetic operator** in the hopping matrix:
`Ĥhop(a + b) = Ĥhop(a) + Ĥhop(b)`.  Each summand `t_{ij} • c†c` is linear in `t`. -/
theorem hubbardKinetic_add (a b : Fin (N + 1) → Fin (N + 1) → ℂ) :
    hubbardKinetic N (fun x y => a x y + b x y)
      = hubbardKinetic N a + hubbardKinetic N b := by
  rw [hubbardKinetic, hubbardKinetic, hubbardKinetic, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [add_smul]

/-- **The kinetic operator of a diagonal hopping is a weighted number operator**
(chemical-potential term): `Ĥhop(diagonal μ) = Σ_x μ_x (n̂_{x↑}+n̂_{x↓})`.  Off-diagonal
entries vanish, and the two spin sectors give the up and down number operators. -/
theorem hubbardKinetic_diagonal (μ : Fin (N + 1) → ℂ) :
    hubbardKinetic N (fun x y => (Matrix.diagonal μ) x y)
      = ∑ x : Fin (N + 1), μ x • (fermionUpNumber N x + fermionDownNumber N x) := by
  rw [hubbardKinetic]
  have hinner : ∀ (σ : Fin 2) (i : Fin (N + 1)),
      (∑ j : Fin (N + 1), (Matrix.diagonal μ) i j •
        (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ)
          * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)))
        = μ i • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ)
          * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N i σ)) := by
    intro σ i
    rw [Finset.sum_congr rfl (fun j _ => by rw [Matrix.diagonal_apply])]
    simp only [ite_smul, zero_smul]
    rw [Finset.sum_ite_eq Finset.univ i
      (fun j => μ i • (fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ)
        * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ))), if_pos (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun i _ => hinner σ i)),
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fin.sum_univ_two, ← smul_add, fermionUpNumber, fermionDownNumber, fermionMultiNumber,
    fermionMultiNumber]

/-! ## The interaction bridge (Tasaki eq. (10.2.11)) -/

/-- **The negated symmetric interaction as attractive interaction plus chemical
potential** (Tasaki eq. (10.2.11), p. 352):
`−Ĥint' = Ĥatt-int + Σ_x (U_x/2)(n̂_{x↑}+n̂_{x↓}) − ¼ Σ_x U_x`.  Expanding each summand
of `Ĥint'` by `symmetricHubbardOnSite_expand` and negating splits into the attractive
density-density term `−U_x n̂↑n̂↓`, the chemical potential `(U_x/2)(n̂↑+n̂↓)`, and the
constant `−(U_x/4)`. -/
theorem neg_symmetricRepulsiveInteraction_eq (U : Fin (N + 1) → ℝ) :
    - symmetricRepulsiveHubbardInteraction N U
      = attractiveHubbardInteraction N U
        + (∑ x : Fin (N + 1),
            ((U x : ℂ) / 2) • (fermionUpNumber N x + fermionDownNumber N x))
        - ((∑ x : Fin (N + 1), (U x : ℂ)) / 4)
            • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
  rw [symmetricRepulsiveHubbardInteraction, ← Finset.sum_neg_distrib,
    attractiveHubbardInteraction, hubbardOnSiteInteractionSite, Finset.sum_div,
    Finset.sum_smul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [symmetricHubbardOnSite_expand]
  module

/-! ## The full conjugation (Tasaki eq. (10.2.10)) -/

/-- **The full Shiba conjugation sends the symmetric repulsive Hamiltonian to an
attractive one** (Tasaki eq. (10.2.10), p. 352):
`Ûᴴ (Ĥhop + Ĥint') Û = attractiveHubbardHamiltonian (T + diag(U/2)) U − ¼ Σ_x U_x`.
The kinetic term is invariant (c4), the interaction reverses sign (c5), and the
chemical shift of `−Ĥint'` is absorbed into the hopping diagonal
(`neg_symmetricRepulsiveInteraction_eq`, eq. (10.2.11)), leaving the negative scalar
`−¼ Σ_x U_x`.  This is the operator identity behind the balanced-sector ground-state
transport in Theorem 10.4 (`Ĥ^att = Û Ĥ^rep Ûᴴ`). -/
theorem shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hsymm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * symmetricRepulsiveHubbardHamiltonian N T U
        * shibaSignedUnitary N (shibaSignFn A)
      = attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U
        - ((∑ x : Fin (N + 1), (U x : ℂ)) / 4)
            • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
  have hfun : (fun x y => ((T + Matrix.diagonal (fun z => U z / 2)) x y : ℂ))
      = (fun x y => (T x y : ℂ) + (Matrix.diagonal (fun z => (U z : ℂ) / 2)) x y) := by
    funext x y
    rw [Matrix.add_apply, Complex.ofReal_add, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos hxy]; push_cast; ring
    · rw [if_neg hxy, if_neg hxy]; push_cast; ring
  have hsplit : hubbardKinetic N (fun x y => ((T + Matrix.diagonal (fun z => U z / 2)) x y : ℂ))
      = hubbardKinetic N (fun x y => (T x y : ℂ))
        + ∑ x : Fin (N + 1),
            ((U x : ℂ) / 2) • (fermionUpNumber N x + fermionDownNumber N x) := by
    rw [hfun, hubbardKinetic_add, hubbardKinetic_diagonal]
  rw [symmetricRepulsiveHubbardHamiltonian, Matrix.mul_add, Matrix.add_mul,
    shibaSignedUnitary_conj_symmetricKinetic hsymm hbip,
    shibaSignedUnitary_conj_symmetricInteraction (shibaSignFn A)
      (shibaSignFn_star_mul_self A) U,
    neg_symmetricRepulsiveInteraction_eq, attractiveHubbardHamiltonian, hsplit]
  abel

end LatticeSystem.Fermion
