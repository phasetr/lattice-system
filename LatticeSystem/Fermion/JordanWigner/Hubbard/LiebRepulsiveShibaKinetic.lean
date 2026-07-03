import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaInteraction
import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopActionCore
import LatticeSystem.Fermion.JordanWigner.HopBasisVec

/-!
# The Shiba down-kinetic conjugation of the symmetric kinetic term (Tasaki §9.3.3, eq. (9.3.52))

Kinetic layer (c4) of the axiom-free portion of **Tasaki Theorem 10.4** (Lieb's
theorem for the repulsive Hubbard model at half-filling), Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §9.3.3, pp. 334–336.

The Shiba transformation leaves the kinetic term **invariant** (Tasaki eq. (9.3.52),
p. 336):
`Ûᴴ Ĥhop Û = Ĥhop`.
The mechanism (p. 336) is that on a bipartite bond `x∈A, y∈B` the particle-hole flip
turns `ĉ†_{x} ĉ_{y}` into `ĉ_{x} ĉ†_{y} = −ĉ†_{y} ĉ_{x}` (CAR sign `−1`, eq. (9.3.43))
while the sublattice gauge contributes `ε_x ε_y = (+1)(−1) = −1`; the two `−1`'s
multiply to `+1`, and the real symmetry `t_{x,y} = t_{y,x}` restores the term.

This file supplies:

* the sublattice gauge `gaugeSign` and its bond-cancellation `gaugeSign_mul_of_bipartite`;
* the down-flip gauge factor `shibaGauge`;
* the **mechanical conjugation reductions** `shibaPermMatrix_conj_apply` (general matrix
  version of `shibaPermMatrix_conj_diagonal`) and `shibaSignedUnitary_conj_apply`, which
  express the conjugated matrix entry `(Ûᴴ M Û)(i,j) = s̄(σi)·M(σi,σj)·s(σj)`
  (`σ = shibaConfig`).

## Main definitions

* `gaugeSign` — the sublattice gauge factor `ε_x = +1 (x∈A), −1 (x∈Aᶜ)`.
* `shibaGauge` — the down-flip sublattice gauge factor of a configuration.

## Main results

* `gaugeSign_mul_of_bipartite` — `ε_x ε_y = −1` on a bipartite bond.
* `shibaPermMatrix_conj_apply` — `(P·M·P)(i,j) = M(σi, σj)`.
* `shibaSignedUnitary_conj_apply` — `(Ûᴴ·M·Û)(i,j) = s̄(σi)·M(σi,σj)·s(σj)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §9.3.3, eqs. (9.3.43)/(9.3.52), pp. 334–336;
E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum PEquiv
open scoped BigOperators

variable {N : ℕ}

/-! ## The sublattice gauge and its bond cancellation -/

/-- The **sublattice gauge factor** `ε_x = +1` for `x∈A`, `−1` for `x∈Aᶜ`
(Tasaki eq. (9.3.49)/(9.3.51), the `(−1)^x` gauge, p. 336). -/
def gaugeSign (A : Finset (Fin (N + 1))) (x : Fin (N + 1)) : ℂ :=
  if x ∈ A then 1 else -1

/-- **Bond cancellation of the gauge on a bipartite bond** (Tasaki p. 336): if
`T x y ≠ 0` then `x` and `y` lie in different sublattices, so
`ε_x ε_y = (+1)(−1) = −1`. -/
theorem gaugeSign_mul_of_bipartite {A : Finset (Fin (N + 1))}
    {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ} (hbip : HoppingRespectsBipartition A T)
    {x y : Fin (N + 1)} (h : T x y ≠ 0) :
    gaugeSign A x * gaugeSign A y = -1 := by
  have hiff : x ∈ A ↔ y ∉ A := hbip h
  unfold gaugeSign
  by_cases hx : x ∈ A
  · have hy : y ∉ A := hiff.mp hx
    rw [if_pos hx, if_neg hy]; ring
  · have hy : y ∈ A := by
      by_contra hy'
      exact hx (hiff.mpr hy')
    rw [if_neg hx, if_pos hy]; ring

/-- The **down-flip sublattice gauge factor** of a configuration `c` (Tasaki
eq. (9.3.50), the gauge part of the Shiba sign): the product over `x∈Aᶜ` of the
occupation sign of the down mode `2x+1`, `∏_{x∈Aᶜ} (−1)^{c(2x+1)}`. -/
noncomputable def shibaGauge (A : Finset (Fin (N + 1))) (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  ∏ x ∈ bipartitionComplement A,
    (if c (spinfulIndex N x 1) = 0 then (1 : ℂ) else -1)

/-- The **single-species Jordan–Wigner crossing parity** at spin `r`: the product
over the occupied spin-`r` modes `spinfulIndex x r` of `(−1)^x` (Tasaki eq. (9.3.50),
string part).  This is the sign the diagonal dressing must supply on a spin-`r` hop so
that the flipped-down crossing factor `(−1)^{p+q}` is cancelled. -/
noncomputable def shibaCrossingSpecies (N : ℕ) (r : Fin 2)
    (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  ∏ x : Fin (N + 1), (if c (spinfulIndex N x r) = 1 then (-1 : ℂ) ^ (x : ℕ) else 1)

/-- The **Jordan–Wigner crossing parity** of a configuration `c` (Tasaki eq. (9.3.50),
string part of the Shiba sign): the product over **all** occupied modes of `(−1)^{site}`,
`∏_{k : c k = 1} (−1)^{⌊k/2⌋}`, realised as the product of the up (`r=0`) and down
(`r=1`) single-species crossing parities.

Both species are needed: the up factor cancels the crossing sign of an up hop and the
down factor cancels that of a down hop (the Shiba flip acts on the down species, so a
down hop also picks up a `(−1)^{p+q}` crossing sign that the down factor cancels). -/
noncomputable def shibaJwFlipParity (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 1 c

/-- The **concrete Shiba sign** `s = (Jordan–Wigner crossing parity) × (sublattice
gauge)` (Tasaki eq. (9.3.50), p. 336): the specific diagonal sign that dresses the
Shiba permutation into the full Shiba unitary `Û = diagonal(s)·P` so that
`Ûᴴ Ĥhop Û = Ĥhop` (kinetic invariance, eq. (9.3.52)). -/
noncomputable def shibaSignFn (A : Finset (Fin (N + 1)))
    (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  shibaJwFlipParity N c * shibaGauge A c

/-- The single-species crossing parity is real: `star (cs r c) = cs r c`. -/
private theorem shibaCrossingSpecies_star (r : Fin 2) (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaCrossingSpecies N r c) = shibaCrossingSpecies N r c := by
  rw [shibaCrossingSpecies, star_prod]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  by_cases h : c (spinfulIndex N x r) = 1
  · rw [if_pos h, star_pow, star_neg, star_one]
  · rw [if_neg h, star_one]

/-- The single-species crossing parity squares to one: `cs r c · cs r c = 1`. -/
private theorem shibaCrossingSpecies_sq (r : Fin 2) (c : Fin (2 * N + 2) → Fin 2) :
    shibaCrossingSpecies N r c * shibaCrossingSpecies N r c = 1 := by
  rw [shibaCrossingSpecies, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun x _ => ?_)
  by_cases h : c (spinfulIndex N x r) = 1
  · rw [if_pos h, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · rw [if_neg h, mul_one]

/-- The crossing parity has modulus one: `s̄ s = 1`. -/
theorem shibaJwFlipParity_star_mul_self (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaJwFlipParity N c) * shibaJwFlipParity N c = 1 := by
  rw [shibaJwFlipParity, star_mul', shibaCrossingSpecies_star, shibaCrossingSpecies_star,
    show shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 1 c
        * (shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 1 c)
      = (shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 0 c)
        * (shibaCrossingSpecies N 1 c * shibaCrossingSpecies N 1 c) from by ring,
    shibaCrossingSpecies_sq, shibaCrossingSpecies_sq, mul_one]

/-- The sublattice gauge factor has modulus one: `s̄ s = 1`. -/
theorem shibaGauge_star_mul_self (A : Finset (Fin (N + 1)))
    (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaGauge A c) * shibaGauge A c = 1 := by
  rw [shibaGauge, star_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun x _ => ?_)
  by_cases h : c (spinfulIndex N x 1) = 0
  · rw [if_pos h, star_one, mul_one]
  · rw [if_neg h, star_neg, star_one]; ring

/-- **The concrete Shiba sign has modulus one** (Tasaki eq. (9.3.50)): `s̄ s = 1`.
This is exactly the hypothesis `hs` required by the interaction conjugation
`shibaSignedUnitary_conj_symmetricInteraction`, so the same `s` fixes both the
kinetic term (this file) and the interaction term (c5). -/
theorem shibaSignFn_star_mul_self (A : Finset (Fin (N + 1)))
    (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaSignFn A c) * shibaSignFn A c = 1 := by
  rw [shibaSignFn, star_mul']
  rw [show star (shibaJwFlipParity N c) * star (shibaGauge A c)
        * (shibaJwFlipParity N c * shibaGauge A c)
      = (star (shibaJwFlipParity N c) * shibaJwFlipParity N c)
        * (star (shibaGauge A c) * shibaGauge A c) from by ring,
    shibaJwFlipParity_star_mul_self, shibaGauge_star_mul_self, mul_one]

/-! ## Mechanical conjugation reductions -/

/-- **General-matrix Shiba permutation conjugation** (the non-diagonal analogue of
`shibaPermMatrix_conj_diagonal`): conjugating any matrix `M` by the Shiba permutation
reindexes both arguments by the involution `σ = shibaConfig`,
`(P·M·P)(i,j) = M(σi, σj)`. -/
theorem shibaPermMatrix_conj_apply
    (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ)
    (i j : Fin (2 * N + 2) → Fin 2) :
    (shibaPermMatrix N * M * shibaPermMatrix N) i j
      = M (shibaConfig N i) (shibaConfig N j) := by
  simp only [shibaPermMatrix, toMatrix_toPEquiv_mul, mul_toMatrix_toPEquiv,
    Matrix.submatrix_apply, id_eq, shibaConfigEquiv_symm, shibaConfigEquiv_apply]

/-- **Entry formula for the sign-dressed Shiba conjugation** (Tasaki eq. (9.3.50)
applied to conjugation): for any diagonal sign `s` and matrix `M`,
`(Ûᴴ·M·Û)(i,j) = s̄(σi)·M(σi,σj)·s(σj)` with `σ = shibaConfig`.  Combines the
conjugate-transpose formula `Ûᴴ = P·diagonal(s̄)`, the diagonal-multiplication
entry laws, and `shibaPermMatrix_conj_apply`. -/
theorem shibaSignedUnitary_conj_apply (s : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (M : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ)
    (i j : Fin (2 * N + 2) → Fin 2) :
    (Matrix.conjTranspose (shibaSignedUnitary N s) * M * shibaSignedUnitary N s) i j
      = star (s (shibaConfig N i)) * M (shibaConfig N i) (shibaConfig N j)
          * s (shibaConfig N j) := by
  rw [shibaSignedUnitary_conjTranspose, shibaSignedUnitary,
    show shibaPermMatrix N * Matrix.diagonal (star s) * M
          * (Matrix.diagonal s * shibaPermMatrix N)
        = shibaPermMatrix N * (Matrix.diagonal (star s) * M * Matrix.diagonal s)
          * shibaPermMatrix N from by simp only [Matrix.mul_assoc],
    shibaPermMatrix_conj_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]

/-! ## The crux: kinetic invariance (Tasaki eq. (9.3.52)) -/

/-- The number of down (odd) modes strictly below the mode `spinfulIndex N m s`
is `m`: the down modes below are exactly `2t+1` for `t < m`.  (This `m = q` count
is the parity that the sublattice gauge and the crossing sign must reproduce.) -/
private theorem oddModes_below_card (m : Fin (N + 1)) (s : Fin 2) :
    ((Finset.univ : Finset (Fin (2 * N + 2))).filter
      (fun k => k.val < (spinfulIndex N m s).val ∧ k.val % 2 = 1)).card = m.val := by
  rw [Finset.card_filter, sum_spinful_reindex]
  have hcol : ∀ t : Fin (N + 1),
      (∑ r : Fin 2, if (spinfulIndex N t r).val < (spinfulIndex N m s).val
          ∧ (spinfulIndex N t r).val % 2 = 1 then (1 : ℕ) else 0)
        = if t.val < m.val then 1 else 0 := by
    intro t
    rw [Fin.sum_univ_two]
    have h0 : (spinfulIndex N t 0).val = 2 * t.val := by simp [spinfulIndex]
    have h1 : (spinfulIndex N t 1).val = 2 * t.val + 1 := by simp [spinfulIndex]
    have hms : (spinfulIndex N m s).val = 2 * m.val + s.val := by simp [spinfulIndex]
    have hs2 : s.val < 2 := s.isLt
    rw [if_neg (by rw [h0]; omega), zero_add]
    by_cases ht : t.val < m.val
    · rw [if_pos ⟨by rw [h1, hms]; omega, by rw [h1]; omega⟩, if_pos ht]
    · rw [if_neg (by rw [h1, hms]; omega), if_neg ht]
  rw [Finset.sum_congr rfl (fun t _ => hcol t), ← Finset.card_filter]
  have hset : (Finset.univ.filter (fun t : Fin (N + 1) => t.val < m.val)) = Finset.Iio m := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    exact Fin.lt_def.symm
  rw [hset, Fin.card_Iio]

/-- The occupation flip contributes `1` to the paired occupation sum:
`(flip a).val + a.val = 1`. -/
private theorem flipOccupation_val_add (a : Fin 2) :
    (flipOccupation a).val + a.val = 1 := by
  fin_cases a <;> rfl

/-- The mode index parity: `(spinfulIndex N y r).val % 2 = r`. -/
private theorem spinfulIndex_val_mod_two (y : Fin (N + 1)) (r : Fin 2) :
    (spinfulIndex N y r).val % 2 = r.val := by
  have := r.isLt; simp only [spinfulIndex]; omega

/-- **The Jordan–Wigner down-flip crossing sign** (foundation of Tasaki eq. (9.3.52)):
flipping the down occupations (as the Shiba permutation does) multiplies the
Jordan–Wigner string sign at mode `j` by `(−1)` to the number of down modes below
`j`.  Stated as a product of the two `±1` signs (so no division is needed):
`jwSign j (shibaConfig c) · jwSign j c = (−1)^{#down modes below j}`.  Each down
mode below `j` flips its occupation, so its `(−1)^{c k}` factor changes sign; the
even (up) modes contribute `2·(c k)` to the exponent, which is parity-neutral. -/
private theorem jwSign_shibaConfig_mul (j : Fin (2 * N + 2))
    (c : Fin (2 * N + 2) → Fin 2) :
    jwSign (2 * N + 1) j (shibaConfig N c) * jwSign (2 * N + 1) j c
      = (-1 : ℂ) ^ ((Finset.univ.filter
          (fun k : Fin (2 * N + 2) => k.val < j.val ∧ k.val % 2 = 1)).card) := by
  rw [jwSign_eq_neg_one_pow, jwSign_eq_neg_one_pow, ← pow_add, ← Finset.sum_add_distrib]
  have key : (∑ k ∈ Finset.univ.filter (fun k : Fin (2 * N + 2) => k.val < j.val),
        ((shibaConfig N c k).val + (c k).val))
      = 2 * (∑ k ∈ Finset.univ.filter
          (fun k : Fin (2 * N + 2) => k.val < j.val ∧ k.val % 2 = 0), (c k).val)
        + (Finset.univ.filter
          (fun k : Fin (2 * N + 2) => k.val < j.val ∧ k.val % 2 = 1)).card := by
    rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun k : Fin (2 * N + 2) => k.val < j.val))
        (fun k => k.val % 2 = 0)
        (fun k => (shibaConfig N c k).val + (c k).val),
      Finset.filter_filter, Finset.filter_filter]
    have heven : (∑ k ∈ Finset.univ.filter
          (fun k : Fin (2 * N + 2) => k.val < j.val ∧ k.val % 2 = 0),
          ((shibaConfig N c k).val + (c k).val))
        = 2 * (∑ k ∈ Finset.univ.filter
          (fun k : Fin (2 * N + 2) => k.val < j.val ∧ k.val % 2 = 0), (c k).val) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨y, r, rfl⟩ := exists_spinfulIndex N k
      have hr : r = 0 := Fin.ext (by
        have := spinfulIndex_val_mod_two (N := N) y r; omega)
      subst hr
      rw [shibaConfig_apply_up]; ring
    have hodd : (∑ k ∈ Finset.univ.filter
          (fun k : Fin (2 * N + 2) => k.val < j.val ∧ ¬ k.val % 2 = 0),
          ((shibaConfig N c k).val + (c k).val))
        = (Finset.univ.filter
          (fun k : Fin (2 * N + 2) => k.val < j.val ∧ k.val % 2 = 1)).card := by
      have hfeq : (Finset.univ.filter
            (fun k : Fin (2 * N + 2) => k.val < j.val ∧ ¬ k.val % 2 = 0))
          = Finset.univ.filter (fun k : Fin (2 * N + 2) => k.val < j.val ∧ k.val % 2 = 1) :=
        Finset.filter_congr (fun k _ => by
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩)
      rw [hfeq, Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      obtain ⟨y, r, rfl⟩ := exists_spinfulIndex N k
      have hr : r = 1 := Fin.ext (by
        have := spinfulIndex_val_mod_two (N := N) y r; omega)
      subst hr
      rw [shibaConfig_apply_down, flipOccupation_val_add]
    rw [heven, hodd]
  rw [key, pow_add, pow_mul, neg_one_sq, one_pow, one_mul]

/-- **The crossing sign at a spinful mode** (Tasaki eq. (9.3.52) ingredient):
`jwSign (spinfulIndex q s) (σc) = (−1)^q · jwSign (spinfulIndex q s) c`.  The number
of down modes below `spinfulIndex q s` is `q` (both for `s = 0` and `s = 1`). -/
private theorem jwSign_shibaConfig_spinful (q : Fin (N + 1)) (s : Fin 2)
    (c : Fin (2 * N + 2) → Fin 2) :
    jwSign (2 * N + 1) (spinfulIndex N q s) (shibaConfig N c)
      = (-1 : ℂ) ^ (q : ℕ) * jwSign (2 * N + 1) (spinfulIndex N q s) c := by
  have hmul := jwSign_shibaConfig_mul (spinfulIndex N q s) c
  rw [oddModes_below_card] at hmul
  have hsq : jwSign (2 * N + 1) (spinfulIndex N q s) c
      * jwSign (2 * N + 1) (spinfulIndex N q s) c = 1 := by
    rw [jwSign_eq_neg_one_pow, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc jwSign (2 * N + 1) (spinfulIndex N q s) (shibaConfig N c)
      = jwSign (2 * N + 1) (spinfulIndex N q s) (shibaConfig N c)
          * (jwSign (2 * N + 1) (spinfulIndex N q s) c
            * jwSign (2 * N + 1) (spinfulIndex N q s) c) := by rw [hsq, mul_one]
    _ = (jwSign (2 * N + 1) (spinfulIndex N q s) (shibaConfig N c)
            * jwSign (2 * N + 1) (spinfulIndex N q s) c)
          * jwSign (2 * N + 1) (spinfulIndex N q s) c := by ring
    _ = (-1 : ℂ) ^ (q : ℕ) * jwSign (2 * N + 1) (spinfulIndex N q s) c := by rw [hmul]

/-- The mode index value: `(spinfulIndex N y r).val = 2 y + r`. -/
private theorem spinfulIndex_val (y : Fin (N + 1)) (r : Fin 2) :
    (spinfulIndex N y r).val = 2 * y.val + r.val := by simp [spinfulIndex]

/-- Pointwise value of the Shiba flip: it fixes even (up) modes and flips odd
(down) modes. -/
private theorem shibaConfig_apply_parity (c : Fin (2 * N + 2) → Fin 2)
    (k : Fin (2 * N + 2)) :
    shibaConfig N c k = if k.val % 2 = 0 then c k else flipOccupation (c k) := by
  obtain ⟨y, r, rfl⟩ := exists_spinfulIndex N k
  rw [spinfulIndex_val_mod_two]
  by_cases hr : r = 0
  · subst hr; simp only [Fin.val_zero, shibaConfig_apply_up, if_true]
  · have hr1 : r = 1 := Fin.ext (by
      have h2 := r.isLt
      have h0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
      omega)
    subst hr1
    rw [shibaConfig_apply_down, if_neg (by decide)]

/-- Updating an up mode commutes with the Shiba flip (which fixes up modes):
`σ(update x (2p) v) = update (σx) (2p) v`. -/
private theorem shibaConfig_update_up (x : Fin (2 * N + 2) → Fin 2)
    (p : Fin (N + 1)) (v : Fin 2) :
    shibaConfig N (Function.update x (spinfulIndex N p 0) v)
      = Function.update (shibaConfig N x) (spinfulIndex N p 0) v := by
  funext k
  by_cases hk : k = spinfulIndex N p 0
  · subst hk; rw [shibaConfig_apply_up, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, shibaConfig_apply_parity, shibaConfig_apply_parity,
      Function.update_of_ne hk]

/-- Updating a down mode commutes with the Shiba flip up to the occupation flip
(which acts on the down species): `σ(update x (2p+1) v) = update (σx) (2p+1) (flip v)`. -/
private theorem shibaConfig_update_down (x : Fin (2 * N + 2) → Fin 2)
    (p : Fin (N + 1)) (v : Fin 2) :
    shibaConfig N (Function.update x (spinfulIndex N p 1) v)
      = Function.update (shibaConfig N x) (spinfulIndex N p 1) (flipOccupation v) := by
  funext k
  by_cases hk : k = spinfulIndex N p 1
  · subst hk; rw [shibaConfig_apply_down, Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, shibaConfig_apply_parity, shibaConfig_apply_parity,
      Function.update_of_ne hk]

/-- The crossing parity is real (a product of `±1`): `star J = J`. -/
private theorem shibaJwFlipParity_star (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaJwFlipParity N c) = shibaJwFlipParity N c := by
  rw [shibaJwFlipParity, star_mul', shibaCrossingSpecies_star, shibaCrossingSpecies_star]

/-- The sublattice gauge is real (a product of `±1`): `star g = g`. -/
private theorem shibaGauge_star (A : Finset (Fin (N + 1))) (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaGauge A c) = shibaGauge A c := by
  unfold shibaGauge
  rw [star_prod]
  refine Finset.prod_congr rfl (fun y _ => ?_)
  by_cases h : c (spinfulIndex N y 1) = 0
  · rw [if_pos h, star_one]
  · rw [if_neg h, star_neg, star_one]

/-- Updating a spin-`s` mode does not change the spin-`r` crossing parity when
`r ≠ s`, since `cs r` reads only the spin-`r` modes. -/
private theorem shibaCrossingSpecies_update_ne (r : Fin 2)
    (c : Fin (2 * N + 2) → Fin 2) (y : Fin (N + 1)) (s : Fin 2) (v : Fin 2) (hs : s ≠ r) :
    shibaCrossingSpecies N r (Function.update c (spinfulIndex N y s) v)
      = shibaCrossingSpecies N r c := by
  unfold shibaCrossingSpecies
  refine Finset.prod_congr rfl (fun z _ => ?_)
  rw [Function.update_of_ne (fun h => hs ((spinfulIndex_eq_iff N z y r s).mp h).2.symm)]

/-- The sublattice gauge is unchanged by updating an up mode, since it reads only
the down occupations `2x+1`: `g(update x (2p) v) = g(x)`. -/
private theorem shibaGauge_update_up (A : Finset (Fin (N + 1)))
    (x : Fin (2 * N + 2) → Fin 2) (p : Fin (N + 1)) (v : Fin 2) :
    shibaGauge A (Function.update x (spinfulIndex N p 0) v) = shibaGauge A x := by
  unfold shibaGauge
  refine Finset.prod_congr rfl (fun z _ => ?_)
  rw [Function.update_of_ne (fun h => by
    exact absurd ((spinfulIndex_eq_iff N z p 1 0).mp h).2 (by decide))]

/-- **The down-hop sublattice-gauge product** (Tasaki eq. (9.3.52), gauge part,
p. 336): when a down hop fires on `d` (`d(2q+1)=1`, `d(2p+1)=0`), the gauge at `d`
times the gauge at the hopped configuration is the product of the two sublattice
signs `ε_p ε_q = gaugeSign A p · gaugeSign A q`.  Only sites `p`, `q` differ, each
contributing `−1` exactly when it lies in `Aᶜ`, i.e. `ε` at that site. -/
private theorem shibaGauge_down_hop_product (A : Finset (Fin (N + 1)))
    (d : Fin (2 * N + 2) → Fin 2) (p q : Fin (N + 1)) (hpq : p ≠ q)
    (hq : d (spinfulIndex N q 1) = 1) (hp : d (spinfulIndex N p 1) = 0) :
    shibaGauge A d * shibaGauge A (Function.update
        (Function.update d (spinfulIndex N q 1) 0) (spinfulIndex N p 1) 1)
      = gaugeSign A p * gaugeSign A q := by
  have hPneQ : spinfulIndex N p 1 ≠ spinfulIndex N q 1 :=
    fun h => hpq ((spinfulIndex_eq_iff N p q 1 1).mp h).1
  set td := Function.update (Function.update d (spinfulIndex N q 1) 0)
    (spinfulIndex N p 1) 1 with htd_def
  have htdp : td (spinfulIndex N p 1) = 1 := by rw [htd_def, Function.update_self]
  have htdq : td (spinfulIndex N q 1) = 0 := by
    rw [htd_def, Function.update_of_ne hPneQ.symm, Function.update_self]
  have htdz : ∀ z : Fin (N + 1), z ≠ p → z ≠ q →
      td (spinfulIndex N z 1) = d (spinfulIndex N z 1) := by
    intro z hzp hzq
    rw [htd_def, Function.update_of_ne (fun h => hzp ((spinfulIndex_eq_iff N z p 1 1).mp h).1),
      Function.update_of_ne (fun h => hzq ((spinfulIndex_eq_iff N z q 1 1).mp h).1)]
  rw [shibaGauge, shibaGauge, ← Finset.prod_mul_distrib]
  have hrest : ∀ z ∈ bipartitionComplement A, z ≠ p → z ≠ q →
      (if d (spinfulIndex N z 1) = 0 then (1 : ℂ) else -1)
        * (if td (spinfulIndex N z 1) = 0 then (1 : ℂ) else -1) = 1 := by
    intro z _ hzp hzq
    rw [htdz z hzp hzq]
    by_cases h : d (spinfulIndex N z 1) = 0
    · rw [if_pos h]; ring
    · rw [if_neg h]; ring
  have hhp : (if d (spinfulIndex N p 1) = 0 then (1 : ℂ) else -1)
      * (if td (spinfulIndex N p 1) = 0 then (1 : ℂ) else -1) = -1 := by
    rw [hp, htdp, if_pos rfl, if_neg (by decide)]; ring
  have hhq : (if d (spinfulIndex N q 1) = 0 then (1 : ℂ) else -1)
      * (if td (spinfulIndex N q 1) = 0 then (1 : ℂ) else -1) = -1 := by
    rw [hq, htdq, if_neg (by decide), if_pos rfl]; ring
  have hmemp : p ∉ A → p ∈ bipartitionComplement A := fun h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩
  have hmemq : q ∉ A → q ∈ bipartitionComplement A := fun h =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩
  have hnotmem : ∀ z ∈ bipartitionComplement A, z ∉ A := fun z hz =>
    (Finset.mem_filter.mp hz).2
  unfold gaugeSign
  by_cases hpA : p ∈ A <;> by_cases hqA : q ∈ A
  · rw [if_pos hpA, if_pos hqA, mul_one]
    refine Finset.prod_eq_one (fun z hz => hrest z hz ?_ ?_)
    · rintro rfl; exact hnotmem z hz hpA
    · rintro rfl; exact hnotmem z hz hqA
  · rw [if_pos hpA, if_neg hqA, one_mul,
      ← Finset.mul_prod_erase (bipartitionComplement A) _ (hmemq hqA), hhq,
      Finset.prod_eq_one (fun z hz => ?_), mul_one]
    rw [Finset.mem_erase] at hz
    exact hrest z hz.2 (fun h => hnotmem z hz.2 (h ▸ hpA)) hz.1
  · rw [if_neg hpA, if_pos hqA, mul_one,
      ← Finset.mul_prod_erase (bipartitionComplement A) _ (hmemp hpA), hhp,
      Finset.prod_eq_one (fun z hz => ?_), mul_one]
    rw [Finset.mem_erase] at hz
    exact hrest z hz.2 hz.1 (fun h => hnotmem z hz.2 (h ▸ hqA))
  · rw [if_neg hpA, if_neg hqA,
      ← Finset.mul_prod_erase (bipartitionComplement A) _ (hmemp hpA),
      ← Finset.mul_prod_erase ((bipartitionComplement A).erase p) _
        (Finset.mem_erase.mpr ⟨fun h => hpq h.symm, hmemq hqA⟩),
      hhp, hhq, Finset.prod_eq_one (fun z hz => ?_), mul_one]
    rw [Finset.mem_erase, Finset.mem_erase] at hz
    exact hrest z hz.2.2 hz.2.1 hz.1

/-- **The single-species crossing-parity product** (the sign the Shiba dressing
supplies on a spin-`r` hop): when the hop `q → p` fires (source `spinful q r`
occupied, target `spinful p r` empty), `cs r c · cs r (hopped c) = (−1)^p (−1)^q`.
Only sites `p`, `q` differ, contributing `(−1)^p`, `(−1)^q`; every other site
squares to `1`. -/
private theorem shibaCrossingSpecies_hop_product (r : Fin 2)
    (c : Fin (2 * N + 2) → Fin 2) (p q : Fin (N + 1))
    (hq : c (spinfulIndex N q r) = 1)
    (hp : (Function.update c (spinfulIndex N q r) 0) (spinfulIndex N p r) = 0) :
    shibaCrossingSpecies N r c
        * shibaCrossingSpecies N r (Function.update
            (Function.update c (spinfulIndex N q r) 0) (spinfulIndex N p r) 1)
      = (-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ) := by
  by_cases hpq : p = q
  · subst hpq
    have htc : Function.update (Function.update c (spinfulIndex N p r) 0)
        (spinfulIndex N p r) 1 = c := by
      rw [Function.update_idem, ← hq, Function.update_eq_self]
    rw [htc, shibaCrossingSpecies_sq, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · have hPneQ : spinfulIndex N p r ≠ spinfulIndex N q r :=
      fun h => hpq ((spinfulIndex_eq_iff N p q r r).mp h).1
    have hcp : c (spinfulIndex N p r) = 0 := by rwa [Function.update_of_ne hPneQ] at hp
    set tc := Function.update (Function.update c (spinfulIndex N q r) 0)
      (spinfulIndex N p r) 1 with htc_def
    have htcp : tc (spinfulIndex N p r) = 1 := by rw [htc_def, Function.update_self]
    have htcq : tc (spinfulIndex N q r) = 0 := by
      rw [htc_def, Function.update_of_ne hPneQ.symm, Function.update_self]
    have htcy : ∀ y : Fin (N + 1), y ≠ p → y ≠ q →
        tc (spinfulIndex N y r) = c (spinfulIndex N y r) := by
      intro y hyp hyq
      rw [htc_def, Function.update_of_ne (fun h => hyp ((spinfulIndex_eq_iff N y p r r).mp h).1),
        Function.update_of_ne (fun h => hyq ((spinfulIndex_eq_iff N y q r r).mp h).1)]
    unfold shibaCrossingSpecies
    rw [← Finset.prod_mul_distrib,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p),
      ← Finset.mul_prod_erase (Finset.univ.erase p) _
        (Finset.mem_erase.mpr ⟨fun h => hpq h.symm, Finset.mem_univ q⟩),
      Finset.prod_eq_one (fun y hy => ?_)]
    · rw [if_neg (by rw [hcp]; decide), if_pos htcp, if_pos hq, if_neg (by rw [htcq]; decide),
        one_mul, mul_one, mul_one]
    · rw [Finset.mem_erase, Finset.mem_erase] at hy
      rw [htcy y hy.2.1 hy.1]
      by_cases h : c (spinfulIndex N y r) = 1
      · rw [if_pos h, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      · rw [if_neg h, mul_one]

/-- **The crossing-parity product on a spin-`r` hop** (up: `r=0`, down: `r=1`):
`J(c) · J(hopped c) = (−1)^p (−1)^q`.  The spin-`r` factor supplies `(−1)^{p+q}`;
the other-species factor is unchanged by the hop and squares to `1`. -/
private theorem shibaJwFlipParity_hop_product (r : Fin 2)
    (c : Fin (2 * N + 2) → Fin 2) (p q : Fin (N + 1))
    (hq : c (spinfulIndex N q r) = 1)
    (hp : (Function.update c (spinfulIndex N q r) 0) (spinfulIndex N p r) = 0) :
    shibaJwFlipParity N c
        * shibaJwFlipParity N (Function.update
            (Function.update c (spinfulIndex N q r) 0) (spinfulIndex N p r) 1)
      = (-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ) := by
  have hprod := shibaCrossingSpecies_hop_product r c p q hq hp
  by_cases hr : r = 0
  · subst hr
    rw [shibaJwFlipParity, shibaJwFlipParity,
      show shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 1 c
          * (shibaCrossingSpecies N 0 (Function.update
              (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1)
            * shibaCrossingSpecies N 1 (Function.update
              (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1))
        = (shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 0 (Function.update
              (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1))
          * (shibaCrossingSpecies N 1 c * shibaCrossingSpecies N 1 (Function.update
              (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1))
        from by ring,
      hprod, shibaCrossingSpecies_update_ne 1 _ p 0 1 (by decide),
      shibaCrossingSpecies_update_ne 1 _ q 0 0 (by decide), shibaCrossingSpecies_sq, mul_one]
  · have hr1 : r = 1 := Fin.ext (by
      have h2 := r.isLt
      have h0 : r.val ≠ 0 := fun h => hr (Fin.ext h)
      omega)
    subst hr1
    rw [shibaJwFlipParity, shibaJwFlipParity,
      show shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 1 c
          * (shibaCrossingSpecies N 0 (Function.update
              (Function.update c (spinfulIndex N q 1) 0) (spinfulIndex N p 1) 1)
            * shibaCrossingSpecies N 1 (Function.update
              (Function.update c (spinfulIndex N q 1) 0) (spinfulIndex N p 1) 1))
        = (shibaCrossingSpecies N 1 c * shibaCrossingSpecies N 1 (Function.update
              (Function.update c (spinfulIndex N q 1) 0) (spinfulIndex N p 1) 1))
          * (shibaCrossingSpecies N 0 c * shibaCrossingSpecies N 0 (Function.update
              (Function.update c (spinfulIndex N q 1) 0) (spinfulIndex N p 1) 1))
        from by ring,
      hprod, shibaCrossingSpecies_update_ne 0 _ p 1 1 (by decide),
      shibaCrossingSpecies_update_ne 0 _ q 1 0 (by decide), shibaCrossingSpecies_sq, mul_one]

/-- **The down-hop CAR sign reversal** (Tasaki eq. (9.3.43), p. 334): swapping a
down hop `q → p` for its reverse `p → q` flips the Jordan–Wigner sign:
`jwSign_Q(c)·jwSign_P(c with Q↦1) = − jwSign_P(c)·jwSign_Q(c with P↦0)`
(source `p` occupied, `q` empty).  Both signs are `(−1)` to a parity of occupied
modes; the parities differ by exactly `1` (one of `P<Q`, `Q<P` holds), giving the
CAR `−1`. -/
private theorem jwSign_down_hop_car (c : Fin (2 * N + 2) → Fin 2) (p q : Fin (N + 1))
    (hpq : p ≠ q) (hcp : c (spinfulIndex N p 1) = 1) (hcq : c (spinfulIndex N q 1) = 0) :
    jwSign (2 * N + 1) (spinfulIndex N q 1) c
        * jwSign (2 * N + 1) (spinfulIndex N p 1) (Function.update c (spinfulIndex N q 1) 1)
      = - (jwSign (2 * N + 1) (spinfulIndex N p 1) c
        * jwSign (2 * N + 1) (spinfulIndex N q 1)
          (Function.update c (spinfulIndex N p 1) 0)) := by
  rw [jwSign_eq_neg_one_pow, jwSign_eq_neg_one_pow, jwSign_eq_neg_one_pow,
    jwSign_eq_neg_one_pow, ← pow_add, ← pow_add]
  have hi : (∑ k ∈ Finset.univ.filter
        (fun k : Fin (2 * N + 2) => k.val < (spinfulIndex N p 1).val),
        ((Function.update c (spinfulIndex N q 1) 1) k).val)
      = (∑ k ∈ Finset.univ.filter (fun k => k.val < (spinfulIndex N p 1).val), (c k).val)
        + (if (spinfulIndex N q 1).val < (spinfulIndex N p 1).val then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun k _ =>
        show ((Function.update c (spinfulIndex N q 1) 1) k).val
          = (c k).val + (if k = spinfulIndex N q 1 then 1 else 0) from by
        by_cases hk : k = spinfulIndex N q 1
        · subst hk; simp [Function.update_self, hcq]
        · rw [Function.update_of_ne hk, if_neg hk, add_zero]),
      Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hii : (∑ k ∈ Finset.univ.filter
        (fun k : Fin (2 * N + 2) => k.val < (spinfulIndex N q 1).val), (c k).val)
      = (∑ k ∈ Finset.univ.filter (fun k => k.val < (spinfulIndex N q 1).val),
          ((Function.update c (spinfulIndex N p 1) 0) k).val)
        + (if (spinfulIndex N p 1).val < (spinfulIndex N q 1).val then 1 else 0) := by
    rw [Finset.sum_congr rfl (fun k _ =>
        show (c k).val = ((Function.update c (spinfulIndex N p 1) 0) k).val
          + (if k = spinfulIndex N p 1 then 1 else 0) from by
        by_cases hk : k = spinfulIndex N p 1
        · subst hk; simp [Function.update_self, hcp]
        · rw [Function.update_of_ne hk, if_neg hk, add_zero]),
      Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hi, hii]
  set S3 := ∑ k ∈ Finset.univ.filter
    (fun k : Fin (2 * N + 2) => k.val < (spinfulIndex N p 1).val), (c k).val
  set S4 := ∑ k ∈ Finset.univ.filter
    (fun k : Fin (2 * N + 2) => k.val < (spinfulIndex N q 1).val),
    ((Function.update c (spinfulIndex N p 1) 0) k).val
  set iP := if (spinfulIndex N p 1).val < (spinfulIndex N q 1).val then 1 else 0 with hiP
  set iQ := if (spinfulIndex N q 1).val < (spinfulIndex N p 1).val then 1 else 0 with hiQ
  have hone : iP + iQ = 1 := by
    have hne : (spinfulIndex N p 1).val ≠ (spinfulIndex N q 1).val :=
      fun h => hpq ((spinfulIndex_eq_iff N p q 1 1).mp (Fin.ext h)).1
    rw [hiP, hiQ]
    rcases lt_or_gt_of_ne hne with h | h
    · rw [if_pos h, if_neg (by omega)]
    · rw [if_neg (by omega), if_pos h]
  rw [show (S4 + iP) + (S3 + iQ) = (S3 + S4) + 1 by omega, pow_succ]
  ring

/-! ### Column (basis-vector) action of the Shiba unitary -/

/-- The Shiba permutation sends a basis vector to the flipped basis vector:
`P ·ᵥ |c⟩ = |σc⟩`. -/
private theorem shibaPermMatrix_mulVec_basisVec (c : Fin (2 * N + 2) → Fin 2) :
    (shibaPermMatrix N).mulVec (basisVec c) = basisVec (shibaConfig N c) := by
  rw [shibaPermMatrix, toMatrix_toPEquiv_mulVec]
  funext d
  simp only [Function.comp_apply, shibaConfigEquiv_apply, basisVec_apply]
  by_cases h : shibaConfig N d = c
  · rw [if_pos h, if_pos (by rw [← h, shibaConfig_shibaConfig])]
  · rw [if_neg h, if_neg (fun h' => h (by rw [h', shibaConfig_shibaConfig]))]

/-- A diagonal matrix scales a basis vector: `diagonal s ·ᵥ |c⟩ = s c • |c⟩`. -/
private theorem diagonal_mulVec_basisVec (s : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (c : Fin (2 * N + 2) → Fin 2) :
    (Matrix.diagonal s).mulVec (basisVec c) = s c • basisVec c := by
  funext d
  rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, basisVec_apply]
  by_cases h : d = c
  · rw [h]
  · rw [if_neg h, mul_zero, mul_zero]

/-- **Column action of the Shiba unitary**: `Û ·ᵥ |c⟩ = s(σc) • |σc⟩`. -/
private theorem shibaSignedUnitary_mulVec_basisVec (s : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (c : Fin (2 * N + 2) → Fin 2) :
    (shibaSignedUnitary N s).mulVec (basisVec c)
      = s (shibaConfig N c) • basisVec (shibaConfig N c) := by
  rw [shibaSignedUnitary, ← Matrix.mulVec_mulVec, shibaPermMatrix_mulVec_basisVec,
    diagonal_mulVec_basisVec]

/-- **Column action of the adjoint Shiba unitary**:
`Ûᴴ ·ᵥ |c⟩ = s̄(c) • |σc⟩`. -/
private theorem shibaSignedUnitary_conjTranspose_mulVec_basisVec
    (s : (Fin (2 * N + 2) → Fin 2) → ℂ) (c : Fin (2 * N + 2) → Fin 2) :
    (Matrix.conjTranspose (shibaSignedUnitary N s)).mulVec (basisVec c)
      = star (s c) • basisVec (shibaConfig N c) := by
  rw [shibaSignedUnitary_conjTranspose, ← Matrix.mulVec_mulVec,
    diagonal_mulVec_basisVec, Matrix.mulVec_smul, shibaPermMatrix_mulVec_basisVec,
    Pi.star_apply]

/-- Two operators agree once their columns (actions on all basis vectors) agree. -/
private theorem matrix_ext_mulVec_basisVec
    {A B : Matrix (Fin (2 * N + 2) → Fin 2) (Fin (2 * N + 2) → Fin 2) ℂ}
    (h : ∀ c, A.mulVec (basisVec c) = B.mulVec (basisVec c)) : A = B := by
  ext i j
  have hij := congrFun (h j) i
  rw [show A.mulVec (basisVec j) i = A i j from sum_mul_basisVec j (fun ρ => A i ρ),
    show B.mulVec (basisVec j) i = B i j from sum_mul_basisVec j (fun ρ => B i ρ)] at hij
  exact hij

/-! ### The up-hop is invariant (Tasaki eq. (9.3.52), up part) -/

/-- **The Shiba conjugation fixes each up hop** (Tasaki eq. (9.3.52), up part,
p. 336): `Ûᴴ (ĉ†_{2p} ĉ_{2q}) Û = ĉ†_{2p} ĉ_{2q}`.  The particle-hole flip acts on
the down species, so it leaves the up creation/annihilation operators untouched; the
only effect is the Jordan–Wigner crossing sign of the flipped down modes below `2q`
and `2p`, and that `(−1)^{p+q}` is exactly cancelled by the crossing parity in the
diagonal dressing `shibaSignFn`. -/
private theorem shibaSignedUnitary_conj_upHop (A : Finset (Fin (N + 1)))
    (p q : Fin (N + 1)) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * (fermionMultiCreation (2 * N + 1) (spinfulIndex N p 0)
            * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N q 0))
        * shibaSignedUnitary N (shibaSignFn A)
      = fermionMultiCreation (2 * N + 1) (spinfulIndex N p 0)
          * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N q 0) := by
  apply matrix_ext_mulVec_basisVec
  intro c
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    shibaSignedUnitary_mulVec_basisVec, Matrix.mulVec_smul,
    fermionMultiCreation_mul_Annihilation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N p 0) (spinfulIndex N q 0) (shibaConfig N c),
    fermionMultiCreation_mul_Annihilation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N p 0) (spinfulIndex N q 0) c]
  have hσQ : shibaConfig N c (spinfulIndex N q 0) = c (spinfulIndex N q 0) :=
    shibaConfig_apply_up c q
  have hupdQ : Function.update (shibaConfig N c) (spinfulIndex N q 0) 0
      = shibaConfig N (Function.update c (spinfulIndex N q 0) 0) :=
    (shibaConfig_update_up c q 0).symm
  by_cases hcond : c (spinfulIndex N q 0) = 1
      ∧ (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) = 0
  · have hcondσ : shibaConfig N c (spinfulIndex N q 0) = 1
        ∧ (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
          (spinfulIndex N p 0) = 0 := by
      rw [hσQ, hupdQ, shibaConfig_apply_up]; exact hcond
    rw [if_pos hcondσ, if_pos hcond]
    have htgt : Function.update (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
          (spinfulIndex N p 0) 1
        = shibaConfig N (Function.update (Function.update c (spinfulIndex N q 0) 0)
            (spinfulIndex N p 0) 1) := by
      rw [hupdQ, ← shibaConfig_update_up]
    rw [smul_smul, htgt, Matrix.mulVec_smul,
      shibaSignedUnitary_conjTranspose_mulVec_basisVec, shibaConfig_shibaConfig, smul_smul]
    congr 1
    have hjQ : jwSign (2 * N + 1) (spinfulIndex N q 0) (shibaConfig N c)
        = (-1 : ℂ) ^ (q : ℕ) * jwSign (2 * N + 1) (spinfulIndex N q 0) c :=
      jwSign_shibaConfig_spinful q 0 c
    have hjP : jwSign (2 * N + 1) (spinfulIndex N p 0)
          (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
        = (-1 : ℂ) ^ (p : ℕ) * jwSign (2 * N + 1) (spinfulIndex N p 0)
          (Function.update c (spinfulIndex N q 0) 0) := by
      rw [hupdQ]; exact jwSign_shibaConfig_spinful p 0 (Function.update c (spinfulIndex N q 0) 0)
    have hqσ : shibaConfig N c (spinfulIndex N q 0) = 1 := by rw [hσQ]; exact hcond.1
    have hpσ : (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
        (spinfulIndex N p 0) = 0 := by rw [hupdQ, shibaConfig_apply_up]; exact hcond.2
    have hστ : shibaConfig N (Function.update (Function.update c (spinfulIndex N q 0) 0)
          (spinfulIndex N p 0) 1)
        = Function.update (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
            (spinfulIndex N p 0) 1 := by
      rw [shibaConfig_update_up, shibaConfig_update_up]
    rw [shibaSignFn, shibaSignFn, hστ, star_mul', shibaGauge_star, shibaJwFlipParity_star,
      shibaGauge_update_up, shibaGauge_update_up, hjQ, hjP]
    have hJprod := shibaJwFlipParity_hop_product 0 (shibaConfig N c) p q hqσ hpσ
    have hg2 : shibaGauge A (shibaConfig N c) * shibaGauge A (shibaConfig N c) = 1 := by
      have h := shibaGauge_star_mul_self A (shibaConfig N c); rwa [shibaGauge_star] at h
    have hab : ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
        * ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ)) = 1 := by
      rw [show ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
            * ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
          = ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (p : ℕ))
            * ((-1 : ℂ) ^ (q : ℕ) * (-1 : ℂ) ^ (q : ℕ)) from by ring,
        ← pow_add, ← pow_add, ← two_mul, ← two_mul, pow_mul, pow_mul, neg_one_sq,
        one_pow, one_pow, one_mul]
    trans (shibaJwFlipParity N (shibaConfig N c) * shibaJwFlipParity N (Function.update
              (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
              (spinfulIndex N p 0) 1))
          * (shibaGauge A (shibaConfig N c) * shibaGauge A (shibaConfig N c))
          * ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
          * (jwSign (2 * N + 1) (spinfulIndex N q 0) c
            * jwSign (2 * N + 1) (spinfulIndex N p 0)
              (Function.update c (spinfulIndex N q 0) 0))
    · ring
    · rw [hJprod, hg2, mul_one, hab, one_mul]
  · have hcondσ : ¬ (shibaConfig N c (spinfulIndex N q 0) = 1
        ∧ (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
          (spinfulIndex N p 0) = 0) := by
      rw [hσQ, hupdQ, shibaConfig_apply_up]; exact hcond
    rw [if_neg hcondσ, if_neg hcond, smul_zero, Matrix.mulVec_zero]

/-! ### The down-hop reverses with the sublattice gauge (Tasaki eq. (9.3.52), down part) -/

/-- **The Shiba conjugation reverses each down hop with the sublattice gauge**
(Tasaki eq. (9.3.52), down part, p. 336): for `p ≠ q`,
`Ûᴴ (ĉ†_{2p+1} ĉ_{2q+1}) Û = −ε_p ε_q · ĉ†_{2q+1} ĉ_{2p+1}`.  The particle-hole flip
on the down species turns `ĉ†_{2p+1} ĉ_{2q+1}` into `ĉ_{2p+1} ĉ†_{2q+1}` (the reversed
hop with a CAR sign `−1`, eq. (9.3.43)); the flipped-down crossing sign `(−1)^{p+q}`
is cancelled by the crossing parity, and the sublattice gauge supplies `ε_p ε_q`. -/
private theorem shibaSignedUnitary_conj_downHop (A : Finset (Fin (N + 1)))
    (p q : Fin (N + 1)) (hpq : p ≠ q) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * (fermionMultiCreation (2 * N + 1) (spinfulIndex N p 1)
            * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N q 1))
        * shibaSignedUnitary N (shibaSignFn A)
      = (- gaugeSign A p * gaugeSign A q) • (fermionMultiCreation (2 * N + 1) (spinfulIndex N q 1)
          * fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N p 1)) := by
  have hPneQ : spinfulIndex N p 1 ≠ spinfulIndex N q 1 :=
    fun h => hpq ((spinfulIndex_eq_iff N p q 1 1).mp h).1
  have hflip1 : ∀ a : Fin 2, flipOccupation a = 1 ↔ a = 0 := by intro a; fin_cases a <;> decide
  have hflip0 : ∀ a : Fin 2, flipOccupation a = 0 ↔ a = 1 := by intro a; fin_cases a <;> decide
  apply matrix_ext_mulVec_basisVec
  intro c
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, shibaSignedUnitary_mulVec_basisVec,
    Matrix.mulVec_smul, fermionMultiCreation_mul_Annihilation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N p 1) (spinfulIndex N q 1) (shibaConfig N c),
    Matrix.smul_mulVec, fermionMultiCreation_mul_Annihilation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N q 1) (spinfulIndex N p 1) c]
  have hcondσ_iff : (shibaConfig N c (spinfulIndex N q 1) = 1
        ∧ (Function.update (shibaConfig N c) (spinfulIndex N q 1) 0) (spinfulIndex N p 1) = 0)
      ↔ (c (spinfulIndex N p 1) = 1
        ∧ (Function.update c (spinfulIndex N p 1) 0) (spinfulIndex N q 1) = 0) := by
    rw [shibaConfig_apply_down, Function.update_of_ne hPneQ, shibaConfig_apply_down,
      Function.update_of_ne hPneQ.symm, hflip1, hflip0]
    tauto
  by_cases hcond : c (spinfulIndex N p 1) = 1
      ∧ (Function.update c (spinfulIndex N p 1) 0) (spinfulIndex N q 1) = 0
  · have hcp : c (spinfulIndex N p 1) = 1 := hcond.1
    have hcq : c (spinfulIndex N q 1) = 0 := by
      have h := hcond.2; rwa [Function.update_of_ne hPneQ.symm] at h
    have hcondσ := hcondσ_iff.mpr hcond
    rw [if_pos hcondσ, if_pos hcond]
    have hupdD : Function.update (shibaConfig N c) (spinfulIndex N q 1) 0
        = shibaConfig N (Function.update c (spinfulIndex N q 1) 1) := by
      rw [shibaConfig_update_down]; rfl
    have htgt : Function.update (Function.update (shibaConfig N c) (spinfulIndex N q 1) 0)
          (spinfulIndex N p 1) 1
        = shibaConfig N (Function.update (Function.update c (spinfulIndex N p 1) 0)
            (spinfulIndex N q 1) 1) := by
      rw [shibaConfig_update_down, shibaConfig_update_down,
        show flipOccupation (0 : Fin 2) = 1 from rfl, show flipOccupation (1 : Fin 2) = 0 from rfl,
        Function.update_comm hPneQ]
    rw [smul_smul, Matrix.mulVec_smul, htgt,
      shibaSignedUnitary_conjTranspose_mulVec_basisVec, shibaConfig_shibaConfig, smul_smul,
      smul_smul]
    congr 1
    have hjQ : jwSign (2 * N + 1) (spinfulIndex N q 1) (shibaConfig N c)
        = (-1 : ℂ) ^ (q : ℕ) * jwSign (2 * N + 1) (spinfulIndex N q 1) c :=
      jwSign_shibaConfig_spinful q 1 c
    have hjP : jwSign (2 * N + 1) (spinfulIndex N p 1)
          (Function.update (shibaConfig N c) (spinfulIndex N q 1) 0)
        = (-1 : ℂ) ^ (p : ℕ) * jwSign (2 * N + 1) (spinfulIndex N p 1)
          (Function.update c (spinfulIndex N q 1) 1) := by
      rw [hupdD]; exact jwSign_shibaConfig_spinful p 1 (Function.update c (spinfulIndex N q 1) 1)
    have hqσ : shibaConfig N c (spinfulIndex N q 1) = 1 := hcondσ.1
    have hpσ : (Function.update (shibaConfig N c) (spinfulIndex N q 1) 0)
        (spinfulIndex N p 1) = 0 := hcondσ.2
    have hpσ2 : shibaConfig N c (spinfulIndex N p 1) = 0 := by rw [shibaConfig_apply_down, hcp]; rfl
    have hJ := shibaJwFlipParity_hop_product 1 (shibaConfig N c) p q hqσ hpσ
    have hg := shibaGauge_down_hop_product A (shibaConfig N c) p q hpq hqσ hpσ2
    have hcar := jwSign_down_hop_car c p q hpq hcp hcq
    have hab : ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
        * ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ)) = 1 := by
      rw [show ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
            * ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
          = ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (p : ℕ))
            * ((-1 : ℂ) ^ (q : ℕ) * (-1 : ℂ) ^ (q : ℕ)) from by ring,
        ← pow_add, ← pow_add, ← two_mul, ← two_mul, pow_mul, pow_mul, neg_one_sq,
        one_pow, one_pow, one_mul]
    rw [shibaSignFn, shibaSignFn, ← htgt, star_mul', shibaGauge_star, shibaJwFlipParity_star,
      hjQ, hjP]
    trans shibaGauge A (shibaConfig N c) * shibaGauge A (Function.update
          (Function.update (shibaConfig N c) (spinfulIndex N q 1) 0) (spinfulIndex N p 1) 1)
        * (shibaJwFlipParity N (shibaConfig N c) * shibaJwFlipParity N (Function.update
            (Function.update (shibaConfig N c) (spinfulIndex N q 1) 0) (spinfulIndex N p 1) 1)
          * ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ)))
        * (jwSign (2 * N + 1) (spinfulIndex N q 1) c
          * jwSign (2 * N + 1) (spinfulIndex N p 1) (Function.update c (spinfulIndex N q 1) 1))
    · ring
    · rw [hJ, hab, hg, hcar]; ring
  · rw [if_neg (fun hc => hcond (hcondσ_iff.mp hc)), if_neg hcond, smul_zero,
      Matrix.mulVec_zero, smul_zero]

end LatticeSystem.Fermion
