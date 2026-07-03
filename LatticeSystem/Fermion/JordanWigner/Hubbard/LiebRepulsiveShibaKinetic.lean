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

/-- The **Jordan–Wigner down-flip crossing parity** of a configuration `c`
(Tasaki eq. (9.3.50), the string part of the Shiba sign): `∏_x (−1)^{x} n̂_{x↑}`,
i.e. the product over occupied up modes `2x` of `(−1)^x`.

This is the sign the diagonal dressing must supply so that the sign-dressed Shiba
unitary `Û = diagonal(s)·P` leaves the *up* kinetic term invariant: flipping the
down occupations below the up mode `2q` (as the permutation `P` does) multiplies the
Jordan–Wigner string sign `jwSign 2q` by `(−1)^q`, and this factor `(−1)^q`
(for the source) times `(−1)^p` (for the target) is exactly cancelled by the ratio
of `shibaJwFlipParity` at the two up-hopped configurations. -/
noncomputable def shibaJwFlipParity (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  ∏ x : Fin (N + 1),
    (if c (spinfulIndex N x 0) = 1 then (-1 : ℂ) ^ (x : ℕ) else 1)

/-- The **concrete Shiba sign** `s = (Jordan–Wigner down-flip crossing parity) ×
(sublattice gauge)` (Tasaki eq. (9.3.50), p. 336): the specific diagonal sign that
dresses the Shiba permutation into the full Shiba unitary `Û = diagonal(s)·P` so that
`Ûᴴ Ĥhop Û = Ĥhop` (kinetic invariance, eq. (9.3.52)). -/
noncomputable def shibaSignFn (A : Finset (Fin (N + 1)))
    (c : Fin (2 * N + 2) → Fin 2) : ℂ :=
  shibaJwFlipParity N c * shibaGauge A c

/-- The crossing parity has modulus one: `s̄ s = 1`.  Each factor is real and equal
to `±1`, so its square is `1` and the product of squares is `1`. -/
theorem shibaJwFlipParity_star_mul_self (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaJwFlipParity N c) * shibaJwFlipParity N c = 1 := by
  rw [shibaJwFlipParity, star_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun x _ => ?_)
  by_cases h : c (spinfulIndex N x 0) = 1
  · rw [if_pos h, star_pow, star_neg, star_one, ← pow_add, ← two_mul, pow_mul]
    norm_num
  · rw [if_neg h, star_one, mul_one]

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

/-- The crossing parity is real (a product of `±1`): `star J = J`. -/
private theorem shibaJwFlipParity_star (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaJwFlipParity N c) = shibaJwFlipParity N c := by
  unfold shibaJwFlipParity
  rw [star_prod]
  refine Finset.prod_congr rfl (fun y _ => ?_)
  by_cases h : c (spinfulIndex N y 0) = 1
  · rw [if_pos h, star_pow, star_neg, star_one]
  · rw [if_neg h, star_one]

/-- The sublattice gauge is real (a product of `±1`): `star g = g`. -/
private theorem shibaGauge_star (A : Finset (Fin (N + 1))) (c : Fin (2 * N + 2) → Fin 2) :
    star (shibaGauge A c) = shibaGauge A c := by
  unfold shibaGauge
  rw [star_prod]
  refine Finset.prod_congr rfl (fun y _ => ?_)
  by_cases h : c (spinfulIndex N y 1) = 0
  · rw [if_pos h, star_one]
  · rw [if_neg h, star_neg, star_one]

/-- The crossing parity is unchanged by the Shiba flip, since it reads only the
(fixed) up occupations: `J(σc) = J(c)`. -/
private theorem shibaJwFlipParity_shibaConfig (c : Fin (2 * N + 2) → Fin 2) :
    shibaJwFlipParity N (shibaConfig N c) = shibaJwFlipParity N c := by
  unfold shibaJwFlipParity
  refine Finset.prod_congr rfl (fun y _ => ?_)
  rw [shibaConfig_apply_up]

/-- The sublattice gauge is unchanged by updating an up mode, since it reads only
the down occupations `2x+1`: `g(update x (2p) v) = g(x)`. -/
private theorem shibaGauge_update_up (A : Finset (Fin (N + 1)))
    (x : Fin (2 * N + 2) → Fin 2) (p : Fin (N + 1)) (v : Fin 2) :
    shibaGauge A (Function.update x (spinfulIndex N p 0) v) = shibaGauge A x := by
  unfold shibaGauge
  refine Finset.prod_congr rfl (fun z _ => ?_)
  rw [Function.update_of_ne (fun h => by
    exact absurd ((spinfulIndex_eq_iff N z p 1 0).mp h).2 (by decide))]

/-- **The up-hop crossing-parity product** (the sign the Shiba dressing supplies on
an up hop): when the hop `q → p` fires (source `2q` occupied, target `2p` empty),
`J(c) · J(hopped c) = (−1)^p (−1)^q`.  Only the sites `p` and `q` differ between the
two configurations, contributing `(−1)^p` and `(−1)^q`; every other site squares to
`1`. -/
private theorem shibaJwFlipParity_up_hop_product (c : Fin (2 * N + 2) → Fin 2)
    (p q : Fin (N + 1)) (hq : c (spinfulIndex N q 0) = 1)
    (hp : (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) = 0) :
    shibaJwFlipParity N c
        * shibaJwFlipParity N (Function.update
            (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1)
      = (-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ) := by
  by_cases hpq : p = q
  · subst hpq
    have htc : Function.update (Function.update c (spinfulIndex N p 0) 0)
        (spinfulIndex N p 0) 1 = c := by
      rw [Function.update_idem, ← hq, Function.update_eq_self]
    rw [htc]
    nth_rewrite 1 [← shibaJwFlipParity_star c]
    rw [shibaJwFlipParity_star_mul_self, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  · have hPneQ : spinfulIndex N p 0 ≠ spinfulIndex N q 0 :=
      fun h => hpq ((spinfulIndex_eq_iff N p q 0 0).mp h).1
    have hcp : c (spinfulIndex N p 0) = 0 := by rwa [Function.update_of_ne hPneQ] at hp
    set tc := Function.update (Function.update c (spinfulIndex N q 0) 0)
      (spinfulIndex N p 0) 1 with htc_def
    have htcp : tc (spinfulIndex N p 0) = 1 := by rw [htc_def, Function.update_self]
    have htcq : tc (spinfulIndex N q 0) = 0 := by
      rw [htc_def, Function.update_of_ne hPneQ.symm, Function.update_self]
    have htcy : ∀ y : Fin (N + 1), y ≠ p → y ≠ q →
        tc (spinfulIndex N y 0) = c (spinfulIndex N y 0) := by
      intro y hyp hyq
      rw [htc_def, Function.update_of_ne (fun h => hyp ((spinfulIndex_eq_iff N y p 0 0).mp h).1),
        Function.update_of_ne (fun h => hyq ((spinfulIndex_eq_iff N y q 0 0).mp h).1)]
    unfold shibaJwFlipParity
    rw [← Finset.prod_mul_distrib,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p),
      ← Finset.mul_prod_erase (Finset.univ.erase p) _
        (Finset.mem_erase.mpr ⟨fun h => hpq h.symm, Finset.mem_univ q⟩),
      Finset.prod_eq_one (fun y hy => ?_)]
    · rw [if_neg (by rw [hcp]; decide), if_pos htcp, if_pos hq, if_neg (by rw [htcq]; decide),
        one_mul, mul_one, mul_one]
    · rw [Finset.mem_erase, Finset.mem_erase] at hy
      rw [htcy y hy.2.1 hy.1]
      by_cases h : c (spinfulIndex N y 0) = 1
      · rw [if_pos h, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      · rw [if_neg h, mul_one]

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
    have hsσc : shibaSignFn A (shibaConfig N c)
        = shibaJwFlipParity N c * shibaGauge A (shibaConfig N c) := by
      rw [shibaSignFn, shibaJwFlipParity_shibaConfig]
    have hstarσt : star (shibaSignFn A (shibaConfig N (Function.update
          (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1)))
        = shibaJwFlipParity N (Function.update (Function.update c (spinfulIndex N q 0) 0)
            (spinfulIndex N p 0) 1)
          * shibaGauge A (shibaConfig N (Function.update
            (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1)) := by
      rw [shibaSignFn, star_mul', shibaGauge_star, shibaJwFlipParity_star,
        shibaJwFlipParity_shibaConfig, mul_comm]
    have hgσt : shibaGauge A (shibaConfig N (Function.update
          (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1))
        = shibaGauge A (shibaConfig N c) := by
      rw [shibaConfig_update_up, shibaConfig_update_up, shibaGauge_update_up,
        shibaGauge_update_up]
    rw [hsσc, hjQ, hjP, hstarσt, hgσt]
    have hJprod := shibaJwFlipParity_up_hop_product c p q hcond.1 hcond.2
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
    rw [show shibaJwFlipParity N c * shibaGauge A (shibaConfig N c)
          * ((-1 : ℂ) ^ (q : ℕ) * jwSign (2 * N + 1) (spinfulIndex N q 0) c
            * ((-1 : ℂ) ^ (p : ℕ) * jwSign (2 * N + 1) (spinfulIndex N p 0)
              (Function.update c (spinfulIndex N q 0) 0)))
          * (shibaJwFlipParity N (Function.update (Function.update c (spinfulIndex N q 0) 0)
              (spinfulIndex N p 0) 1) * shibaGauge A (shibaConfig N c))
        = (shibaJwFlipParity N c * shibaJwFlipParity N (Function.update
              (Function.update c (spinfulIndex N q 0) 0) (spinfulIndex N p 0) 1))
          * (shibaGauge A (shibaConfig N c) * shibaGauge A (shibaConfig N c))
          * ((-1 : ℂ) ^ (p : ℕ) * (-1 : ℂ) ^ (q : ℕ))
          * (jwSign (2 * N + 1) (spinfulIndex N q 0) c
            * jwSign (2 * N + 1) (spinfulIndex N p 0)
              (Function.update c (spinfulIndex N q 0) 0)) from by ring,
      hJprod, hg2, mul_one, hab, one_mul]
  · have hcondσ : ¬ (shibaConfig N c (spinfulIndex N q 0) = 1
        ∧ (Function.update (shibaConfig N c) (spinfulIndex N q 0) 0)
          (spinfulIndex N p 0) = 0) := by
      rw [hσQ, hupdQ, shibaConfig_apply_up]; exact hcond
    rw [if_neg hcondσ, if_neg hcond, smul_zero, Matrix.mulVec_zero]

end LatticeSystem.Fermion
