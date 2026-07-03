import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaInteraction

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

end LatticeSystem.Fermion
