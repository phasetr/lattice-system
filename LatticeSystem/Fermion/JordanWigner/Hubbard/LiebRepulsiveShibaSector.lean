import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaInteraction
import LatticeSystem.Fermion.JordanWigner.Hubbard.ChargesCore

/-!
# The Shiba unitary exchanges the number and spin-`z` charges (Tasaki §9.3.3/§10.2.2)

Sector layer (c7 foundation) of the axiom-free portion of **Tasaki Theorem 10.4** (Lieb's
theorem for the repulsive Hubbard model at half-filling), Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §§9.3.3/10.2.2,
pp. 334–352.

The Shiba particle–hole flip on the down species (`n̂_{x↓} ↦ 1 − n̂_{x↓}`, `shibaConfig`)
does **not** preserve the electron-number sectors: it interchanges the total particle
number `N̂` and (twice) the total spin-`z` charge `Ŝ³ = ½(N̂_↑ − N̂_↓)`.  On the Fock
occupation basis, with `Û = shibaSignedUnitary N s` (modulus-one sign `s`):

* `Û · N̂ · Ûᴴ = 2 Ŝ³ + (|Λ|) · 1`  (`shibaSignedUnitary_conj_totalNumber`), and
* `Ûᴴ · Ŝ³ · Û = ½ (N̂ − (|Λ|) · 1)`  (`shibaSignedUnitary_conj_totalSpinZ`),

where `|Λ| = N + 1`.  Both are diagonal-conjugation computations: `N̂` and `Ŝ³` are
diagonal in the occupation basis, and the flip `shibaConfig` fixes the up occupations
while sending `n̂_{x↓} ↦ 1 − n̂_{x↓}`.  These are the identities that transport the
attractive-model **number**-sector ground state (Theorem 10.2) to the repulsive-model
**spin-`z`**-sector ground state at half filling (Theorem 10.4).

## Main results

* `sum_spinful_split` — the occupation sum splits over the spin/site bijection.
* `fermionTotalNumber_eq_diagonal` / `fermionTotalUpNumber_eq_diagonal` /
  `fermionTotalDownNumber_eq_diagonal` / `fermionTotalSpinZ_eq_diagonal` — the charges
  are diagonal in the occupation basis.
* `shibaSignedUnitary_conj_diagonal` / `shibaSignedUnitary_self_conj_diagonal` — the two
  diagonal-conjugation directions reindex a diagonal matrix by `shibaConfig`.
* `shibaSignedUnitary_conj_totalNumber` — `Û N̂ Ûᴴ = 2 Ŝ³ + (N+1)·1`.
* `shibaSignedUnitary_conj_totalSpinZ` — `Ûᴴ Ŝ³ Û = ½(N̂ − (N+1)·1)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §§9.3.3/10.2.2, eqs. (9.3.48)/(9.3.50), pp. 334–352;
E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## The occupation sum splits over the spin/site bijection -/

/-- **The occupation sum splits over the spin/site bijection** `(x, σ) ↦ 2x + σ`:
`∑_{j} g j = ∑_{x} (g(2x) + g(2x+1))`.  The map `spinfulIndex` is a bijection
`Fin (N+1) × Fin 2 ≃ Fin (2N+2)` (`spinfulIndex_eq_iff` + `exists_spinfulIndex`). -/
theorem sum_spinful_split {M : Type*} [AddCommMonoid M] (N : ℕ) (g : Fin (2 * N + 2) → M) :
    ∑ j : Fin (2 * N + 2), g j
      = ∑ x : Fin (N + 1), (g (spinfulIndex N x 0) + g (spinfulIndex N x 1)) := by
  have hbij : Function.Bijective
      (fun p : Fin (N + 1) × Fin 2 => spinfulIndex N p.1 p.2) := by
    constructor
    · rintro ⟨a, r⟩ ⟨b, s⟩ h
      obtain ⟨h1, h2⟩ := (spinfulIndex_eq_iff N a b r s).mp h
      simp only [Prod.mk.injEq]
      exact ⟨h1, h2⟩
    · intro k
      obtain ⟨a, r, hk⟩ := exists_spinfulIndex N k
      exact ⟨(a, r), hk.symm⟩
  rw [← Fintype.sum_bijective (fun p : Fin (N + 1) × Fin 2 => spinfulIndex N p.1 p.2) hbij
        (fun p => g (spinfulIndex N p.1 p.2)) g (fun _ => rfl), Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun x _ => Fin.sum_univ_two _)

/-! ## The conserved charges are diagonal in the occupation basis -/

/-- **The total particle number is diagonal**: `N̂ = diagonal (c ↦ ∑_j c j)`. -/
theorem fermionTotalNumber_eq_diagonal (N : ℕ) :
    fermionTotalNumber (2 * N + 1)
      = Matrix.diagonal (fun c => ∑ j : Fin (2 * N + 2), ((c j).val : ℂ)) := by
  rw [fermionTotalNumber,
    Finset.sum_congr rfl (fun j _ => fermionMultiNumber_eq_diagonal (2 * N + 1) j)]
  funext τ ρ
  rw [Matrix.sum_apply]
  simp only [Matrix.diagonal_apply]
  by_cases h : τ = ρ
  · simp only [if_pos h]
  · simp only [if_neg h, Finset.sum_const_zero]

/-- **The total spin-up number is diagonal**: `N̂_↑ = diagonal (c ↦ ∑_x c(2x))`. -/
theorem fermionTotalUpNumber_eq_diagonal (N : ℕ) :
    fermionTotalUpNumber N
      = Matrix.diagonal (fun c => ∑ x : Fin (N + 1), ((c (spinfulIndex N x 0)).val : ℂ)) := by
  rw [fermionTotalUpNumber]
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [fermionUpNumber, fermionMultiNumber_eq_diagonal])]
  funext τ ρ
  rw [Matrix.sum_apply]
  simp only [Matrix.diagonal_apply]
  by_cases h : τ = ρ
  · simp only [if_pos h]
  · simp only [if_neg h, Finset.sum_const_zero]

/-- **The total spin-down number is diagonal**: `N̂_↓ = diagonal (c ↦ ∑_x c(2x+1))`. -/
theorem fermionTotalDownNumber_eq_diagonal (N : ℕ) :
    fermionTotalDownNumber N
      = Matrix.diagonal (fun c => ∑ x : Fin (N + 1), ((c (spinfulIndex N x 1)).val : ℂ)) := by
  rw [fermionTotalDownNumber]
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [fermionDownNumber, fermionMultiNumber_eq_diagonal])]
  funext τ ρ
  rw [Matrix.sum_apply]
  simp only [Matrix.diagonal_apply]
  by_cases h : τ = ρ
  · simp only [if_pos h]
  · simp only [if_neg h, Finset.sum_const_zero]

/-- **The total spin-`z` charge is diagonal**:
`Ŝ³ = diagonal (c ↦ ½(∑_x c(2x) − ∑_x c(2x+1)))`. -/
theorem fermionTotalSpinZ_eq_diagonal (N : ℕ) :
    fermionTotalSpinZ N
      = Matrix.diagonal (fun c => (1 / 2 : ℂ) *
          ((∑ x : Fin (N + 1), ((c (spinfulIndex N x 0)).val : ℂ)) -
            (∑ x : Fin (N + 1), ((c (spinfulIndex N x 1)).val : ℂ)))) := by
  rw [fermionTotalSpinZ, fermionTotalUpNumber_eq_diagonal, fermionTotalDownNumber_eq_diagonal]
  funext τ ρ
  by_cases h : τ = ρ
  · subst h
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, smul_eq_mul,
      if_true]
  · simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, smul_eq_mul,
      if_neg h, sub_zero, mul_zero]

/-! ## Diagonal conjugation by the Shiba unitary -/

/-- **Conjugating a diagonal by the sign-dressed Shiba unitary** reindexes it by the
Shiba flip: `Ûᴴ · diagonal d · Û = diagonal (d ∘ shibaConfig)` (modulus-one sign). -/
theorem shibaSignedUnitary_conj_diagonal (s : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hs : ∀ c, star (s c) * s c = 1) (d : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    Matrix.conjTranspose (shibaSignedUnitary N s) * Matrix.diagonal d * shibaSignedUnitary N s
      = Matrix.diagonal (fun c => d (shibaConfig N c)) := by
  rw [shibaSignedUnitary_conjTranspose, shibaSignedUnitary,
    show shibaPermMatrix N * Matrix.diagonal (star s) * Matrix.diagonal d
          * (Matrix.diagonal s * shibaPermMatrix N)
        = shibaPermMatrix N
          * (Matrix.diagonal (star s) * Matrix.diagonal d * Matrix.diagonal s)
          * shibaPermMatrix N from by simp only [Matrix.mul_assoc],
    diagonal_mul_diagonal, diagonal_mul_diagonal,
    show (fun c => (star s) c * d c * s c) = d from by
      funext c
      simp only [Pi.star_apply]
      rw [show star (s c) * d c * s c = d c * (star (s c) * s c) from by ring, hs c, mul_one],
    shibaPermMatrix_conj_diagonal]

/-- **Conjugating a diagonal by the Shiba unitary on the other side** reindexes it by
the Shiba flip: `Û · diagonal d · Ûᴴ = diagonal (d ∘ shibaConfig)` (modulus-one sign). -/
theorem shibaSignedUnitary_self_conj_diagonal (s : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hs : ∀ c, star (s c) * s c = 1) (d : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    shibaSignedUnitary N s * Matrix.diagonal d * Matrix.conjTranspose (shibaSignedUnitary N s)
      = Matrix.diagonal (fun c => d (shibaConfig N c)) := by
  rw [shibaSignedUnitary_conjTranspose, shibaSignedUnitary,
    show Matrix.diagonal s * shibaPermMatrix N * Matrix.diagonal d
          * (shibaPermMatrix N * Matrix.diagonal (star s))
        = Matrix.diagonal s
          * (shibaPermMatrix N * Matrix.diagonal d * shibaPermMatrix N)
          * Matrix.diagonal (star s) from by simp only [Matrix.mul_assoc],
    shibaPermMatrix_conj_diagonal, diagonal_mul_diagonal, diagonal_mul_diagonal,
    show (fun c => s c * d (shibaConfig N c) * (star s) c)
          = (fun c => d (shibaConfig N c)) from by
      funext c
      simp only [Pi.star_apply]
      rw [show s c * d (shibaConfig N c) * star (s c)
            = d (shibaConfig N c) * (star (s c) * s c) from by ring, hs c, mul_one]]

/-! ## The Shiba unitary exchanges `N̂` and `2 Ŝ³` -/

/-- **The Shiba unitary sends the number operator to `2 Ŝ³` plus a shift**
(Tasaki §9.3.3, p. 336): `Û · N̂ · Ûᴴ = 2 Ŝ³ + (N+1) · 1`.  Under `shibaConfig` the
up occupations are fixed and each down occupation `a` becomes `1 − a`, so
`∑_j (shibaConfig c) j = (N̂_↑ − N̂_↓)(c) + (N+1)`, and `N̂_↑ − N̂_↓ = 2 Ŝ³`. -/
theorem shibaSignedUnitary_conj_totalNumber (s : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hs : ∀ c, star (s c) * s c = 1) :
    shibaSignedUnitary N s * fermionTotalNumber (2 * N + 1)
        * Matrix.conjTranspose (shibaSignedUnitary N s)
      = (2 : ℂ) • fermionTotalSpinZ N
        + ((N : ℂ) + 1) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
  rw [fermionTotalNumber_eq_diagonal, shibaSignedUnitary_self_conj_diagonal s hs,
    fermionTotalSpinZ_eq_diagonal]
  funext τ ρ
  by_cases h : τ = ρ
  · subst h
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul, if_true]
    rw [sum_spinful_split N (fun j => ((shibaConfig N τ j).val : ℂ))]
    simp only [shibaConfig_apply_up, shibaConfig_apply_down, flipOccupation_val_complex]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul, if_neg h, mul_zero, add_zero]

/-- **The Shiba unitary sends the spin-`z` charge to a half-shifted number operator**
(Tasaki §9.3.3, p. 336): `Ûᴴ · Ŝ³ · Û = ½ (N̂ − (N+1) · 1)`.  Under `shibaConfig` the
up occupations are fixed and each down occupation `a` becomes `1 − a`, so
`Ŝ³(shibaConfig c) = ½((N̂_↑ + N̂_↓)(c) − (N+1)) = ½(N̂(c) − (N+1))`. -/
theorem shibaSignedUnitary_conj_totalSpinZ (s : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hs : ∀ c, star (s c) * s c = 1) :
    Matrix.conjTranspose (shibaSignedUnitary N s) * fermionTotalSpinZ N
        * shibaSignedUnitary N s
      = (1 / 2 : ℂ) • (fermionTotalNumber (2 * N + 1)
          - ((N : ℂ) + 1) • (1 : ManyBodyOp (Fin (2 * N + 2)))) := by
  rw [fermionTotalSpinZ_eq_diagonal, shibaSignedUnitary_conj_diagonal s hs,
    fermionTotalNumber_eq_diagonal]
  funext τ ρ
  by_cases h : τ = ρ
  · subst h
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul, if_true]
    rw [sum_spinful_split N (fun j => ((τ j).val : ℂ))]
    simp only [shibaConfig_apply_up, shibaConfig_apply_down, flipOccupation_val_complex]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  · simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.one_apply,
      smul_eq_mul, if_neg h, mul_zero, sub_zero]

end LatticeSystem.Fermion
