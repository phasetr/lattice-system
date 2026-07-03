import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaKinetic
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionSiteSpin
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractive

/-!
# The Shiba conjugation of the per-site spin operators (Tasaki §10.2.2, eq. (10.2.13))

Operator layer for **Tasaki Theorem 10.5** (Shen–Qiu–Tian; Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.2, p. 353,
eq. (10.2.13)).  The Shiba particle–hole transformation on the down species sends the
transverse spin operators to the on-site pair (η-pairing) operators:

`Ûᴴ Ŝ⁺_x Û = ε_x · ĉ†_{x↑} ĉ†_{x↓}`, `Ûᴴ Ŝ⁻_x Û = ε_x · ĉ_{x↓} ĉ_{x↑}`,

where `ε_x = gaugeSign A x = ±1` is the sublattice gauge.  Consequently
`Ûᴴ (Ŝ⁺_x Ŝ⁻_y) Û = (ε_x ε_y) · ĉ†_{x↑} ĉ†_{x↓} ĉ_{y↓} ĉ_{y↑}`, the on-site
pair-transfer correlation operator `hubbardPairCorrelationOp` of Theorem 10.3.

The mechanism is the same as the down-kinetic conjugation
(`shibaSignedUnitary_conj_downHop`): the particle–hole flip turns the down annihilation
into a down creation (and vice versa), the flipped-down Jordan–Wigner crossing sign
`(−1)^x (−1)^x = 1` cancels, and the sublattice gauge supplies the on-site factor `ε_x`.

## Main results

* `shibaSignedUnitary_conj_siteSpinPlus` — `Ûᴴ Ŝ⁺_x Û = ε_x · ĉ†_{x↑} ĉ†_{x↓}`.
* `shibaSignedUnitary_conj_siteSpinMinus` — `Ûᴴ Ŝ⁻_x Û = ε_x · ĉ_{x↓} ĉ_{x↑}`.
* `fermionSiteSpinMinus_mul_Plus_comm` — `Ŝ⁻_x Ŝ⁺_y = Ŝ⁺_y Ŝ⁻_x` for `x ≠ y`.
* `shibaSignedUnitary_conj_spinPlusMinus` —
  `Ûᴴ (Ŝ⁺_x Ŝ⁻_y) Û = (ε_x ε_y) · hubbardPairCorrelationOp N x y`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.2, eq. (10.2.13), p. 353; E. H. Lieb, *Phys. Rev. Lett.* **62**
(1989) 1201; S.-Q. Shen, Z.-M. Qiu, G.-S. Tian, *Phys. Rev. Lett.* **72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## Single-site sign products of the Shiba dressing -/

/-- **Single-mode crossing-parity flip product**: flipping the occupation of the
spin-`r` mode at site `x` multiplies the spin-`r` crossing parity by `(−1)^x`.  Stated
as a `±1` product to avoid division:
`cs r (update c (2x+r) w) · cs r c = (−1)^x` whenever the update actually flips the
occupation (`c (2x+r) ≠ w`); the two occupations differ, so exactly one factor is
`(−1)^x` and the other is `1`, while every other site squares to `1`. -/
theorem shibaCrossingSpecies_update_flip_product (r : Fin 2)
    (c : Fin (2 * N + 2) → Fin 2) (x : Fin (N + 1)) (w : Fin 2)
    (h : c (spinfulIndex N x r) ≠ w) :
    shibaCrossingSpecies N r (Function.update c (spinfulIndex N x r) w)
        * shibaCrossingSpecies N r c = (-1 : ℂ) ^ (x : ℕ) := by
  have hrest : ∀ y ∈ Finset.univ.erase x,
      (if (Function.update c (spinfulIndex N x r) w) (spinfulIndex N y r) = 1
          then (-1 : ℂ) ^ (y : ℕ) else 1)
        * (if c (spinfulIndex N y r) = 1 then (-1 : ℂ) ^ (y : ℕ) else 1) = 1 := by
    intro y hy
    rw [Finset.mem_erase] at hy
    have hne : spinfulIndex N y r ≠ spinfulIndex N x r :=
      fun hh => hy.1 ((spinfulIndex_eq_iff N y x r r).mp hh).1
    rw [Function.update_of_ne hne]
    by_cases hc : c (spinfulIndex N y r) = 1
    · rw [if_pos hc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    · rw [if_neg hc, mul_one]
  rw [shibaCrossingSpecies, shibaCrossingSpecies, ← Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
    Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one, Function.update_self]
  by_cases hw : w = 1
  · subst hw
    rw [if_pos rfl, if_neg h, mul_one]
  · have hw0 : w = 0 := by omega
    subst hw0
    rw [if_neg (by decide : ¬ (0 : Fin 2) = 1),
      if_pos (show c (spinfulIndex N x r) = 1 by omega), one_mul]

/-- **Single-down-mode sublattice-gauge flip product**: flipping the occupation of the
down mode `2x+1` multiplies the sublattice gauge by `ε_x = gaugeSign A x`.
`g (update c (2x+1) w) · g c = ε_x` whenever the update flips the occupation.  If
`x ∈ A` the down mode `2x+1` is not read by the gauge (which ranges over `Aᶜ`), so the
product is `1 = ε_x`; if `x ∈ Aᶜ` the flipped factor contributes `−1 = ε_x`. -/
theorem shibaGauge_update_down_flip_product (A : Finset (Fin (N + 1)))
    (c : Fin (2 * N + 2) → Fin 2) (x : Fin (N + 1)) (w : Fin 2)
    (h : c (spinfulIndex N x 1) ≠ w) :
    shibaGauge A (Function.update c (spinfulIndex N x 1) w) * shibaGauge A c
      = gaugeSign A x := by
  unfold gaugeSign
  by_cases hxA : x ∈ A
  · rw [if_pos hxA, shibaGauge, shibaGauge, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun y hy => ?_)
    have hyx : y ≠ x := by rintro rfl; exact (Finset.mem_filter.mp hy).2 hxA
    have hne : spinfulIndex N y 1 ≠ spinfulIndex N x 1 :=
      fun hh => hyx ((spinfulIndex_eq_iff N y x 1 1).mp hh).1
    rw [Function.update_of_ne hne]
    by_cases hc : c (spinfulIndex N y 1) = 0
    · rw [if_pos hc]; ring
    · rw [if_neg hc]; ring
  · have hrest : ∀ y ∈ (bipartitionComplement A).erase x,
        (if (Function.update c (spinfulIndex N x 1) w) (spinfulIndex N y 1) = 0
            then (1 : ℂ) else -1)
          * (if c (spinfulIndex N y 1) = 0 then (1 : ℂ) else -1) = 1 := by
      intro y hy
      rw [Finset.mem_erase] at hy
      have hne : spinfulIndex N y 1 ≠ spinfulIndex N x 1 :=
        fun hh => hy.1 ((spinfulIndex_eq_iff N y x 1 1).mp hh).1
      rw [Function.update_of_ne hne]
      by_cases hc : c (spinfulIndex N y 1) = 0
      · rw [if_pos hc]; ring
      · rw [if_neg hc]; ring
    rw [if_neg hxA, shibaGauge, shibaGauge, ← Finset.prod_mul_distrib,
      ← Finset.mul_prod_erase (bipartitionComplement A) _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxA⟩),
      Finset.prod_congr rfl hrest, Finset.prod_const_one, mul_one, Function.update_self]
    have hkey : ∀ a b : Fin 2, a ≠ b →
        (if b = 0 then (1 : ℂ) else -1) * (if a = 0 then 1 else -1) = -1 := by
      intro a b hab; fin_cases a <;> fin_cases b <;> simp_all
    exact hkey (c (spinfulIndex N x 1)) w h

/-! ## The Shiba conjugation of `Ŝ⁺` (Tasaki eq. (10.2.13)) -/

/-- **The Shiba conjugation sends `Ŝ⁺_x` to the on-site pair creation** (Tasaki
eq. (10.2.13), p. 353):
`Ûᴴ Ŝ⁺_x Û = ε_x · ĉ†_{x↑} ĉ†_{x↓}` with `ε_x = gaugeSign A x`.  The particle–hole
flip turns the down annihilation `ĉ_{x↓}` into the down creation `ĉ†_{x↓}`; the up
creation `ĉ†_{x↑}` is untouched.  The flipped-down crossing sign `(−1)^x (−1)^x = 1`
cancels and the sublattice gauge supplies `ε_x`. -/
theorem shibaSignedUnitary_conj_siteSpinPlus (A : Finset (Fin (N + 1))) (x : Fin (N + 1)) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * fermionSiteSpinPlus N x * shibaSignedUnitary N (shibaSignFn A)
      = gaugeSign A x • (fermionUpCreation N x * fermionDownCreation N x) := by
  have hP01 : spinfulIndex N x 0 ≠ spinfulIndex N x 1 :=
    fun h => (by decide : (0 : Fin 2) ≠ 1) ((spinfulIndex_eq_iff N x x 0 1).mp h).2
  have hflip1 : ∀ a : Fin 2, flipOccupation a = 1 ↔ a = 0 := by intro a; fin_cases a <;> decide
  apply matrix_ext_mulVec_basisVec
  intro c
  simp only [fermionSiteSpinPlus, fermionUpCreation, fermionDownCreation, fermionDownAnnihilation]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, shibaSignedUnitary_mulVec_basisVec,
    Matrix.mulVec_smul, fermionMultiCreation_mul_Annihilation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N x 0) (spinfulIndex N x 1) (shibaConfig N c),
    Matrix.smul_mulVec, fermionMultiCreation_mul_Creation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N x 0) (spinfulIndex N x 1) c]
  have hcondσ_iff : (shibaConfig N c (spinfulIndex N x 1) = 1
        ∧ (Function.update (shibaConfig N c) (spinfulIndex N x 1) 0) (spinfulIndex N x 0) = 0)
      ↔ (c (spinfulIndex N x 1) = 0
        ∧ (Function.update c (spinfulIndex N x 1) 1) (spinfulIndex N x 0) = 0) := by
    rw [shibaConfig_apply_down, Function.update_of_ne hP01, shibaConfig_apply_up,
      Function.update_of_ne hP01, hflip1]
  by_cases hcond : c (spinfulIndex N x 1) = 0
      ∧ (Function.update c (spinfulIndex N x 1) 1) (spinfulIndex N x 0) = 0
  · have hcondσ := hcondσ_iff.mpr hcond
    have hcP0 : c (spinfulIndex N x 0) = 0 := by
      have := hcond.2; rwa [Function.update_of_ne hP01] at this
    set dL : Fin (2 * N + 2) → Fin 2 :=
      Function.update (Function.update (shibaConfig N c) (spinfulIndex N x 1) 0)
        (spinfulIndex N x 0) 1 with hdL
    have hσdL : shibaConfig N dL
        = Function.update (Function.update c (spinfulIndex N x 1) 1) (spinfulIndex N x 0) 1 := by
      rw [hdL, shibaConfig_update_up, shibaConfig_update_down, shibaConfig_shibaConfig,
        show flipOccupation (0 : Fin 2) = 1 from rfl]
    -- The sublattice-gauge factor `⟨s(dL)⟩ s(σc) = ε_x`.
    have hg1 : shibaGauge A dL
        = shibaGauge A (Function.update (shibaConfig N c) (spinfulIndex N x 1) 0) :=
      shibaGauge_update_up A (Function.update (shibaConfig N c) (spinfulIndex N x 1) 0) x 1
    have hg2 : shibaGauge A (Function.update (shibaConfig N c) (spinfulIndex N x 1) 0)
        * shibaGauge A (shibaConfig N c) = gaugeSign A x := by
      refine shibaGauge_update_down_flip_product A (shibaConfig N c) x 0 ?_
      rw [shibaConfig_apply_down, hcond.1]; decide
    have hgauge : shibaGauge A dL * shibaGauge A (shibaConfig N c) = gaugeSign A x := by
      rw [hg1]; exact hg2
    -- The crossing-parity factor `J(dL) J(σc) = 1`.
    have hxx : ((-1 : ℂ) ^ (x : ℕ)) * ((-1 : ℂ) ^ (x : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hjf0 : shibaCrossingSpecies N 0 dL * shibaCrossingSpecies N 0 (shibaConfig N c)
        = (-1 : ℂ) ^ (x : ℕ) := by
      rw [hdL, Function.update_comm hP01.symm (0 : Fin 2) (1 : Fin 2) (shibaConfig N c),
        shibaCrossingSpecies_update_ne 0 _ x 1 0 (by decide)]
      refine shibaCrossingSpecies_update_flip_product 0 (shibaConfig N c) x 1 ?_
      rw [shibaConfig_apply_up, hcP0]; decide
    have hjf1 : shibaCrossingSpecies N 1 dL * shibaCrossingSpecies N 1 (shibaConfig N c)
        = (-1 : ℂ) ^ (x : ℕ) := by
      rw [hdL, shibaCrossingSpecies_update_ne 1 _ x 0 1 (by decide)]
      refine shibaCrossingSpecies_update_flip_product 1 (shibaConfig N c) x 0 ?_
      rw [shibaConfig_apply_down, hcond.1]; decide
    have hjflip : shibaJwFlipParity N dL * shibaJwFlipParity N (shibaConfig N c) = 1 := by
      rw [shibaJwFlipParity, shibaJwFlipParity,
        show (shibaCrossingSpecies N 0 dL * shibaCrossingSpecies N 1 dL)
              * (shibaCrossingSpecies N 0 (shibaConfig N c)
                * shibaCrossingSpecies N 1 (shibaConfig N c))
            = (shibaCrossingSpecies N 0 dL * shibaCrossingSpecies N 0 (shibaConfig N c))
              * (shibaCrossingSpecies N 1 dL * shibaCrossingSpecies N 1 (shibaConfig N c))
          from by ring, hjf0, hjf1, hxx]
    have hstar : star (shibaSignFn A dL) = shibaJwFlipParity N dL * shibaGauge A dL := by
      simp only [shibaSignFn, star_mul', shibaJwFlipParity_star, shibaGauge_star]
    have hsign : star (shibaSignFn A dL) * shibaSignFn A (shibaConfig N c) = gaugeSign A x := by
      rw [hstar, shibaSignFn]
      calc shibaJwFlipParity N dL * shibaGauge A dL
              * (shibaJwFlipParity N (shibaConfig N c) * shibaGauge A (shibaConfig N c))
          = (shibaJwFlipParity N dL * shibaJwFlipParity N (shibaConfig N c))
              * (shibaGauge A dL * shibaGauge A (shibaConfig N c)) := by ring
        _ = 1 * gaugeSign A x := by rw [hjflip, hgauge]
        _ = gaugeSign A x := one_mul _
    -- The Jordan–Wigner string signs reduce the flipped-`σ` state to the plain state.
    have hj0 : jwSign (2 * N + 1) (spinfulIndex N x 1) (shibaConfig N c)
        = (-1 : ℂ) ^ (x : ℕ) * jwSign (2 * N + 1) (spinfulIndex N x 1) c :=
      jwSign_shibaConfig_spinful x 1 c
    have hupd : Function.update (shibaConfig N c) (spinfulIndex N x 1) 0
        = shibaConfig N (Function.update c (spinfulIndex N x 1) 1) := by
      rw [shibaConfig_update_down, show flipOccupation (1 : Fin 2) = 0 from rfl]
    have hj1 : jwSign (2 * N + 1) (spinfulIndex N x 0)
          (Function.update (shibaConfig N c) (spinfulIndex N x 1) 0)
        = (-1 : ℂ) ^ (x : ℕ) * jwSign (2 * N + 1) (spinfulIndex N x 0)
          (Function.update c (spinfulIndex N x 1) 1) := by
      rw [hupd]; exact jwSign_shibaConfig_spinful x 0 (Function.update c (spinfulIndex N x 1) 1)
    rw [if_pos hcondσ, if_pos hcond, smul_smul, Matrix.mulVec_smul,
      shibaSignedUnitary_conjTranspose_mulVec_basisVec, hσdL, smul_smul, smul_smul]
    congr 1
    rw [hj0, hj1]
    linear_combination (jwSign (2 * N + 1) (spinfulIndex N x 1) c
        * jwSign (2 * N + 1) (spinfulIndex N x 0) (Function.update c (spinfulIndex N x 1) 1)
        * ((-1 : ℂ) ^ (x : ℕ) * (-1 : ℂ) ^ (x : ℕ))) * hsign
      + (jwSign (2 * N + 1) (spinfulIndex N x 1) c
        * jwSign (2 * N + 1) (spinfulIndex N x 0) (Function.update c (spinfulIndex N x 1) 1)
        * gaugeSign A x) * hxx
  · rw [if_neg (fun h => hcond (hcondσ_iff.mp h)), smul_zero, Matrix.mulVec_zero, if_neg hcond,
      smul_zero]

/-- **The Shiba conjugation sends `Ŝ⁻_x` to the on-site pair annihilation** (Tasaki
eq. (10.2.13), p. 353):
`Ûᴴ Ŝ⁻_x Û = ε_x · ĉ_{x↓} ĉ_{x↑}` with `ε_x = gaugeSign A x`.  The particle–hole
flip turns the down creation `ĉ†_{x↓}` into the down annihilation `ĉ_{x↓}`; the up
annihilation `ĉ_{x↑}` is untouched.  The crossing sign cancels as in
`shibaSignedUnitary_conj_siteSpinPlus`, and the sublattice gauge supplies `ε_x`. -/
theorem shibaSignedUnitary_conj_siteSpinMinus (A : Finset (Fin (N + 1))) (x : Fin (N + 1)) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * fermionSiteSpinMinus N x * shibaSignedUnitary N (shibaSignFn A)
      = gaugeSign A x • (fermionDownAnnihilation N x * fermionUpAnnihilation N x) := by
  have hP01 : spinfulIndex N x 0 ≠ spinfulIndex N x 1 :=
    fun h => (by decide : (0 : Fin 2) ≠ 1) ((spinfulIndex_eq_iff N x x 0 1).mp h).2
  have hflip0 : ∀ a : Fin 2, flipOccupation a = 0 ↔ a = 1 := by intro a; fin_cases a <;> decide
  apply matrix_ext_mulVec_basisVec
  intro c
  simp only [fermionSiteSpinMinus, fermionDownCreation, fermionUpAnnihilation,
    fermionDownAnnihilation]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, shibaSignedUnitary_mulVec_basisVec,
    Matrix.mulVec_smul, fermionMultiCreation_mul_Annihilation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N x 1) (spinfulIndex N x 0) (shibaConfig N c),
    Matrix.smul_mulVec, fermionMultiAnnihilation_mul_Annihilation_mulVec_basisVec (2 * N + 1)
      (spinfulIndex N x 1) (spinfulIndex N x 0) c]
  have hcondσ_iff : (shibaConfig N c (spinfulIndex N x 0) = 1
        ∧ (Function.update (shibaConfig N c) (spinfulIndex N x 0) 0) (spinfulIndex N x 1) = 0)
      ↔ (c (spinfulIndex N x 0) = 1
        ∧ (Function.update c (spinfulIndex N x 0) 0) (spinfulIndex N x 1) = 1) := by
    rw [shibaConfig_apply_up, Function.update_of_ne hP01.symm, shibaConfig_apply_down,
      Function.update_of_ne hP01.symm, hflip0]
  by_cases hcond : c (spinfulIndex N x 0) = 1
      ∧ (Function.update c (spinfulIndex N x 0) 0) (spinfulIndex N x 1) = 1
  · have hcondσ := hcondσ_iff.mpr hcond
    have hcP1 : c (spinfulIndex N x 1) = 1 := by
      have := hcond.2; rwa [Function.update_of_ne hP01.symm] at this
    set dL : Fin (2 * N + 2) → Fin 2 :=
      Function.update (Function.update (shibaConfig N c) (spinfulIndex N x 0) 0)
        (spinfulIndex N x 1) 1 with hdL
    have hσdL : shibaConfig N dL
        = Function.update (Function.update c (spinfulIndex N x 0) 0) (spinfulIndex N x 1) 0 := by
      rw [hdL, shibaConfig_update_down, shibaConfig_update_up, shibaConfig_shibaConfig,
        show flipOccupation (1 : Fin 2) = 0 from rfl]
    have hg1 : shibaGauge A dL
        = shibaGauge A (Function.update (shibaConfig N c) (spinfulIndex N x 1) 1) := by
      rw [hdL, Function.update_comm hP01 (0 : Fin 2) (1 : Fin 2) (shibaConfig N c)]
      exact shibaGauge_update_up A (Function.update (shibaConfig N c) (spinfulIndex N x 1) 1) x 0
    have hg2 : shibaGauge A (Function.update (shibaConfig N c) (spinfulIndex N x 1) 1)
        * shibaGauge A (shibaConfig N c) = gaugeSign A x := by
      refine shibaGauge_update_down_flip_product A (shibaConfig N c) x 1 ?_
      rw [shibaConfig_apply_down, hcP1]; decide
    have hgauge : shibaGauge A dL * shibaGauge A (shibaConfig N c) = gaugeSign A x := by
      rw [hg1]; exact hg2
    have hxx : ((-1 : ℂ) ^ (x : ℕ)) * ((-1 : ℂ) ^ (x : ℕ)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hjf0 : shibaCrossingSpecies N 0 dL * shibaCrossingSpecies N 0 (shibaConfig N c)
        = (-1 : ℂ) ^ (x : ℕ) := by
      rw [hdL, shibaCrossingSpecies_update_ne 0 _ x 1 1 (by decide)]
      refine shibaCrossingSpecies_update_flip_product 0 (shibaConfig N c) x 0 ?_
      rw [shibaConfig_apply_up, hcond.1]; decide
    have hjf1 : shibaCrossingSpecies N 1 dL * shibaCrossingSpecies N 1 (shibaConfig N c)
        = (-1 : ℂ) ^ (x : ℕ) := by
      rw [hdL, Function.update_comm hP01 (0 : Fin 2) (1 : Fin 2) (shibaConfig N c),
        shibaCrossingSpecies_update_ne 1 _ x 0 0 (by decide)]
      refine shibaCrossingSpecies_update_flip_product 1 (shibaConfig N c) x 1 ?_
      rw [shibaConfig_apply_down, hcP1]; decide
    have hjflip : shibaJwFlipParity N dL * shibaJwFlipParity N (shibaConfig N c) = 1 := by
      rw [shibaJwFlipParity, shibaJwFlipParity,
        show (shibaCrossingSpecies N 0 dL * shibaCrossingSpecies N 1 dL)
              * (shibaCrossingSpecies N 0 (shibaConfig N c)
                * shibaCrossingSpecies N 1 (shibaConfig N c))
            = (shibaCrossingSpecies N 0 dL * shibaCrossingSpecies N 0 (shibaConfig N c))
              * (shibaCrossingSpecies N 1 dL * shibaCrossingSpecies N 1 (shibaConfig N c))
          from by ring, hjf0, hjf1, hxx]
    have hstar : star (shibaSignFn A dL) = shibaJwFlipParity N dL * shibaGauge A dL := by
      simp only [shibaSignFn, star_mul', shibaJwFlipParity_star, shibaGauge_star]
    have hsign : star (shibaSignFn A dL) * shibaSignFn A (shibaConfig N c) = gaugeSign A x := by
      rw [hstar, shibaSignFn]
      calc shibaJwFlipParity N dL * shibaGauge A dL
              * (shibaJwFlipParity N (shibaConfig N c) * shibaGauge A (shibaConfig N c))
          = (shibaJwFlipParity N dL * shibaJwFlipParity N (shibaConfig N c))
              * (shibaGauge A dL * shibaGauge A (shibaConfig N c)) := by ring
        _ = 1 * gaugeSign A x := by rw [hjflip, hgauge]
        _ = gaugeSign A x := one_mul _
    have hj0 : jwSign (2 * N + 1) (spinfulIndex N x 0) (shibaConfig N c)
        = (-1 : ℂ) ^ (x : ℕ) * jwSign (2 * N + 1) (spinfulIndex N x 0) c :=
      jwSign_shibaConfig_spinful x 0 c
    have hupd : Function.update (shibaConfig N c) (spinfulIndex N x 0) 0
        = shibaConfig N (Function.update c (spinfulIndex N x 0) 0) :=
      (shibaConfig_update_up c x 0).symm
    have hj1 : jwSign (2 * N + 1) (spinfulIndex N x 1)
          (Function.update (shibaConfig N c) (spinfulIndex N x 0) 0)
        = (-1 : ℂ) ^ (x : ℕ) * jwSign (2 * N + 1) (spinfulIndex N x 1)
          (Function.update c (spinfulIndex N x 0) 0) := by
      rw [hupd]; exact jwSign_shibaConfig_spinful x 1 (Function.update c (spinfulIndex N x 0) 0)
    rw [if_pos hcondσ, if_pos hcond, smul_smul, Matrix.mulVec_smul,
      shibaSignedUnitary_conjTranspose_mulVec_basisVec, hσdL, smul_smul, smul_smul]
    congr 1
    rw [hj0, hj1]
    linear_combination (jwSign (2 * N + 1) (spinfulIndex N x 0) c
        * jwSign (2 * N + 1) (spinfulIndex N x 1) (Function.update c (spinfulIndex N x 0) 0)
        * ((-1 : ℂ) ^ (x : ℕ) * (-1 : ℂ) ^ (x : ℕ))) * hsign
      + (jwSign (2 * N + 1) (spinfulIndex N x 0) c
        * jwSign (2 * N + 1) (spinfulIndex N x 1) (Function.update c (spinfulIndex N x 0) 0)
        * gaugeSign A x) * hxx
  · rw [if_neg (fun h => hcond (hcondσ_iff.mp h)), smul_zero, Matrix.mulVec_zero, if_neg hcond,
      smul_zero]

/-! ## Transverse correlation reduces to the pair-transfer correlation -/

/-- **The Shiba conjugation of the transverse product** (Tasaki eq. (10.2.13), p. 353):
`Ûᴴ (Ŝ⁺_x Ŝ⁻_y) Û = (ε_x ε_y) · ĉ†_{x↑} ĉ†_{x↓} ĉ_{y↓} ĉ_{y↑}`, the sublattice-signed
pair-transfer correlation operator `hubbardPairCorrelationOp N x y` of Theorem 10.3. -/
theorem shibaSignedUnitary_conj_spinPlusMinus (A : Finset (Fin (N + 1))) (x y : Fin (N + 1)) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
        * shibaSignedUnitary N (shibaSignFn A)
      = (gaugeSign A x * gaugeSign A y) • hubbardPairCorrelationOp N x y := by
  have hUUc : shibaSignedUnitary N (shibaSignFn A)
      * Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A)) = 1 :=
    shibaSignedUnitary_self_mul_conjTranspose (shibaSignFn A)
      (fun c => shibaSignFn_star_mul_self A c)
  have hsplit : Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * (fermionSiteSpinPlus N x * fermionSiteSpinMinus N y)
        * shibaSignedUnitary N (shibaSignFn A)
      = (Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
          * fermionSiteSpinPlus N x * shibaSignedUnitary N (shibaSignFn A))
        * (Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
          * fermionSiteSpinMinus N y * shibaSignedUnitary N (shibaSignFn A)) := by
    rw [show (Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
            * fermionSiteSpinPlus N x * shibaSignedUnitary N (shibaSignFn A))
          * (Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
            * fermionSiteSpinMinus N y * shibaSignedUnitary N (shibaSignFn A))
        = Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A)) * fermionSiteSpinPlus N x
            * (shibaSignedUnitary N (shibaSignFn A)
              * Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A)))
            * fermionSiteSpinMinus N y * shibaSignedUnitary N (shibaSignFn A) from by
        noncomm_ring, hUUc, Matrix.mul_one]
    noncomm_ring
  rw [hsplit, shibaSignedUnitary_conj_siteSpinPlus, shibaSignedUnitary_conj_siteSpinMinus,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, hubbardPairCorrelationOp,
    ← mul_assoc (fermionUpCreation N x * fermionDownCreation N x) (fermionDownAnnihilation N y)
      (fermionUpAnnihilation N y)]

end LatticeSystem.Fermion
