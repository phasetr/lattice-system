import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorExchange
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJDiagonalMatrixElement
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeBondSum
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJStepRelation

/-!
# Tasaki 11.5.3: the exchange bond acts as a half spin-swap on the filled sector (Theorem 11.26
PR3i)

On a fully occupied hard-core configuration `|Φ_s⟩` (`∀ k, s k ≠ 0`) the per-bond exchange operator
`¼ n̂_x n̂_y − Ŝ_x·Ŝ_y` of `tJExchange` acts as a half difference between `|Φ_s⟩` and the
spin-swapped state:

* `tJExchangeBond_mulVec_tJConfigOf_full` —
  `(¼ n̂_x n̂_y − Ŝ_x·Ŝ_y) |Φ_s⟩ = ½ (|Φ_s⟩ − |Φ_{tJSpinSwap s x y}⟩)`  (`x ≠ y`).

This is the ferromagnetic-Heisenberg singlet projector written on the configuration basis: the
diagonal `¼ n̂_x n̂_y − Ŝ³_x Ŝ³_y` and the ladder `½(Ŝ⁺_xŜ⁻_y + Ŝ⁻_xŜ⁺_y)` combine, using the
sign-free spin-swap action (`fermionSiteSpinPlus_mul_Minus_mulVec_tJConfigOf`).  Consequently a
ground state of `tJExchange` has spin-swap-invariant amplitudes on every bond — the input to the
half-filling degeneracy upper bound.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.3, Theorem 11.26 (pp. 445–447).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The exchange ladder `Ŝ⁺_i Ŝ⁻_j` annihilates a configuration whose source is not `↑`.**
If `s j ≠ ↑` the lowering `Ŝ⁻_j = ĉ†_{j↓}ĉ_{j↑}` hits an empty up-orbital. -/
theorem fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_source (N : ℕ)
    (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) (hj : s j ≠ 1) :
    (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec (basisVec (tJConfigOf N s)) = 0 :=
        by
  have hmin : (fermionSiteSpinMinus N j).mulVec (basisVec (tJConfigOf N s)) = 0 := by
    unfold fermionSiteSpinMinus fermionDownCreation fermionUpAnnihilation
    rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec,
      if_neg (show tJConfigOf N s (spinfulIndex N j 0) ≠ 1 by
        rw [tJConfigOf_apply_up, if_neg hj]; decide),
      Matrix.mulVec_zero]
  rw [← Matrix.mulVec_mulVec, hmin, Matrix.mulVec_zero]

/-- **The exchange ladder `Ŝ⁺_i Ŝ⁻_j` annihilates a configuration whose target is not `↓`.**
For `i ≠ j` with `s i ≠ ↓`, the raising `Ŝ⁺_i = ĉ†_{i↑}ĉ_{i↓}` hits an empty down-orbital at `i`
(unchanged by the `j`-local lowering `Ŝ⁻_j`). -/
theorem fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_target (N : ℕ)
    (s : Fin (N + 1) → Fin 3) (i j : Fin (N + 1)) (hij : i ≠ j) (hi : s i ≠ 2) :
    (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec (basisVec (tJConfigOf N s)) = 0 :=
        by
  by_cases hj : s j = 1
  · -- `Ŝ⁻_j |Φ_s⟩ = scalar • |c'⟩` with `c'` differing from `tJConfigOf s` only at `j`'s orbitals
    have hmin : (fermionSiteSpinMinus N j).mulVec (basisVec (tJConfigOf N s)) =
        jwSign (2 * N + 1) (spinfulIndex N j 0) (tJConfigOf N s) •
          jwSign (2 * N + 1) (spinfulIndex N j 1)
              (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0) •
            basisVec (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
              (spinfulIndex N j 1) 1) := by
      unfold fermionSiteSpinMinus fermionDownCreation fermionUpAnnihilation
      rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec,
        if_pos (show tJConfigOf N s (spinfulIndex N j 0) = 1 by
          rw [tJConfigOf_apply_up, if_pos hj]),
        Matrix.mulVec_smul, fermionMultiCreation_mulVec_basisVec,
        if_pos (show (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
            (spinfulIndex N j 1) = 0 by
          rw [Function.update_of_ne (by
              rw [ne_eq, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)),
            tJConfigOf_apply_down, if_neg (by rw [hj]; decide)])]
    -- `Ŝ⁺_i = ĉ†_{i↑}ĉ_{i↓}`; the down-annihilation at `i` hits an empty orbital (`s i ≠ ↓`)
    have hidx1 : Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
        (spinfulIndex N j 1) 1 (spinfulIndex N i 1) = 0 := by
      rw [Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 1 1).mp h).1),
        Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 1 0).mp h).1),
        tJConfigOf_apply_down, if_neg hi]
    rw [show fermionSiteSpinPlus N i * fermionSiteSpinMinus N j =
        fermionUpCreation N i * (fermionDownAnnihilation N i * fermionSiteSpinMinus N j) by
      rw [fermionSiteSpinPlus, mul_assoc],
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hmin]
    unfold fermionDownAnnihilation
    simp only [Matrix.mulVec_smul]
    rw [fermionMultiAnnihilation_mulVec_basisVec, if_neg (by rw [hidx1]; decide)]
    simp
  · exact fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_source N s i j hj

/-- **The reversed ladder `Ŝ⁻_x Ŝ⁺_y` as a sign-free swap.**  For an antiparallel pair `s x = ↑`,
`s y = ↓` (`x ≠ y`), `Ŝ⁻_x Ŝ⁺_y |Φ_s⟩ = |Φ_{tJSpinSwap s x y}⟩` (commute to `Ŝ⁺_y Ŝ⁻_x` at
`(y,x)`). -/
theorem fermionSpinMinusPlus_mulVec_tJConfigOf (N : ℕ) (s : Fin (N + 1) → Fin 3) (x y : Fin (N + 1))
    (hxy : x ≠ y) (hx : s x = 1) (hy : s y = 2) :
    (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y).mulVec (basisVec (tJConfigOf N s)) =
      basisVec (tJConfigOf N (tJSpinSwap s x y)) := by
  rw [fermionSiteSpinMinus_mul_Plus_comm N x y hxy,
    fermionSiteSpinPlus_mul_Minus_mulVec_tJConfigOf N s y x hy hx]
  congr 1
  rw [tJSpinSwap_eq_comp_swap, tJSpinSwap_eq_comp_swap, Equiv.swap_comm]

/-- The spin-swap is the identity move on a parallel pair (`s x = s y`). -/
theorem tJSpinSwap_eq_self_of_eq (s : Fin (N + 1) → Fin 3) (x y : Fin (N + 1)) (h : s x = s y) :
    tJSpinSwap s x y = s := by
  funext k
  simp only [tJSpinSwap]
  split_ifs with h1 h2
  · subst h1; exact h.symm
  · subst h2; exact h
  · rfl

/-- The reversed ladder `Ŝ⁻_x Ŝ⁺_y` annihilates a parallel configuration (`s x = s y`):
commute to `Ŝ⁺_y Ŝ⁻_x` and apply the source/target vanishing at `(y,x)`. -/
theorem fermionSpinMinusPlus_mulVec_tJConfigOf_eq_zero_of_eq (N : ℕ) (s : Fin (N + 1) → Fin 3)
    (x y : Fin (N + 1)) (hxy : x ≠ y) (h : s x = s y) :
    (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y).mulVec (basisVec (tJConfigOf N s)) = 0 :=
        by
  rw [fermionSiteSpinMinus_mul_Plus_comm N x y hxy]
  rcases (show ∀ a : Fin 3, a ≠ 0 ∨ a = 0 from fun a => by tauto) (s x) with _ | _ <;>
  · by_cases hsx1 : s x = 1
    · exact fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_target N s y x hxy.symm
        (by rw [← h, hsx1]; decide)
    · exact fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_source N s y x hsx1

/-- The reversed ladder `Ŝ⁻_x Ŝ⁺_y` annihilates a configuration with `s x ≠ ↑`: commute to
`Ŝ⁺_y Ŝ⁻_x` whose source `x` is not `↑`. -/
theorem fermionSpinMinusPlus_mulVec_tJConfigOf_eq_zero_of_source (N : ℕ) (s : Fin (N + 1) → Fin 3)
    (x y : Fin (N + 1)) (hxy : x ≠ y) (hsx : s x ≠ 1) :
    (fermionSiteSpinMinus N x * fermionSiteSpinPlus N y).mulVec (basisVec (tJConfigOf N s))
      = 0 := by
  rw [fermionSiteSpinMinus_mul_Plus_comm N x y hxy]
  exact fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_source N s y x hsx

/-- **The exchange bond acts as a half spin-swap on a filled configuration.**
For `x ≠ y` and `|Φ_s⟩` fully occupied (`s x ≠ 0`, `s y ≠ 0`),
`(¼ n̂_x n̂_y − Ŝ_x·Ŝ_y) |Φ_s⟩ = ½ (|Φ_s⟩ − |Φ_{tJSpinSwap s x y}⟩)`. -/
theorem tJExchangeBond_mulVec_tJConfigOf_full (N : ℕ) (s : Fin (N + 1) → Fin 3) (x y : Fin (N + 1))
    (hxy : x ≠ y) (hx : s x ≠ 0) (hy : s y ≠ 0) :
    ((1 / 4 : ℂ) • (fermionSiteNumber N x * fermionSiteNumber N y) - fermionSpinDot N x y).mulVec
        (basisVec (tJConfigOf N s))
      = (1 / 2 : ℂ) • (basisVec (tJConfigOf N s) - basisVec (tJConfigOf N (tJSpinSwap s x y))) := by
  have h3 : ∀ a : Fin 3, a ≠ 0 → a = 1 ∨ a = 2 := by decide
  -- the number product acts as the identity on a filled bond
  have hnn : (fermionSiteNumber N x * fermionSiteNumber N y).mulVec (basisVec (tJConfigOf N s))
      = (1 : ℂ) • basisVec (tJConfigOf N s) := by
    rw [← Matrix.mulVec_mulVec, fermionSiteNumber_mulVec_basisVec, Matrix.mulVec_smul,
      fermionSiteNumber_mulVec_basisVec, smul_smul]
    congr 1
    rw [tJConfigOf_apply_up, tJConfigOf_apply_down, tJConfigOf_apply_up, tJConfigOf_apply_down]
    rcases h3 (s x) hx with h | h <;> rcases h3 (s y) hy with h' | h' <;>
      simp only [h, h'] <;> norm_num
  -- the spin-z product acts as the parallel/antiparallel sign
  have hzz : (fermionSiteSpinZ N x * fermionSiteSpinZ N y).mulVec (basisVec (tJConfigOf N s))
      = (((1 / 2 : ℂ) * (((tJConfigOf N s (spinfulIndex N y 0)).val : ℂ)
            - ((tJConfigOf N s (spinfulIndex N y 1)).val : ℂ)))
          * ((1 / 2 : ℂ) * (((tJConfigOf N s (spinfulIndex N x 0)).val : ℂ)
            - ((tJConfigOf N s (spinfulIndex N x 1)).val : ℂ))))
        • basisVec (tJConfigOf N s) := by
    rw [← Matrix.mulVec_mulVec, fermionSiteSpinZ_mulVec_basisVec, Matrix.mulVec_smul,
      fermionSiteSpinZ_mulVec_basisVec, smul_smul]
  unfold fermionSpinDot
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hnn, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.add_mulVec, hzz]
  rcases h3 (s x) hx with hsx | hsx <;> rcases h3 (s y) hy with hsy | hsy
  · -- (↑,↑): both ladder terms vanish, parallel ⟹ swap = s
    rw [fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_target N s x y hxy (by rw [hsx]; decide),
      fermionSpinMinusPlus_mulVec_tJConfigOf_eq_zero_of_eq N s x y hxy (by rw [hsx, hsy]),
      tJSpinSwap_eq_self_of_eq s x y (by rw [hsx, hsy]),
      tJConfigOf_apply_up, tJConfigOf_apply_up, tJConfigOf_apply_down, tJConfigOf_apply_down]
    simp only [hsx, hsy, if_true, if_false, Fin.reduceEq, Fin.val_zero, Fin.val_one,
      Nat.cast_zero, Nat.cast_one]; module
  · -- (↑,↓): Ŝ⁻_xŜ⁺_y is the active swap
    rw [fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_source N s x y (by rw [hsy]; decide),
      fermionSpinMinusPlus_mulVec_tJConfigOf N s x y hxy hsx hsy,
      tJConfigOf_apply_up, tJConfigOf_apply_up, tJConfigOf_apply_down, tJConfigOf_apply_down]
    simp only [hsx, hsy, if_true, if_false, Fin.reduceEq, Fin.val_zero, Fin.val_one,
      Nat.cast_zero, Nat.cast_one]; module
  · -- (↓,↑): Ŝ⁺_xŜ⁻_y is the active swap
    rw [fermionSiteSpinPlus_mul_Minus_mulVec_tJConfigOf N s x y hsx hsy,
      fermionSpinMinusPlus_mulVec_tJConfigOf_eq_zero_of_source N s x y hxy (by rw [hsx]; decide),
      tJConfigOf_apply_up, tJConfigOf_apply_up, tJConfigOf_apply_down, tJConfigOf_apply_down]
    simp only [hsx, hsy, if_true, if_false, Fin.reduceEq, Fin.val_zero, Fin.val_one,
      Nat.cast_zero, Nat.cast_one]; module
  · -- (↓,↓): both ladder terms vanish, parallel ⟹ swap = s
    rw [fermionSpinPlusMinus_mulVec_tJConfigOf_eq_zero_of_source N s x y (by rw [hsy]; decide),
      fermionSpinMinusPlus_mulVec_tJConfigOf_eq_zero_of_eq N s x y hxy (by rw [hsx, hsy]),
      tJSpinSwap_eq_self_of_eq s x y (by rw [hsx, hsy]),
      tJConfigOf_apply_up, tJConfigOf_apply_up, tJConfigOf_apply_down, tJConfigOf_apply_down]
    simp only [hsx, hsy, if_true, if_false, Fin.reduceEq, Fin.val_zero, Fin.val_one,
      Nat.cast_zero, Nat.cast_one]; module

end LatticeSystem.Fermion
