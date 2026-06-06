import LatticeSystem.Fermion.JordanWigner.Hubbard.TJExchangeMatrixElement

/-!
# Tasaki 11.5: the exchange spin-flip matrix element is `0` or `1` (Prop 11.24 PR-B7-3g)

The off-diagonal exchange entry of the t-J effective matrix comes from the spin-flip ladder
`Ŝ⁺_i Ŝ⁻_j` (the `n̂_x n̂_y / 4` and `Ŝ³_x Ŝ³_y` parts are diagonal and drop off-diagonally).  This
file shows the per-bond exchange matrix element is `{0,1}`-valued, hence non-negative, mirroring the
kinetic non-negativity:

* `Ŝ⁻_j = ĉ†_{j↓} ĉ_{j↑}` kills `|Φ_s⟩` unless site `j` carries spin `↑` (`s j = ↑`);
* with `s j = ↑`, the subsequent `Ŝ⁺_i = ĉ†_{i↑} ĉ_{i↓}` kills the state unless site `i` carries
  spin `↓` (`s i = ↓`), for `i ≠ j`;
* for the antiparallel pair `s i = ↓`, `s j = ↑` the element is the sign-free indicator
  `[s' = tJSpinSwap s i j] ∈ {0,1}` (`fermionSpinFlip_matrixElement`).

Combined with the cyclic graph coupling, every per-pair summand
`couplingOf(cycleGraph) i j · ⟨Φ_{s'}|Ŝ⁺_i Ŝ⁻_j|Φ_s⟩` is therefore `0` or `1`; the exchange
off-diagonal entry `−(J/2)·(…) ≤ 0` for `J ≥ 0`, feeding the Perron–Frobenius step.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- **The source-empty exchange matrix element vanishes.**  If site `j` does not carry spin `↑`
(`s j ≠ ↑`), the lowering operator `Ŝ⁻_j = ĉ†_{j↓} ĉ_{j↑}` annihilates `|Φ_s⟩` (its inner `ĉ_{j↑}`
hits an empty up-orbital), so `⟨Φ_{s'}|Ŝ⁺_i Ŝ⁻_j|Φ_s⟩ = 0`. -/
theorem fermionSpinFlip_matrixElement_eq_zero_of_source (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) (hj : s j ≠ 1) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
            (basisVec (tJConfigOf N s))) w) = 0 := by
  have hmin : (fermionSiteSpinMinus N j).mulVec (basisVec (tJConfigOf N s)) = 0 := by
    unfold fermionSiteSpinMinus fermionDownCreation fermionUpAnnihilation
    rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec,
      if_neg (show tJConfigOf N s (spinfulIndex N j 0) ≠ 1 by
        rw [tJConfigOf_apply_up, if_neg hj]; decide),
      Matrix.mulVec_zero]
  have hzero : (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
      (basisVec (tJConfigOf N s)) = 0 := by
    rw [← Matrix.mulVec_mulVec, hmin, Matrix.mulVec_zero]
  rw [hzero]; simp

/-- **The target-occupied exchange matrix element vanishes.**  For `i ≠ j` with `s j = ↑` but
`s i ≠ ↓`, the lowering `Ŝ⁻_j` succeeds (flipping `j` to `↓`) but the raising
`Ŝ⁺_i = ĉ†_{i↑} ĉ_{i↓}` then hits an empty down-orbital at site `i`, so
`⟨Φ_{s'}|Ŝ⁺_i Ŝ⁻_j|Φ_s⟩ = 0`. -/
theorem fermionSpinFlip_matrixElement_eq_zero_of_target (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) (hij : i ≠ j) (hj : s j = 1) (hi : s i ≠ 2) :
    (∑ w, basisVec (tJConfigOf N s') w *
        ((fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
            (basisVec (tJConfigOf N s))) w) = 0 := by
  -- `Ŝ⁻_j |Φ_s⟩` produces the `j`-lowered configuration (up two orbital updates at site `j`).
  have hmin : (fermionSiteSpinMinus N j).mulVec (basisVec (tJConfigOf N s)) =
      jwSign (2 * N + 1) (spinfulIndex N j 0) (tJConfigOf N s) •
        jwSign (2 * N + 1) (spinfulIndex N j 1)
            (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0) •
          basisVec (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
            (spinfulIndex N j 1) 1) := by
    unfold fermionSiteSpinMinus fermionDownCreation fermionUpAnnihilation
    rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec,
      if_pos (show tJConfigOf N s (spinfulIndex N j 0) = 1 by rw [tJConfigOf_apply_up, if_pos hj]),
      Matrix.mulVec_smul, fermionMultiCreation_mulVec_basisVec,
      if_pos (show (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
          (spinfulIndex N j 1) = 0 by
        rw [Function.update_of_ne (by
            rw [ne_eq, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)),
          tJConfigOf_apply_down, if_neg (by rw [hj]; decide)])]
  -- The subsequent `Ŝ⁺_i` raising fails: site `i`'s down-orbital is empty in the lowered config.
  have hplus : (fermionSiteSpinPlus N i).mulVec
      (basisVec (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
        (spinfulIndex N j 1) 1)) = 0 := by
    unfold fermionSiteSpinPlus fermionUpCreation fermionDownAnnihilation
    rw [← Matrix.mulVec_mulVec, fermionMultiAnnihilation_mulVec_basisVec,
      if_neg (show (Function.update (Function.update (tJConfigOf N s) (spinfulIndex N j 0) 0)
          (spinfulIndex N j 1) 1) (spinfulIndex N i 1) ≠ 1 by
        rw [Function.update_of_ne (fun h => hij ((spinfulIndex_eq_iff N i j 1 1).mp h).1),
          Function.update_of_ne (by
            rw [ne_eq, spinfulIndex_eq_iff]; rintro ⟨_, h⟩; exact absurd h (by decide)),
          tJConfigOf_apply_down, if_neg hi]; decide),
      Matrix.mulVec_zero]
  have hzero : (fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
      (basisVec (tJConfigOf N s)) = 0 := by
    rw [← Matrix.mulVec_mulVec, hmin, Matrix.mulVec_smul, Matrix.mulVec_smul, hplus,
      smul_zero, smul_zero]
  rw [hzero]; simp

/-- **Each cyclic exchange summand is `0` or `1`.**  The graph-weighted spin-flip matrix element
`couplingOf(cycleGraph) i j · ⟨Φ_{s'}|Ŝ⁺_i Ŝ⁻_j|Φ_s⟩` is `0` or `1`: non-adjacent pairs are
killed by the coupling, and for an adjacent pair the element vanishes unless `s j = ↑` and
`s i = ↓`, in which
case the sign-free exchange indicator `[s' = tJSpinSwap s i j] ∈ {0,1}`. -/
theorem tJ_exchange_summand_zero_or_one (N : ℕ) (s s' : Fin (N + 1) → Fin 3)
    (i j : Fin (N + 1)) :
    couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
              (basisVec (tJConfigOf N s))) w) = 0 ∨
      couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionSiteSpinPlus N i * fermionSiteSpinMinus N j).mulVec
              (basisVec (tJConfigOf N s))) w) = 1 := by
  by_cases hAdj : (cycleGraph (N + 1)).Adj i j
  · have hcoup : couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j = 1 := by
      unfold couplingOf; rw [if_pos hAdj]
    have hij : i ≠ j := hAdj.ne
    rw [hcoup, one_mul]
    by_cases hj : s j = 1
    · by_cases hi : s i = 2
      · rw [fermionSpinFlip_matrixElement N s s' i j hi hj]; split_ifs <;> simp
      · rw [fermionSpinFlip_matrixElement_eq_zero_of_target N s s' i j hij hj hi]
        exact Or.inl rfl
    · rw [fermionSpinFlip_matrixElement_eq_zero_of_source N s s' i j hj]
      exact Or.inl rfl
  · have hcoup : couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j = 0 := by
      unfold couplingOf; rw [if_neg hAdj]
    rw [hcoup, zero_mul]; exact Or.inl rfl

end LatticeSystem.Fermion
