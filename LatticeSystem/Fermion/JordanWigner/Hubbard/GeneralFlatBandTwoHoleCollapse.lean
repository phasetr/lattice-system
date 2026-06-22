import LatticeSystem.Fermion.JordanWigner.Hubbard.GeneralFlatBandTwoHoleCollapseCore

/-!
# Two-hole double-peel collapse and the eq. (11.3.49) sign flip (Tasaki §11.3.4)

The collapse of the canonical double peel `ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I σ)` to a single term at
the `(a,b)`-emptied target config, and the resulting Koszul sign flip under the `a↔b` spin swap.
Built on the determination lemmas in `GeneralFlatBandCanonicalCoord.lean`: the inner-sum collapse
(`flatBandSpinConfig_inner_sum_collapse`) and its off-diagonal vanishing
(`flatBandSpinConfig_inner_sum_other_outer_zero`), the single-term coordinate
`cDownUp_canonical_repr_twoHole`, the `σ`-independence and eraseIdx position arithmetic of canonical
positions (`flatBandSpinConfigList_choose_eq`, `flatBandSpinConfigList_choose_erase_shift`), and the
sign flip `cDownUp_canonical_repr_twoHole_swap_eq_neg` (= `coord_σ = -coord_{σ∘swap}`).

Split from `GeneralFlatBandCanonicalCoord.lean` (the coordinate/config/determination machinery) for
build speed.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.4, eq. (11.3.49).  Tracked in Issue #4363.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum Module
open scoped BigOperators ComplexOrder

variable {M : ℕ}

/-- **A flat-band Slater coordinate vanishes off the two relevant spin configs** (the eq. (11.3.49)
sum-collapse engine): if `τ` is neither `σ` nor `σ ∘ swap a b` on `I`, then the `(a,b)`-emptied
coordinate of `ĉ_{x,↓}ĉ_{x,↑}Slater(canonical I τ)` is zero.  Each double-peel term of
`cDownUp_canonical_repr_eq_sum` vanishes: a term with both guards (outer up, inner down) holding and
nonzero rest coordinate would force the config equality of
`flatBandSpinConfig_doublePeel_config_eq`, hence `τ = σ` or `τ = σ ∘ swap a b` on `I`, contradicting
the hypotheses; the other terms vanish by the failing guard. -/
theorem cDownUp_canonical_repr_eq_zero_of_ne {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ τ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (hσa : σ a = 0) (hσb : σ b = 1)
    (hne1 : ¬ ∀ z ∈ I, τ z = σ z) (hne2 : ¬ ∀ z ∈ I, τ z = (σ ∘ ⇑(Equiv.swap a b)) z) :
    (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ (flatBandSpinConfigList I τ)))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) = 0 := by
  -- per-(i,j) helper
  have hterm : ∀ (i : ℕ) (hi : i < (flatBandSpinConfigList I τ).length),
      ((flatBandSpinConfigList I τ)[i]).2 = 0 →
      ∀ (j : ℕ) (hj : j <
        (flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ).length),
      ((flatBandSpinConfigList (I.erase ((flatBandSpinConfigList I τ)[i]).1) τ)[j]).2 = 1 →
      (generalOccBasis eμ).repr (generalFlatBandSlaterState μ
        (((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) = 0 := by
    intro i hi hgi j hj hgj
    have hnd : (((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j).Nodup := by
      rw [flatBandSpinConfigList_eraseIdx_eraseIdx I τ hi hj]
      exact flatBandSpinConfigList_nodup _ _
    have hsub : ∀ q ∈ ((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j, q.1 ∈ I := by
      rw [flatBandSpinConfigList_eraseIdx_eraseIdx I τ hi hj]
      intro q hq
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
        (flatBandSpinConfigList_mem_fst_mem _ τ hq))
    obtain ⟨z, _, heq⟩ := generalFlatBandSlaterState_over_I_repr hbasis eμ idx hidx
      (((flatBandSpinConfigList I τ).eraseIdx i).eraseIdx j) hnd hsub _
    rw [heq]
    split_ifs with hcond
    · exfalso
      rcases flatBandSpinConfig_doublePeel_config_eq hbasis hidx σ τ hσa hσb hi hgi hj hgj hcond
        with h | h
      · exact hne1 h
      · exact hne2 h
    · ring
  -- main
  rw [cDownUp_canonical_repr_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hgi : ((flatBandSpinConfigList I τ).get i).2 = 0
  · rw [if_pos hgi]
    have hgi' : ((flatBandSpinConfigList I τ)[(i:ℕ)]'i.2).2 = 0 := by
      rw [← List.get_eq_getElem]; exact hgi
    have hpr38 := flatBandSpinConfigList_eraseIdx I τ i.2
    rw [Finset.sum_eq_zero, mul_zero, mul_zero]
    intro j _
    by_cases hgj : (((flatBandSpinConfigList I τ).eraseIdx (i:ℕ)).get j).2 = 1
    · have hjc : (j : ℕ) < (flatBandSpinConfigList
          (I.erase ((flatBandSpinConfigList I τ)[(i:ℕ)]'i.2).1) τ).length := by
        rw [← hpr38]; exact j.2
      have hgjc : ((flatBandSpinConfigList
          (I.erase ((flatBandSpinConfigList I τ)[(i:ℕ)]'i.2).1) τ)[(j:ℕ)]'hjc).2 = 1 := by
        rw [← List.getElem_of_eq hpr38 j.2, ← List.get_eq_getElem]; exact hgj
      rw [if_pos hgj, hterm (i:ℕ) i.2 hgi' (j:ℕ) hjc hgjc, mul_zero, mul_zero]
    · rw [if_neg hgj, zero_mul, mul_zero]
  · rw [if_neg hgi, zero_mul, mul_zero]

/-- **The ground-state coordinate sum collapses to two terms** (the eq. (11.3.49) sum collapse):
summing the `(a,b)`-emptied coordinate of `ĉ_{x,↓}ĉ_{x,↑}Slater` over all spin configs
`s : I → Fin 2` (weighted by `D s`) keeps only the two configs `σ|_I` and `(σ ∘ swap a b)|_I`, every
other config
contributing zero by `cDownUp_canonical_repr_eq_zero_of_ne`. -/
theorem cDownUp_canonicalSum_eq_two_terms {T : Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ}
    {I : Finset (Fin (M + 1))}
    {μ : Fin (M + 1) → Fin (M + 1) → ℂ} (hbasis : IsGeneralFlatBandSpecialBasis T I μ)
    {eμ : Module.Basis (Fin (M + 1)) ℂ (Fin (M + 1) → ℂ)} {idx : Fin (M + 1) → Fin (M + 1)}
    (hidx : ∀ z ∈ I, (eμ (idx z) : Fin (M + 1) → ℂ) = μ z) (σ : Fin (M + 1) → Fin 2)
    (x : Fin (M + 1)) {a b : Fin (M + 1)} (ha : a ∈ I) (_hb : b ∈ I) (_hab : a ≠ b)
    (hσa : σ a = 0) (hσb : σ b = 1) (D : (I → Fin 2) → ℂ) :
    ∑ s : I → Fin 2, D s * (generalOccBasis eμ).repr
        ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
          (flatBandSpinConfigList I (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0))))
        (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))
      = D (fun z : I => σ z.1) * (generalOccBasis eμ).repr
          ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
            (flatBandSpinConfigList I
              (fun z => if h : z ∈ I then (fun z : I => σ z.1) ⟨z, h⟩ else 0))))
          (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ))
        + D (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) * (generalOccBasis eμ).repr
          ((generalCDownUp M x).mulVec (generalFlatBandSlaterState μ
            (flatBandSpinConfigList I (fun z => if h : z ∈ I then
              (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) ⟨z, h⟩ else 0))))
          (idxConfigOf idx (flatBandSpinConfigList ((I.erase a).erase b) σ)) := by
  have hne : (fun z : I => σ z.1) ≠ (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1) := by
    intro h
    have := congrFun h ⟨a, ha⟩
    simp only [Function.comp, Equiv.swap_apply_left, hσa, hσb] at this
    exact absurd this (by decide)
  rw [← Finset.sum_subset (Finset.subset_univ {(fun z : I => σ z.1),
      (fun z : I => (σ ∘ ⇑(Equiv.swap a b)) z.1)})]
  · rw [Finset.sum_pair hne]
  · intro s _ hs
    rw [Finset.mem_insert, Finset.mem_singleton] at hs
    push Not at hs
    have hvanish := cDownUp_canonical_repr_eq_zero_of_ne hbasis hidx σ
      (fun z => if h : z ∈ I then s ⟨z, h⟩ else 0) x hσa hσb
      (by intro hh; apply hs.1; funext z; have := hh z.1 z.2; simpa [z.2] using this)
      (by intro hh; apply hs.2; funext z; have := hh z.1 z.2; simpa [z.2] using this)
    rw [hvanish, mul_zero]

end LatticeSystem.Fermion
