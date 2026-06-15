import LatticeSystem.Fermion.JordanWigner.Hubbard.TJKineticNonneg
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJKineticMatrixElement
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOffDiagonal
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJSectorHopBackwardWrap

/-!
# Tasaki 11.5: each cyclic kinetic summand is `0` or `1` (Prop 11.24 PR-B7-3f)

The off-diagonal kinetic matrix element expands over spins and ordered site pairs as
`⟨Φ_{s'}|K|Φ_s⟩ = Σ_σ Σ_i Σ_j couplingOf(cycleGraph) i j · ⟨Φ_{s'}|ĉ†_{iσ}ĉ_{jσ}|Φ_s⟩`.  Each
summand
is either `0` or `1`: non-adjacent pairs are killed by the graph coupling; for an adjacent pair the
single-hop element vanishes unless the source carries spin `σ` and the target site is empty, in
which
case the directional (rightward / leftward nearest-neighbour, or wrap) hop matrix element gives the
sign-free indicator `[s' = tJSiteHop …] ∈ {0,1}`.  Hence the kinetic matrix element is a
non-negative
real, the input to the Perron–Frobenius step.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-- A `Fin 3` site value is `0`, `1`, or `2`. -/
theorem tJ_fin3_cases (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
  fin_cases v <;> simp

/-- An occupied `σ`-orbital forces the site spin: `tJConfigOf s (spinfulIndex i σ) = 1` gives
`s i = 1` for `σ = ↑` and `s i = 2` for `σ = ↓`. -/
private theorem tJ_site_of_orbital (N : ℕ) (s : Fin (N + 1) → Fin 3) (i : Fin (N + 1)) (σ : Fin 2)
    (h : tJConfigOf N s (spinfulIndex N i σ) = 1) :
    s i = if σ = 0 then 1 else 2 := by
  rcases tJ_fin2_eq σ with rfl | rfl
  · rw [tJConfigOf_apply_up] at h; split at h
    · simpa using ‹s i = 1›
    · exact absurd h (by decide)
  · rw [tJConfigOf_apply_down] at h; split at h
    · simpa using ‹s i = 2›
    · exact absurd h (by decide)

/-- The four oriented adjacency cases of the cyclic chain, in `Fin`-value form. -/
theorem cycleGraph_adj_val_cases (N : ℕ) (hpos : 0 < N) (i j : Fin (N + 1))
    (h : (cycleGraph (N + 1)).Adj i j) :
    j.val = i.val + 1 ∨ i.val = j.val + 1 ∨ (i.val = N ∧ j.val = 0) ∨ (j.val = N ∧ i.val = 0) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [cycleGraph_adj_iff] at h
  rcases h with h | h
  · have hv : (i + 1).val = if i = Fin.last (M + 1) then 0 else i.val + 1 := Fin.val_add_one i
    rw [h] at hv
    by_cases hil : i = Fin.last (M + 1)
    · rw [if_pos hil] at hv
      exact Or.inr (Or.inr (Or.inl ⟨by rw [hil]; rfl, hv⟩))
    · rw [if_neg hil] at hv; exact Or.inl hv
  · have hv : (j + 1).val = if j = Fin.last (M + 1) then 0 else j.val + 1 := Fin.val_add_one j
    rw [h] at hv
    by_cases hjl : j = Fin.last (M + 1)
    · rw [if_pos hjl] at hv
      exact Or.inr (Or.inr (Or.inr ⟨by rw [hjl]; rfl, hv⟩))
    · rw [if_neg hjl] at hv; exact Or.inr (Or.inl hv)

/-- **Each cyclic kinetic summand is `0` or `1`.**  The graph-weighted single-hop matrix element
`couplingOf(cycleGraph) i j · ⟨Φ_{s'}|ĉ†_{iσ}ĉ_{jσ}|Φ_s⟩` is `0` or `1`: non-adjacent pairs are
killed by the coupling, and for an adjacent pair the element vanishes unless the source carries
spin `σ` and the target site is empty, where the directional hop matrix element gives the sign-free
indicator `[s' = tJSiteHop …] ∈ {0,1}`. -/
theorem tJ_kinetic_summand_zero_or_one (N : ℕ) (hpos : 0 < N) (s s' : Fin (N + 1) → Fin 3)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne)
    (σ : Fin 2) (i j : Fin (N + 1)) :
    couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
              (basisVec (tJConfigOf N s))) w) = 0 ∨
      couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
              (basisVec (tJConfigOf N s))) w) = 1 := by
  by_cases hAdj : (cycleGraph (N + 1)).Adj i j
  · have hcoup : couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j = 1 := by
      unfold couplingOf; rw [if_pos hAdj]
    have hij : i ≠ j := hAdj.ne
    rw [hcoup, one_mul]
    by_cases hsrc : tJConfigOf N s (spinfulIndex N j σ) = 1
    · have hsj : s j = if σ = 0 then 1 else 2 := tJ_site_of_orbital N s j σ hsrc
      rcases tJ_fin3_cases (s i) with hsi0 | hsi1 | hsi2
      · -- target site empty: fully allowed
        rcases tJ_fin2_eq σ with rfl | rfl
        · rw [if_pos rfl] at hsj
          rcases cycleGraph_adj_val_cases N hpos i j hAdj with hd | hd | ⟨hiN, hj0⟩ | ⟨hjN, hi0v⟩
          · rw [tJ_uphop_backward_nn_matrixElement N s s' i j hd hsj hsi0]
            split_ifs <;> simp
          · rw [tJ_uphop_nn_matrixElement N s s' j i hd hsj hsi0]; split_ifs <;> simp
          · rw [tJ_uphop_wrap_matrixElement N s s' j i hpos hj0 hiN hsj hsi0 Ne hNe hodd]
            split_ifs <;> simp
          · rw [tJ_uphop_backward_wrap_matrixElement N s s' i j hpos hi0v hjN hsj hsi0 Ne hNe hodd]
            split_ifs <;> simp
        · simp only [if_neg (by decide : ¬ (1 : Fin 2) = 0)] at hsj
          rcases cycleGraph_adj_val_cases N hpos i j hAdj with hd | hd | ⟨hiN, hj0⟩ | ⟨hjN, hi0v⟩
          · rw [tJ_downhop_backward_nn_matrixElement N s s' i j hd hsj hsi0]
            split_ifs <;> simp
          · rw [tJ_downhop_nn_matrixElement N s s' j i hd hsj hsi0]; split_ifs <;> simp
          · rw [tJ_downhop_wrap_matrixElement N s s' j i hpos hj0 hiN hsj hsi0 Ne hNe hodd]
            split_ifs <;> simp
          · rw [tJ_downhop_backward_wrap_matrixElement N s s' i j hpos hi0v hjN hsj hsi0 Ne hNe hodd]
            split_ifs <;> simp
      · -- target site ↑
        rcases tJ_fin2_eq σ with rfl | rfl
        · rw [tJ_hop_matrixElement_eq_zero_of_target N s s' i j 0 hij
            (by rw [tJConfigOf_apply_up, if_pos hsi1])]
          exact Or.inl rfl
        · rw [tJ_hop_matrixElement_eq_zero_of_target_other N s s' i j 1 0 (by decide) hij
            (by rw [tJConfigOf_apply_up, if_pos hsi1])]
          exact Or.inl rfl
      · -- target site ↓
        rcases tJ_fin2_eq σ with rfl | rfl
        · rw [tJ_hop_matrixElement_eq_zero_of_target_other N s s' i j 0 1 (by decide) hij
            (by rw [tJConfigOf_apply_down, if_pos hsi2])]
          exact Or.inl rfl
        · rw [tJ_hop_matrixElement_eq_zero_of_target N s s' i j 1 hij
            (by rw [tJConfigOf_apply_down, if_pos hsi2])]
          exact Or.inl rfl
    · -- source empty
      have hsrc0 : tJConfigOf N s (spinfulIndex N j σ) = 0 := by
        rcases tJ_fin2_eq σ with rfl | rfl
        · rw [tJConfigOf_apply_up]; split
          · exact absurd (by rw [tJConfigOf_apply_up, if_pos ‹_›] at hsrc; exact hsrc) (by simp_all)
          · rfl
        · rw [tJConfigOf_apply_down]; split
          · exact absurd (by rw [tJConfigOf_apply_down, if_pos ‹_›] at hsrc; exact hsrc) (by simp_all)
          · rfl
      rw [tJ_hop_matrixElement_eq_zero_of_source N s s' i j σ hsrc0]
      exact Or.inl rfl
  · have hcoup : couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j = 0 := by
      unfold couplingOf; rw [if_neg hAdj]
    rw [hcoup, zero_mul]; exact Or.inl rfl

/-- **The cyclic kinetic matrix element is a non-negative real.**  `⟨Φ_{s'}|K|Φ_s⟩ ≥ 0` (real part
non-negative, imaginary part zero), since it is the sum of `{0,1}`-valued summands.  Hence the
kinetic off-diagonal entry `−τ·⟨Φ_{s'}|K|Φ_s⟩ ≤ 0` for `τ ≥ 0`, feeding the Perron–Frobenius step.
-/
theorem tJKinetic_matrixElement_nonneg (N : ℕ) (hpos : 0 < N) (s s' : Fin (N + 1) → Fin 3)
    (Ne : ℕ) (hNe : (Finset.univ.filter (fun k => s k = 1)).card
        + (Finset.univ.filter (fun k => s k = 2)).card = Ne) (hodd : Odd Ne) :
    0 ≤ (∑ w, basisVec (tJConfigOf N s') w *
          ((hubbardKineticOnGraph N (cycleGraph (N + 1)) 1).mulVec
            (basisVec (tJConfigOf N s))) w).re ∧
      (∑ w, basisVec (tJConfigOf N s') w *
          ((hubbardKineticOnGraph N (cycleGraph (N + 1)) 1).mulVec
            (basisVec (tJConfigOf N s))) w).im = 0 := by
  have hsumm : ∀ σ i j, 0 ≤ (couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
              (basisVec (tJConfigOf N s))) w)).re ∧
      (couplingOf (cycleGraph (N + 1)) (1 : ℂ) i j *
        (∑ w, basisVec (tJConfigOf N s') w *
          ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i σ) *
              fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j σ)).mulVec
              (basisVec (tJConfigOf N s))) w)).im = 0 := by
    intro σ i j
    rcases tJ_kinetic_summand_zero_or_one N hpos s s' Ne hNe hodd σ i j with h | h <;>
      rw [h] <;> simp
  rw [tJKinetic_matrixElement_expand]
  refine ⟨?_, ?_⟩
  · simp only [Complex.re_sum]
    refine Finset.sum_nonneg fun σ _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact (hsumm σ i j).1
  · simp only [Complex.im_sum]
    refine Finset.sum_eq_zero fun σ _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    exact (hsumm σ i j).2

end LatticeSystem.Fermion
