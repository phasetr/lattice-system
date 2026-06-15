import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOperatorLift

/-!
# Tasaki 11.5: the full `N̂ = Ne` filling basis and its completeness (Prop 11.24 PR-E2 ≥)

The all-`Ŝ³` analog of the `Ŝ³ = ½` sector basis: the hard-core configurations at fixed electron
number `Ne` (the physical space `W = (N̂ = Ne) ∩ H^hc`), indexed by the filling site-states
`TJFillingSector N Ne = {s : Fin (N+1) → Fin 3 // #↑ + #↓ = Ne}`.  A hard-core `N̂ = Ne` vector is
supported on these configurations (`tJ_mulVec_apply_eq_zero_of_not_filling`), hence equals its
filling expansion (`tJ_filling_completeness`).

This is the orthonormal basis of `W` in which `Ĥ_tJ` compresses to the filling effective matrix, the
foundation for identifying `groundEnergyAtFilling` with that matrix's minimum eigenvalue (E2 `≥`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The `N̂ = Ne` filling sector of t-J site-states.**  Site-states `s : Fin (N+1) → Fin 3`
(`0/1/2 = ∅/↑/↓`) with total electron count `Ne` (any `Ŝ³`).  Indexes the hard-core fixed-filling
space `W`. -/
abbrev TJFillingSector (N Ne : ℕ) :=
  {s : Fin (N + 1) → Fin 3 //
    (Finset.univ.filter (fun k => s k = 1)).card
      + (Finset.univ.filter (fun k => s k = 2)).card = Ne}

/-- **The filling expansion** `Φ = Σ_s v_s |Φ_s⟩` over the `N̂ = Ne` filling basis. -/
noncomputable def tJFillingExpansion (N Ne : ℕ) (v : TJFillingSector N Ne → ℂ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  ∑ s, v s • basisVec (tJConfigOf N s.val)

/-- **The filling coefficient functional** `⟨Φ_s, u⟩ = Σ_w |Φ_s⟩(w) · u(w)`. -/
noncomputable def tJFillingExpansionCoeff (N Ne : ℕ) (u : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    TJFillingSector N Ne → ℂ :=
  fun s => ∑ w, basisVec (tJConfigOf N s.val) w * u w

/-- **Left inverse: the coefficient functional inverts the filling expansion.**  The filling basis
is
orthonormal, so `tJFillingExpansionCoeff (Σ_s v_s |Φ_s⟩) = v`. -/
theorem tJFillingExpansionCoeff_tJFillingExpansion (Ne : ℕ) (v : TJFillingSector N Ne → ℂ) :
    tJFillingExpansionCoeff N Ne (tJFillingExpansion N Ne v) = v := by
  funext s
  unfold tJFillingExpansionCoeff tJFillingExpansion
  have hstep : ∀ w, basisVec (tJConfigOf N s.val) w *
        (∑ s', v s' • basisVec (tJConfigOf N s'.val)) w
      = ∑ s', v s' * (basisVec (tJConfigOf N s.val) w * basisVec (tJConfigOf N s'.val) w) := by
    intro w
    rw [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s' _ => by rw [Pi.smul_apply, smul_eq_mul]; ring)
  rw [Finset.sum_congr rfl (fun w _ => hstep w), Finset.sum_comm]
  rw [show (∑ s', ∑ w, v s' * (basisVec (tJConfigOf N s.val) w * basisVec (tJConfigOf N s'.val) w))
      = ∑ s', v s' * (∑ w, basisVec (tJConfigOf N s.val) w * basisVec (tJConfigOf N s'.val) w) from
    Finset.sum_congr rfl (fun s' _ => by rw [Finset.mul_sum])]
  rw [Finset.sum_congr rfl (fun s' _ => by rw [tJConfigOf_basisVec_inner])]
  simp only [← Subtype.ext_iff, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ s (fun s' => v s'), if_pos (Finset.mem_univ s)]

/-- **Support of a hard-core `N̂ = Ne` vector.**  If `u` is hard-core and an `N̂ = Ne` eigenvector,
then `u(w) = 0` at every configuration `w` that is not a filling configuration. -/
theorem tJ_mulVec_apply_eq_zero_of_not_filling (Ne : ℕ)
    (u : (Fin (2 * N + 2) → Fin 2) → ℂ) (hhc : u ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec u = (Ne : ℂ) • u)
    (w : Fin (2 * N + 2) → Fin 2)
    (hw : ¬ ∃ s : TJFillingSector N Ne, tJConfigOf N s.val = w) :
    u w = 0 := by
  by_cases hd : ∃ i, w (spinfulIndex N i 0) = 1 ∧ w (spinfulIndex N i 1) = 1
  · obtain ⟨i, h0, h1⟩ := hd
    exact hardcore_mulVec_apply_eq_zero_of_double N u hhc w i h0 h1
  · have hwhc : ∀ i, ¬ (w (spinfulIndex N i 0) = 1 ∧ w (spinfulIndex N i 1) = 1) :=
      fun i hi => hd ⟨i, hi.1, hi.2⟩
    have hcfg : tJConfigOf N (tJSiteStateOf N w) = w :=
      tJConfigOf_tJSiteStateOf_of_hardcore N w hwhc
    by_contra hu
    apply hw
    set s₀ := tJSiteStateOf N w with hs₀
    have hcount : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = (Ne : ℂ) := by
      by_contra hcontra
      exact hu (mulVec_apply_eq_zero_of_number_ne N u (Ne : ℂ) hN w hcontra)
    have htot : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) =
        (((Finset.univ.filter (fun k => s₀ k = 1)).card +
            (Finset.univ.filter (fun k => s₀ k = 2)).card : ℕ) : ℂ) := by
      rw [← hcfg, ← Nat.cast_sum, tJConfigOf_total_count N s₀]
    have hsum : (Finset.univ.filter (fun k => s₀ k = 1)).card +
        (Finset.univ.filter (fun k => s₀ k = 2)).card = Ne := by
      have := hcount; rw [htot] at this; exact_mod_cast this
    exact ⟨⟨s₀, hsum⟩, hcfg⟩

/-- **Completeness of the filling basis.**  A hard-core `N̂ = Ne` vector equals its filling
expansion `tJFillingExpansion (tJFillingExpansionCoeff u)`. -/
theorem tJ_filling_completeness (Ne : ℕ) (u : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hhc : u ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec u = (Ne : ℂ) • u) :
    u = tJFillingExpansion N Ne (tJFillingExpansionCoeff N Ne u) := by
  funext w
  unfold tJFillingExpansion tJFillingExpansionCoeff
  rw [Finset.sum_apply]
  by_cases hw : ∃ s : TJFillingSector N Ne, tJConfigOf N s.val = w
  · obtain ⟨s₀, rfl⟩ := hw
    rw [Finset.sum_eq_single s₀]
    · rw [Pi.smul_apply, smul_eq_mul, basisVec_apply, if_pos rfl, mul_one, basisVec_sum_mul]
    · intro s _ hss₀
      rw [Pi.smul_apply, smul_eq_mul, basisVec_apply,
        if_neg (fun h => hss₀ (Subtype.ext (tJConfigOf_injective N h.symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  · rw [tJ_mulVec_apply_eq_zero_of_not_filling Ne u hhc hN w hw]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    rw [Pi.smul_apply, smul_eq_mul, basisVec_apply, if_neg (fun h => hw ⟨s, h.symm⟩), mul_zero]

end LatticeSystem.Fermion
