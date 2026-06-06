import LatticeSystem.Fermion.JordanWigner.Hubbard.TJCompleteness
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJNumberCommute
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJHardcorePreserve
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJOccupationCount

/-!
# Tasaki 11.5: the t-J operator lift on a sector basis state (Prop 11.24 PR-E1c)

`Ĥ_tJ |Φ_s⟩` reassembles its sector-matrix column: for a sector state `s`,
`Ĥ_tJ |Φ_s⟩ = Σ_{s'} ⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩ |Φ_{s'}⟩` (`tJHamiltonian_mulVec_tJConfigOf`). This is the
bridge from the operator `Ĥ_tJ` to the finite sector matrix, mirroring the Nagaoka
`hubbardEffectiveHamiltonian_mulVec_tasakiState`.

The proof uses sector-basis completeness (`tJ_completeness`): `Ĥ_tJ |Φ_s⟩` is supported on the
sector configurations because it stays hard-core (`tJHamiltonian_mulVec_mem_hardcore`) and keeps the
`N̂ = Ne` / `Ŝ³ = ½` eigenvalues (`[Ĥ_tJ, N̂] = [Ĥ_tJ, Ŝ³] = 0`). The key new input is the support
restriction `tJ_mulVec_apply_eq_zero_of_not_sector`: a hard-core vector with those two eigenvalues
vanishes off the sector configurations, since a hard-core configuration with electron count `Ne` and
`Ŝ³` count `½` is exactly a sector basis index.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.5.2, p. 443.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Lattice SimpleGraph
open scoped BigOperators

variable {N : ℕ}

/-! ## The total spin-`z` operator is diagonal -/

/-- `N̂_↑` is diagonal: `(N̂_↑ ψ)(w) = (Σ_i w_{i↑}) · ψ(w)`. -/
theorem fermionTotalUpNumber_mulVec_apply (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (w : Fin (2 * N + 2) → Fin 2) :
    (fermionTotalUpNumber N).mulVec v w =
      (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) * v w := by
  unfold fermionTotalUpNumber fermionUpNumber
  rw [Matrix.sum_mulVec, Finset.sum_apply,
    Finset.sum_congr rfl (fun i _ => fermionMultiNumber_mulVec_apply N (spinfulIndex N i 0) v w),
    ← Finset.sum_mul]

/-- `N̂_↓` is diagonal: `(N̂_↓ ψ)(w) = (Σ_i w_{i↓}) · ψ(w)`. -/
theorem fermionTotalDownNumber_mulVec_apply (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (w : Fin (2 * N + 2) → Fin 2) :
    (fermionTotalDownNumber N).mulVec v w =
      (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) * v w := by
  unfold fermionTotalDownNumber fermionDownNumber
  rw [Matrix.sum_mulVec, Finset.sum_apply,
    Finset.sum_congr rfl (fun i _ => fermionMultiNumber_mulVec_apply N (spinfulIndex N i 1) v w),
    ← Finset.sum_mul]

/-- `Ŝ³_tot` is diagonal: `(Ŝ³ ψ)(w) = ½(Σ_i w_{i↑} − Σ_i w_{i↓}) · ψ(w)`. -/
theorem fermionTotalSpinZ_mulVec_apply (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (w : Fin (2 * N + 2) → Fin 2) :
    (fermionTotalSpinZ N).mulVec v w =
      (((∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) -
          (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ))) / 2) * v w := by
  unfold fermionTotalSpinZ
  rw [Matrix.smul_mulVec, Pi.smul_apply, Matrix.sub_mulVec, Pi.sub_apply,
    fermionTotalUpNumber_mulVec_apply, fermionTotalDownNumber_mulVec_apply]
  simp only [smul_eq_mul]
  ring

/-- A `Ŝ³_tot`-eigenstate vanishes off its `Ŝ³` shell: if `Ŝ³ v = k • v` then `v(w) = 0` whenever
the `Ŝ³` count `½(Σ_i w_{i↑} − Σ_i w_{i↓})` differs from `k`. -/
theorem mulVec_apply_eq_zero_of_spinZ_ne (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (hv : (fermionTotalSpinZ N).mulVec v = k • v)
    (w : Fin (2 * N + 2) → Fin 2)
    (hne : ((∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) -
        (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ))) / 2 ≠ k) :
    v w = 0 := by
  have h1 : (((∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) -
        (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ))) / 2) * v w = k * v w := by
    rw [← fermionTotalSpinZ_mulVec_apply, hv, Pi.smul_apply, smul_eq_mul]
  have h2 : ((((∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) -
        (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ))) / 2) - k) * v w = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

/-! ## Support of a hard-core `N̂ = Ne`, `Ŝ³ = ½` eigenstate -/

/-- **Support restriction.** If `u` is hard-core, an `N̂ = Ne` eigenstate, and an `Ŝ³ = ½`
eigenstate, then `u(w) = 0` at every configuration `w` that is not a sector configuration. A
non-vanishing `w` must be hard-core (else double occupancy kills it), so `w = tJConfigOf s₀` with
`s₀ = tJSiteStateOf w`; the `N̂` eigenvalue forces `#↑(s₀) + #↓(s₀) = Ne` and the `Ŝ³` eigenvalue
forces `#↑(s₀) = #↓(s₀) + 1`, placing `s₀` in the sector. -/
theorem tJ_mulVec_apply_eq_zero_of_not_sector (Ne : ℕ)
    (u : (Fin (2 * N + 2) → Fin 2) → ℂ) (hhc : u ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec u = (Ne : ℂ) • u)
    (hSz : (fermionTotalSpinZ N).mulVec u = ((1 / 2 : ℝ) : ℂ) • u)
    (w : Fin (2 * N + 2) → Fin 2)
    (hw : ¬ ∃ s : TJSpinHalfFillingSector N Ne, tJConfigOf N s.val = w) :
    u w = 0 := by
  by_cases hd : ∃ i, w (spinfulIndex N i 0) = 1 ∧ w (spinfulIndex N i 1) = 1
  · obtain ⟨i, h0, h1⟩ := hd
    exact hardcore_mulVec_apply_eq_zero_of_double N u hhc w i h0 h1
  · -- `w` is hard-core.
    have hwhc : ∀ i, ¬ (w (spinfulIndex N i 0) = 1 ∧ w (spinfulIndex N i 1) = 1) :=
      fun i hi => hd ⟨i, hi.1, hi.2⟩
    have hcfg : tJConfigOf N (tJSiteStateOf N w) = w :=
      tJConfigOf_tJSiteStateOf_of_hardcore N w hwhc
    by_contra hu
    apply hw
    -- Electron count `Σ_j w_j = Ne`.
    have hcount : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) = (Ne : ℂ) := by
      by_contra hcontra
      exact hu (mulVec_apply_eq_zero_of_number_ne N u (Ne : ℂ) hN w hcontra)
    -- `Ŝ³` count `½(Σ↑ − Σ↓) = ½`.
    have hspin : ((∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) -
        (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ))) / 2 = ((1 / 2 : ℝ) : ℂ) := by
      by_contra hcontra
      exact hu (mulVec_apply_eq_zero_of_spinZ_ne u ((1 / 2 : ℝ) : ℂ) hSz w hcontra)
    -- Convert the complex count equations to natural-number counts of `s₀ = tJSiteStateOf w`.
    set s₀ := tJSiteStateOf N w with hs₀
    have hup : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 0)).val : ℂ)) =
        ((Finset.univ.filter (fun k => s₀ k = 1)).card : ℂ) := by
      rw [← hcfg, ← Nat.cast_sum, tJConfigOf_up_count N s₀]
    have hdown : (∑ i : Fin (N + 1), ((w (spinfulIndex N i 1)).val : ℂ)) =
        ((Finset.univ.filter (fun k => s₀ k = 2)).card : ℂ) := by
      rw [← hcfg, ← Nat.cast_sum, tJConfigOf_down_count N s₀]
    have htot : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) =
        (((Finset.univ.filter (fun k => s₀ k = 1)).card +
            (Finset.univ.filter (fun k => s₀ k = 2)).card : ℕ) : ℂ) := by
      rw [← hcfg, ← Nat.cast_sum, tJConfigOf_total_count N s₀]
    -- The two membership conditions.
    have hsum : (Finset.univ.filter (fun k => s₀ k = 1)).card +
        (Finset.univ.filter (fun k => s₀ k = 2)).card = Ne := by
      have := hcount; rw [htot] at this; exact_mod_cast this
    have hdiff : (Finset.univ.filter (fun k => s₀ k = 1)).card =
        (Finset.univ.filter (fun k => s₀ k = 2)).card + 1 := by
      have hh := hspin
      rw [hup, hdown] at hh
      have h2 : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
      rw [h2] at hh
      have hc : ((Finset.univ.filter (fun k => s₀ k = 1)).card : ℂ) =
          ((Finset.univ.filter (fun k => s₀ k = 2)).card : ℂ) + 1 := by
        linear_combination 2 * hh
      exact_mod_cast hc
    exact ⟨⟨s₀, hdiff, hsum⟩, hcfg⟩

/-! ## The t-J Hamiltonian preserves the sector eigenvalues -/

/-- `Ĥ_tJ` preserves `N̂`-eigenstates (from `[Ĥ_tJ, N̂] = 0`). -/
theorem tJHamiltonian_mulVec_preserves_number (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = k • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec ((tJHamiltonian N G τ J).mulVec v) =
      k • ((tJHamiltonian N G τ J).mulVec v) := by
  rw [Matrix.mulVec_mulVec, (fermionTotalNumber_commute_tJHamiltonian G τ J).eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- `Ĥ_tJ` preserves `Ŝ³`-eigenstates (from `[Ĥ_tJ, Ŝ³] = 0`). -/
theorem tJHamiltonian_mulVec_preserves_spinZ (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (hv : (fermionTotalSpinZ N).mulVec v = k • v) :
    (fermionTotalSpinZ N).mulVec ((tJHamiltonian N G τ J).mulVec v) =
      k • ((tJHamiltonian N G τ J).mulVec v) := by
  rw [Matrix.mulVec_mulVec, (fermionTotalSpinZ_commute_tJHamiltonian N G τ J).eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-! ## The operator lift -/

/-- **Operator lift.** `Ĥ_tJ |Φ_s⟩` reassembles its sector-matrix column:
`Ĥ_tJ |Φ_s⟩ = Σ_{s'} ⟨Φ_{s'}|Ĥ_tJ|Φ_s⟩ |Φ_{s'}⟩`. Because `Ĥ_tJ |Φ_s⟩` is hard-core and keeps the
`N̂ = Ne` / `Ŝ³ = ½` eigenvalues, it is supported on the sector configurations, where the sector
basis is complete. -/
theorem tJHamiltonian_mulVec_tJConfigOf (G : SimpleGraph (Fin (N + 1))) [DecidableRel G.Adj]
    (τ J : ℝ) (Ne : ℕ) (s : TJSpinHalfFillingSector N Ne) :
    (tJHamiltonian N G τ J).mulVec (basisVec (tJConfigOf N s.val)) =
      tJExpansion N Ne
        (tJExpansionCoeff N Ne ((tJHamiltonian N G τ J).mulVec (basisVec (tJConfigOf N s.val)))) :=
  tJ_completeness Ne _ (fun w hw =>
    tJ_mulVec_apply_eq_zero_of_not_sector Ne _
      (tJHamiltonian_mulVec_mem_hardcore G τ J (tJConfigOf_mem_hardcore N s.val))
      (tJHamiltonian_mulVec_preserves_number G τ J _ (Ne : ℂ)
        (fermionTotalNumber_mulVec_tJConfigOf_eq N s.val Ne s.2.2))
      (tJHamiltonian_mulVec_preserves_spinZ G τ J _ ((1 / 2 : ℝ) : ℂ)
        (fermionTotalSpinZ_mulVec_tJConfigOf_half N s.val s.2.1))
      w hw)

end LatticeSystem.Fermion
