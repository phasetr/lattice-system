import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheorem
import LatticeSystem.Fermion.JordanWigner.Hubbard.HardcoreSpan

/-!
# Tasaki Theorem 11.5: existence of the ferromagnetic ground state

The capstone `weakNagaoka_spinMultiplet`
(`Fermion/JordanWigner/Hubbard/WeakNagaokaTheorem.lean`) reduces the weak Nagaoka
theorem to the *existence* of a nonzero highest-weight `Ĥ_eff`-eigenvector — a
ferromagnetic ground state. Following Tasaki's §11.2.1 proof, this is obtained by
the variational (Schwarz) argument, **not** by Perron–Frobenius (PF and the
connectivity/irreducibility condition belong to §11.2.2, Theorem 11.7):

1. Take an arbitrary ground state `|Φ_GS⟩` of `Ĥ_eff`, expanded in the one-hole
   hard-core Tasaki basis with (real) coefficients `ϕ(x, σ)` (eq. (11.2.6)).
2. Ferromagnetize it: `ξ_x = (Σ_σ ϕ(x, σ)²)^{1/2}` (eq. (11.2.7)) and
   `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩` (eq. (11.2.8)).
3. The Schwarz inequality (eq. (11.2.9), already formalized as
   `hubbardWeakNagaoka_energy_bound`) gives `⟨Φ_↑|Ĥ_eff|Φ_↑⟩ ≤ ⟨Φ_GS|Ĥ_eff|Φ_GS⟩`,
   and `|Φ_↑⟩` has the same norm (`tasakiFerro_normSq_eq`), so `|Φ_↑⟩` is also a
   ground state.
4. `|Φ_↑⟩` is a highest-weight maximal-spin state, so `weakNagaoka_spinMultiplet`
   produces the full `(2 S_max + 1)`-multiplet.

This file builds the ferromagnetic state `|Φ_↑⟩ = Σ_x ξ_x |Φ_{x,↑}⟩` and its
highest-weight (maximal-spin) and nonvanishing properties.

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, Theorem 11.5, pp. 382-385.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## The ferromagnetic state -/

/-- The ferromagnetic state `|Φ_↑⟩ = Σ_x ξ_x |Φ^T_{x,↑}⟩` (Tasaki eq. (11.2.8))
built from real weights `ξ`: a superposition over hole positions of the all-up
Tasaki basis states. With `ξ_x` the ferromagnetized coefficients (`ferroXi`) of a
ground state, this is the ferromagnetic ground state `|Φ_↑⟩`. -/
noncomputable def pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℝ) :
    (Fin (2 * N + 2) → Fin 2) → ℂ :=
  ∑ x : Fin (N + 1), (ξ x : ℂ) • tasakiState N ⟨x, holeSpinUp N x⟩

/-- `Ŝ^+_tot` annihilates the ferromagnetic state: it is a highest-weight state
(all electrons spin-up, none to raise). -/
theorem fermionTotalSpinPlus_mulVec_pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℝ) :
    (fermionTotalSpinPlus N).mulVec (pfFerroState N ξ) = 0 := by
  unfold pfFerroState
  rw [Matrix.mulVec_sum]
  apply Finset.sum_eq_zero
  intro x _
  rw [Matrix.mulVec_smul,
    show tasakiState N ⟨x, holeSpinUp N x⟩ = hubbardTasakiBasisState N x (fun _ => true) from rfl,
    fermionTotalSpinPlus_mulVec_hubbardTasakiBasisStateUp, smul_zero]

/-- `Ŝ^z_tot` acts on the ferromagnetic state with eigenvalue `N/2 = S_max`: it is
the maximal-spin state. -/
theorem fermionTotalSpinZ_mulVec_pfFerroState (N : ℕ) (ξ : Fin (N + 1) → ℝ) :
    (fermionTotalSpinZ N).mulVec (pfFerroState N ξ) =
      ((N : ℂ) / 2) • pfFerroState N ξ := by
  unfold pfFerroState
  rw [Matrix.mulVec_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mulVec_smul,
    show tasakiState N ⟨x, holeSpinUp N x⟩ = hubbardTasakiBasisState N x (fun _ => true) from rfl,
    fermionTotalSpinZ_mulVec_hubbardTasakiBasisStateUp, smul_comm]

/-- The ferromagnetic state is nonzero when the weights are strictly positive: its
squared norm is `Σ_x ξ_x² > 0` by orthonormality of the Tasaki basis. -/
theorem pfFerroState_ne_zero (N : ℕ) (ξ : Fin (N + 1) → ℝ) (hξ : ∀ x, 0 < ξ x) :
    pfFerroState N ξ ≠ 0 := by
  classical
  intro h
  set ψ : ((x : Fin (N + 1)) × HoleSpin N x) → ℝ :=
    fun p => if p.2 = holeSpinUp N p.1 then ξ p.1 else 0 with hψdef
  have hexp : pfFerroState N ξ = ∑ p, (ψ p : ℂ) • tasakiState N p := by
    rw [pfFerroState, Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_eq_single (holeSpinUp N x)
      (fun σ _ hσ => by simp only [hψdef, if_neg hσ, Complex.ofReal_zero, zero_smul])
      (fun hmem => absurd (Finset.mem_univ _) hmem)]
    simp only [hψdef, if_pos rfl]
  have hnorm := tasakiExpansion_normSq N ψ
  rw [← hexp, h] at hnorm
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hnorm
  have hsum : (∑ p, (ψ p) ^ 2) = 0 := by exact_mod_cast hnorm.symm
  have hpos : 0 < ∑ p, (ψ p) ^ 2 := by
    refine Finset.sum_pos' (fun p _ => sq_nonneg _)
      ⟨⟨Classical.arbitrary (Fin (N + 1)), holeSpinUp N _⟩, Finset.mem_univ _, ?_⟩
    simp only [hψdef, if_pos rfl]
    exact pow_pos (hξ _) 2
  linarith

/-! ## The effective Hamiltonian conserves particle number

These prepare the operator-lift step: `Ĥ_eff` maps the one-hole hard-core sector
to itself (it preserves both the hard-core constraint and the electron number),
so its action on the Tasaki basis stays in the span of the basis. -/

/-- The same-site double-occupancy operator commutes with the total electron
number (it is a product of number operators). -/
theorem hubbardDoubleOccupancy_commute_fermionTotalNumber (N : ℕ) (i : Fin (N + 1)) :
    Commute (hubbardDoubleOccupancy N i) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardDoubleOccupancy fermionUpNumber fermionDownNumber
  exact (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N i 0)).mul_left
    (fermionMultiNumber_commute_fermionTotalNumber (2 * N + 1) (spinfulIndex N i 1))

/-- Each hard-core factor `1 - n_{i,↑} n_{i,↓}` commutes with the total electron
number. -/
theorem hubbardHardcoreFactor_commute_fermionTotalNumber (N : ℕ) (i : Fin (N + 1)) :
    Commute (hubbardHardcoreFactor N i) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHardcoreFactor
  exact (Commute.one_left _).sub_left (hubbardDoubleOccupancy_commute_fermionTotalNumber N i)

/-- The hard-core projection commutes with the total electron number. -/
theorem hubbardHardcoreProjection_commute_fermionTotalNumber (N : ℕ) :
    Commute (hubbardHardcoreProjection N) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardHardcoreProjection
  exact (Finset.noncommProd_commute _ _ _ _
    (fun i _ => (hubbardHardcoreFactor_commute_fermionTotalNumber N i).symm)).symm

/-- **`Ĥ_eff` conserves the total electron number** `[Ĥ_eff, N̂] = 0`: it is built
from the number-conserving Hubbard Hamiltonian compressed by the
number-conserving hard-core projection. Hence `Ĥ_eff` preserves the fixed-electron
sectors, in particular the one-hole hard-core sector. -/
theorem hubbardEffectiveHamiltonian_commute_fermionTotalNumber
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ) :
    Commute (hubbardEffectiveHamiltonian N t U) (fermionTotalNumber (2 * N + 1)) := by
  unfold hubbardEffectiveHamiltonian
  exact ((hubbardHardcoreProjection_commute_fermionTotalNumber N).mul_left
    (hubbardHamiltonian_commute_fermionTotalNumber N t U)).mul_left
    (hubbardHardcoreProjection_commute_fermionTotalNumber N)

/-- The total electron number acts diagonally on a computational basis state with
the total occupation as eigenvalue: `N̂ |c⟩ = (Σ_j c_j) |c⟩`. -/
theorem fermionTotalNumber_mulVec_basisVec (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    (fermionTotalNumber (2 * N + 1)).mulVec (basisVec c) =
      (∑ j : Fin (2 * N + 2), ((c j).val : ℂ)) • basisVec c := by
  unfold fermionTotalNumber
  rw [Matrix.sum_mulVec,
    Finset.sum_congr rfl (fun j _ => fermionMultiNumber_mulVec_basisVec (2 * N + 1) j c),
    ← Finset.sum_smul]

/-- **`Ĥ_eff` preserves `N̂`-eigenstates.** If `v` is an electron-number
eigenstate at eigenvalue `k`, then so is `Ĥ_eff v` (since `[Ĥ_eff, N̂] = 0`). This
keeps `Ĥ_eff |Φ_p⟩` in the fixed-electron-number sector. -/
theorem hubbardEffectiveHamiltonian_mulVec_preserves_number
    (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = k • v) :
    (fermionTotalNumber (2 * N + 1)).mulVec
        ((hubbardEffectiveHamiltonian N t U).mulVec v) =
      k • ((hubbardEffectiveHamiltonian N t U).mulVec v) := by
  rw [Matrix.mulVec_mulVec,
    ← (hubbardEffectiveHamiltonian_commute_fermionTotalNumber N t U).eq,
    ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul]

/-- The one-hole configuration has exactly `N` electrons: `Σ_j c_j = N` (one
empty site among the `N + 1` sites, each other site singly occupied). -/
theorem hubbardOneHoleConfig_electron_count (N : ℕ) (x : Fin (N + 1))
    (σ : Fin (N + 1) → Bool) :
    (∑ j : Fin (2 * N + 2), ((hubbardOneHoleConfig N x σ j).val : ℂ)) = (N : ℂ) := by
  rw [sum_spinful_reindex N (fun j => ((hubbardOneHoleConfig N x σ j).val : ℂ))]
  have hsite : ∀ y : Fin (N + 1),
      (∑ r : Fin 2, ((hubbardOneHoleConfig N x σ (spinfulIndex N y r)).val : ℂ))
        = if y ≠ x then 1 else 0 := by
    intro y
    rw [Fin.sum_univ_two, hubbardOneHoleConfig_apply_up, hubbardOneHoleConfig_apply_down]
    rcases eq_or_ne y x with h | h
    · subst h; simp
    · have hv : ¬ (y.val = x.val) := fun hh => h (Fin.ext hh)
      rw [if_neg hv, if_neg hv, if_pos h]
      cases hσ : σ y <;> simp
  rw [Finset.sum_congr rfl (fun y _ => hsite y), Finset.sum_boole, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-- The Tasaki basis state is an `N`-electron eigenstate of `N̂`:
`N̂ |Φ_p⟩ = N |Φ_p⟩` (one hole among `N + 1` sites). -/
theorem fermionTotalNumber_mulVec_tasakiState (N : ℕ)
    (p : (x : Fin (N + 1)) × HoleSpin N x) :
    (fermionTotalNumber (2 * N + 1)).mulVec (tasakiState N p) =
      (N : ℂ) • tasakiState N p := by
  obtain ⟨x, σ⟩ := p
  change (fermionTotalNumber (2 * N + 1)).mulVec (hubbardTasakiBasisState N x σ.val) =
    (N : ℂ) • hubbardTasakiBasisState N x σ.val
  rw [hubbardTasakiBasisState_eq_smul_basisVec, Matrix.mulVec_smul,
    fermionTotalNumber_mulVec_basisVec, hubbardOneHoleConfig_electron_count, smul_comm]

/-! ## Pointwise diagonal action of the number operators -/

/-- The site-occupation number operator is diagonal: `(n_j ψ)(w) = w_j · ψ(w)`
for an arbitrary state `ψ`. -/
theorem fermionMultiNumber_mulVec_apply (N : ℕ) (j : Fin (2 * N + 2))
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (w : Fin (2 * N + 2) → Fin 2) :
    (fermionMultiNumber (2 * N + 1) j).mulVec v w = ((w j).val : ℂ) * v w := by
  rw [fermionMultiNumber_eq_onSite]
  unfold Matrix.mulVec dotProduct
  rw [show (∑ σ : Fin (2 * N + 2) → Fin 2,
        (onSite j (spinHalfOpMinus * spinHalfOpPlus)) w σ * v σ) =
      ∑ σ : Fin (2 * N + 2) → Fin 2,
        (if σ = w then ((w j).val : ℂ) * v σ else 0) from ?_]
  · rw [Finset.sum_ite_eq']; simp
  · refine Finset.sum_congr rfl (fun σ _ => ?_)
    simp only [onSite_apply]
    by_cases hagree : ∀ k, k ≠ j → w k = σ k
    · rw [if_pos hagree]
      by_cases hx : w j = σ j
      · have hwσ : w = σ := funext fun k => by
          by_cases hk : k = j
          · rw [hk]; exact hx
          · exact hagree k hk
        rw [if_pos hwσ.symm, hwσ]
        rcases (show σ j = 0 ∨ σ j = 1 from by
          rcases (σ j) with ⟨r, hr⟩; interval_cases r; exacts [Or.inl rfl, Or.inr rfl])
          with h | h <;>
          rw [h] <;>
          simp [spinHalfOpMinus, spinHalfOpPlus, Matrix.mul_apply, Fin.sum_univ_two]
      · have hwσ : ¬ σ = w := fun h => hx (by rw [h])
        rw [if_neg hwσ]
        rcases (show w j = 0 ∨ w j = 1 from by
          rcases (w j) with ⟨r, hr⟩; interval_cases r; exacts [Or.inl rfl, Or.inr rfl])
          with hw | hw <;>
        rcases (show σ j = 0 ∨ σ j = 1 from by
          rcases (σ j) with ⟨r, hr⟩; interval_cases r; exacts [Or.inl rfl, Or.inr rfl])
          with hs | hs <;>
        first
        | (exact absurd (hw.trans hs.symm) hx)
        | (rw [hw, hs];
           simp [spinHalfOpMinus, spinHalfOpPlus, Matrix.mul_apply, Fin.sum_univ_two])
    · rw [if_neg hagree]
      have hwσ : ¬ σ = w := fun h => hagree (fun k _ => by rw [h])
      rw [if_neg hwσ, zero_mul]

/-- The total electron number is diagonal: `(N̂ ψ)(w) = (Σ_j w_j) · ψ(w)`. -/
theorem fermionTotalNumber_mulVec_apply (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (w : Fin (2 * N + 2) → Fin 2) :
    (fermionTotalNumber (2 * N + 1)).mulVec v w =
      (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) * v w := by
  unfold fermionTotalNumber
  rw [Matrix.sum_mulVec, Finset.sum_apply,
    Finset.sum_congr rfl (fun j _ => fermionMultiNumber_mulVec_apply N j v w),
    ← Finset.sum_mul]

/-- A number eigenstate vanishes off its electron-number shell: if `N̂ v = k • v`
then `v(w) = 0` whenever `Σ_j w_j ≠ k`. -/
theorem mulVec_apply_eq_zero_of_number_ne (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℂ)
    (hv : (fermionTotalNumber (2 * N + 1)).mulVec v = k • v)
    (w : Fin (2 * N + 2) → Fin 2)
    (hne : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) ≠ k) :
    v w = 0 := by
  have h1 : (∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) * v w = k * v w := by
    rw [← fermionTotalNumber_mulVec_apply, hv, Pi.smul_apply, smul_eq_mul]
  have h2 : ((∑ j : Fin (2 * N + 2), ((w j).val : ℂ)) - k) * v w = 0 := by
    rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hne)

/-! ## Hard-core states vanish on doubly-occupied configurations -/

/-- The same-site double-occupancy operator is diagonal:
`(n_{i,↑} n_{i,↓} φ)(w) = w_{i,↑} · w_{i,↓} · φ(w)`. -/
theorem hubbardDoubleOccupancy_mulVec_apply (N : ℕ) (i : Fin (N + 1))
    (φ : (Fin (2 * N + 2) → Fin 2) → ℂ) (w : Fin (2 * N + 2) → Fin 2) :
    (hubbardDoubleOccupancy N i).mulVec φ w =
      ((w (spinfulIndex N i 0)).val : ℂ) * ((w (spinfulIndex N i 1)).val : ℂ) * φ w := by
  unfold hubbardDoubleOccupancy fermionUpNumber fermionDownNumber
  rw [← Matrix.mulVec_mulVec, fermionMultiNumber_mulVec_apply,
    fermionMultiNumber_mulVec_apply]
  ring

/-- A hard-core state vanishes at every doubly-occupied configuration: if
`φ ∈ H_hc` and `w` has both orbitals occupied at some site `i`, then `φ(w) = 0`. -/
theorem hardcore_mulVec_apply_eq_zero_of_double (N : ℕ)
    (φ : (Fin (2 * N + 2) → Fin 2) → ℂ) (hφ : φ ∈ hubbardHardcoreSubspace N)
    (w : Fin (2 * N + 2) → Fin 2) (i : Fin (N + 1))
    (h0 : w (spinfulIndex N i 0) = 1) (h1 : w (spinfulIndex N i 1) = 1) :
    φ w = 0 := by
  have hD : (hubbardDoubleOccupancy N i).mulVec φ = 0 :=
    (mem_hubbardHardcoreSubspace_iff N).mp hφ i
  have hw := congrFun hD w
  rw [hubbardDoubleOccupancy_mulVec_apply, h0, h1] at hw
  simpa using hw

/-! ## Counting: no double occupancy + `N` electrons ⟹ one-hole hard-core -/

/-- A hard-core configuration with exactly `N` electrons is one-hole hard-core:
no double occupancy plus `N` electrons on `N + 1` sites forces a unique empty
site (the hole). -/
theorem isOneHoleHardcore_of_noDouble_count (N : ℕ) (c : Fin (2 * N + 2) → Fin 2)
    (hnd : ∀ i : Fin (N + 1),
      c (spinfulIndex N i 0) = 0 ∨ c (spinfulIndex N i 1) = 0)
    (hcount : (∑ j : Fin (2 * N + 2), (c j).val) = N) :
    IsOneHoleHardcoreConfig N c := by
  classical
  -- per-site occupation g i ∈ {0,1}; g i = 0 ⟺ site i is empty (the hole)
  set g : Fin (N + 1) → ℕ :=
    fun i => (c (spinfulIndex N i 0)).val + (c (spinfulIndex N i 1)).val with hg
  have hg_le : ∀ i, g i ≤ 1 := by
    intro i
    rcases hnd i with h | h
    · rw [hg]; simp only [h]; have := (c (spinfulIndex N i 1)).isLt; omega
    · rw [hg]; simp only [h]; have := (c (spinfulIndex N i 0)).isLt; omega
  have hre : (∑ j : Fin (2 * N + 2), (c j).val) = ∑ i : Fin (N + 1), g i :=
    (sum_spinful_reindex N (fun j => (c j).val)).trans
      (Finset.sum_congr rfl (fun i _ => by simp only [hg, Fin.sum_univ_two]))
  have hsum : (∑ i : Fin (N + 1), g i) = N := hre.symm.trans hcount
  -- the empty sites are exactly {i | g i = 0}; there is exactly one
  have hcard : (Finset.univ.filter (fun i => g i = 0)).card = 1 := by
    have hones : (Finset.univ.filter (fun i => g i = 1)).card = N := by
      rw [Finset.card_filter,
        show (∑ i : Fin (N + 1), if g i = 1 then 1 else 0) = ∑ i : Fin (N + 1), g i from
          Finset.sum_congr rfl (fun i _ => by
            have := hg_le i; interval_cases h : g i <;> simp)]
      exact hsum
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin (N + 1)))) (p := fun i => g i = 0)
    have hneg : (Finset.univ.filter (fun i => ¬ g i = 0)) =
        (Finset.univ.filter (fun i => g i = 1)) :=
      Finset.filter_congr (fun i _ => by have := hg_le i; omega)
    rw [hneg, hones, Finset.card_univ, Fintype.card_fin] at hsplit
    omega
  obtain ⟨h, hh⟩ := Finset.card_eq_one.mp hcard
  refine ⟨hnd, h, ?_, ?_⟩
  · have hmem : h ∈ Finset.univ.filter (fun i => g i = 0) := by
      rw [hh]; exact Finset.mem_singleton_self h
    rw [Finset.mem_filter] at hmem
    have hgh : g h = 0 := hmem.2
    simp only [hg] at hgh
    have e0 : (c (spinfulIndex N h 0)).val = 0 := by omega
    have e1 : (c (spinfulIndex N h 1)).val = 0 := by omega
    exact ⟨Fin.ext e0, Fin.ext e1⟩
  · intro y hy
    have hy0 : g y = 0 := by simp only [hg, hy.1, hy.2]; rfl
    have hmem : y ∈ Finset.univ.filter (fun i => g i = 0) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ y, hy0⟩
    rw [hh, Finset.mem_singleton] at hmem
    exact hmem

/-- A `Fin 2` value that is not `0` equals `1`. -/
private theorem fin2_eq_one_of_ne_zero {a : Fin 2} (h : a ≠ 0) : a = 1 :=
  Fin.ext (by have := a.isLt; have : a.val ≠ 0 := fun hv => h (Fin.ext hv); omega)

/-- **Support of a hard-core number eigenstate.** If `v` lies in the hard-core
subspace and is an `N`-electron eigenstate (`N̂ v = N • v`), then `v(w) = 0` at
every configuration `w` that is not one-hole hard-core. So `v` is supported on
the one-hole hard-core configurations. -/
theorem mulVec_apply_eq_zero_of_not_oneHole (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hhc : v ∈ hubbardHardcoreSubspace N)
    (hN : (fermionTotalNumber (2 * N + 1)).mulVec v = (N : ℂ) • v)
    (w : Fin (2 * N + 2) → Fin 2) (hw : ¬ IsOneHoleHardcoreConfig N w) :
    v w = 0 := by
  by_cases hd : ∃ i, w (spinfulIndex N i 0) = 1 ∧ w (spinfulIndex N i 1) = 1
  · obtain ⟨i, h0, h1⟩ := hd
    exact hardcore_mulVec_apply_eq_zero_of_double N v hhc w i h0 h1
  · have hnd : ∀ i, w (spinfulIndex N i 0) = 0 ∨ w (spinfulIndex N i 1) = 0 := by
      intro i
      by_contra hcon
      rw [not_or] at hcon
      exact hd ⟨i, fin2_eq_one_of_ne_zero hcon.1, fin2_eq_one_of_ne_zero hcon.2⟩
    refine mulVec_apply_eq_zero_of_number_ne N v (N : ℂ) hN w (fun heq => hw ?_)
    refine isOneHoleHardcore_of_noDouble_count N w hnd ?_
    exact_mod_cast heq

end LatticeSystem.Fermion
