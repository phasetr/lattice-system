import LatticeSystem.Fermion.JordanWigner.Hubbard.TasakiHopAction
import LatticeSystem.Math.FinCases
import LatticeSystem.Fermion.JordanWigner.Hubbard.EffectiveHamiltonian

/-!
# The effective-Hamiltonian matrix element (11.2.5)

This file proves Tasaki eq. (11.2.5): the off-diagonal matrix element of the
one-hole effective Hamiltonian `Ĥ_eff = P̂_hc · H · P̂_hc` between two Tasaki
basis states is the hopping amplitude (with the textbook sign) times the
indicator that the target spin configuration is the moved one:

  `⟨Φ_{y,τ} | Ĥ_eff | Φ_{x,σ}⟩ = -t_{x,y}`   if `τ = σ_{y→x}` (and `x ≠ y`),
  and `0` otherwise.

The proof drops the outer hard-core projection (it acts as the identity on the
hard-core component `C_{y,τ}`, since `P̂_hc` is Hermitian and fixes the basis
states), reduces `Ĥ_eff` to the projected kinetic term on the hard-core sector,
and expands the kinetic operator over spin/site sums. Only the hole-filling
channel `(i, j, s) = (x, y, σ_y)` survives — every other term either annihilates
an empty orbital, creates a doubly-occupied site, or returns the hole to `x`,
none of which overlaps the one-hole state `|Φ_{y,τ}⟩`. The surviving channel is
evaluated by the uniform-sign hole-filling action `hubbardTasakiHop_mulVec`
(eq. (11.2.4)), so no fermion-sign bookkeeping is repeated here.

Codebase sign convention: `hubbardKinetic` uses `+t_{ij}` (Tasaki's `H_hop` uses
`-t`); the uniform `-1` of (11.2.4) supplies the minus, so the realized matrix
element is `-t_{x,y}`, matching Tasaki's (11.2.5).

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2, eq. (11.2.5), p. 384.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Dropping the hard-core projection on a hard-core component -/

/-- The hard-core projection acts as the identity on the component of any vector
at a one-hole hard-core configuration: `(P̂_hc u)(C_{y,τ}) = u(C_{y,τ})`. The
projection fixes the basis vector `|C_{y,τ}⟩` (its column at `C_{y,τ}` is the
unit vector), and Hermiticity transfers this to the row at `C_{y,τ}`. -/
private theorem hardcore_proj_apply (N : ℕ) (y : Fin (N + 1)) (τ : Fin (N + 1) → Bool)
    (u : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    (hubbardHardcoreProjection N *ᵥ u) (hubbardOneHoleConfig N y τ) =
      u (hubbardOneHoleConfig N y τ) := by
  set C := hubbardOneHoleConfig N y τ
  -- Column at `C` is the unit vector: `P w C = [w = C]`.
  have hcol : ∀ w, hubbardHardcoreProjection N w C = if w = C then 1 else 0 := by
    intro w
    have h := congrFun (hubbardHardcoreProjection_mulVec_basisState N y τ) w
    rw [hubbardHardcoreBasisState] at h
    have hexp : (hubbardHardcoreProjection N *ᵥ basisVec C) w
        = hubbardHardcoreProjection N w C := by
      simp only [Matrix.mulVec, dotProduct]
      exact sum_mul_basisVec C (fun v => hubbardHardcoreProjection N w v)
    rw [hexp, basisVec_apply] at h
    exact h
  -- Row at `C` is the unit vector, by Hermiticity.
  have hrow : ∀ w, hubbardHardcoreProjection N C w = if w = C then 1 else 0 := by
    intro w
    have hH := (hubbardHardcoreProjection_isHermitian N).apply C w
    rw [hcol w] at hH
    rw [← hH]
    split_ifs <;> simp
  simp only [Matrix.mulVec, dotProduct, hrow, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-! ## Auxiliary facts about one-hole configurations -/

/-- The one-hole configuration is empty on both orbitals of its hole site. -/
private theorem oneHole_hole_zero (N : ℕ) (y : Fin (N + 1)) (τ : Fin (N + 1) → Bool)
    (r : Fin 2) : hubbardOneHoleConfig N y τ (spinfulIndex N y r) = 0 := by
  rcases fin2_eq_zero_or_one r with rfl | rfl
  · rw [hubbardOneHoleConfig_apply_up, if_pos rfl]
  · rw [hubbardOneHoleConfig_apply_down, if_pos rfl]

/-- A non-hole site is occupied at its spin-selected orbital. -/
private theorem oneHole_occupied (N : ℕ) (x : Fin (N + 1)) (σ : Fin (N + 1) → Bool)
    (t : Fin (N + 1)) (htx : t ≠ x) :
    hubbardOneHoleConfig N x σ (spinfulIndex N t (if σ t then 0 else 1)) = 1 := by
  have htx' : t.val ≠ x.val := fun h => htx (Fin.ext h)
  by_cases hσ : σ t
  · rw [show (if σ t then (0 : Fin 2) else 1) = 0 from by simp [hσ],
      hubbardOneHoleConfig_apply_up, if_neg htx']
    simp [hσ]
  · rw [show (if σ t then (0 : Fin 2) else 1) = 1 from by simp [hσ],
      hubbardOneHoleConfig_apply_down, if_neg htx']
    simp [hσ]

/-! ## Only the hole-filling channel survives -/

/-- If a single hop turns the configuration of `|Φ_{x,σ}⟩` into that of
`|Φ_{y,τ}⟩` with `x ≠ y`, then the hop must be the hole-filling one:
create at the hole `x`, annihilate the spin-`σ_y` electron at `y`. Evaluating
the resulting configuration at the occupied orbital of `y` (forcing the
annihilation site/spin) and at the occupied orbital of `x` (forcing the creation
site) pins `i = x`, `j = y`, `s = σ_y`. -/
private theorem hop_config_forces (N : ℕ) (x y i j : Fin (N + 1))
    (σ τ : Fin (N + 1) → Bool) (s : Fin 2) (hxy : x ≠ y)
    (hupd : Function.update
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)
        (spinfulIndex N i s) 1 = hubbardOneHoleConfig N y τ) :
    i = x ∧ j = y ∧ s = (if σ y then 0 else 1) := by
  have hyx : y ≠ x := fun h => hxy h.symm
  -- Evaluate at `(y, σ_y)`: the annihilation must occur there.
  have e1 := congrFun hupd (spinfulIndex N y (if σ y then 0 else 1))
  rw [Function.update_apply, Function.update_apply,
    oneHole_occupied N x σ y hyx, oneHole_hole_zero] at e1
  have hjy : j = y ∧ s = (if σ y then 0 else 1) := by
    by_cases h1 : spinfulIndex N y (if σ y then 0 else 1) = spinfulIndex N i s
    · rw [if_pos h1] at e1; exact absurd e1 one_ne_zero
    · rw [if_neg h1] at e1
      by_cases h2 : spinfulIndex N y (if σ y then 0 else 1) = spinfulIndex N j s
      · obtain ⟨hyj, hsy⟩ := (spinfulIndex_eq_iff N y j _ s).mp h2
        exact ⟨hyj.symm, hsy.symm⟩
      · rw [if_neg h2] at e1; exact absurd e1 one_ne_zero
  obtain ⟨hjy', hsy'⟩ := hjy
  -- Evaluate at `(x, τ_x)`: the creation must occur there.
  have e2 := congrFun hupd (spinfulIndex N x (if τ x then 0 else 1))
  rw [Function.update_apply, Function.update_apply] at e2
  -- The annihilation orbital `(j, s) = (y, σ_y)` differs from `(x, τ_x)` (x ≠ y).
  have hxne : ¬ spinfulIndex N x (if τ x then 0 else 1) = spinfulIndex N j s := by
    rw [hjy', hsy']
    intro h; exact hxy ((spinfulIndex_eq_iff N x y _ _).mp h).1
  rw [if_neg hxne,
    show hubbardOneHoleConfig N x σ (spinfulIndex N x (if τ x then 0 else 1)) = 0 from
      by rcases fin2_eq_zero_or_one (if τ x then (0 : Fin 2) else 1) with h | h <;>
        rw [h] <;> [rw [hubbardOneHoleConfig_apply_up, if_pos rfl];
          rw [hubbardOneHoleConfig_apply_down, if_pos rfl]],
    oneHole_occupied N y τ x hxy] at e2
  by_cases h3 : spinfulIndex N x (if τ x then 0 else 1) = spinfulIndex N i s
  · obtain ⟨hxi, _⟩ := (spinfulIndex_eq_iff N x i _ s).mp h3
    exact ⟨hxi.symm, hjy', hsy'⟩
  · rw [if_neg h3] at e2; exact absurd e2.symm one_ne_zero

/-! ## The matrix element (11.2.5) -/

/-- Tasaki eq. (11.2.5): the off-diagonal one-hole effective-Hamiltonian matrix
element in the Tasaki basis. For `x ≠ y` it equals `-t_{x,y}` when the target
spin configuration is the moved one `σ_{y→x}` (i.e. their one-hole
configurations coincide), and `0` otherwise. -/
theorem hubbardEffective_tasaki_matrixElement (N : ℕ) (x y : Fin (N + 1))
    (σ τ : Fin (N + 1) → Bool) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hxy : x ≠ y) :
    (∑ w : Fin (2 * N + 2) → Fin 2, hubbardTasakiBasisState N y τ w *
        ((hubbardEffectiveHamiltonian N t U) *ᵥ hubbardTasakiBasisState N x σ) w) =
      -t x y * (if hubbardOneHoleConfig N y (hubbardSpinMove N σ x y) =
        hubbardOneHoleConfig N y τ then 1 else 0) := by
  -- `Φ^T_{x,σ}` is hard-core, so `Ĥ_eff` reduces to the projected kinetic term.
  have hmem : hubbardTasakiBasisState N x σ ∈ hubbardHardcoreSubspace N := by
    rw [hubbardTasakiBasisState_eq_smul_basisVec]
    exact Submodule.smul_mem _ _ (hubbardHardcoreBasisState_mem_hardcoreSubspace N x σ)
  rw [hubbardEffectiveHamiltonian_mulVec_eq_projected_kinetic_of_mem N t U hmem]
  -- Extract the `C_{y,τ}` component, dropping the outer projection.
  have hyfac : ∀ w, hubbardTasakiBasisState N y τ w =
      hubbardTasakiBasisSign N y τ * basisVec (hubbardOneHoleConfig N y τ) w := by
    intro w; rw [hubbardTasakiBasisState_eq_smul_basisVec]; rfl
  simp_rw [hyfac]
  rw [show (∑ w : Fin (2 * N + 2) → Fin 2, hubbardTasakiBasisSign N y τ *
        basisVec (hubbardOneHoleConfig N y τ) w *
        (hubbardHardcoreProjection N *ᵥ
          hubbardKinetic N t *ᵥ hubbardTasakiBasisState N x σ) w) =
      hubbardTasakiBasisSign N y τ * ∑ w : Fin (2 * N + 2) → Fin 2,
        basisVec (hubbardOneHoleConfig N y τ) w *
        (hubbardHardcoreProjection N *ᵥ
          hubbardKinetic N t *ᵥ hubbardTasakiBasisState N x σ) w from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => by ring),
    basisVec_sum_mul, hardcore_proj_apply]
  -- Expand the kinetic operator over spin/site sums.
  have hexpand : (hubbardKinetic N t *ᵥ hubbardTasakiBasisState N x σ)
        (hubbardOneHoleConfig N y τ) =
      ∑ s : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), t i j *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i s) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j s)) *ᵥ
          hubbardTasakiBasisState N x σ) (hubbardOneHoleConfig N y τ) := by
    unfold hubbardKinetic
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hexpand]
  -- Per-term value, and vanishing of every non-hole-filling channel.
  have hterm : ∀ (s : Fin 2) (i j : Fin (N + 1)),
      ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i s) *
          fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j s)) *ᵥ
        hubbardTasakiBasisState N x σ) (hubbardOneHoleConfig N y τ) =
      hubbardTasakiBasisSign N x σ *
        (if hubbardOneHoleConfig N x σ (spinfulIndex N j s) = 1 ∧
            (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)
              (spinfulIndex N i s) = 0 then
          (jwSign (2 * N + 1) (spinfulIndex N j s) (hubbardOneHoleConfig N x σ) *
            jwSign (2 * N + 1) (spinfulIndex N i s)
              (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)) *
            (if hubbardOneHoleConfig N y τ =
                Function.update (Function.update (hubbardOneHoleConfig N x σ)
                  (spinfulIndex N j s) 0) (spinfulIndex N i s) 1 then 1 else 0)
        else 0) := by
    intro s i j
    rw [hubbardTasakiBasisState_eq_smul_basisVec, Matrix.mulVec_smul,
      show basisVec (hubbardOneHoleConfig N x σ) = hubbardHardcoreBasisState N x σ from rfl,
      hubbardHardcoreBasisState, fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
    by_cases hv : hubbardOneHoleConfig N x σ (spinfulIndex N j s) = 1 ∧
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)
          (spinfulIndex N i s) = 0
    · rw [if_pos hv, if_pos hv, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul, basisVec_apply]
    · simp [hv]
  simp_rw [hterm]
  -- The only surviving channel is `(s, i, j) = (σ_y-orbital, x, y)`.
  set sstar : Fin 2 := if σ y then 0 else 1 with hsstar
  have hvanish : ∀ (s : Fin 2) (i j : Fin (N + 1)),
      ¬(i = x ∧ j = y ∧ s = sstar) →
      hubbardTasakiBasisSign N x σ *
        (if hubbardOneHoleConfig N x σ (spinfulIndex N j s) = 1 ∧
            (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)
              (spinfulIndex N i s) = 0 then
          (jwSign (2 * N + 1) (spinfulIndex N j s) (hubbardOneHoleConfig N x σ) *
            jwSign (2 * N + 1) (spinfulIndex N i s)
              (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)) *
            (if hubbardOneHoleConfig N y τ =
                Function.update (Function.update (hubbardOneHoleConfig N x σ)
                  (spinfulIndex N j s) 0) (spinfulIndex N i s) 1 then 1 else 0)
        else 0) = 0 := by
    intro s i j hne
    refine mul_eq_zero.mpr (Or.inr ?_)
    by_cases hv : hubbardOneHoleConfig N x σ (spinfulIndex N j s) = 1 ∧
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)
          (spinfulIndex N i s) = 0
    · rw [if_pos hv]
      refine mul_eq_zero.mpr (Or.inr ?_)
      rw [if_neg]
      intro hc
      exact hne (hop_config_forces N x y i j σ τ s hxy hc.symm)
    · rw [if_neg hv]
  -- Collapse the triple sum to the surviving channel.
  rw [Finset.sum_eq_single sstar
    (fun s _ hs => Finset.sum_eq_zero (fun i _ => Finset.sum_eq_zero (fun j _ => by
      rw [hvanish s i j (fun h => hs h.2.2), mul_zero])))
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [Finset.sum_eq_single x
    (fun i _ hi => Finset.sum_eq_zero (fun j _ => by
      rw [hvanish sstar i j (fun h => hi h.1), mul_zero]))
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [Finset.sum_eq_single y
    (fun j _ hj => by rw [hvanish sstar x j (fun h => hj h.2.1), mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  -- Evaluate the surviving channel via the uniform-sign action (11.2.4).
  have hocc : hubbardOneHoleConfig N x σ (spinfulIndex N y sstar) = 1 := by
    rw [hsstar]; exact oneHole_occupied N x σ y (fun h => hxy h.symm)
  have hhop := hubbardTasakiHop_mulVec N x y σ sstar hxy hocc
  rw [← hterm sstar x y, hhop]
  -- `(-Φ^T_{y,σ_{y→x}})(C_{y,τ}) = -ε(y, σ_{y→x}) · [match]`
  rw [Pi.neg_apply, hubbardTasakiBasisState_eq_smul_basisVec, Pi.smul_apply,
    smul_eq_mul, basisVec_apply, hubbardTasakiBasisSign_eq, hubbardTasakiBasisSign_eq]
  have hsq : (-1 : ℂ) ^ y.val * (-1) ^ y.val = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨y.val, rfl⟩
  by_cases hmatch : hubbardOneHoleConfig N y (hubbardSpinMove N σ x y) =
      hubbardOneHoleConfig N y τ
  · rw [if_pos hmatch, if_pos hmatch.symm, mul_one, mul_one,
      show (-1 : ℂ) ^ y.val * (t x y * -(-1 : ℂ) ^ y.val)
        = -(t x y) * ((-1 : ℂ) ^ y.val * (-1) ^ y.val) from by ring, hsq, mul_one]
  · rw [if_neg hmatch, if_neg (fun h => hmatch h.symm), mul_zero, mul_zero,
      neg_zero, mul_zero, mul_zero]

/-! ## The diagonal matrix element (no self-hopping) -/

/-- A single hop returning the hole to its original site `x` must be the trivial
on-site `i = j` move: any genuine hop (`i ≠ j`) empties the source site `j`
without refilling it, producing a configuration whose hole is not at `x` alone,
which cannot equal the one-hole configuration `C_{x,τ}`. -/
private theorem hop_diag_forces (N : ℕ) (x i j : Fin (N + 1))
    (σ τ : Fin (N + 1) → Bool) (s : Fin 2)
    (hvj : hubbardOneHoleConfig N x σ (spinfulIndex N j s) = 1)
    (hupd : Function.update
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)
        (spinfulIndex N i s) 1 = hubbardOneHoleConfig N x τ) :
    i = j := by
  by_contra hij
  have hjx : j ≠ x := by
    intro h; subst h; rw [oneHole_hole_zero] at hvj; exact absurd hvj (by decide)
  have hjx' : j.val ≠ x.val := fun h => hjx (Fin.ext h)
  -- `s` is the occupied orbital of `j`.
  have hsoj : s = (if σ j then 0 else 1) := by
    rcases fin2_eq_zero_or_one s with rfl | rfl
    · rw [hubbardOneHoleConfig_apply_up, if_neg hjx'] at hvj
      by_cases hσ : σ j
      · simp [hσ]
      · rw [if_neg hσ] at hvj; exact absurd hvj (by decide)
    · rw [hubbardOneHoleConfig_apply_down, if_neg hjx'] at hvj
      by_cases hσ : σ j
      · rw [if_pos hσ] at hvj; exact absurd hvj (by decide)
      · simp [hσ]
  have e := congrFun hupd (spinfulIndex N j (if τ j then 0 else 1))
  rw [Function.update_apply, Function.update_apply, oneHole_occupied N x τ j hjx] at e
  by_cases h1 : spinfulIndex N j (if τ j then 0 else 1) = spinfulIndex N i s
  · exact hij ((spinfulIndex_eq_iff N j i _ s).mp h1).1.symm
  · rw [if_neg h1] at e
    by_cases h2 : spinfulIndex N j (if τ j then 0 else 1) = spinfulIndex N j s
    · rw [if_pos h2] at e; exact absurd e.symm one_ne_zero
    · rw [if_neg h2] at e
      have hoτs : (if τ j then (0 : Fin 2) else 1) ≠ (if σ j then 0 else 1) := by
        rw [← hsoj]; exact fun h => h2 (by rw [h])
      have hz : hubbardOneHoleConfig N x σ
          (spinfulIndex N j (if τ j then 0 else 1)) = 0 := by
        rcases fin2_eq_zero_or_one (if τ j then (0 : Fin 2) else 1) with hoτ | hoτ
        · rw [hoτ, hubbardOneHoleConfig_apply_up, if_neg hjx',
            if_neg (show ¬ σ j from fun hσ => hoτs (by rw [hoτ, if_pos hσ]))]
        · rw [hoτ, hubbardOneHoleConfig_apply_down, if_neg hjx',
            if_pos (show σ j by by_contra hσ; exact hoτs (by rw [hoτ, if_neg hσ]))]
      rw [hz] at e; exact absurd e.symm one_ne_zero

/-- Diagonal case of Tasaki eq. (11.2.5): when the hopping matrix has no
self-hopping (`t_{ii} = 0` for all `i`), the on-site (`x = y`) effective
matrix element vanishes. With no diagonal kinetic term, `Ĥ_eff` moves the hole
off `x`, so its image is orthogonal to the one-hole state `|Φ_{x,τ}⟩`. -/
theorem hubbardEffective_tasaki_matrixElement_diag (N : ℕ) (x : Fin (N + 1))
    (σ τ : Fin (N + 1) → Bool) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (htdiag : ∀ i, t i i = 0) :
    (∑ w : Fin (2 * N + 2) → Fin 2, hubbardTasakiBasisState N x τ w *
        ((hubbardEffectiveHamiltonian N t U) *ᵥ hubbardTasakiBasisState N x σ) w) = 0 := by
  have hmem : hubbardTasakiBasisState N x σ ∈ hubbardHardcoreSubspace N := by
    rw [hubbardTasakiBasisState_eq_smul_basisVec]
    exact Submodule.smul_mem _ _ (hubbardHardcoreBasisState_mem_hardcoreSubspace N x σ)
  rw [hubbardEffectiveHamiltonian_mulVec_eq_projected_kinetic_of_mem N t U hmem]
  have hyfac : ∀ w, hubbardTasakiBasisState N x τ w =
      hubbardTasakiBasisSign N x τ * basisVec (hubbardOneHoleConfig N x τ) w := by
    intro w; rw [hubbardTasakiBasisState_eq_smul_basisVec]; rfl
  simp_rw [hyfac]
  rw [show (∑ w : Fin (2 * N + 2) → Fin 2, hubbardTasakiBasisSign N x τ *
        basisVec (hubbardOneHoleConfig N x τ) w *
        (hubbardHardcoreProjection N *ᵥ
          hubbardKinetic N t *ᵥ hubbardTasakiBasisState N x σ) w) =
      hubbardTasakiBasisSign N x τ * ∑ w : Fin (2 * N + 2) → Fin 2,
        basisVec (hubbardOneHoleConfig N x τ) w *
        (hubbardHardcoreProjection N *ᵥ
          hubbardKinetic N t *ᵥ hubbardTasakiBasisState N x σ) w from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => by ring),
    basisVec_sum_mul, hardcore_proj_apply]
  refine mul_eq_zero.mpr (Or.inr ?_)
  have hexpand : (hubbardKinetic N t *ᵥ hubbardTasakiBasisState N x σ)
        (hubbardOneHoleConfig N x τ) =
      ∑ s : Fin 2, ∑ i : Fin (N + 1), ∑ j : Fin (N + 1), t i j *
        ((fermionMultiCreation (2 * N + 1) (spinfulIndex N i s) *
            fermionMultiAnnihilation (2 * N + 1) (spinfulIndex N j s)) *ᵥ
          hubbardTasakiBasisState N x σ) (hubbardOneHoleConfig N x τ) := by
    unfold hubbardKinetic
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
  rw [hexpand]
  refine Finset.sum_eq_zero (fun s _ => Finset.sum_eq_zero (fun i _ =>
    Finset.sum_eq_zero (fun j _ => ?_)))
  rw [hubbardTasakiBasisState_eq_smul_basisVec, Matrix.mulVec_smul,
    show basisVec (hubbardOneHoleConfig N x σ) = hubbardHardcoreBasisState N x σ from rfl,
    hubbardHardcoreBasisState, fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  by_cases hij : i = j
  · subst hij; rw [htdiag i]; ring
  · by_cases hv : hubbardOneHoleConfig N x σ (spinfulIndex N j s) = 1 ∧
        (Function.update (hubbardOneHoleConfig N x σ) (spinfulIndex N j s) 0)
          (spinfulIndex N i s) = 0
    · rw [if_pos hv, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
        basisVec_apply,
        if_neg (fun hc => hij (hop_diag_forces N x i j σ τ s hv.1 hc.symm))]
      ring
    · simp [hv]

end LatticeSystem.Fermion
