import LatticeSystem.Quantum.SpinS.LiebSchultzMattisProof
import LatticeSystem.Quantum.SpinS.TotalSpin
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Tasaki §6.2: Lieb–Schultz–Mattis — orthogonality of the twisted state (Lemma 6.2)

Discharge of the §6.2 axiom `lsm_ground_twist_orthogonal` (Lemma 6.2, eq. (6.2.18)): for a
**half-odd-integer** spin chain (`N` odd) with a unique ground state in the `Ŝ_tot^{(3)} = 0`
sector, the LSM trial state is orthogonal to the ground state, `⟨Φ_GS, Û_LSM Φ_GS⟩ = 0`.

The proof uses the **translation operator** `T̂` (cyclic site shift).  Since `Û_LSM`, its generator,
and `Ŝ_tot^{(3)}` are all diagonal, while `T̂` is a permutation, the key transformation law
(eq. (6.2.17)) `T̂† Û_LSM T̂ = (−1)^{2S} Û_LSM e^{i(2π/L)Ŝ_tot^{(3)}}` reduces to a
per-configuration scalar identity for `lsmPhase`.  Translation invariance of the unique ground
state then gives
`⟨Φ_GS, Û_LSM Φ_GS⟩ = (−1)^{2S} ⟨Φ_GS, Û_LSM Φ_GS⟩`, which vanishes for `N` odd.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, eqs. (6.2.12)–(6.2.18), pp. 160–161.
-/

namespace LatticeSystem.Quantum

open Matrix

/-- The **cyclic configuration shift** `(T σ) i = σ (i + 1)` on the ring `Fin L` (relabelling
sites by the rotation `finRotate L`), as an equivalence of spin configurations. -/
noncomputable def chainConfigShiftEquiv (L N : ℕ) :
    (Fin L → Fin (N + 1)) ≃ (Fin L → Fin (N + 1)) :=
  Equiv.arrowCongr (finRotate L).symm (Equiv.refl (Fin (N + 1)))

/-- Pointwise form of the configuration shift: `(T σ) i = σ (finRotate L i) = σ (i + 1)`. -/
theorem chainConfigShiftEquiv_apply (L N : ℕ) (σ : Fin L → Fin (N + 1)) (i : Fin L) :
    chainConfigShiftEquiv L N σ i = σ (finRotate L i) := rfl

/-- The **translation operator** `T̂` on the spin chain: the permutation matrix of the cyclic
configuration shift, `T̂_{σ'σ} = 1` iff `σ' = T σ`. -/
noncomputable def chainTranslationOp (L N : ℕ) : ManyBodyOpS (Fin L) N :=
  fun σ' σ => if σ' = chainConfigShiftEquiv L N σ then 1 else 0

/-- Matrix element of the translation operator. -/
theorem chainTranslationOp_apply (L N : ℕ) (σ' σ : Fin L → Fin (N + 1)) :
    chainTranslationOp L N σ' σ = if σ' = chainConfigShiftEquiv L N σ then 1 else 0 := rfl

/-- The conjugate transpose of the translation operator: `T̂†_{σ'σ} = 1` iff `σ = T σ'`. -/
theorem chainTranslationOp_conjTranspose_apply (L N : ℕ) (σ' σ : Fin L → Fin (N + 1)) :
    (chainTranslationOp L N).conjTranspose σ' σ =
      if σ = chainConfigShiftEquiv L N σ' then 1 else 0 := by
  rw [Matrix.conjTranspose_apply, chainTranslationOp_apply]
  split <;> simp_all

/-- **Translation is unitary** (`T̂† T̂ = 1`): the shift is a permutation, so its permutation matrix
is orthogonal. -/
theorem chainTranslationOp_unitary (L N : ℕ) :
    (chainTranslationOp L N).conjTranspose * chainTranslationOp L N = 1 := by
  ext σ' σ
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [chainTranslationOp_conjTranspose_apply, chainTranslationOp_apply]
  rw [Finset.sum_eq_single (chainConfigShiftEquiv L N σ')]
  · rw [if_pos rfl, one_mul]
    by_cases h : σ' = σ
    · subst h; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun hc => h ((chainConfigShiftEquiv L N).injective hc)), if_neg h]
  · intro b _ hb
    rw [if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Translation is unitary** (`T̂ T̂† = 1`). -/
theorem chainTranslationOp_unitary' (L N : ℕ) :
    chainTranslationOp L N * (chainTranslationOp L N).conjTranspose = 1 :=
  mul_eq_one_comm.mpr (chainTranslationOp_unitary L N)

/-- **Master conjugation law**: conjugating any operator `M` by the translation reindexes both
configuration arguments by the shift, `(T̂† M T̂)_{σ'σ} = M_{(Tσ')(Tσ)}`. -/
theorem chainTranslation_conj_apply (L N : ℕ) (M : ManyBodyOpS (Fin L) N)
    (σ' σ : Fin L → Fin (N + 1)) :
    ((chainTranslationOp L N).conjTranspose * M * chainTranslationOp L N) σ' σ =
      M (chainConfigShiftEquiv L N σ') (chainConfigShiftEquiv L N σ) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (chainConfigShiftEquiv L N σ)]
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single (chainConfigShiftEquiv L N σ')]
    · rw [chainTranslationOp_conjTranspose_apply, if_pos rfl, one_mul,
        chainTranslationOp_apply, if_pos rfl, mul_one]
    · intro b _ hb
      rw [chainTranslationOp_conjTranspose_apply, if_neg hb, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro b _ hb
    rw [chainTranslationOp_apply, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Translation conjugation shifts the site of an on-site operator**:
`T̂† (onSiteS i A) T̂ = onSiteS (finRotate L i) A` (the site index advances by one). -/
theorem chainTranslation_conj_onSiteS (L N : ℕ) (i : Fin L)
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    (chainTranslationOp L N).conjTranspose * onSiteS i A * chainTranslationOp L N =
      onSiteS (finRotate L i) A := by
  ext σ' σ
  rw [chainTranslation_conj_apply, onSiteS_apply, onSiteS_apply]
  have hpred : (∀ k, k ≠ i →
        chainConfigShiftEquiv L N σ' k = chainConfigShiftEquiv L N σ k) ↔
      (∀ k, k ≠ finRotate L i → σ' k = σ k) := by
    constructor
    · intro h m hm
      have hk : (finRotate L).symm m ≠ i := by
        intro hc
        exact hm (by rw [← Equiv.apply_symm_apply (finRotate L) m, hc])
      have := h ((finRotate L).symm m) hk
      simpa [chainConfigShiftEquiv_apply, Equiv.apply_symm_apply] using this
    · intro h k hk
      simp only [chainConfigShiftEquiv_apply]
      exact h (finRotate L k) (fun hc => hk ((finRotate L).injective hc))
  by_cases hc : ∀ k, k ≠ finRotate L i → σ' k = σ k
  · rw [if_pos (hpred.mpr hc), if_pos hc, chainConfigShiftEquiv_apply, chainConfigShiftEquiv_apply]
  · rw [if_neg (fun h => hc (hpred.mp h)), if_neg hc]

/-- **Conjugation is multiplicative** (`T̂` is unitary): `T̂† (A B) T̂ = (T̂† A T̂)(T̂† B T̂)`. -/
theorem chainTranslation_conj_mul (L N : ℕ) (A B : ManyBodyOpS (Fin L) N) :
    (chainTranslationOp L N).conjTranspose * (A * B) * chainTranslationOp L N =
      ((chainTranslationOp L N).conjTranspose * A * chainTranslationOp L N) *
        ((chainTranslationOp L N).conjTranspose * B * chainTranslationOp L N) := by
  calc (chainTranslationOp L N).conjTranspose * (A * B) * chainTranslationOp L N
      = (chainTranslationOp L N).conjTranspose * A *
          (chainTranslationOp L N * (chainTranslationOp L N).conjTranspose) *
          (B * chainTranslationOp L N) := by
        rw [chainTranslationOp_unitary']; noncomm_ring
    _ = ((chainTranslationOp L N).conjTranspose * A * chainTranslationOp L N) *
          ((chainTranslationOp L N).conjTranspose * B * chainTranslationOp L N) := by
        noncomm_ring

/-- **Translation conjugation shifts both sites of a two-site dot product**:
`T̂† (Ŝ_x · Ŝ_y) T̂ = Ŝ_{x+1} · Ŝ_{y+1}`. -/
theorem chainTranslation_conj_spinSDot (L N : ℕ) (x y : Fin L) :
    (chainTranslationOp L N).conjTranspose * spinSDot x y N * chainTranslationOp L N =
      spinSDot (finRotate L x) (finRotate L y) N := by
  rw [spinSDot_def, spinSDot_def]
  simp only [Matrix.mul_add, Matrix.add_mul, chainTranslation_conj_mul,
    chainTranslation_conj_onSiteS]

/-- `(finRotate L z).val = (z.val + 1) % L` (cyclic successor on the ring). -/
theorem val_finRotate (L : ℕ) (z : Fin L) : (finRotate L z).val = (z.val + 1) % L := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos z).ne'
  rw [finRotate_succ_apply, Fin.val_add_one]
  split_ifs with h
  · subst h; simp [Fin.val_last]
  · rw [Nat.mod_eq_of_lt (by have := Fin.val_lt_last h; omega)]

/-- **The ring coupling is translation invariant**: shifting both endpoints by the cyclic
successor preserves the nearest-neighbor coupling. -/
theorem ringCoupling_finRotate (L : ℕ) (x y : Fin L) :
    ringCoupling L (finRotate L x) (finRotate L y) = ringCoupling L x y := by
  unfold ringCoupling
  rw [val_finRotate, val_finRotate]
  have hiff : ((y.val + 1) % L = ((x.val + 1) % L + 1) % L) ↔ (y.val = (x.val + 1) % L) := by
    constructor
    · intro h
      have hm : y.val ≡ (x.val + 1) % L [MOD L] := Nat.ModEq.add_right_cancel' 1 h
      rwa [Nat.ModEq, Nat.mod_eq_of_lt y.isLt, Nat.mod_mod_of_dvd _ dvd_rfl] at hm
    · intro h; rw [h]
  simp only [hiff]

/-- **The translation commutes with the AFM Heisenberg chain Hamiltonian**: `T̂ Ĥ = Ĥ T̂`. -/
theorem chainTranslation_commute_hamiltonian (L N : ℕ) :
    chainTranslationOp L N * afmHeisenbergChainHamiltonianS L N =
      afmHeisenbergChainHamiltonianS L N * chainTranslationOp L N := by
  have hconj : (chainTranslationOp L N).conjTranspose * afmHeisenbergChainHamiltonianS L N *
      chainTranslationOp L N = afmHeisenbergChainHamiltonianS L N := by
    unfold afmHeisenbergChainHamiltonianS heisenbergHamiltonianS
    have key : ∀ x y : Fin L, (chainTranslationOp L N).conjTranspose *
          (ringCoupling L x y • spinSDot x y N) * chainTranslationOp L N =
        ringCoupling L x y • spinSDot (finRotate L x) (finRotate L y) N := by
      intro x y
      rw [Matrix.mul_smul, Matrix.smul_mul, chainTranslation_conj_spinSDot]
    rw [show (chainTranslationOp L N).conjTranspose *
          (∑ x : Fin L, ∑ y : Fin L, ringCoupling L x y • spinSDot x y N) *
          chainTranslationOp L N =
        ∑ x : Fin L, ∑ y : Fin L, (chainTranslationOp L N).conjTranspose *
          (ringCoupling L x y • spinSDot x y N) * chainTranslationOp L N from by
        simp only [Finset.mul_sum, Finset.sum_mul]]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => key x y))]
    rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by
      rw [← ringCoupling_finRotate L x y]))]
    rw [Finset.sum_congr rfl (fun x _ => (Equiv.sum_comp (finRotate L)
      (fun b => ringCoupling L (finRotate L x) b • spinSDot (finRotate L x) b N)))]
    rw [Equiv.sum_comp (finRotate L)
      (fun a => ∑ b : Fin L, ringCoupling L a b • spinSDot a b N)]
  calc chainTranslationOp L N * afmHeisenbergChainHamiltonianS L N
      = chainTranslationOp L N * ((chainTranslationOp L N).conjTranspose *
          afmHeisenbergChainHamiltonianS L N * chainTranslationOp L N) := by rw [hconj]
    _ = (chainTranslationOp L N * (chainTranslationOp L N).conjTranspose) *
          afmHeisenbergChainHamiltonianS L N * chainTranslationOp L N := by noncomm_ring
    _ = afmHeisenbergChainHamiltonianS L N * chainTranslationOp L N := by
        rw [chainTranslationOp_unitary', Matrix.one_mul]

/-- **Per-site twist-angle shift**: `θ_x = θ_{x+1} − 2π/L + 2π·[x = last]`, the source of the
boundary `(−1)^{2S}` factor in the translation law. -/
theorem lsmAngle_finRotate (L : ℕ) (hL : 0 < L) (x : Fin L) :
    ((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) : ℝ) =
      ((2 * Real.pi * (((finRotate L x).val : ℝ) + 1)) / (L : ℝ) : ℝ) - 2 * Real.pi / (L : ℝ) +
        (if x.val + 1 = L then 2 * Real.pi else 0) := by
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  rw [val_finRotate]
  by_cases h : x.val + 1 = L
  · rw [if_pos h, h, Nat.mod_self]
    have hxL : ((x.val : ℝ) + 1) = (L : ℝ) := by exact_mod_cast h
    rw [hxL]; push_cast; field_simp; ring
  · rw [if_neg h, Nat.mod_eq_of_lt (by have := x.isLt; omega)]
    push_cast; field_simp; ring

/-- **LSM phase of the shifted configuration** (eq. (6.2.15)–(6.2.16) at the diagonal level):
`φ(Tσ) = φ(σ) − (2π/L)·Σ_x(S − σ_x) + (boundary)`.  The boundary indicator sum (the single last-site
term `2π(S − σ_0)`) is the wrap that produces `(−1)^{2S}` after exponentiation. -/
theorem lsmPhase_chainConfigShift (L N : ℕ) (hL : 0 < L) (σ : Fin L → Fin (N + 1)) :
    lsmPhase L N (chainConfigShiftEquiv L N σ) =
      lsmPhase L N σ -
          ((2 * Real.pi / (L : ℝ) : ℝ) : ℂ) *
            (∑ x : Fin L, ((N : ℂ) / 2 - ((σ x).val : ℂ))) +
        (∑ x : Fin L, (if x.val + 1 = L then
          (2 * Real.pi : ℂ) * ((N : ℂ) / 2 - ((σ (finRotate L x)).val : ℂ)) else 0)) := by
  simp only [lsmPhase, chainConfigShiftEquiv_apply]
  rw [show (∑ x : Fin L, (((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) *
        ((N : ℂ) / 2 - ((σ (finRotate L x)).val : ℂ))) =
      ∑ x : Fin L, (((((2 * Real.pi * (((finRotate L x).val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) -
            ((2 * Real.pi / (L : ℝ) : ℝ) : ℂ) +
            (if x.val + 1 = L then (2 * Real.pi : ℂ) else 0)) *
          ((N : ℂ) / 2 - ((σ (finRotate L x)).val : ℂ))) from by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [lsmAngle_finRotate L hL x]
        push_cast
        split_ifs <;> push_cast <;> ring]
  simp only [sub_mul, add_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Equiv.sum_comp (finRotate L)
        (fun j => (((2 * Real.pi * ((j.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) *
          ((N : ℂ) / 2 - ((σ j).val : ℂ))),
    ← Finset.mul_sum,
    Equiv.sum_comp (finRotate L) (fun j => ((N : ℂ) / 2 - ((σ j).val : ℂ)))]
  rw [show (∑ x : Fin L, (if x.val + 1 = L then (2 * Real.pi : ℂ) else 0) *
        ((N : ℂ) / 2 - ((σ (finRotate L x)).val : ℂ))) =
      ∑ x : Fin L, (if x.val + 1 = L then
        (2 * Real.pi : ℂ) * ((N : ℂ) / 2 - ((σ (finRotate L x)).val : ℂ)) else 0) from by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        split_ifs <;> ring]
  rw [Finset.sum_sub_distrib]

end LatticeSystem.Quantum
