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

end LatticeSystem.Quantum
