import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockCoeff

/-!
# Gauge independence of the up-kinetic coefficient matrix (Tasaki §10.2.1)

Eighth layer (PR8) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

The per-column matrix `hubbardBlockKineticUpCoeffMatrix N T h` of PR6 is shown to
be **independent of the hole label `h`** (equivalently, of the fixed down
configuration). This identifies the up-kinetic action on the block coefficient
matrix as left multiplication by a single fixed matrix — the second-quantized
up-Fock kinetic operator. The reason is that, in block order, all up orbitals lie
below all down orbitals, so the Jordan–Wigner string of an up-spin hop sees only
the up configuration; hence the up-kinetic matrix entry between two configurations
with the same down part does not depend on that down part.

## Main results

* `basisVec_hubbardBlockMerge_same_down_eq` — a basis-vector value between two
  block-merge configs with a common down part is independent of that down part.
* `jwSign_blockZero_congr_of_eq_below` — the JW string sign at an up block index
  depends only on the up orbitals.
* `hubbardBlockKineticUp_apply_merge_indep_down` — the up-kinetic matrix entry
  between configs with a common down part is independent of that down part.
* `hubbardBlockKineticUpCoeffMatrix_indep_down` — the up-kinetic per-column matrix
  is independent of the hole label.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- A basis-vector value between two block-merge configs sharing a down part is
independent of that down part (it is `1` iff the up parts agree). -/
theorem basisVec_hubbardBlockMerge_same_down_eq (N : ℕ) (a b d d' : hubbardSpinConfig N) :
    basisVec (hubbardBlockMergeConfig N a d) (hubbardBlockMergeConfig N b d)
      = basisVec (hubbardBlockMergeConfig N a d') (hubbardBlockMergeConfig N b d') := by
  simp only [basisVec_apply]
  have key : ∀ e : hubbardSpinConfig N,
      (hubbardBlockMergeConfig N b e = hubbardBlockMergeConfig N a e) ↔ b = a := by
    intro e
    constructor
    · intro h; simpa using congrArg (hubbardBlockUpConfig N) h
    · intro h; rw [h]
  by_cases hba : b = a
  · rw [if_pos ((key d).mpr hba), if_pos ((key d').mpr hba)]
  · rw [if_neg (fun h => hba ((key d).mp h)), if_neg (fun h => hba ((key d').mp h))]

/-- The JW string sign at an up block index depends only on the orbitals below it,
all of which are up orbitals; so two configs agreeing on the up orbitals give the
same sign. -/
theorem jwSign_blockZero_congr_of_eq_below (N : ℕ) (i : Fin (N + 1))
    (c c' : Fin (2 * N + 2) → Fin 2)
    (hcc : ∀ k : Fin (2 * N + 2), k.val < N + 1 → c k = c' k) :
    jwSign (2 * N + 1) (hubbardBlockIndex N i 0) c
      = jwSign (2 * N + 1) (hubbardBlockIndex N i 0) c' := by
  unfold jwSign
  refine Finset.prod_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_filter, hubbardBlockIndex_zero_val] at hk
  rw [hcc k (by have := i.isLt; omega)]

/-- Two block merges with a common down part agree on every up orbital. -/
theorem hubbardBlockMergeConfig_eq_below_of_up (N : ℕ) (u d d' : hubbardSpinConfig N)
    (k : Fin (2 * N + 2)) (hk : k.val < N + 1) :
    hubbardBlockMergeConfig N u d k = hubbardBlockMergeConfig N u d' k := by
  rw [hubbardBlockMergeConfig_of_lt N u d k hk, hubbardBlockMergeConfig_of_lt N u d' k hk]

/-- The matrix entry of a single up hop between configs sharing a down part is
independent of that down part. -/
theorem hubbardBlock_upHop_apply_merge_indep_down (N : ℕ) (i j : Fin (N + 1))
    (u u' d d' : hubbardSpinConfig N) :
    (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
          fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0))
        (hubbardBlockMergeConfig N u d) (hubbardBlockMergeConfig N u' d)
      = (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
          fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0))
        (hubbardBlockMergeConfig N u d') (hubbardBlockMergeConfig N u' d') := by
  have e : ∀ D : hubbardSpinConfig N,
      (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0))
          (hubbardBlockMergeConfig N u D) (hubbardBlockMergeConfig N u' D)
        = ((fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
            fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0)).mulVec
            (basisVec (hubbardBlockMergeConfig N u' D)))
          (hubbardBlockMergeConfig N u D) := by
    intro D
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_mul_basisVec (hubbardBlockMergeConfig N u' D)
      (fun k => (fermionMultiCreation (2 * N + 1) (hubbardBlockIndex N i 0) *
        fermionMultiAnnihilation (2 * N + 1) (hubbardBlockIndex N j 0))
        (hubbardBlockMergeConfig N u D) k)]
  -- equality of the conditions, signs and basis-vector values across `d`, `d'`
  have hcond : ∀ D : hubbardSpinConfig N,
      ((hubbardBlockMergeConfig N u' D) (hubbardBlockIndex N j 0) = 1 ∧
        (Function.update (hubbardBlockMergeConfig N u' D) (hubbardBlockIndex N j 0) 0)
          (hubbardBlockIndex N i 0) = 0)
      ↔ (u' j = 1 ∧ (Function.update (hubbardBlockMergeConfig N u' d) (hubbardBlockIndex N j 0) 0)
          (hubbardBlockIndex N i 0) = 0) := by
    intro D
    have hfst : hubbardBlockMergeConfig N u' D (hubbardBlockIndex N j 0) = u' j :=
      hubbardBlockMergeConfig_blockIndex_zero N u' D j
    have hsec : (Function.update (hubbardBlockMergeConfig N u' D) (hubbardBlockIndex N j 0) 0)
          (hubbardBlockIndex N i 0)
        = (Function.update (hubbardBlockMergeConfig N u' d) (hubbardBlockIndex N j 0) 0)
          (hubbardBlockIndex N i 0) := by
      by_cases hij : (hubbardBlockIndex N i 0) = (hubbardBlockIndex N j 0)
      · rw [hij, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hij, Function.update_of_ne hij,
          hubbardBlockMergeConfig_blockIndex_zero, hubbardBlockMergeConfig_blockIndex_zero]
    rw [hfst, hsec]
  rw [e d, e d', fermionMultiCreation_mul_Annihilation_mulVec_basisVec,
    fermionMultiCreation_mul_Annihilation_mulVec_basisVec]
  rw [apply_ite (f := fun w : (Fin (2 * N + 2) → Fin 2) → ℂ => w (hubbardBlockMergeConfig N u d)),
    apply_ite (f := fun w : (Fin (2 * N + 2) → Fin 2) → ℂ => w (hubbardBlockMergeConfig N u d'))]
  refine if_congr ((hcond d).trans (hcond d').symm) ?_ rfl
  -- the `then` branch: signs agree (jwSign congruence) and basis-vector value agrees
  have hbelow : ∀ k : Fin (2 * N + 2), k.val < N + 1 →
      hubbardBlockMergeConfig N u' d k = hubbardBlockMergeConfig N u' d' k :=
    fun k hk => hubbardBlockMergeConfig_eq_below_of_up N u' d d' k hk
  have hbelow' : ∀ k : Fin (2 * N + 2), k.val < N + 1 →
      (Function.update (hubbardBlockMergeConfig N u' d) (hubbardBlockIndex N j 0) 0) k
        = (Function.update (hubbardBlockMergeConfig N u' d') (hubbardBlockIndex N j 0) 0) k := by
    intro k hk
    by_cases hkj : k = hubbardBlockIndex N j 0
    · rw [hkj, Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hkj, Function.update_of_ne hkj]; exact hbelow k hk
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [jwSign_blockZero_congr_of_eq_below N j _ _ hbelow,
    jwSign_blockZero_congr_of_eq_below N i _ _ hbelow']
  congr 1
  -- basisVec (update (update (merge u' d) (block j 0) 0) (block i 0) 1) (merge u d)
  --   = basisVec (... d' ...) (merge u d')
  rw [← hubbardBlockMergeConfig_update_up N u' d j 0,
    ← hubbardBlockMergeConfig_update_up N (Function.update u' j 0) d i 1,
    ← hubbardBlockMergeConfig_update_up N u' d' j 0,
    ← hubbardBlockMergeConfig_update_up N (Function.update u' j 0) d' i 1]
  exact basisVec_hubbardBlockMerge_same_down_eq N
    (Function.update (Function.update u' j 0) i 1) u d d'

/-- The up-kinetic matrix entry between configs sharing a down part is independent
of that down part. -/
theorem hubbardBlockKineticUp_apply_merge_indep_down (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (u u' d d' : hubbardSpinConfig N) :
    (hubbardBlockKineticUp N T)
        (hubbardBlockMergeConfig N u d) (hubbardBlockMergeConfig N u' d)
      = (hubbardBlockKineticUp N T)
        (hubbardBlockMergeConfig N u d') (hubbardBlockMergeConfig N u' d') := by
  simp only [hubbardBlockKineticUp, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hubbardBlock_upHop_apply_merge_indep_down N i j u u' d d']

/-- **The up-kinetic per-column coefficient matrix is independent of the hole
label.** Hence the up kinetic operator acts on the block coefficient matrix as
left multiplication by a single fixed matrix. -/
theorem hubbardBlockKineticUpCoeffMatrix_indep_down (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (h h' : hubbardSpinConfig N) :
    hubbardBlockKineticUpCoeffMatrix N T h = hubbardBlockKineticUpCoeffMatrix N T h' := by
  funext u u'
  exact hubbardBlockKineticUp_apply_merge_indep_down N T u u'
    (particleHoleConfig N h) (particleHoleConfig N h')

end LatticeSystem.Fermion
