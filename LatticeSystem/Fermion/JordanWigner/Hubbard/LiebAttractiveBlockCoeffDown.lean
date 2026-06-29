import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockCoeff

/-!
# The column-local down-kinetic action on the block coefficient matrix (Tasaki §10.2.1)

Seventh layer (PR7) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

This is the **down-spin dual** of the row-local up-kinetic action of
`LiebAttractiveBlockCoeff.lean` (PR6). The block coefficient matrix gauges the
down index as a hole (`particleHoleConfig`), so the down kinetic operator — which
mixes the down configuration while keeping the up configuration fixed — acts on
the **column** index of the coefficient matrix, through the particle-hole
involution. The result is a column-local (right) action.

## Main definitions

* `particleHoleConfigEquiv` — the particle-hole involution as a permutation.
* `hubbardBlockKineticDownCoeffMatrix` / `hubbardBlockKineticDownCoeffAction` —
  the per-row matrix (indexed by hole labels) and the induced column-local action.

## Main results

* `hubbardBlockFixedUpSubmodule_apply_eq_zero_of_ne` — a state in the fixed-up
  fiber vanishes on block-merge configs with a different up configuration.
* `hubbardBlockKineticDown_apply_eq_zero_of_up_ne` — the down-kinetic matrix entry
  between configs with different up parts vanishes.
* `hubbardBlockCoeff_hubbardBlockKineticDown_mulVec` — the down kinetic operator
  acts on the block coefficient matrix as a column-local action.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- The particle-hole involution on configurations, as a permutation. -/
def particleHoleConfigEquiv (N : ℕ) : hubbardSpinConfig N ≃ hubbardSpinConfig N :=
  (particleHoleConfig_involutive N).toPerm

/-! ## Fixed-up fiber vanishing -/

/-- A state in the fixed-up fiber over `u'` vanishes on a block-merge config with
a different up configuration `u`. -/
theorem hubbardBlockFixedUpSubmodule_apply_eq_zero_of_ne (N : ℕ)
    {u u' : hubbardSpinConfig N} (huu : u' ≠ u)
    {φ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hφ : φ ∈ hubbardBlockFixedUpSubmodule N u') (d : hubbardSpinConfig N) :
    φ (hubbardBlockMergeConfig N u d) = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d', rfl⟩ := hx
    exact basisVec_of_ne (fun he => huu
      (by simpa using (congrArg (hubbardBlockUpConfig N) he).symm))
  | zero => rfl
  | add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Pi.smul_apply, hx, smul_zero]

/-- The down-kinetic matrix entry between configs with different up parts vanishes. -/
theorem hubbardBlockKineticDown_apply_eq_zero_of_up_ne (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    {u u' d d' : hubbardSpinConfig N} (huu : u' ≠ u) :
    (hubbardBlockKineticDown N T)
        (hubbardBlockMergeConfig N u d) (hubbardBlockMergeConfig N u' d') = 0 := by
  have hmem := hubbardBlockKineticDown_mulVec_basisVec_mem_fixedUp N T u' d'
  have hentry : (hubbardBlockKineticDown N T)
      (hubbardBlockMergeConfig N u d) (hubbardBlockMergeConfig N u' d')
      = ((hubbardBlockKineticDown N T).mulVec
          (basisVec (hubbardBlockMergeConfig N u' d'))) (hubbardBlockMergeConfig N u d) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_mul_basisVec (hubbardBlockMergeConfig N u' d')
      (fun k => (hubbardBlockKineticDown N T) (hubbardBlockMergeConfig N u d) k)]
  rw [hentry]
  exact hubbardBlockFixedUpSubmodule_apply_eq_zero_of_ne N huu hmem d

/-! ## The column-local down-kinetic action on the block coefficient matrix -/

/-- The per-row matrix (indexed by hole labels) by which the down kinetic operator
transforms each row of the block coefficient matrix. -/
noncomputable def hubbardBlockKineticDownCoeffMatrix (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (u : hubbardSpinConfig N) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  fun h h' => (hubbardBlockKineticDown N T)
    (hubbardBlockMergeConfig N u (particleHoleConfig N h))
    (hubbardBlockMergeConfig N u (particleHoleConfig N h'))

/-- The induced column-local action of the down kinetic operator on the block
coefficient matrix. -/
noncomputable def hubbardBlockKineticDownCoeffAction (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  fun u h => (hubbardBlockKineticDownCoeffMatrix N T u).mulVec (fun h' => C u h') h

/-- **The down kinetic operator acts on the block coefficient matrix as a
column-local action through the particle-hole-gauged column index.** -/
theorem hubbardBlockCoeff_hubbardBlockKineticDown_mulVec (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    hubbardBlockCoeff N ((hubbardBlockKineticDown N T).mulVec ψ)
      = hubbardBlockKineticDownCoeffAction N T (hubbardBlockCoeff N ψ) := by
  funext u h
  have hRHS : hubbardBlockKineticDownCoeffAction N T (hubbardBlockCoeff N ψ) u h
      = ∑ h' : hubbardSpinConfig N,
          (hubbardBlockKineticDown N T)
              (hubbardBlockMergeConfig N u (particleHoleConfig N h))
              (hubbardBlockMergeConfig N u (particleHoleConfig N h'))
            * ψ (hubbardBlockMergeConfig N u (particleHoleConfig N h')) := by
    simp only [hubbardBlockKineticDownCoeffAction, hubbardBlockKineticDownCoeffMatrix,
      hubbardBlockCoeff, Matrix.mulVec, dotProduct]
  rw [hRHS]
  simp only [hubbardBlockCoeff]
  rw [show (hubbardBlockKineticDown N T).mulVec ψ
        (hubbardBlockMergeConfig N u (particleHoleConfig N h))
      = ∑ c, (hubbardBlockKineticDown N T)
          (hubbardBlockMergeConfig N u (particleHoleConfig N h)) c * ψ c from rfl,
    ← Equiv.sum_comp (hubbardBlockSpinConfigEquiv N).symm
      (fun c => (hubbardBlockKineticDown N T)
        (hubbardBlockMergeConfig N u (particleHoleConfig N h)) c * ψ c)]
  simp only [hubbardBlockSpinConfigEquiv, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single u]
  · rw [← Equiv.sum_comp (particleHoleConfigEquiv N)
      (fun d' => (hubbardBlockKineticDown N T)
        (hubbardBlockMergeConfig N u (particleHoleConfig N h))
        (hubbardBlockMergeConfig N u d') * ψ (hubbardBlockMergeConfig N u d'))]
    simp only [particleHoleConfigEquiv, Function.Involutive.coe_toPerm]
  · intro u' _ hu'
    refine Finset.sum_eq_zero (fun d' _ => ?_)
    rw [hubbardBlockKineticDown_apply_eq_zero_of_up_ne N T hu', zero_mul]
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

end LatticeSystem.Fermion
