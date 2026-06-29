import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockKinetic

/-!
# The block coefficient matrix and the row-local up-kinetic action (Tasaki §10.2.1)

Sixth layer (PR6) toward discharging `theorem_10_2_lieb_attractive_unique_singlet`
(Lieb's theorem for the attractive Hubbard model).

Building on the species factorization of `LiebAttractiveBlockKinetic.lean`, this
file introduces the **block coefficient matrix** `hubbardBlockCoeff` (the analogue
of the interleaved `spinReflectionCoeff` but read in block order) and proves that
the block-order up kinetic operator acts on it as a **row-local (left) action**:
each column `h` of the coefficient matrix is transformed by a fixed matrix, with
no mixing between columns. This is the "left multiplication on the coefficient
matrix" structure of Lieb's argument; identifying the per-column matrix with the
single-species Fock kinetic operator, and connecting the block order to the
interleaved `hubbardKinetic`, are subsequent layers (PR7+).

## Main definitions

* `hubbardBlockUpConfig` / `hubbardBlockDownConfig` / `hubbardBlockSpinConfigEquiv`
  / `hubbardBlockCoeffLinearEquiv` — the block analogue of the up/down
  factorization and coefficient-matrix isomorphism.
* `hubbardBlockCoeff` — the block (down-hole-gauged) coefficient matrix.
* `hubbardBlockKineticUpCoeffMatrix` / `hubbardBlockKineticUpCoeffAction` — the
  per-column matrix and the induced row-local action.

## Main results

* `hubbardBlockFixedDownSubmodule_apply_eq_zero_of_ne` — a state in the fixed-down
  fiber vanishes on block-merge configs with a different down configuration.
* `hubbardBlockKineticUp_apply_eq_zero_of_down_ne` — the up-kinetic matrix entry
  between configs with different down parts vanishes.
* `hubbardBlockCoeff_hubbardBlockKineticUp_mulVec` — the up-kinetic acts on the
  block coefficient matrix as the row-local action `C ↦ (column-wise left mult)`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-! ## The block up/down factorization and coefficient matrix -/

/-- The up part of a spin-orbital configuration read in block order. -/
def hubbardBlockUpConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : hubbardSpinConfig N :=
  fun i => c (hubbardBlockIndex N i 0)

/-- The down part of a spin-orbital configuration read in block order. -/
def hubbardBlockDownConfig (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) : hubbardSpinConfig N :=
  fun i => c (hubbardBlockIndex N i 1)

/-- The block up projection recovers the up part of a block merge. -/
@[simp]
theorem hubbardBlockUpConfig_merge (N : ℕ) (u d : hubbardSpinConfig N) :
    hubbardBlockUpConfig N (hubbardBlockMergeConfig N u d) = u := by
  funext i; simp [hubbardBlockUpConfig]

/-- The block down projection recovers the down part of a block merge. -/
@[simp]
theorem hubbardBlockDownConfig_merge (N : ℕ) (u d : hubbardSpinConfig N) :
    hubbardBlockDownConfig N (hubbardBlockMergeConfig N u d) = d := by
  funext i; simp [hubbardBlockDownConfig]

/-- Merging the block up/down projections recovers the configuration. -/
@[simp]
theorem hubbardBlockMergeConfig_up_down (N : ℕ) (c : Fin (2 * N + 2) → Fin 2) :
    hubbardBlockMergeConfig N (hubbardBlockUpConfig N c) (hubbardBlockDownConfig N c) = c := by
  funext o
  obtain ⟨a, r, rfl⟩ := exists_hubbardBlockIndex N o
  fin_cases r
  · simp [hubbardBlockUpConfig]
  · simp [hubbardBlockDownConfig]

/-- The block-order factorization `H = H↑ ⊗ H↓` as an `Equiv`. -/
def hubbardBlockSpinConfigEquiv (N : ℕ) :
    (Fin (2 * N + 2) → Fin 2) ≃ hubbardSpinConfig N × hubbardSpinConfig N where
  toFun c := (hubbardBlockUpConfig N c, hubbardBlockDownConfig N c)
  invFun p := hubbardBlockMergeConfig N p.1 p.2
  left_inv c := by simp
  right_inv p := by obtain ⟨u, d⟩ := p; simp

/-- The block-order linear isomorphism between a state vector and its coefficient
matrix `M_{u,d} = ψ (merge u d)` (the block analogue of
`hubbardSpinCoeffLinearEquiv`). -/
noncomputable def hubbardBlockCoeffLinearEquiv (N : ℕ) :
    ((Fin (2 * N + 2) → Fin 2) → ℂ) ≃ₗ[ℂ]
      Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ where
  toFun ψ := fun u d => ψ (hubbardBlockMergeConfig N u d)
  map_add' ψ φ := by funext u d; simp
  map_smul' a ψ := by funext u d; simp
  invFun M := fun c => M (hubbardBlockUpConfig N c) (hubbardBlockDownConfig N c)
  left_inv ψ := by funext c; simp
  right_inv M := by funext u d; simp

/-- The block (down-hole-gauged) coefficient matrix of a state vector. -/
noncomputable def hubbardBlockCoeff (N : ℕ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  fun u h => ψ (hubbardBlockMergeConfig N u (particleHoleConfig N h))

/-! ## Fixed-fiber vanishing -/

/-- A state in the fixed-down fiber over `d'` vanishes on a block-merge config with
a different down configuration `d`. -/
theorem hubbardBlockFixedDownSubmodule_apply_eq_zero_of_ne (N : ℕ)
    {d d' : hubbardSpinConfig N} (hdd : d' ≠ d)
    {φ : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hφ : φ ∈ hubbardBlockFixedDownSubmodule N d') (u : hubbardSpinConfig N) :
    φ (hubbardBlockMergeConfig N u d) = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u', rfl⟩ := hx
    exact basisVec_of_ne (fun he => hdd
      (by simpa using (congrArg (hubbardBlockDownConfig N) he).symm))
  | zero => rfl
  | add x y _ _ hx hy => rw [Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Pi.smul_apply, hx, smul_zero]

/-- The up-kinetic matrix entry between configs with different down parts vanishes. -/
theorem hubbardBlockKineticUp_apply_eq_zero_of_down_ne (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    {u u' d d' : hubbardSpinConfig N} (hdd : d' ≠ d) :
    (hubbardBlockKineticUp N T)
        (hubbardBlockMergeConfig N u d) (hubbardBlockMergeConfig N u' d') = 0 := by
  have hmem := hubbardBlockKineticUp_mulVec_basisVec_mem_fixedDown N T u' d'
  have hentry : (hubbardBlockKineticUp N T)
      (hubbardBlockMergeConfig N u d) (hubbardBlockMergeConfig N u' d')
      = ((hubbardBlockKineticUp N T).mulVec
          (basisVec (hubbardBlockMergeConfig N u' d'))) (hubbardBlockMergeConfig N u d) := by
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_mul_basisVec (hubbardBlockMergeConfig N u' d')
      (fun k => (hubbardBlockKineticUp N T) (hubbardBlockMergeConfig N u d) k)]
  rw [hentry]
  exact hubbardBlockFixedDownSubmodule_apply_eq_zero_of_ne N hdd hmem u

/-! ## The row-local up-kinetic action on the block coefficient matrix -/

/-- The per-column matrix by which the up kinetic operator transforms each column
of the block coefficient matrix. -/
noncomputable def hubbardBlockKineticUpCoeffMatrix (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ) (h : hubbardSpinConfig N) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  fun u u' => (hubbardBlockKineticUp N T)
    (hubbardBlockMergeConfig N u (particleHoleConfig N h))
    (hubbardBlockMergeConfig N u' (particleHoleConfig N h))

/-- The induced row-local (left) action of the up kinetic operator on the block
coefficient matrix. -/
noncomputable def hubbardBlockKineticUpCoeffAction (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (C : Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ) :
    Matrix (hubbardSpinConfig N) (hubbardSpinConfig N) ℂ :=
  fun u h => (hubbardBlockKineticUpCoeffMatrix N T h).mulVec (fun u' => C u' h) u

/-- **The up kinetic operator acts on the block coefficient matrix as a row-local
(left) action.** -/
theorem hubbardBlockCoeff_hubbardBlockKineticUp_mulVec (N : ℕ)
    (T : Fin (N + 1) → Fin (N + 1) → ℂ)
    (ψ : (Fin (2 * N + 2) → Fin 2) → ℂ) :
    hubbardBlockCoeff N ((hubbardBlockKineticUp N T).mulVec ψ)
      = hubbardBlockKineticUpCoeffAction N T (hubbardBlockCoeff N ψ) := by
  funext u h
  have hRHS : hubbardBlockKineticUpCoeffAction N T (hubbardBlockCoeff N ψ) u h
      = ∑ u' : hubbardSpinConfig N,
          (hubbardBlockKineticUp N T)
              (hubbardBlockMergeConfig N u (particleHoleConfig N h))
              (hubbardBlockMergeConfig N u' (particleHoleConfig N h))
            * ψ (hubbardBlockMergeConfig N u' (particleHoleConfig N h)) := by
    simp only [hubbardBlockKineticUpCoeffAction, hubbardBlockKineticUpCoeffMatrix,
      hubbardBlockCoeff, Matrix.mulVec, dotProduct]
  rw [hRHS]
  simp only [hubbardBlockCoeff]
  rw [show (hubbardBlockKineticUp N T).mulVec ψ
        (hubbardBlockMergeConfig N u (particleHoleConfig N h))
      = ∑ c, (hubbardBlockKineticUp N T)
          (hubbardBlockMergeConfig N u (particleHoleConfig N h)) c * ψ c from rfl,
    ← Equiv.sum_comp (hubbardBlockSpinConfigEquiv N).symm
      (fun c => (hubbardBlockKineticUp N T)
        (hubbardBlockMergeConfig N u (particleHoleConfig N h)) c * ψ c)]
  simp only [hubbardBlockSpinConfigEquiv, Equiv.coe_fn_symm_mk]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun u' _ => ?_)
  rw [Finset.sum_eq_single (particleHoleConfig N h)]
  · intro d' _ hd'
    rw [hubbardBlockKineticUp_apply_eq_zero_of_down_ne N T hd', zero_mul]
  · intro hcontra; exact absurd (Finset.mem_univ _) hcontra

end LatticeSystem.Fermion
