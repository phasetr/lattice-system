import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebAttractiveBlockCoeff

/-!
# The block ↔ interleaved orbital relabeling (Tasaki §10.2.1)

Eleventh layer (PR11) toward discharging
`theorem_10_2_lieb_attractive_unique_singlet` (Lieb's theorem for the attractive
Hubbard model).

The system has two orderings of the `2N+2` spin-orbitals: the **interleaved**
order `spinfulIndex N i σ = 2 i + σ` (used by the actual Hamiltonian and the SRP
coefficient matrix `spinReflectionCoeff`) and the **block** order
`hubbardBlockIndex N i σ = i + σ (N+1)` (used by the coefficient-matrix kinetic
factorization). This file builds the combinatorial bijection relating the two —
the orbital permutation and the induced configuration relabeling — together with
its compatibility with the merge maps. The signed fermionic operator conjugacy is
a later layer.

## Main definitions

* `hubbardSpinfulSiteSpinEquiv` / `hubbardBlockSiteSpinEquiv` — the two
  factorizations `(site, spin) ≃ spin-orbital`.
* `hubbardBlockToSpinfulOrbitalEquiv` — the orbital permutation sending a block
  index to the interleaved index.
* `hubbardBlockToSpinfulConfigEquiv` — the induced configuration relabeling.

## Main results

* `hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex` /
  `…_symm_spinfulIndex` — the permutation matches block and interleaved indices.
* `hubbardBlockToSpinfulConfigEquiv_apply_spinfulIndex` /
  `…_hubbardBlockMergeConfig` — the config relabeling reads block configs and
  carries the block merge to the interleaved merge.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
1st ed., Springer 2020, §10.2.1; E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

variable {N : ℕ}

/-- The interleaved factorization `(site, spin) ≃ spin-orbital`, `(i, σ) ↦ 2 i + σ`. -/
def hubbardSpinfulSiteSpinEquiv (N : ℕ) :
    (Fin (N + 1) × Fin 2) ≃ Fin (2 * N + 2) where
  toFun p := spinfulIndex N p.1 p.2
  invFun k := (⟨k.val / 2, by have := k.isLt; omega⟩, ⟨k.val % 2, by omega⟩)
  left_inv := by
    rintro ⟨i, s⟩
    have hs := s.isLt
    refine Prod.ext (Fin.ext ?_) (Fin.ext ?_) <;> simp only [spinfulIndex] <;> omega
  right_inv := by
    intro k
    apply Fin.ext
    simp only [spinfulIndex]
    omega

/-- The block factorization `(site, spin) ≃ spin-orbital`, `(i, σ) ↦ i + σ (N+1)`,
built from the injectivity/surjectivity of `hubbardBlockIndex`. -/
noncomputable def hubbardBlockSiteSpinEquiv (N : ℕ) :
    (Fin (N + 1) × Fin 2) ≃ Fin (2 * N + 2) :=
  Equiv.ofBijective (fun p => hubbardBlockIndex N p.1 p.2) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp only [Fintype.card_prod, Fintype.card_fin]; omega⟩
    rintro ⟨a, r⟩ ⟨b, s⟩ h
    obtain rfl | rfl : r = 0 ∨ r = 1 := by omega
    · obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
      · exact Prod.ext ((hubbardBlockIndex_zero_inj N a b).mp h) rfl
      · exact absurd h (hubbardBlockIndex_zero_ne_one N a b)
    · obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
      · exact absurd h (hubbardBlockIndex_one_ne_zero N a b)
      · exact Prod.ext ((hubbardBlockIndex_one_inj N a b).mp h) rfl)

/-- `hubbardBlockSiteSpinEquiv` sends `(i, σ)` to the block index. -/
@[simp]
theorem hubbardBlockSiteSpinEquiv_apply (N : ℕ) (i : Fin (N + 1)) (s : Fin 2) :
    hubbardBlockSiteSpinEquiv N (i, s) = hubbardBlockIndex N i s := rfl

/-- The orbital permutation relabeling block order to interleaved order. -/
noncomputable def hubbardBlockToSpinfulOrbitalEquiv (N : ℕ) : Fin (2 * N + 2) ≃ Fin (2 * N + 2) :=
  (hubbardBlockSiteSpinEquiv N).symm.trans (hubbardSpinfulSiteSpinEquiv N)

/-- The orbital permutation sends a block index to the interleaved index. -/
@[simp]
theorem hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex (N : ℕ)
    (i : Fin (N + 1)) (s : Fin 2) :
    hubbardBlockToSpinfulOrbitalEquiv N (hubbardBlockIndex N i s) = spinfulIndex N i s := by
  simp only [hubbardBlockToSpinfulOrbitalEquiv, Equiv.trans_apply]
  rw [← hubbardBlockSiteSpinEquiv_apply, Equiv.symm_apply_apply]
  rfl

/-- The inverse orbital permutation sends an interleaved index to the block index. -/
@[simp]
theorem hubbardBlockToSpinfulOrbitalEquiv_symm_spinfulIndex (N : ℕ)
    (i : Fin (N + 1)) (s : Fin 2) :
    (hubbardBlockToSpinfulOrbitalEquiv N).symm (spinfulIndex N i s)
      = hubbardBlockIndex N i s := by
  rw [Equiv.symm_apply_eq, hubbardBlockToSpinfulOrbitalEquiv_hubbardBlockIndex]

/-- The configuration relabeling induced by the orbital permutation. -/
noncomputable def hubbardBlockToSpinfulConfigEquiv (N : ℕ) :
    (Fin (2 * N + 2) → Fin 2) ≃ (Fin (2 * N + 2) → Fin 2) :=
  (hubbardBlockToSpinfulOrbitalEquiv N).arrowCongr (Equiv.refl (Fin 2))

/-- The relabeled config reads the block config at the corresponding block index. -/
@[simp]
theorem hubbardBlockToSpinfulConfigEquiv_apply_spinfulIndex (N : ℕ)
    (c : Fin (2 * N + 2) → Fin 2) (i : Fin (N + 1)) (s : Fin 2) :
    hubbardBlockToSpinfulConfigEquiv N c (spinfulIndex N i s)
      = c (hubbardBlockIndex N i s) := by
  simp only [hubbardBlockToSpinfulConfigEquiv, Equiv.arrowCongr_apply,
    Equiv.coe_refl, Function.comp_apply, id_eq,
    hubbardBlockToSpinfulOrbitalEquiv_symm_spinfulIndex]

/-- The config relabeling carries the block merge to the interleaved merge. -/
@[simp]
theorem hubbardBlockToSpinfulConfigEquiv_hubbardBlockMergeConfig (N : ℕ)
    (u d : hubbardSpinConfig N) :
    hubbardBlockToSpinfulConfigEquiv N (hubbardBlockMergeConfig N u d)
      = hubbardMergeConfig N u d := by
  funext o
  obtain ⟨i, s, rfl⟩ := exists_spinfulIndex N o
  rw [hubbardBlockToSpinfulConfigEquiv_apply_spinfulIndex]
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · rw [hubbardBlockMergeConfig_blockIndex_zero, hubbardMergeConfig_spinfulIndex_zero]
  · rw [hubbardBlockMergeConfig_blockIndex_one, hubbardMergeConfig_spinfulIndex_one]

end LatticeSystem.Fermion
