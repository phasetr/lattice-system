import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveBalancedGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.FermionTotalSpinCasimirCharges
import LatticeSystem.Math.MatrixAnalysis.MinEnergyOnSubspace

/-!
# Casimir sector machinery for Theorem 10.4 (Tasaki §10.2.2, PR-3)

Third installment of the Theorem 10.4 discharge arc (issue #5320). PR-1
(`repulsiveSpinZSector_ground_unique`, `LiebRepulsiveBalancedGround.lean`) supplies a *unique*
ground state on the spin-`z` sector `Ŝ³ = m₀`, pinned to the fixed number eigenvalue `N̂ = N + 1`.
This file refines that joint number/spin-`z` sector by the total-spin Casimir `Ŝ² = (Ŝ_tot)²`,
building the sector machinery that the later homotopy/perturbation PRs (PR-4 to PR-11) use to
locate the one Casimir eigenvalue the transported ground state actually occupies.

## Contents

* `numberSpinZSectorEuclidean N L m₀` — the joint sector `K = {N̂ = L} ⊓ {Ŝ³ = m₀}`, generalizing
  `spinZSectorEuclidean` (`LiebRepulsiveBalancedGround.lean`) by also fixing the total number `N̂`.
* `numberSpinZCasimirSectorEuclidean N L m₀ c` — the Casimir-refined sector `K_c = K ⊓ ker(Ŝ² − c)`.
  `K_c` is defined purely from the fixed charges `N̂`, `Ŝ³`, `Ŝ²`; it carries no dependence on any
  particular Hamiltonian of the homotopy family `H_s` (spin-orbit-coupling parameter `s`,
  PR-4/PR-5) used later in the arc.
* **Proposition 1** (invariance): any Hamiltonian `H` commuting with `N̂`, `Ŝ³` (and, for `K_c`,
  also `Ŝ²`) preserves `K` and `K_c`
  (`numberSpinZSectorEuclidean_mem_of_commute`,
  `numberSpinZCasimirSectorEuclidean_mem_of_commute`).
* **Proposition 2** (unique strict minimality): if `H` is Hermitian, commutes with `N̂`, `Ŝ³`, `Ŝ²`,
  and has a *unique* normalized ground state on `K`, then some occupied Casimir sector `K_c`
  (`K_c ≠ ⊥`) attains the ground energy, and it is the only occupied one that does — every other
  occupied sector is strictly higher (`exists_unique_casimir_sector_strict_min`).

This is a **thin wrapper**: no new mathematical framework is introduced. `K`/`K_c` are plain
`Module.End.eigenspace` intersections (as `spinZSectorEuclidean` already is), invariance is the
standard "commuting operators preserve each other's eigenspaces" fact, and the strict-minimality
argument is the elementary observation that a commuting operator acts by a scalar on a
one-dimensional invariant subspace, combined with the variational reachability API of
`minEnergyOn` (`MinEnergyOnSubspace.lean`).

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §10.2.2, pp. 350–353.
-/

namespace LatticeSystem.Fermion

open Matrix Module Module.End LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

/-! ## The joint number/spin-`z` sector `K` and its Casimir refinement `K_c` -/

/-- The **joint number/spin-`z` sector** `K = {N̂ = L} ⊓ {Ŝ³ = m₀}`: the subspace of
`EuclideanSpace` configurations that are simultaneously `N̂`-eigenvectors at eigenvalue `L` and
`Ŝ³`-eigenvectors at eigenvalue `m₀`. Generalizes `spinZSectorEuclidean`
(`LiebRepulsiveBalancedGround.lean`) by additionally fixing the total electron number. -/
noncomputable def numberSpinZSectorEuclidean (N : ℕ) (L m₀ : ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :=
  Module.End.eigenspace (Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1))) L ⊓
    spinZSectorEuclidean N m₀

/-- The **Casimir-refined sector** `K_c = K ⊓ ker(Ŝ² − c)`: the total-spin-Casimir eigenspace at
eigenvalue `c`, intersected with the joint number/spin-`z` sector `K`. -/
noncomputable def numberSpinZCasimirSectorEuclidean (N : ℕ) (L m₀ c : ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)) :=
  numberSpinZSectorEuclidean N L m₀ ⊓
    Module.End.eigenspace (Matrix.toEuclideanLin (fermionTotalSpinSquared N)) c

/-! ## Proposition 1: invariance of `K` and `K_c` -/

/-- If `A` commutes with `B` then `A` maps every `B`-eigenspace of `EuclideanSpace ℂ n` into
itself. `EuclideanSpace` counterpart of `mulVec_mem_eigenspace_of_commute`
(`LiebAttractiveFullSectorUnique.lean`). -/
private theorem toEuclideanLin_mem_eigenspace_of_commute {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (hAB : Commute A B) {e : ℂ} {v : EuclideanSpace ℂ n}
    (hv : v ∈ Module.End.eigenspace (Matrix.toEuclideanLin B) e) :
    Matrix.toEuclideanLin A v ∈ Module.End.eigenspace (Matrix.toEuclideanLin B) e := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have hv' : B.mulVec (WithLp.ofLp v) = e • WithLp.ofLp v := by
    have h := congrArg WithLp.ofLp hv
    simpa using h
  apply WithLp.ofLp_injective (p := 2) (V := n → ℂ)
  change B.mulVec (A.mulVec (WithLp.ofLp v)) = e • A.mulVec (WithLp.ofLp v)
  rw [Matrix.mulVec_mulVec, ← hAB.eq, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_smul]

/-- **Proposition 1a** (invariance of `K`): any Hamiltonian `H` commuting with the total number
`N̂` and the spin-`z` charge `Ŝ³` preserves the joint sector `K`. -/
theorem numberSpinZSectorEuclidean_mem_of_commute {N : ℕ} {H : ManyBodyOp (Fin (2 * N + 2))}
    (hHN : Commute H (fermionTotalNumber (2 * N + 1))) (hHS3 : Commute H (fermionTotalSpinZ N))
    {L m₀ : ℂ} {v : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hv : v ∈ numberSpinZSectorEuclidean N L m₀) :
    Matrix.toEuclideanLin H v ∈ numberSpinZSectorEuclidean N L m₀ := by
  rw [numberSpinZSectorEuclidean, Submodule.mem_inf] at hv ⊢
  obtain ⟨hN, hS3⟩ := hv
  rw [spinZSectorEuclidean] at hS3 ⊢
  exact ⟨toEuclideanLin_mem_eigenspace_of_commute hHN hN,
    toEuclideanLin_mem_eigenspace_of_commute hHS3 hS3⟩

/-- **Proposition 1b** (invariance of `K_c`): any Hamiltonian `H` commuting with `N̂`, `Ŝ³`, and
the total-spin Casimir `Ŝ²` preserves the sector `K_c`, for every eigenvalue `c` of `Ŝ²`. This is
what makes `K_c` a legitimate energy-restriction target for `minEnergyOn` along the whole homotopy
family `H_s` of the later arc PRs (PR-4/PR-5), given `[Ŝ², H_s] = 0`. -/
theorem numberSpinZCasimirSectorEuclidean_mem_of_commute {N : ℕ} {H : ManyBodyOp (Fin (2 * N + 2))}
    (hHN : Commute H (fermionTotalNumber (2 * N + 1))) (hHS3 : Commute H (fermionTotalSpinZ N))
    (hHS2 : Commute H (fermionTotalSpinSquared N))
    {L m₀ c : ℂ} {v : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hv : v ∈ numberSpinZCasimirSectorEuclidean N L m₀ c) :
    Matrix.toEuclideanLin H v ∈ numberSpinZCasimirSectorEuclidean N L m₀ c := by
  rw [numberSpinZCasimirSectorEuclidean, Submodule.mem_inf] at hv ⊢
  exact ⟨numberSpinZSectorEuclidean_mem_of_commute hHN hHS3 hv.1,
    toEuclideanLin_mem_eigenspace_of_commute hHS2 hv.2⟩

/-! ## Proposition 2: unique strict Casimir-sector minimality -/

/-- **Proposition 2** (unique strict Casimir-sector minimality): if `H` is Hermitian, commutes with
`N̂`, `Ŝ³`, `Ŝ²`, and has a *unique* normalized ground state `φ` on the joint sector `K`, then there
is an *occupied* Casimir eigenvalue `c` (`K_c ≠ ⊥`) whose sector-restricted minimum energy
`minEnergyOn K_c H` attains the ground energy `E`, and it is unique among occupied sectors: every
other occupied Casimir sector `K_{c'}` (`c' ≠ c`, `K_{c'} ≠ ⊥`) has strictly higher minimum energy.

The side condition `K_{c'} ≠ ⊥` is the standing convention of `minEnergyOn`
(`MinEnergyOnSubspace.lean`): the zero subspace has no unit vector, so `minEnergyOn ⊥ H = sInf ∅`
is a junk value unrelated to `H`, and all but finitely many `c' : ℂ` index such an empty sector.

Proof idea: `Ŝ²` commutes with `H` and preserves the (one-dimensional, by uniqueness) `E`-eigenspace
of `H` on `K`, hence acts there by a scalar `c`; `φ` is therefore already an `Ŝ²`-eigenvector with
eigenvalue `c`, giving `φ ∈ K_c` and (via the reachability sharpness of `minEnergyOn`)
`minEnergyOn K_c H = E`. For `c' ≠ c`, any putative energy-`E` witness on `K_{c'}` would, by
reachability, be an `E`-eigenvector of `H` on `K`, hence a scalar multiple of `φ` by uniqueness —
forcing `c' = c`, a contradiction; so `minEnergyOn K_{c'} H` is strictly above `E`. -/
theorem exists_unique_casimir_sector_strict_min {N : ℕ} {H : ManyBodyOp (Fin (2 * N + 2))}
    (hH : H.IsHermitian)
    (hHN : Commute H (fermionTotalNumber (2 * N + 1))) (hHS3 : Commute H (fermionTotalSpinZ N))
    (hHS2 : Commute H (fermionTotalSpinSquared N))
    {L m₀ : ℂ} {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (numberSpinZSectorEuclidean N L m₀) H E φ) :
    ∃ c : ℂ, numberSpinZCasimirSectorEuclidean N L m₀ c ≠ ⊥ ∧
      minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c) H = E ∧
      ∀ c' : ℂ, c' ≠ c → numberSpinZCasimirSectorEuclidean N L m₀ c' ≠ ⊥ →
        E < minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ c') H := by
  obtain ⟨hφK, hφnorm, hφeig, hground, huniq⟩ := hGS
  have hφne : φ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hφnorm
    exact zero_ne_one hφnorm
  have hInv : ∀ d : ℂ, ∀ v ∈ numberSpinZCasimirSectorEuclidean N L m₀ d,
      Matrix.toEuclideanLin H v ∈ numberSpinZCasimirSectorEuclidean N L m₀ d :=
    fun _ _ hv => numberSpinZCasimirSectorEuclidean_mem_of_commute hHN hHS3 hHS2 hv
  have hsub : ∀ d : ℂ, numberSpinZCasimirSectorEuclidean N L m₀ d
      ≤ numberSpinZSectorEuclidean N L m₀ := by
    intro d
    rw [numberSpinZCasimirSectorEuclidean]
    exact inf_le_left
  have hEle : ∀ d : ℂ, numberSpinZCasimirSectorEuclidean N L m₀ d ≠ ⊥ →
      E ≤ minEnergyOn (numberSpinZCasimirSectorEuclidean N L m₀ d) H := by
    intro d hd
    obtain ⟨⟨ψ, hψmem, hψne, hψeig⟩, -⟩ := minEnergyOn_isGroundEigenvalueOn hH (hInv d) hd
    exact hground.2 _ ⟨ψ, hsub d hψmem, hψne, hψeig⟩
  have hS2mem : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ
      ∈ numberSpinZSectorEuclidean N L m₀ :=
    numberSpinZSectorEuclidean_mem_of_commute
      (fermionTotalSpinSquared_commute_fermionTotalNumber N)
      (fermionTotalSpinSquared_commute_fermionTotalSpinZ N) hφK
  have hS2eig : Matrix.toEuclideanLin H (Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ)
      = (E : ℂ) • Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ :=
    Module.End.mem_eigenspace_iff.mp (toEuclideanLin_mem_eigenspace_of_commute hHS2.symm
      (Module.End.mem_eigenspace_iff.mpr hφeig))
  obtain ⟨c, hc⟩ := huniq _ hS2mem hS2eig
  have hφKc : φ ∈ numberSpinZCasimirSectorEuclidean N L m₀ c := by
    rw [numberSpinZCasimirSectorEuclidean, Submodule.mem_inf]
    exact ⟨hφK, Module.End.mem_eigenspace_iff.mpr hc⟩
  have hKcne : numberSpinZCasimirSectorEuclidean N L m₀ c ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hφKc
    exact hφne hφKc
  refine ⟨c, hKcne, le_antisymm ?_ (hEle c hKcne), ?_⟩
  · exact (minEnergyOn_isGroundEigenvalueOn hH (hInv c) hKcne).2 E ⟨φ, hφKc, hφne, hφeig⟩
  intro c' hcc' hc'ne
  refine lt_of_le_of_ne (hEle c' hc'ne) fun heq => ?_
  obtain ⟨⟨ψ, hψmem, hψne, hψeig⟩, -⟩ := minEnergyOn_isGroundEigenvalueOn hH (hInv c') hc'ne
  rw [← heq] at hψeig
  have hψS2 : Matrix.toEuclideanLin (fermionTotalSpinSquared N) ψ = c' • ψ := by
    rw [numberSpinZCasimirSectorEuclidean, Submodule.mem_inf] at hψmem
    exact Module.End.mem_eigenspace_iff.mp hψmem.2
  obtain ⟨a, ha⟩ := huniq ψ (hsub c' hψmem) hψeig
  have hane : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at ha
    exact hψne ha
  rw [ha, map_smul, hc, smul_smul, smul_smul] at hψS2
  have hzero : (a * c - c' * a) • φ = 0 := by rw [sub_smul, hψS2, sub_self]
  rcases smul_eq_zero.mp hzero with h | h
  · exact hcc' (mul_left_cancel₀ hane (by linear_combination -h))
  · exact hφne h

end LatticeSystem.Fermion
