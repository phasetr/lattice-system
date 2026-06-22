import LatticeSystem.Fermion.JordanWigner.Hubbard.WeakNagaokaTheoremCore

/-!
# Tasaki Theorem 11.5 (weak version of Nagaoka's theorem)

This file builds toward Tasaki Theorem 11.5: for a Hubbard model with
`t_{x,y} = t_{y,x} ≥ 0` (and `t_{i,i} = 0`), `N = |Λ| − 1` electrons, `U ↑ ∞`,
among the ground states of the effective Hamiltonian there are at least
`(2 S_max + 1)` states with total spin `S_tot = S_max = N/2`.

The first ingredient (this commit) is that the *ferromagnetic hole state*
`|Φ_{x,(↑)}⟩` — the one-hole state with every occupied site spin-up — lies in
the maximal-spin sector: `(Ŝ_tot)² |Φ_{x,(↑)}⟩ = S_max(S_max+1) |Φ_{x,(↑)}⟩`
with `S_max = N/2`. Indeed `Ŝ^+_tot` annihilates it (no down electrons to
raise) and `Ŝ^z_tot` acts with eigenvalue `N/2` (the `N` up electrons).

Tracked in Issue #4130. Reference: Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, 1st edition, §11.2.1, Theorem 11.5, pp. 382-385.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum

/-! ## Raising-after-lowering via the Casimir -/

/-- **`Ŝ^+_tot Ŝ^-_tot = (Ŝ_tot)² − Ŝ^z_tot (Ŝ^z_tot − 1)`**: the
raising-after-lowering product expressed through the Casimir. On a state with
Casimir eigenvalue `S(S+1)` and `Ŝ^z` eigenvalue `m`, this gives
`Ŝ^+_tot Ŝ^-_tot = S(S+1) − m(m−1)`, which is the squared norm of the lowered
state and the engine behind the spin-multiplet's nonvanishing. Derived from the
Casimir definition `(Ŝ_tot)² = Ŝ^-_tot Ŝ^+_tot + Ŝ^z_tot (Ŝ^z_tot + 1)` and the
ladder commutator `Ŝ^+_tot Ŝ^-_tot = Ŝ^-_tot Ŝ^+_tot + 2 Ŝ^z_tot`. -/
theorem fermionTotalSpinPlus_mul_fermionTotalSpinMinus (N : ℕ) :
    fermionTotalSpinPlus N * fermionTotalSpinMinus N =
      fermionTotalSpinSquared N -
        fermionTotalSpinZ N * (fermionTotalSpinZ N - 1) := by
  have hPM : fermionTotalSpinPlus N * fermionTotalSpinMinus N =
      fermionTotalSpinMinus N * fermionTotalSpinPlus N +
        (2 : ℂ) • fermionTotalSpinZ N := by
    have h := fermionTotalSpinPlus_commutator_fermionTotalSpinMinus N
    rwa [sub_eq_iff_eq_add'] at h
  rw [hPM]
  unfold fermionTotalSpinSquared
  rw [two_smul]
  noncomm_ring

/-! ## The spin-lowering multiplet is nonzero and linearly independent -/

/-- **Abstract Casimir tower.** If `(Ŝ_tot)² v = λ v` then
`(Ŝ_tot)² (Ŝ^-_tot)^k v = λ (Ŝ^-_tot)^k v`, since `[(Ŝ_tot)², Ŝ^-_tot] = 0`. The
whole spin-lowering tower stays in a single total-spin sector. -/
theorem fermionTotalSpinSquared_mulVec_spinMinusPow (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (lam : ℂ) (k : ℕ)
    (hcas : (fermionTotalSpinSquared N).mulVec v = lam • v) :
    (fermionTotalSpinSquared N).mulVec (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      lam • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  rw [Matrix.mulVec_mulVec,
    (Commute.pow_right (fermionTotalSpinSquared_commute_fermionTotalSpinMinus N) k).eq,
    ← Matrix.mulVec_mulVec, hcas, Matrix.mulVec_smul]

/-- **Abstract `Ŝ^+ Ŝ^-` ladder eigenvalue.** For a maximal-spin highest state
(`Ŝ^z v = (N/2) v`, `(Ŝ_tot)² v = (N/2)(N/2+1) v`),
`Ŝ^+_tot Ŝ^-_tot (Ŝ^-_tot)^k v = ((N/2)(N/2+1) − (N/2−k)(N/2−k−1)) (Ŝ^-_tot)^k v`;
the eigenvalue equals `(k+1)(N−k)`. -/
theorem fermionTotalSpinPlusMinus_mulVec_spinMinusPow (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (k : ℕ)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((N : ℂ) / 2) • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) • v) :
    (fermionTotalSpinPlus N * fermionTotalSpinMinus N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1) -
          ((N : ℂ) / 2 - k) * ((N : ℂ) / 2 - k - 1)) •
        (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  rw [fermionTotalSpinPlus_mul_fermionTotalSpinMinus, Matrix.sub_mulVec,
    fermionTotalSpinSquared_mulVec_spinMinusPow N v _ k hcas,
    ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    fermionTotalSpinZ_mulVec_spinMinusPow N v k hsz,
    Matrix.mulVec_sub, Matrix.mulVec_smul,
    fermionTotalSpinZ_mulVec_spinMinusPow N v k hsz]
  module

/-- **Abstract multiplet nonvanishing.** A nonzero maximal-spin highest state has
`(Ŝ^-_tot)^k v ≠ 0` for all `k ≤ N`. Purely algebraic, no inner product: if it
vanished then `Ŝ^+_tot (Ŝ^-_tot)^{k+1} v = (k+1)(N−k) (Ŝ^-_tot)^k v` would also
vanish, but `(k+1)(N−k) ≠ 0` for `k < N` and `(Ŝ^-_tot)^k v ≠ 0` by induction. -/
theorem spinMinusPow_ne_zero (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hv : v ≠ 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((N : ℂ) / 2) • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) • v) :
    ∀ k : ℕ, k ≤ N → ((fermionTotalSpinMinus N) ^ k).mulVec v ≠ 0 := by
  intro k
  induction k with
  | zero =>
    intro _ h
    rw [pow_zero, Matrix.one_mulVec] at h
    exact hv h
  | succ k ih =>
    intro hk hzero
    have hk' : k ≤ N := Nat.le_of_succ_le hk
    have hklt : k < N := hk
    have hψk := ih hk'
    have hc : (N : ℂ) / 2 * ((N : ℂ) / 2 + 1) -
        ((N : ℂ) / 2 - k) * ((N : ℂ) / 2 - k - 1) ≠ 0 := by
      have heq : (N : ℂ) / 2 * ((N : ℂ) / 2 + 1) -
          ((N : ℂ) / 2 - k) * ((N : ℂ) / 2 - k - 1) = ((k : ℂ) + 1) * ((N : ℂ) - k) := by
        ring
      rw [heq]
      refine mul_ne_zero (Nat.cast_add_one_ne_zero k) ?_
      rw [sub_ne_zero]
      exact_mod_cast (Nat.ne_of_lt hklt).symm
    have harg : (fermionTotalSpinMinus N).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec v) = 0 := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']; exact hzero
    have key := fermionTotalSpinPlusMinus_mulVec_spinMinusPow N v k hsz hcas
    rw [← Matrix.mulVec_mulVec, harg, Matrix.mulVec_zero] at key
    rcases smul_eq_zero.mp key.symm with h | h
    · exact hc h
    · exact hψk h

/-- **Abstract multiplet linear independence.** The `N + 1` states `(Ŝ^-_tot)^k v`
(`k = 0, …, N`) of a nonzero maximal-spin highest state are linearly independent:
nonzero `Ŝ^z_tot`-eigenvectors with the pairwise-distinct eigenvalues `N/2 − k`. -/
theorem spinMinusPow_linearIndependent (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (hv : v ≠ 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((N : ℂ) / 2) • v)
    (hcas : (fermionTotalSpinSquared N).mulVec v =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) • v) :
    LinearIndependent ℂ (fun k : Fin (N + 1) =>
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) := by
  apply Module.End.eigenvectors_linearIndependent' (fermionTotalSpinZ N).mulVecLin
    (fun k : Fin (N + 1) => (N : ℂ) / 2 - (k : ℕ))
  · intro a b hab
    rw [sub_right_inj] at hab
    have h2 : (a : ℕ) = (b : ℕ) := by exact_mod_cast hab
    exact Fin.ext h2
  · intro k
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact fermionTotalSpinZ_mulVec_spinMinusPow N v (k : ℕ) hsz
    · exact spinMinusPow_ne_zero N v hv hsz hcas (k : ℕ) (Nat.le_of_lt_succ k.isLt)

/-! ## Energy degeneracy of the whole tower -/

/-- **Abstract energy tower.** If `v` is an `Ĥ_eff`-eigenvector at energy `E`,
so is every `(Ŝ^-_tot)^k v` (degeneracy, via `[Ĥ_eff, Ŝ^-_tot] = 0`). -/
theorem hubbardEffectiveHamiltonian_mulVec_spinMinusPow (N : ℕ)
    (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℂ)
    (hE : (hubbardEffectiveHamiltonian N t U).mulVec v = E • v) (k : ℕ) :
    (hubbardEffectiveHamiltonian N t U).mulVec
        (((fermionTotalSpinMinus N) ^ k).mulVec v) =
      E • (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
  induction k with
  | zero => rw [pow_zero, Matrix.one_mulVec]; exact hE
  | succ k ih =>
    have hexp : ((fermionTotalSpinMinus N) ^ (k + 1)).mulVec v =
        (fermionTotalSpinMinus N).mulVec
          (((fermionTotalSpinMinus N) ^ k).mulVec v) := by
      rw [pow_succ', Matrix.mulVec_mulVec]
    rw [hexp]
    exact hubbardEffectiveHamiltonian_mulVec_spinMinus N t U hJ hU
      (((fermionTotalSpinMinus N) ^ k).mulVec v) E ih

/-! ## Weak Nagaoka spin multiplet (Tasaki Theorem 11.5 core) -/

/-- A maximal-`Ŝ^z` highest-weight state is automatically maximal-spin: if
`Ŝ^+_tot v = 0` and `Ŝ^z_tot v = (N/2) v` then `(Ŝ_tot)² v = (N/2)(N/2+1) v`,
because `(Ŝ_tot)² = Ŝ^-_tot Ŝ^+_tot + Ŝ^z_tot(Ŝ^z_tot + 1)` and the all-up
sector is entirely `S_tot = S_max`. -/
theorem fermionTotalSpinSquared_mulVec_of_isTop (N : ℕ)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (htop : (fermionTotalSpinPlus N).mulVec v = 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((N : ℂ) / 2) • v) :
    (fermionTotalSpinSquared N).mulVec v =
      ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) • v := by
  unfold fermionTotalSpinSquared
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, htop, Matrix.mulVec_zero, zero_add,
    ← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, hsz, Matrix.mulVec_add,
    Matrix.mulVec_smul, hsz, smul_smul, ← add_smul]
  congr 1
  ring

/-- **Weak Nagaoka spin multiplet (core of Tasaki Theorem 11.5).** Let `v` be a
nonzero `Ĥ_eff`-eigenvector at energy `E` that is a maximal-`Ŝ^z` highest-weight
state (`Ŝ^+_tot v = 0`, `Ŝ^z_tot v = (N/2) v`) — e.g. a ferromagnetic ground
state. Then the `(2 S_max + 1) = N + 1` states `(Ŝ^-_tot)^k v` (`k = 0, …, N`):
(1) are linearly independent; (2) are all `Ĥ_eff`-eigenvectors at the same energy
`E` (degenerate with `v`); (3) all lie in the maximal-spin sector
`S_tot = S_max = N/2`. So a ferromagnetic ground state generates
`≥ (2 S_max + 1)` degenerate ground states with `S_tot = S_max` — the weak
Nagaoka conclusion (Tasaki §11.2.1, eq. (11.2.9)). What remains for the full
theorem is the existence of such a ground state `v` (the Perron–Frobenius
ferromagnetic ground state of the one-hole sector). -/
theorem weakNagaoka_spinMultiplet (N : ℕ) (t : Fin (N + 1) → Fin (N + 1) → ℂ) (U : ℂ)
    (hJ : ∀ i j, star (t i j) = t j i) (hU : star U = U)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ) (E : ℂ)
    (hE : (hubbardEffectiveHamiltonian N t U).mulVec v = E • v)
    (htop : (fermionTotalSpinPlus N).mulVec v = 0)
    (hsz : (fermionTotalSpinZ N).mulVec v = ((N : ℂ) / 2) • v)
    (hv : v ≠ 0) :
    LinearIndependent ℂ (fun k : Fin (N + 1) =>
        ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) ∧
      (∀ k : Fin (N + 1), (hubbardEffectiveHamiltonian N t U).mulVec
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) =
        E • (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v)) ∧
      (∀ k : Fin (N + 1), (fermionTotalSpinSquared N).mulVec
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v) =
        ((N : ℂ) / 2 * ((N : ℂ) / 2 + 1)) •
          (((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec v)) := by
  have hcas := fermionTotalSpinSquared_mulVec_of_isTop N v htop hsz
  refine ⟨spinMinusPow_linearIndependent N v hv hsz hcas, fun k => ?_, fun k => ?_⟩
  · exact hubbardEffectiveHamiltonian_mulVec_spinMinusPow N t U hJ hU v E hE (k : ℕ)
  · exact fermionTotalSpinSquared_mulVec_spinMinusPow N v _ (k : ℕ) hcas

/-! ## The ferromagnetic hole state is a highest-weight maximal-spin state -/

/-- The localized ferromagnetic hole state `|Φ_{x,(↑)}⟩` is a nonzero
highest-weight maximal-spin state: `Ŝ^+_tot` annihilates it, `Ŝ^z_tot` acts with
`N/2`, and `(Ŝ_tot)²` with `S_max(S_max+1)`. Hence its `N + 1` spin-lowering
descendants are linearly independent (instance of
`spinMinusPow_linearIndependent`). It is *not* in general an `Ĥ_eff`-eigenvector
(the hole is localized), so the full degeneracy statement
`weakNagaoka_spinMultiplet` applies to the Perron–Frobenius ground state rather
than to this localized state. -/
theorem spinMinusPow_ferroHole_linearIndependent (N : ℕ) (x : Fin (N + 1)) :
    LinearIndependent ℂ (fun k : Fin (N + 1) =>
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec (basisVec (ferroHoleConfig N x))) := by
  refine spinMinusPow_linearIndependent N (basisVec (ferroHoleConfig N x)) ?_
    (fermionTotalSpinZ_mulVec_ferroHole N x) (fermionTotalSpinSquared_mulVec_ferroHole N x)
  intro h
  have h2 := congrFun h (ferroHoleConfig N x)
  rw [Pi.zero_apply, basisVec_self] at h2
  exact one_ne_zero h2

end LatticeSystem.Fermion
