import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveMultipletCompanion
import LatticeSystem.Fermion.JordanWigner.Hubbard.SpinLoweringTowerGeneral
import LatticeSystem.Fermion.JordanWigner.Hubbard.TJRaisingTower

/-!
# §10.2.3 (Theorem 10.6): the ground multiplet is a single `SU(2)` lowering tower

Theorem 10.4 says that the `(N+1)`-electron ground submodule

  `G = hubbardGroundSubmoduleAtElectronNumber (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N+1)`

of Lieb's half-filled repulsive Hubbard model carries the single total spin
`S₀ = ||A| − |B||/2` (`liebRepulsiveSpinCasimir`) and has dimension `2S₀ + 1 = L + 1`
(`liebRepulsiveGroundMultiplicity`), where `L := sublatticeImbalance A`.  This module turns those
two numbers into the concrete `SU(2)` multiplet structure that Tasaki's ferrimagnetic bound
(10.2.17) is evaluated on: `G` is spanned by the lowering tower `(Ŝ⁻_tot)^k w` (`k = 0, …, L`) of a
single highest-weight ground vector `w`, whose members are mutually orthogonal and stay orthogonal
after applying any `Ŝ³_tot`-commuting observable.

Theorem 10.4's conclusions enter as hypotheses (`hcas`, `hrank`, `hne`), so nothing here re-derives
the half-filling apparatus.  The chain is:

* `liebRepulsive_ground_spinZ_abs_le` — every `Ŝ³_tot`-eigenvector of `G` has weight in
  `[−L/2, L/2]`, the generic band `fermionTotalSpin_abs_weight_le` at `J = L/2`;
* `liebRepulsive_ground_exists_topWeight` — raising a `Ŝ³_tot`-eigenvector seed of `G` terminates
  (the band forbids weights above `L/2`), producing a highest-weight vector of `G` whose weight is
  pinned to `L/2` because the band excludes the second root `−(L/2 + 1)` of the Casimir equation;
* `liebRepulsive_ground_spinMinusPow_mem` — lowering stays inside `G`;
* `liebRepulsive_ground_tower_ne_zero`, `liebRepulsive_ground_tower_linearIndependent` — the `L + 1`
  lowered iterates are nonzero and independent, by the general highest-weight tower lemmas of
  `SpinLoweringTowerGeneral.lean`;
* `liebRepulsive_ground_eq_span_tower` — dimension counting against `hrank` upgrades the inclusion
  `span ≤ G` to equality;
* `liebRepulsive_tower_crossTerm_eq_zero` — distinct tower members carry distinct real `Ŝ³_tot`
  weights, so all cross terms of a weight-preserving observable vanish (instantiated downstream at
  `O = 1` and at the squared staggered order parameter `fermionStaggeredCasimirOp`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17).
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math

/-- Theorem 10.4's Casimir eigenvalue rewritten as the real cast `J (J + 1)` at `J = L/2`, the
shape consumed by the generic weight band `fermionTotalSpin_abs_weight_le` and by the `N = 0`
branch of the ferrimagnetic bound. -/
theorem liebRepulsiveSpinCasimir_eq_ofReal {N : ℕ} (A : Finset (Fin (N + 1))) :
    liebRepulsiveSpinCasimir A =
      ((((sublatticeImbalance A : ℝ) / 2) * ((sublatticeImbalance A : ℝ) / 2 + 1) : ℝ) : ℂ) := by
  rw [liebRepulsiveSpinCasimir]
  push_cast
  ring

/-! ## The `Ŝ³_tot` weight band on the ground submodule -/

/-- **The ground submodule's `Ŝ³_tot` weight band.**  Under Theorem 10.4's Casimir conclusion
`hcas`, every nonzero `Ŝ³_tot`-eigenvector `w ∈ G` at a real weight `m` satisfies
`|m| ≤ ||A| − |B||/2`: the generic bound `fermionTotalSpin_abs_weight_le` instantiated at
`J = sublatticeImbalance A / 2`. -/
theorem liebRepulsive_ground_spinZ_abs_le (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hw0 : w ≠ 0) {m : ℝ}
    (h3 : (fermionTotalSpinZ N).mulVec w = (m : ℂ) • w) :
    |m| ≤ (sublatticeImbalance A : ℝ) / 2 := by
  refine fermionTotalSpin_abs_weight_le N hw0 (by positivity) ?_ h3
  rw [hcas w hwG, liebRepulsiveSpinCasimir_eq_ofReal]

/-! ## Existence of a highest-weight ground vector -/

/-- **A highest-weight vector inside the ground submodule.**  If `G` is nonzero, it contains a
nonzero `w` with `Ŝ⁺_tot w = 0` and `Ŝ³_tot w = (L/2) w`, `L := sublatticeImbalance A`.

Route: `G` is `Ŝ³_tot`-invariant, so it has a `Ŝ³_tot`-eigenvector seed `v` at a real weight `m`;
`Ŝ⁺_tot` also preserves `G`, and each raising step increases the weight by one, so the weight band
`liebRepulsive_ground_spinZ_abs_le` forces `(Ŝ⁺_tot)^{L+1} v = 0`.  The last nonvanishing iterate
`w := (Ŝ⁺_tot)^{k₀−1} v` (`k₀` the first vanishing exponent) is a highest-weight vector, and its
weight `m + (k₀−1)` solves `μ(μ+1) = (L/2)(L/2+1)`; of the two roots `L/2` and `−(L/2+1)` the band
leaves only `L/2`. -/
theorem liebRepulsive_ground_exists_topWeight (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    (hne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥) :
    ∃ w : (Fin (2 * N + 2) → Fin 2) → ℂ, w ≠ 0 ∧
      w ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ∧
      (fermionTotalSpinPlus N).mulVec w = 0 ∧
      (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w := by
  classical
  -- A `Ŝ³_tot`-eigenvector seed of `G`, at a real weight `m`.
  have hZinv : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≤
    (hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1)).comap
        (fermionTotalSpinZ N).mulVecLin :=
    liebRepulsive_groundSubmodule_le_comap_of_commute N T U E₀ (fermionTotalSpinZ N)
      (fermionTotalSpinZ_commute_symmetricRepulsiveHubbardHamiltonian N T U)
      (fermionTotalSpinZ_commute_fermionTotalNumber N)
  obtain ⟨μ, v, hvG, hv0, hvμ⟩ :=
    exists_eigenvector_in_invariant_submodule (fermionTotalSpinZ N).mulVecLin _ hZinv hne
  rw [Matrix.mulVecLin_apply] at hvμ
  obtain ⟨m, hm⟩ :=
    isHermitian_mulVec_eigenvalue_eq_ofReal (fermionTotalSpinZ_isHermitian N) hv0 hvμ
  have hv3 : (fermionTotalSpinZ N).mulVec v = (m : ℂ) • v := by rw [hvμ, hm]
  -- Raising preserves `G` and raises the weight by one.
  have hraise : ∀ k : ℕ, ((fermionTotalSpinPlus N) ^ k).mulVec v ∈
      hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) := by
    intro k
    have h := liebRepulsive_groundSubmodule_le_comap_of_commute N T U E₀
      ((fermionTotalSpinPlus N) ^ k)
      ((fermionTotalSpinPlus_commute_symmetricRepulsiveHubbardHamiltonian N T U).pow_left k)
      ((fermionTotalSpinPlus_commute_fermionTotalNumber N).pow_left k) hvG
    rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h
  have hweight : ∀ k : ℕ,
      (fermionTotalSpinZ N).mulVec (((fermionTotalSpinPlus N) ^ k).mulVec v)
        = ((m + k : ℝ) : ℂ) • (((fermionTotalSpinPlus N) ^ k).mulVec v) := by
    intro k
    rw [show (((m + k : ℝ)) : ℂ) = (m : ℂ) + (k : ℕ) by push_cast; ring]
    exact fermionTotalSpinZ_mulVec_spinPlusPow N v (m : ℂ) k hv3
  have hband : ∀ k : ℕ, ((fermionTotalSpinPlus N) ^ k).mulVec v ≠ 0 →
      |m + k| ≤ (sublatticeImbalance A : ℝ) / 2 := fun k hk =>
    liebRepulsive_ground_spinZ_abs_le N A T U E₀ hcas (hraise k) hk (hweight k)
  -- The raising tower terminates: weight `m + (L+1)` would break the band.
  have hterm : ∃ k : ℕ, ((fermionTotalSpinPlus N) ^ k).mulVec v = 0 := by
    by_contra hall
    have hall' : ∀ k : ℕ, ((fermionTotalSpinPlus N) ^ k).mulVec v ≠ 0 :=
      fun k hk => hall ⟨k, hk⟩
    have h0 := hband 0 (hall' 0)
    have h1 := hband (sublatticeImbalance A + 1) (hall' _)
    rw [abs_le] at h0 h1
    push_cast at h0 h1
    linarith [h0.1, h1.2]
  have hk0 := Nat.find_spec hterm
  have hk0ne : Nat.find hterm ≠ 0 := by
    intro h
    rw [h, pow_zero, Matrix.one_mulVec] at hk0
    exact hv0 hk0
  obtain ⟨j, hj⟩ : ∃ j : ℕ, Nat.find hterm = j + 1 :=
    ⟨Nat.find hterm - 1, by omega⟩
  have hwne : ((fermionTotalSpinPlus N) ^ j).mulVec v ≠ 0 := Nat.find_min hterm (by omega)
  have hwG : ((fermionTotalSpinPlus N) ^ j).mulVec v ∈
      hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) := hraise j
  have htop : (fermionTotalSpinPlus N).mulVec (((fermionTotalSpinPlus N) ^ j).mulVec v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← pow_succ', ← hj]
    exact hk0
  -- The highest weight `m + j` solves `μ(μ+1) = (L/2)(L/2+1)`; the band picks the root `L/2`.
  have hcastop := fermionTotalSpinSquared_mulVec_of_isTop_general N
    (((fermionTotalSpinPlus N) ^ j).mulVec v) ((m + j : ℝ) : ℂ) htop (hweight j)
  have hsub : (((m + j : ℝ) : ℂ) * (((m + j : ℝ) : ℂ) + 1) - liebRepulsiveSpinCasimir A) •
      (((fermionTotalSpinPlus N) ^ j).mulVec v) = 0 := by
    rw [sub_smul, ← hcastop, ← hcas _ hwG, sub_self]
  have hscal : ((m + j : ℝ) : ℂ) * (((m + j : ℝ) : ℂ) + 1) = liebRepulsiveSpinCasimir A :=
    sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hwne)
  have hreal : (m + j) * ((m + j) + 1)
      = ((sublatticeImbalance A : ℝ) / 2) * ((sublatticeImbalance A : ℝ) / 2 + 1) := by
    rw [liebRepulsiveSpinCasimir_eq_ofReal] at hscal
    exact_mod_cast hscal
  have hbandw : |m + j| ≤ (sublatticeImbalance A : ℝ) / 2 :=
    liebRepulsive_ground_spinZ_abs_le N A T U E₀ hcas hwG hwne (hweight j)
  rw [abs_le] at hbandw
  have hfac : ((m + j) - (sublatticeImbalance A : ℝ) / 2) *
      ((m + j) + (sublatticeImbalance A : ℝ) / 2 + 1) = 0 := by linear_combination hreal
  have hroot : m + j = (sublatticeImbalance A : ℝ) / 2 := by
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith [hbandw.1]
  refine ⟨((fermionTotalSpinPlus N) ^ j).mulVec v, hwne, hwG, htop, ?_⟩
  rw [hweight j, show (((m + j : ℝ)) : ℂ) = ((sublatticeImbalance A : ℂ) / 2) by
    rw [hroot]; push_cast; ring]

/-! ## The lowering tower inside the ground submodule -/

/-- **Lowering stays inside the ground submodule.**  `Ŝ⁻_tot` commutes with the symmetric
repulsive Hamiltonian (for a symmetric hopping matrix) and with `N̂`, so each power `(Ŝ⁻_tot)^k`
preserves the intersection of the two eigenspaces that defines `G`. -/
theorem liebRepulsive_ground_spinMinusPow_mem (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1)) :
    ∀ k : ℕ, ((fermionTotalSpinMinus N) ^ k).mulVec w ∈
      hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) := by
  intro k
  have h := liebRepulsive_groundSubmodule_le_comap_of_commute N T U E₀
    ((fermionTotalSpinMinus N) ^ k)
    ((fermionTotalSpinMinus_commute_symmetricRepulsiveHubbardHamiltonian N T hT U).pow_left k)
    ((fermionTotalSpinMinus_commute_fermionTotalNumber N).pow_left k) hwG
  rwa [Submodule.mem_comap, Matrix.mulVecLin_apply] at h

/-- **The tower does not die before step `L`.**  For a nonzero highest-weight ground vector `w`
(`Ŝ³_tot w = (L/2) w`, `L := sublatticeImbalance A`), every lowered iterate `(Ŝ⁻_tot)^k w` with
`k ≤ L` is nonzero — the general tower lemma `spinMinusPow_ne_zero_general` fed with Theorem
10.4's Casimir value. -/
theorem liebRepulsive_ground_tower_ne_zero (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    ∀ k : ℕ, k ≤ sublatticeImbalance A → ((fermionTotalSpinMinus N) ^ k).mulVec w ≠ 0 := by
  refine spinMinusPow_ne_zero_general N (sublatticeImbalance A) w hw0 hz ?_
  rw [hcas w hwG, liebRepulsiveSpinCasimir]

/-- **The `L + 1` tower members are linearly independent.**  They are eigenvectors of `Ŝ³_tot` at
the pairwise distinct weights `L/2 − k`, so `spinMinusPow_linearIndependent_general` applies to the
highest-weight ground vector `w` with Theorem 10.4's Casimir value. -/
theorem liebRepulsive_ground_tower_linearIndependent (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    LinearIndependent ℂ (fun k : Fin (sublatticeImbalance A + 1) =>
      ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec w) := by
  refine spinMinusPow_linearIndependent_general N (sublatticeImbalance A) w hw0 hz ?_
  rw [hcas w hwG, liebRepulsiveSpinCasimir]

/-! ## The ground submodule is exactly the tower span -/

/-- **The ground submodule is the span of the tower.**  The `L + 1` lowered iterates of a nonzero
highest-weight ground vector `w` lie in `G` and are independent, so their span is an
`(L + 1)`-dimensional subspace of `G`; Theorem 10.4's dimension count
`finrank G = liebRepulsiveGroundMultiplicity A = L + 1` forces equality. -/
theorem liebRepulsive_ground_eq_span_tower (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    (hrank : Module.finrank ℂ (hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
      = liebRepulsiveGroundMultiplicity A)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) =
      Submodule.span ℂ (Set.range fun k : Fin (sublatticeImbalance A + 1) =>
        ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec w) := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [Submodule.span_le]
    rintro x ⟨k, rfl⟩
    exact liebRepulsive_ground_spinMinusPow_mem N T hT U E₀ hwG (k : ℕ)
  · rw [finrank_span_eq_card
      (liebRepulsive_ground_tower_linearIndependent N A T U E₀ hcas hw0 hwG hz),
      Fintype.card_fin, hrank, liebRepulsiveGroundMultiplicity]

/-! ## Weight orthogonality of the tower -/

/-- **Cross terms between distinct tower members vanish.**  For any observable `O` commuting with
`Ŝ³_tot` and `j ≠ k`, `⟨(Ŝ⁻_tot)^j w, O (Ŝ⁻_tot)^k w⟩ = 0`: both vectors are `Ŝ³_tot`-eigenvectors
(the second because `O` preserves the weight) at the distinct real weights `L/2 − j` and `L/2 − k`,
`L := sublatticeImbalance A`, and `Ŝ³_tot` is Hermitian
(`Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne`).  The `O = 1` instance is the plain
orthogonality of the tower. -/
theorem liebRepulsive_tower_crossTerm_eq_zero (N : ℕ) (A : Finset (Fin (N + 1)))
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ}
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (O : ManyBodyOp (Fin (2 * N + 2))) (hO : Commute O (fermionTotalSpinZ N))
    {j k : ℕ} (hjk : j ≠ k) :
    star (((fermionTotalSpinMinus N) ^ j).mulVec w) ⬝ᵥ
        (O.mulVec (((fermionTotalSpinMinus N) ^ k).mulVec w)) = 0 := by
  have hstar : ∀ n : ℕ, star ((sublatticeImbalance A : ℂ) / 2 - (n : ℕ))
      = (sublatticeImbalance A : ℂ) / 2 - (n : ℕ) := fun n => by
    simp only [star_sub, star_div₀, RCLike.star_def, Complex.conj_natCast, map_ofNat]
  have hne : (sublatticeImbalance A : ℂ) / 2 - (j : ℕ)
      ≠ (sublatticeImbalance A : ℂ) / 2 - (k : ℕ) := by
    intro h
    have hc : (j : ℂ) = (k : ℂ) := by linear_combination -h
    exact hjk (Nat.cast_injective hc)
  have hjw := fermionTotalSpinZ_mulVec_spinMinusPow_general N w
    ((sublatticeImbalance A : ℂ) / 2) j hz
  have hkw := fermionTotalSpinZ_mulVec_spinMinusPow_general N w
    ((sublatticeImbalance A : ℂ) / 2) k hz
  have hOk : (fermionTotalSpinZ N).mulVec (O.mulVec (((fermionTotalSpinMinus N) ^ k).mulVec w))
      = ((sublatticeImbalance A : ℂ) / 2 - (k : ℕ)) •
        O.mulVec (((fermionTotalSpinMinus N) ^ k).mulVec w) := by
    rw [Matrix.mulVec_mulVec, ← hO.eq, ← Matrix.mulVec_mulVec, hkw, Matrix.mulVec_smul]
  exact Matrix.IsHermitian.dotProduct_eq_zero_of_eigenvalues_ne
    (fermionTotalSpinZ_isHermitian N) (hstar j) (hstar k) hjw hOk hne

end LatticeSystem.Fermion
