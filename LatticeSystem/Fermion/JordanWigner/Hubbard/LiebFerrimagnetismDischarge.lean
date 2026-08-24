import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismCenteredBound
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismLadderRatio
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebFerrimagnetismSU2Invariance
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveHalfFillingDischarge

/-!
# Theorem 10.6 discharge: the ferrimagnetic bound for every ground state

Tasaki's Theorem 10.6 (Shen–Qiu–Tian ferrimagnetism, eq. (10.2.17)) states that **every**
normalized ground state `v` of Lieb's half-filled repulsive Hubbard model satisfies

  `⟨v| (Ô_L)² |v⟩ ≥ S₀²`,   `S₀ = ||A| − |B||/2`,

for the squared staggered order parameter `(Ô_L)² = Σ_{x,y} ε_x ε_y Ŝ_x · Ŝ_y`
(`fermionStaggeredCasimirOp`).  The centered-sector layer
(`LiebFerrimagnetismCenteredBound.lean`) proves the bound on the single tower member
`u = (Ŝ⁻_tot)^{k₀} w` on which Theorem 10.5's correlation signs are available.  This module
removes both restrictions — from that one vector to the whole ground multiplet, and from the
symmetric interaction form to either Hamiltonian of `IsLiebRepulsiveModel` — and lands the
capstone.

The universalization runs in two steps.

* **Tower transport.**  `(Ô_L)²` commutes with `Ŝ⁺_tot`
  (`fermionStaggeredCasimirOp_commute_fermionTotalSpinPlus`), so the ladder-ratio invariance
  `fermionSpinMinus_expectationRatioRe_invariant` makes the real Rayleigh quotient
  `⟨(Ô_L)²⟩.re / ‖·‖²` constant along the lowering tower: `liebFerrimagnetism_tower_ratioRe_eq`.
  Feeding it the centered-sector bound gives `S₀² ≤ ⟨(Ô_L)²⟩.re / ‖w_k‖²` for every `k ≤ L`
  (`liebFerrimagnetism_tower_ratioRe_ge_sq`).
* **Tower expansion.**  The ground submodule is exactly the span of the tower
  (`liebRepulsive_ground_eq_span_tower`), and `(Ô_L)²` commutes with `Ŝ³_tot`
  (`fermionStaggeredCasimirOp_commute_fermionTotalSpinZ`), so all cross terms of an expansion
  `v = Σ_k c_k w_k` vanish (`liebRepulsive_tower_crossTerm_eq_zero`) for `(Ô_L)²` and for `1`
  alike.  Both quadratic forms are therefore diagonal in the tower, and the per-member bound
  averages to `S₀² ≤ ⟨v| (Ô_L)² |v⟩.re`: `liebFerrimagnetism_bound_of_mem_ground`.

Assembling with Theorem 10.4 (which supplies the Casimir value and the multiplet dimension at
its own ground energy, identified with the caller's by two-sided minimality) gives
`liebFerrimagnetism_symmetric`, and splitting `IsLiebRepulsiveModel`'s Hamiltonian disjunction —
the uniform form differs from the symmetric one by the constant energy shift of
`symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform` — gives the capstone
`theorem_10_6_lieb_ferrimagnetism`.  On a single site (`N = 0`) there is no room for the tower
argument; there `(Ô_L)²` is the plain Casimir `(Ŝ_tot)²`
(`fermionStaggeredCasimirOp_zero_eq_totalSpinSquared`), whose ground expectation `S₀(S₀ + 1)`
exceeds `S₀²` outright.

The capstone lives here rather than in `LiebFerrimagnetism.lean`, which defines
`fermionStaggeredCasimirOp` and is imported by every module of the proof: the statement's home
sits strictly upstream of its proof, exactly as for `theorem_10_4_lieb_repulsive_half_filling`
in `LiebRepulsiveHalfFillingDischarge.lean`.

## Main results

* `liebFerrimagnetism_tower_ratioRe_eq` — the real expectation ratio of `(Ô_L)²` is the same on
  every member of the ground multiplet's lowering tower.
* `liebFerrimagnetism_tower_ratioRe_ge_sq` — the centered-sector bound propagates to every tower
  member.
* `liebFerrimagnetism_bound_of_mem_ground` — every normalized vector of the ground submodule
  satisfies the ferrimagnetic bound.
* `liebFerrimagnetism_symmetric` — the bound for the symmetric-form repulsive Hubbard model,
  with Theorem 10.4's conclusions assembled internally.
* `theorem_10_6_lieb_ferrimagnetism` — **Tasaki Theorem 10.6** itself, for either Hamiltonian
  form of `IsLiebRepulsiveModel`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer 2020, §10.2.3, p. 356, eqs. (10.2.16)/(10.2.17); §10.2.2 (Theorems 10.4/10.5),
pp. 350–353; S.-Q. Shen, Z.-M. Qiu, G.-S. Tian, *Phys. Rev. Lett.* **72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix Module LatticeSystem.Quantum LatticeSystem.Math

/-! ## Identification of the ground energy -/

/-- **Energy-minimal ground energies coincide.**  Two energies whose `(N+1)`-electron ground
submodules of the symmetric repulsive Hubbard Hamiltonian are both nonzero and both minimal have
equal real parts by a two-sided pinch, and each is the cast of its own real part because the
Hamiltonian is Hermitian (`liebRepulsive_groundEnergy_eq_ofReal`).  This is what transports
Theorem 10.4's conclusions, stated at the energy Theorem 10.4 produces, to the ground energy the
caller supplies. -/
private theorem liebRepulsive_groundEnergy_eq_of_min (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (U : Fin (N + 1) → ℝ) {E₀ E₁ : ℂ}
    (hne₀ : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hmin₀ : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (hne₁ : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₁ (N + 1) ≠ ⊥)
    (hmin₁ : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₁.re ≤ E.re) :
    E₀ = E₁ := by
  have hre : E₀.re = E₁.re := le_antisymm (hmin₀ E₁ hne₁) (hmin₁ E₀ hne₀)
  rw [← liebRepulsive_groundEnergy_eq_ofReal N T hT U E₀ hne₀,
    ← liebRepulsive_groundEnergy_eq_ofReal N T hT U E₁ hne₁, hre]

/-! ## Transport of the ratio along the lowering tower -/

/-- **The real expectation ratio of `(Ô_L)²` is constant along the tower.**  For a nonzero
highest-weight ground vector `w` (`Ŝ³_tot w = (L/2) w`, `L := sublatticeImbalance A`), every
lowered iterate `w_k = (Ŝ⁻_tot)^k w` with `k ≤ L` carries the same real Rayleigh quotient
`⟨(Ô_L)²⟩.re / ‖·‖²` as `w` itself.

Induction on `k`: the iterate `w_j` is a joint eigenvector of `Ŝ³_tot`
(`fermionTotalSpinZ_mulVec_spinMinusPow_general`) and of the Casimir
(`fermionTotalSpinSquared_mulVec_spinMinusPow`, which needs Theorem 10.4's value only at `w`, so
no hopping symmetry is required), and `w_{j+1} ≠ 0` while `j + 1 ≤ L`
(`liebRepulsive_ground_tower_ne_zero`), so the ladder-ratio invariance
`fermionSpinMinus_expectationRatioRe_invariant` applies at `O = (Ô_L)²`, whose `Ŝ⁺_tot`
commutation is `fermionStaggeredCasimirOp_commute_fermionTotalSpinPlus`. -/
theorem liebFerrimagnetism_tower_ratioRe_eq (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w) :
    ∀ k : ℕ, k ≤ sublatticeImbalance A →
      (vectorExpectation (fermionStaggeredCasimirOp N A)
          (((fermionTotalSpinMinus N) ^ k).mulVec w)).re /
        (star (((fermionTotalSpinMinus N) ^ k).mulVec w) ⬝ᵥ
            ((fermionTotalSpinMinus N) ^ k).mulVec w).re
      = (vectorExpectation (fermionStaggeredCasimirOp N A) w).re / (star w ⬝ᵥ w).re := by
  intro k
  induction k with
  | zero => intro _; simp only [pow_zero, Matrix.one_mulVec]
  | succ j ih =>
    intro hj
    have hstep : ((fermionTotalSpinMinus N) ^ (j + 1)).mulVec w
        = (fermionTotalSpinMinus N).mulVec (((fermionTotalSpinMinus N) ^ j).mulVec w) := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    have hne : (fermionTotalSpinMinus N).mulVec (((fermionTotalSpinMinus N) ^ j).mulVec w) ≠ 0 := by
      rw [← hstep]
      exact liebRepulsive_ground_tower_ne_zero N A T U E₀ hcas hw0 hwG hz (j + 1) hj
    have hinv := fermionSpinMinus_expectationRatioRe_invariant N (fermionStaggeredCasimirOp N A)
      (fermionStaggeredCasimirOp_commute_fermionTotalSpinPlus N A)
      (fermionTotalSpinZ_mulVec_spinMinusPow_general N w ((sublatticeImbalance A : ℂ) / 2) j hz)
      (fermionTotalSpinSquared_mulVec_spinMinusPow N w (liebRepulsiveSpinCasimir A) j
        (hcas w hwG)) hne
    rw [← ih (Nat.le_of_succ_le hj)]
    simp only [vectorExpectation]
    rw [hstep]
    exact hinv

/-- **The centered-sector bound propagates to every tower member.**  Since the real Rayleigh
quotient of `(Ô_L)²` is the same on all of `w_0, …, w_L`, the bound `S₀² ≤ ⟨(Ô_L)²⟩.re / ‖·‖²`
established on the centered member `w_{k₀}` (`k₀ = L / 2 ≤ L`, the member on which Theorem 10.5's
correlation signs live) holds on every member. -/
theorem liebFerrimagnetism_tower_ratioRe_ge_sq (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ v ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1),
      (fermionTotalSpinSquared N).mulVec v = liebRepulsiveSpinCasimir A • v)
    {w : (Fin (2 * N + 2) → Fin 2) → ℂ} (hw0 : w ≠ 0)
    (hwG : w ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (hcentered : ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A)
          (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w)).re /
        (star (((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w) ⬝ᵥ
            ((fermionTotalSpinMinus N) ^ (sublatticeImbalance A / 2)).mulVec w).re) :
    ∀ k : ℕ, k ≤ sublatticeImbalance A →
      ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
        (vectorExpectation (fermionStaggeredCasimirOp N A)
            (((fermionTotalSpinMinus N) ^ k).mulVec w)).re /
          (star (((fermionTotalSpinMinus N) ^ k).mulVec w) ⬝ᵥ
              ((fermionTotalSpinMinus N) ^ k).mulVec w).re := by
  intro k hk
  rw [liebFerrimagnetism_tower_ratioRe_eq N A T U E₀ hcas hw0 hwG hz k hk,
    ← liebFerrimagnetism_tower_ratioRe_eq N A T U E₀ hcas hw0 hwG hz
      (sublatticeImbalance A / 2) (Nat.div_le_self _ _)]
  exact hcentered

/-! ## Diagonalization of a quadratic form in an orthogonal family -/

/-- **A quadratic form with vanishing cross terms is diagonal.**  If `⟨u_j, O u_k⟩ = 0` for all
`j ≠ k`, then the quadratic form of `O` on a combination `Σ_k c_k u_k` is the weighted sum of its
values on the `u_k`, with weights `|c_k|²`.  Stated for a general `O` so that it serves both the
numerator (`O = (Ô_L)²`) and the denominator (`O = 1`, i.e. the squared norm) of a Rayleigh
quotient. -/
private theorem vectorExpectation_diagonal_of_crossTerm_zero {ι n : Type*} [Fintype ι]
    [Fintype n] (O : Matrix n n ℂ) (u : ι → n → ℂ) (c : ι → ℂ)
    (hcross : ∀ j k : ι, j ≠ k → star (u j) ⬝ᵥ O.mulVec (u k) = 0) :
    star (∑ k, c k • u k) ⬝ᵥ O.mulVec (∑ k, c k • u k)
      = ∑ k, (star (c k) * c k) * (star (u k) ⬝ᵥ O.mulVec (u k)) := by
  have hmul : O.mulVec (∑ k, c k • u k) = ∑ k, c k • O.mulVec (u k) := by
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun k _ => Matrix.mulVec_smul _ _ _
  have hexpand : star (∑ k, c k • u k) ⬝ᵥ O.mulVec (∑ k, c k • u k)
      = ∑ j, ∑ k, (star (c j) * c k) * (star (u j) ⬝ᵥ O.mulVec (u k)) := by
    rw [hmul]
    simp only [star_sum, star_smul, sum_dotProduct, dotProduct_sum, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hexpand]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_eq_single j (fun k _ hkj => ?_) (fun hj => absurd (Finset.mem_univ j) hj)
  rw [hcross j k (Ne.symm hkj), mul_zero]

/-! ## The bound on every ground vector -/

/-- **Tasaki's ferrimagnetic bound (10.2.17) on the whole ground multiplet.**  Every normalized
vector `v` of the `(N+1)`-electron ground submodule — not only the tower members — satisfies
`S₀² ≤ ⟨v| (Ô_L)² |v⟩.re`.

The ground submodule is the span of the tower (`liebRepulsive_ground_eq_span_tower`, whence the
hopping symmetry `hT` and Theorem 10.4's dimension count `hrank`), so `v = Σ_k c_k w_k`.  Since
`(Ô_L)²` commutes with `Ŝ³_tot`, the cross terms of both the numerator and the squared norm
vanish (`liebRepulsive_tower_crossTerm_eq_zero` at `O = (Ô_L)²` and at `O = 1`), so both are
diagonal with weights `|c_k|²`; the normalization makes the weighted squared norms sum to one and
the per-member bound `hratio` then averages to the claim. -/
theorem liebFerrimagnetism_bound_of_mem_ground (N : ℕ) (A : Finset (Fin (N + 1)))
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
    (hz : (fermionTotalSpinZ N).mulVec w = ((sublatticeImbalance A : ℂ) / 2) • w)
    (hratio : ∀ k : ℕ, k ≤ sublatticeImbalance A →
      ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
        (vectorExpectation (fermionStaggeredCasimirOp N A)
            (((fermionTotalSpinMinus N) ^ k).mulVec w)).re /
          (star (((fermionTotalSpinMinus N) ^ k).mulVec w) ⬝ᵥ
              ((fermionTotalSpinMinus N) ^ k).mulVec w).re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hnorm : star v ⬝ᵥ v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re := by
  classical
  rw [liebRepulsive_ground_eq_span_tower N A T hT U E₀ hcas hrank hw0 hwG hz] at hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  set u : Fin (sublatticeImbalance A + 1) → (Fin (2 * N + 2) → Fin 2) → ℂ :=
    fun k => ((fermionTotalSpinMinus N) ^ (k : ℕ)).mulVec w with hu
  have hcross : ∀ (O : ManyBodyOp (Fin (2 * N + 2))), Commute O (fermionTotalSpinZ N) →
      ∀ j k : Fin (sublatticeImbalance A + 1), j ≠ k →
        star (u j) ⬝ᵥ O.mulVec (u k) = 0 := fun O hO j k hjk =>
    liebRepulsive_tower_crossTerm_eq_zero N A hz O hO fun h => hjk (Fin.val_injective h)
  have hpos : ∀ k : Fin (sublatticeImbalance A + 1), 0 < (star (u k) ⬝ᵥ u k).re := fun k =>
    dotProduct_star_self_re_pos
      (liebRepulsive_ground_tower_ne_zero N A T U E₀ hcas hw0 hwG hz (k : ℕ)
        (Nat.lt_succ_iff.mp k.isLt))
  have hcoef : ∀ k : Fin (sublatticeImbalance A + 1),
      star (c k) * c k = ((Complex.normSq (c k) : ℝ) : ℂ) := fun k => by
    rw [Complex.star_def, mul_comm, Complex.mul_conj]
  -- The squared norm is diagonal in the tower, and normalized.
  have hden : (1 : ℝ) = ∑ k : Fin (sublatticeImbalance A + 1),
      Complex.normSq (c k) * (star (u k) ⬝ᵥ u k).re := by
    have h := vectorExpectation_diagonal_of_crossTerm_zero
      (1 : ManyBodyOp (Fin (2 * N + 2))) u c (hcross 1 (Commute.one_left _))
    rw [hc, Matrix.one_mulVec, hnorm] at h
    simp only [Matrix.one_mulVec, hcoef] at h
    rw [← Complex.one_re, h]
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  -- The numerator is diagonal in the tower.
  have hnum : (vectorExpectation (fermionStaggeredCasimirOp N A) v).re
      = ∑ k : Fin (sublatticeImbalance A + 1), Complex.normSq (c k) *
          (star (u k) ⬝ᵥ (fermionStaggeredCasimirOp N A).mulVec (u k)).re := by
    have h := vectorExpectation_diagonal_of_crossTerm_zero (fermionStaggeredCasimirOp N A) u c
      (hcross _ (fermionStaggeredCasimirOp_commute_fermionTotalSpinZ N A))
    rw [hc] at h
    simp only [hcoef] at h
    rw [vectorExpectation, h]
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  -- Each tower member obeys the bound with its squared norm cleared.
  have hmem : ∀ k : Fin (sublatticeImbalance A + 1),
      ((sublatticeImbalance A : ℝ) / 2) ^ 2 * (Complex.normSq (c k) * (star (u k) ⬝ᵥ u k).re)
        ≤ Complex.normSq (c k) * (star (u k) ⬝ᵥ (fermionStaggeredCasimirOp N A).mulVec (u k)).re :=
    fun k => by
      have hk := hratio (k : ℕ) (Nat.lt_succ_iff.mp k.isLt)
      rw [vectorExpectation, le_div_iff₀ (hpos k)] at hk
      have := mul_le_mul_of_nonneg_left hk (Complex.normSq_nonneg (c k))
      nlinarith [this]
  calc ((sublatticeImbalance A : ℝ) / 2) ^ 2
      = ((sublatticeImbalance A : ℝ) / 2) ^ 2 * ∑ k : Fin (sublatticeImbalance A + 1),
          Complex.normSq (c k) * (star (u k) ⬝ᵥ u k).re := by rw [← hden, mul_one]
    _ = ∑ k : Fin (sublatticeImbalance A + 1), ((sublatticeImbalance A : ℝ) / 2) ^ 2 *
          (Complex.normSq (c k) * (star (u k) ⬝ᵥ u k).re) := Finset.mul_sum _ _ _
    _ ≤ ∑ k : Fin (sublatticeImbalance A + 1), Complex.normSq (c k) *
          (star (u k) ⬝ᵥ (fermionStaggeredCasimirOp N A).mulVec (u k)).re :=
        Finset.sum_le_sum fun k _ => hmem k
    _ = (vectorExpectation (fermionStaggeredCasimirOp N A) v).re := hnum.symm

/-! ## The single-site branch -/

/-- **The ferrimagnetic bound on a single site.**  For `N = 0` the staggered order parameter is
the plain total-spin Casimir (`fermionStaggeredCasimirOp_zero_eq_totalSpinSquared`), so Theorem
10.4's Casimir conclusion evaluates the expectation of a normalized ground vector as
`γ₀ = S₀(S₀ + 1)` outright, and `S₀² ≤ S₀(S₀ + 1)` because `S₀ ≥ 0`.  No tower argument (hence no
`1 ≤ N`, which the centered-sector layer requires) is involved. -/
private theorem liebFerrimagnetism_N_zero (A : Finset (Fin (0 + 1)))
    (T : Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ) (U : Fin (0 + 1) → ℝ) (E₀ : ℂ)
    (hcas : ∀ x ∈ hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian 0 T U) E₀ (0 + 1),
      (fermionTotalSpinSquared 0).mulVec x = liebRepulsiveSpinCasimir A • x)
    (v : (Fin (2 * 0 + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian 0 T U) E₀ (0 + 1))
    (hnorm : star v ⬝ᵥ v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp 0 A) v).re := by
  have hexp : vectorExpectation (fermionStaggeredCasimirOp 0 A) v = liebRepulsiveSpinCasimir A := by
    rw [vectorExpectation, fermionStaggeredCasimirOp_zero_eq_totalSpinSquared, hcas v hv,
      dotProduct_smul, smul_eq_mul, hnorm, mul_one]
  have h0 : (0 : ℝ) ≤ (sublatticeImbalance A : ℝ) / 2 := by positivity
  have hexpand : ((sublatticeImbalance A : ℝ) / 2) * ((sublatticeImbalance A : ℝ) / 2 + 1)
      = ((sublatticeImbalance A : ℝ) / 2) ^ 2 + (sublatticeImbalance A : ℝ) / 2 := by ring
  rw [hexp, liebRepulsiveSpinCasimir_eq_ofReal, Complex.ofReal_re, hexpand]
  linarith

/-! ## Assembly -/

/-- **The ferrimagnetic bound for the symmetric-form repulsive Hubbard model.**  Theorem 10.4
supplies the Casimir value and the multiplet dimension at its own ground energy, which
`liebRepulsive_groundEnergy_eq_of_min` identifies with the caller's `E₀`; the centered-sector
existential (`liebRepulsive_exists_centered_ratioRe_ge_sq`, Theorem 10.5's sign step) supplies a
highest-weight ground vector realizing the bound on its centered tower member, which the tower
transport spreads over the whole multiplet and the tower expansion carries to an arbitrary
normalized ground vector.  The single-site case, excluded by the centered-sector layer's `1 ≤ N`,
is the separate elementary branch. -/
theorem liebFerrimagnetism_symmetric (N : ℕ) (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (hT : ∀ i j, T i j = T j i)
    (hbip : HoppingRespectsBipartition A T)
    (hT_conn : (hoppingSupportGraph T).Preconnected)
    (U : Fin (N + 1) → ℝ) (hU : ∀ x, 0 < U x) (E₀ : ℂ)
    (hGS_ne : hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1) ≠ ⊥)
    (hMin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
        (symmetricRepulsiveHubbardHamiltonian N T U) E (N + 1) ≠ ⊥ → E₀.re ≤ E.re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber
      (symmetricRepulsiveHubbardHamiltonian N T U) E₀ (N + 1))
    (hnorm : star v ⬝ᵥ v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re := by
  obtain ⟨E₁, hne₁, hmin₁, hcas, hrank⟩ :=
    theorem_10_4_lieb_repulsive_half_filling A T (symmetricRepulsiveHubbardHamiltonian N T U)
      ⟨hT, hbip, hT_conn, Or.inr ⟨U, hU, rfl⟩⟩
  obtain rfl : E₁ = E₀ :=
    liebRepulsive_groundEnergy_eq_of_min N T hT U hne₁ hmin₁ hGS_ne hMin
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact liebFerrimagnetism_N_zero A T U E₁ hcas v hv hnorm
  · obtain ⟨w, hw0, hwG, hz, hcentered⟩ := liebRepulsive_exists_centered_ratioRe_ge_sq N A T hT
      hbip hT_conn U hU hN E₁ hGS_ne hMin hcas
    exact liebFerrimagnetism_bound_of_mem_ground N A T hT U E₁ hcas hrank hw0 hwG hz
      (liebFerrimagnetism_tower_ratioRe_ge_sq N A T U E₁ hcas hw0 hwG hz hcentered) v hv hnorm

/-- **Tasaki Theorem 10.6** (Shen–Qiu–Tian ferrimagnetism; 1st ed., Springer 2020, §10.2.3,
p. 356, eqs. (10.2.16)/(10.2.17)). Under the hypotheses of Theorem 10.4, every normalized ground
state `v` of the repulsive Hubbard model satisfies the ferrimagnetic order-parameter bound

  `⟨v| (Ô_L)² |v⟩ ≥ ((|A| − |B|)/2)²`.

(The book also notes the left-hand side is independent of the ground state — visible here in that
the bound holds for every `v` of the ground submodule.)  Proved via Theorem 10.4 and Theorem 10.5
(inequality (10.2.7)), exactly as Theorem 4.4, and **not** by reflection positivity: the symmetric
disjunct is `liebFerrimagnetism_symmetric`, and the uniform disjunct differs from it by the
constant energy shift of `symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform`, which
moves the ground submodule and its minimality but not the conclusion. -/
theorem theorem_10_6_lieb_ferrimagnetism {N : ℕ}
    (A : Finset (Fin (N + 1)))
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ)
    (H : ManyBodyOp (Fin (2 * N + 2)))
    (hModel : IsLiebRepulsiveModel A T H)
    (E₀ : ℂ)
    (hGS_ne : hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1) ≠ ⊥)
    (hMin : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber H E (N + 1) ≠ ⊥ →
      E₀.re ≤ E.re)
    (v : (Fin (2 * N + 2) → Fin 2) → ℂ)
    (hv : v ∈ hubbardGroundSubmoduleAtElectronNumber H E₀ (N + 1))
    (hnorm : dotProduct (star v) v = 1) :
    ((sublatticeImbalance A : ℝ) / 2) ^ 2 ≤
      (vectorExpectation (fermionStaggeredCasimirOp N A) v).re := by
  obtain ⟨hsymm, hbip, hconn, hham⟩ := hModel
  rcases hham with ⟨U, hU, rfl⟩ | ⟨U, hU, rfl⟩
  · have key : ∀ E : ℂ, hubbardGroundSubmoduleAtElectronNumber
          (symmetricRepulsiveHubbardHamiltonian N T (fun _ => U)) E (N + 1)
        = hubbardGroundSubmoduleAtElectronNumber (repulsiveHubbardHamiltonian N T U)
            (E - (-(U : ℂ) / 2 * ((N + 1 : ℕ) : ℂ) + (U : ℂ) / 4 * ((N : ℂ) + 1))) (N + 1) :=
      fun E => symmetricRepulsiveHubbardHamiltonian_groundSubmodule_eq_uniform N T U (N + 1) E
    refine liebFerrimagnetism_symmetric N A T hsymm hbip hconn (fun _ => U) (fun _ => hU)
      (E₀ + (-(U : ℂ) / 2 * ((N + 1 : ℕ) : ℂ) + (U : ℂ) / 4 * ((N : ℂ) + 1))) ?_ ?_ v ?_ hnorm
    · rw [key, add_sub_cancel_right]
      exact hGS_ne
    · intro E hE
      rw [key] at hE
      have hle := hMin _ hE
      simp only [Complex.add_re, Complex.sub_re] at hle ⊢
      linarith
    · rw [key, add_sub_cancel_right]
      exact hv
  · exact liebFerrimagnetism_symmetric N A T hsymm hbip hconn U hU E₀ hGS_ne hMin v hv hnorm

end LatticeSystem.Fermion
