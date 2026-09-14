import LatticeSystem.Quantum.SpinS.Theorem22Connected
import LatticeSystem.Quantum.SpinS.MagnetizationDirectSum
import LatticeSystem.Math.EigenspaceWeightFinrank
import LatticeSystem.Math.SubmoduleFinrankLeOne

/-!
# Tasaki §2.5 Theorem 2.3, p. 42 — total spin and degeneracy of the unbalanced ground states

The Marshall–Lieb–Mattis theorem for a *connected* bipartite antiferromagnet whose two
sublattices need not be balanced: the ground states carry total spin `S_tot = ||A| − |B|| · S`,
the ground eigenspace is `2 S_tot + 1` fold degenerate, and every admissible magnetization
sector carries the Marshall-signed expansion (2.5.4) with strictly positive coefficients.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.3, p. 42 (statement), proof sketch pp. 42–43; the expansion (2.5.4), p. 39;
general exchange couplings by the Remark and eq. (2.5.13), p. 43; bipartiteness is standing from
p. 37; connectedness is Footnote 28, p. 33; the degeneracy count is Theorem A.16, p. 473.
Theorem 2.2, p. 39 (`tasaki_2_5_theorem_2_2_of_connected`), is the balanced case `|A| = |B|`,
where `S_tot = 0` and the degeneracy is `1`.

The complete bipartite graph is **not** a hypothesis: it is only the bond graph of the toy
Hamiltonian (2.5.10), p. 41, internal to Tasaki's own proof.  The summation convention — the
printed unordered bond sum (2.5.1), p. 37, is the ordered-pair coupling `couplingOf G (1/2)`,
and no conclusion can see the normalisation because the energy is existentially quantified — is
the one recorded in the module doc of `Theorem22Connected.lean`, where
`heisenbergHamiltonianS_couplingOf_half_eq_bondSum` pins the weight `1/2` as the printed one.

## Orientation

The printed theorem assumes nothing about which sublattice is the larger, and its `S_tot`
carries an **outer** absolute value, so the statement is invariant under exchanging the two
sublattices.  The chain assembled here is not: `tasaki23_strict_hOutside_of_connected` and the
per-sector Casimir lift both fix the orientation `|B| ≤ |A|`.  The capstone therefore quantifies
over both orientations and discharges that hypothesis internally by a case split, running the
oriented workhorse at the exchanged marker `fun x => ! A x` in the other case and transporting
its conclusions back along the marker-exchange lemmas of the first section below.  Every object
the statement mentions is invariant under the exchange except the Marshall sign, which acquires
the sector-constant factor `(−1)^M` (`marshallSignS_not`); being a non-zero scalar it is
absorbed by the eigenvector equation.

## Degeneracy

The degeneracy is the dimension of the Hamiltonian's ground eigenspace *in the whole Hilbert
space*, which is what Theorem A.16, p. 473, settles in Tasaki's sketch.  It is not the number of
admissible sectors: `tasaki23GroundStateSectors_card` equals the same number unconditionally, by
interval arithmetic, with no Hamiltonian, coupling or connectivity input anywhere in its proof.
The dimension count here runs over the `Ŝ³_tot`-weight blocks of the ground eigenspace: each
admissible sector contributes exactly one dimension (Perron–Frobenius simplicity above, the
Marshall-positive sector vector below) and the non-admissible sectors contribute nothing
(`heisenbergHamiltonianS_outside_projection_zero_of_strict_sectors`).
-/

open LatticeSystem.Lattice

namespace LatticeSystem.Quantum

open Matrix Module

/-! ## Exchanging the two sublattices -/

section MarkerExchange

variable {V : Type*} [Fintype V]

/-- Double negation of a Boolean sublattice marker leaves its fiber unchanged. -/
private theorem tasaki23_filter_not_not (A : V → Bool) :
    Finset.univ.filter (fun x : V => (! ! A x) = true) =
      Finset.univ.filter (fun x : V => A x = true) := by
  ext x
  simp

/-- Exchanging the two sublattices leaves the admissible sector interval unchanged: the interval
`[min(|A|, |B|)·N, max(|A|, |B|)·N]` is symmetric in the two cardinalities. -/
private theorem tasaki23GroundStateSectors_not (A : V → Bool) (N : ℕ) :
    tasaki23GroundStateSectors (V := V) (fun x => ! A x) N =
      tasaki23GroundStateSectors (V := V) A N := by
  ext M
  rw [tasaki23GroundStateSectors_mem_iff, tasaki23GroundStateSectors_mem_iff,
    tasaki23_filter_not_not, min_comm, max_comm]

/-- Exchanging the two sublattices leaves the predicted total spin `S_tot = ||A| − |B||·S`
unchanged: this is exactly what the outer absolute value of the printed formula provides. -/
private theorem tasaki23PredictedTotalSpin_not (A : V → Bool) (N : ℕ) :
    tasaki23PredictedTotalSpin (V := V) (fun x => ! A x) N =
      tasaki23PredictedTotalSpin (V := V) A N := by
  unfold tasaki23PredictedTotalSpin
  rw [tasaki23_filter_not_not, abs_sub_comm]

/-- Exchanging the two sublattices leaves the predicted Casimir value `S_tot(S_tot + 1)`
unchanged. -/
private theorem tasaki23PredictedCasimirValue_not (A : V → Bool) (N : ℕ) :
    tasaki23PredictedCasimirValue (V := V) (fun x => ! A x) N =
      tasaki23PredictedCasimirValue (V := V) A N := by
  unfold tasaki23PredictedCasimirValue
  rw [tasaki23PredictedTotalSpin_not]

/-- Exchanging the two sublattices leaves the predicted degeneracy `2 S_tot + 1` unchanged. -/
private theorem tasaki23PredictedDegeneracy_not (A : V → Bool) (N : ℕ) :
    tasaki23PredictedDegeneracy (V := V) (fun x => ! A x) N =
      tasaki23PredictedDegeneracy (V := V) A N := by
  have habs : ∀ a b : ℕ, Int.natAbs ((a : ℤ) - (b : ℤ)) = Int.natAbs ((b : ℤ) - (a : ℤ)) := by
    intro a b
    omega
  unfold tasaki23PredictedDegeneracy
  rw [tasaki23_filter_not_not, habs]

/-- **Marshall sign under sublattice exchange.**  Every site carries the factor `(−1)^{σ_x}` in
exactly one of the two markers, so the two Marshall signs differ by the global factor
`(−1)^{magSumS σ}`, which is constant on each magnetization sector. -/
private theorem marshallSignS_not (A : V → Bool) {N : ℕ} (σ : V → Fin (N + 1)) :
    marshallSignS (fun x => ! A x) σ = (-1 : ℂ) ^ magSumS σ * marshallSignS A σ := by
  have hprod : marshallSignS A σ * marshallSignS (fun x => ! A x) σ
      = (-1 : ℂ) ^ magSumS σ := by
    unfold marshallSignS magSumS
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun x _ => ?_
    by_cases hAx : A x <;> simp [hAx]
  calc marshallSignS (fun x => ! A x) σ
      = marshallSignS A σ * marshallSignS A σ * marshallSignS (fun x => ! A x) σ := by
        rw [marshallSignS_sq, one_mul]
    _ = marshallSignS A σ * (marshallSignS A σ * marshallSignS (fun x => ! A x) σ) :=
        mul_assoc _ _ _
    _ = (-1 : ℂ) ^ magSumS σ * marshallSignS A σ := by rw [hprod, mul_comm]

end MarkerExchange

/-! ## Ground states of a connected bipartite antiferromagnet -/

section GroundStates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Off-sector projections of a ground state vanish (finite-set form).**  Suppose every
magnetization sector outside a finite set `S` has all of its real sector eigenvalues strictly
above `μ`.  Then a full Heisenberg eigenvector at `μ` has zero projection to every sector
outside `S`.

This is the `Finset`-indexed analogue of
`heisenbergHamiltonianS_outside_projection_zero_of_strict_sector_lower`, which excludes a single
sector `M0`.  The singleton form cannot express what Theorem 2.3 needs, namely the whole
admissible band excluded at once: away from the balanced case the admissible sectors other than
a chosen one realise `μ` rather than exceeding it, so the singleton hypothesis is unavailable. -/
theorem heisenbergHamiltonianS_outside_projection_zero_of_strict_sectors
    (J : V → V → ℂ) {N : ℕ} (S : Finset ℕ) {μ : ℝ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (h_strict_outside : ∀ {M : ℕ}, M ∉ S → [Nonempty (magConfigS V N M)] →
      ∀ {μM : ℝ} {φ : magConfigS V N M → ℝ}, φ ≠ 0 →
        (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μM • φ →
        μ < μM)
    {Ψ : (V → Fin (N + 1)) → ℂ}
    (hΨ : (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ)
    {M : ℕ} (hM : M ∉ S) :
    magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0 := by
  classical
  by_cases hW_zero : magSectorRestriction (M := M) Ψ = 0
  · rw [hW_zero, magSectorEmbedding_zero]
  · haveI : Nonempty (magConfigS V N M) := by
      by_contra h
      rw [not_nonempty_iff] at h
      exact hW_zero (funext (fun τ => (h.false τ).elim))
    have hW_eig : (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
        (magSectorRestriction (M := M) Ψ) =
        (μ : ℂ) • magSectorRestriction (M := M) Ψ :=
      heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen J hΨ
    obtain ⟨φ, hφ_ne, hφ⟩ :
        ∃ φ : magConfigS V N M → ℝ, φ ≠ 0 ∧
          (heisenbergHamiltonianSReMatrixOnMagSector J N M).mulVec φ = μ • φ := by
      by_cases hre : (fun σ => (magSectorRestriction (M := M) Ψ σ).re) =
          (0 : magConfigS V N M → ℝ)
      · refine ⟨fun σ => (magSectorRestriction (M := M) Ψ σ).im, ?_,
          heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
            N hJ_real hW_eig⟩
        intro him
        apply hW_zero
        funext τ
        have hr := congrFun hre τ
        have hi := congrFun him τ
        simp only [Pi.zero_apply] at hr hi ⊢
        exact Complex.ext hr hi
      · exact ⟨fun σ => (magSectorRestriction (M := M) Ψ σ).re, hre,
          heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
            N hJ_real hW_eig⟩
    exact absurd (h_strict_outside hM hφ_ne hφ) (lt_irrefl μ)

end GroundStates

end LatticeSystem.Quantum
