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

/-- **Tasaki §2.5 Theorem 2.3, p. 42, at a fixed orientation of the two sublattices.**

The workhorse behind `tasaki_2_5_theorem_2_3_of_connected`, carrying the extra hypothesis
`horient : |B| ≤ |A|` that the printed theorem does not state and that the underlying chain
(`tasaki23_strict_hOutside_of_connected`, the per-sector Casimir lift) requires.  The capstone
below quantifies over both orientations and discharges `horient` by a case split, so this
hypothesis never reaches the public statement.

The five conclusions are the printed ones at a fixed orientation: the ground eigenspace has
dimension `2 S_tot + 1`; every admissible sector carries the Marshall-signed expansion (2.5.4)
with strictly positive coefficients; a ground state exists; every ground state is a
`(Ŝ_tot)²`-eigenvector at the predicted `S_tot(S_tot + 1)`; and `μ` is the least eigenvalue. -/
private theorem tasaki23_groundStates_of_connected_oriented
    (A : V → Bool) (G : SimpleGraph V) (N : ℕ)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re) :
    ∃ μ : ℝ,
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ))
          = tasaki23PredictedDegeneracy (V := V) A N ∧
      (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
        Nonempty (magConfigS V N M) →
        ∃ v : magConfigS V N M → ℝ, (∀ σ, 0 < v σ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ∧
      (∃ Φ : (V → Fin (N + 1)) → ℂ, Φ ≠ 0 ∧
        (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ) ∧
      (∀ {Φ : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ →
        (totalSpinSSquared V N).mulVec Φ =
          ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Φ) ∧
      (∀ {μM : ℝ} {φ : (V → Fin (N + 1)) → ℂ}, φ ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec φ = (μM : ℂ) • φ → μ ≤ μM) := by
  classical
  obtain ⟨c, hc⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix A J N
  obtain ⟨c_toy, hc_toy⟩ :=
    exists_strict_diag_bound_dressedHeisenbergSReMatrix A (bipartiteCoupling A) N
  have hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 := by
    have hb : (0 : ℝ) < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcardB
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  obtain ⟨μ, hcommon, hstrict⟩ :=
    tasaki23_strict_hOutside_of_connected A G N c c_toy horient hsB hGconn hGbip
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G hc hc_toy hN hcardA hcardB
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b with
    | false => exact ⟨b, hAb⟩
    | true => rw [hAb] at hbf; cases hbf
  -- Per-admissible-sector package: the Marshall-positive ground vector, its lift to the full
  -- Hilbert space, its predicted Casimir value, and Perron-Frobenius simplicity of its sector.
  have hpack : ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      ∃ v : magConfigS V N M → ℝ, (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          (μ : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
          ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • magSectorEmbedding
            (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∧
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
            (heisenbergHamiltonianSMatrixOnMagSector J N M)) (μ : ℂ)) ≤ 1 := by
    intro M hM
    haveI : Nonempty (magConfigS V N M) :=
      magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM)
    obtain ⟨v, hv_pos, hReEig⟩ := hcommon M hM
    have hIrred : (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible :=
      isIrreducible_shiftedDressedSReMatrixOnMagSector_connected A c hGconn hGbip
        hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc
    obtain ⟨hLift, hCas⟩ :=
      tasaki23_sector_lift_and_casimir_of_irreducible A c c_toy horient hsB hM
        hJ_real hc_toy hA_ne hB_ne hN hIrred hv_pos hReEig
    have hpf :=
      heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
        A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc hv_pos hReEig
    exact ⟨v, hv_pos, hLift, hCas, hpf⟩
  have hmemE : ∀ Ψ : (V → Fin (N + 1)) → ℂ,
      Ψ ∈ End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ↔
        (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ := by
    intro Ψ
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]
  -- A ground state has no component outside the admissible band.
  have hoff : ∀ {Ψ : (V → Fin (N + 1)) → ℂ},
      (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ →
      ∀ {M : ℕ}, M ∉ tasaki23GroundStateSectors (V := V) A N →
        magSectorEmbedding (magSectorRestriction (M := M) Ψ) = 0 := by
    intro Ψ hΨ M hM
    exact heisenbergHamiltonianS_outside_projection_zero_of_strict_sectors J _ hJ_real
      hstrict hΨ hM
  -- Each weight component of a ground state is again a ground state, inside its own sector.
  have hcomp : ∀ Ψ : (V → Fin (N + 1)) → ℂ,
      (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ → ∀ M : ℕ,
      magSectorEmbedding (magSectorRestriction (M := M) Ψ) ∈
        End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
          magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) := by
    intro Ψ hΨ M
    refine Submodule.mem_inf.mpr ⟨(hmemE _).mpr ?_, magSectorEmbedding_mem_magSubspaceS _⟩
    exact heisenbergHamiltonianS_mulVec_magSectorEmbedding J _
      (heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen J hΨ)
  -- Every admissible weight block of the ground eigenspace is exactly one-dimensional.
  have hblock1 : ∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
        magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ))) = 1 := by
    intro M hM
    haveI : Nonempty (magConfigS V N M) :=
      magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM)
    obtain ⟨v, hv_pos, hLift, _, hpf⟩ := hpack M hM
    set W := End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
      magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) with hWdef
    have hle : finrank ℂ ↥W ≤ 1 := by
      rw [hWdef]
      exact heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
        (Λ := V) (N := N) J M (μ : ℂ) hpf
    have hXne : magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ≠ 0 :=
      tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos
    have hXmem : magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈ W := by
      rw [hWdef]
      exact Submodule.mem_inf.mpr
        ⟨(hmemE _).mpr hLift, magSectorEmbedding_mem_magSubspaceS _⟩
    have hspan : Submodule.span ℂ
        {magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))} ≤ W := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hXmem
    have hge := Submodule.finrank_mono hspan
    rw [finrank_span_singleton hXne] at hge
    omega
  -- Index the admissible band by `Fin (2 S_tot + 1)` and read off the dimension.
  have hscard : (tasaki23GroundStateSectors (V := V) A N).card =
      tasaki23PredictedDegeneracy (V := V) A N := tasaki23GroundStateSectors_card A N
  set e := (tasaki23GroundStateSectors (V := V) A N).orderIsoOfFin hscard with he
  set wt : Fin (tasaki23PredictedDegeneracy (V := V) A N) → ℂ :=
    fun a => ((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (((e a : ℕ)) : ℂ) with hwtdef
  have hwt_inj : Function.Injective wt := by
    intro a b hab
    simp only [hwtdef] at hab
    have h1 : (((e a : ℕ)) : ℂ) = (((e b : ℕ)) : ℂ) := by linear_combination -hab
    exact e.injective (Subtype.ext (Nat.cast_injective h1))
  have hsup : ⨆ a, End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
        End.eigenspace ((totalSpinSOp3 V N).mulVecLin) (wt a) =
      End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) := by
    refine le_antisymm (iSup_le fun a => inf_le_left) ?_
    intro Ψ hΨ
    have heig : (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ := (hmemE Ψ).mp hΨ
    have hsum := eq_sum_magSectorEmbedding_magSectorRestriction Ψ
    rw [hsum]
    refine Submodule.sum_mem _ fun M _ => ?_
    by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
    · obtain ⟨a, ha⟩ : ∃ a, ((e a : ℕ)) = M :=
        ⟨e.symm ⟨M, hM⟩, by rw [OrderIso.apply_symm_apply]⟩
      refine Submodule.mem_iSup_of_mem a ?_
      simp only [hwtdef, ha, ← magSubspaceS_eq_eigenspace]
      exact hcomp Ψ heig M
    · rw [hoff heig hM]
      exact Submodule.zero_mem _
  have hblockE : ∀ a : Fin (tasaki23PredictedDegeneracy (V := V) A N),
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
        End.eigenspace ((totalSpinSOp3 V N).mulVecLin) (wt a)) = 1 := by
    intro a
    have heq : End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
          magSubspaceS V N (wt a) =
        End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
          End.eigenspace ((totalSpinSOp3 V N).mulVecLin) (wt a) := by
      rw [magSubspaceS_eq_eigenspace]
    refine (congrArg
      (fun S : Submodule ℂ ((V → Fin (N + 1)) → ℂ) => finrank ℂ ↥S) heq).symm.trans ?_
    exact hblock1 ((e a : ℕ)) (e a).2
  have hdim : finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ))
      = tasaki23PredictedDegeneracy (V := V) A N := by
    rw [LatticeSystem.Math.finrank_eq_sum_of_weight_blocks _ _ wt hwt_inj hsup]
    simp [hblockE]
  -- Every ground state carries the predicted total spin.
  have hcasall : ∀ Ψ : (V → Fin (N + 1)) → ℂ,
      (heisenbergHamiltonianS J N).mulVec Ψ = (μ : ℂ) • Ψ →
      (totalSpinSSquared V N).mulVec Ψ =
        ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Ψ := by
    intro Ψ hΨ
    have hcomp_cas : ∀ M : ℕ,
        (totalSpinSSquared V N).mulVec (magSectorEmbedding (magSectorRestriction (M := M) Ψ)) =
          ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
            magSectorEmbedding (magSectorRestriction (M := M) Ψ) := by
      intro M
      by_cases hM : M ∈ tasaki23GroundStateSectors (V := V) A N
      · haveI : Nonempty (magConfigS V N M) :=
          magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM)
        obtain ⟨v, hv_pos, hLift, hCas, _⟩ := hpack M hM
        have hXne : magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ≠ 0 :=
          tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos
        have hXmem : magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ)) ∈
            End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ) ⊓
              magSubspaceS V N (((Fintype.card V : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) :=
          Submodule.mem_inf.mpr ⟨(hmemE _).mpr hLift, magSectorEmbedding_mem_magSubspaceS _⟩
        obtain ⟨r, hr⟩ := LatticeSystem.Math.exists_smul_of_mem_of_finrank_le_one
          (hblock1 M hM).le hXmem (hcomp Ψ hΨ M) hXne
        rw [← hr, Matrix.mulVec_smul, hCas, smul_comm]
      · rw [hoff hΨ hM, Matrix.mulVec_zero, smul_zero]
    have hsum := eq_sum_magSectorEmbedding_magSectorRestriction Ψ
    calc (totalSpinSSquared V N).mulVec Ψ
        = (totalSpinSSquared V N).mulVecLin
            (∑ M ∈ Finset.range (Fintype.card V * N + 1),
              magSectorEmbedding (magSectorRestriction (M := M) Ψ)) := by
          rw [Matrix.mulVecLin_apply, ← hsum]
      _ = ∑ M ∈ Finset.range (Fintype.card V * N + 1),
            (totalSpinSSquared V N).mulVecLin
              (magSectorEmbedding (magSectorRestriction (M := M) Ψ)) := map_sum _ _ _
      _ = ∑ M ∈ Finset.range (Fintype.card V * N + 1),
            ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
              magSectorEmbedding (magSectorRestriction (M := M) Ψ) := by
          refine Finset.sum_congr rfl fun M _ => ?_
          rw [Matrix.mulVecLin_apply]
          exact hcomp_cas M
      _ = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) •
            ∑ M ∈ Finset.range (Fintype.card V * N + 1),
              magSectorEmbedding (magSectorRestriction (M := M) Ψ) := (Finset.smul_sum).symm
      _ = ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Ψ := by rw [← hsum]
  -- Global minimality of the common admissible energy.
  have hminimal : ∀ (μM : ℝ) (φ : (V → Fin (N + 1)) → ℂ), φ ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec φ = (μM : ℂ) • φ → μ ≤ μM := by
    intro μM φ hφ_ne hφ
    refine tasaki23_eigenvalue_ge_common A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc
      hcommon (fun {M} hM_non {μ' φ'} hφ'_ne hφ' => ?_) hφ_ne hφ
    haveI : Nonempty (magConfigS V N M) := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      exact hφ'_ne (funext fun τ => (hcon.false τ).elim)
    exact le_of_lt (hstrict hM_non hφ'_ne hφ')
  refine ⟨μ, hdim, fun M hM _ => ?_, ?_, fun {Φ} hΦ => hcasall Φ hΦ,
    fun {μM φ} hφ_ne hφ => hminimal μM φ hφ_ne hφ⟩
  · obtain ⟨v, hv_pos, hLift, _, _⟩ := hpack M hM
    exact ⟨v, hv_pos, hLift⟩
  · have hlo := tasaki23GroundStateSectors_left_mem (V := V) A N
    haveI : Nonempty (magConfigS V N
        (min (Finset.univ.filter (fun x : V => A x = true)).card
          (Finset.univ.filter (fun x : V => (! A x) = true)).card * N)) :=
      magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hlo)
    obtain ⟨v, hv_pos, hLift, _, _⟩ := hpack _ hlo
    exact ⟨_, tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos, hLift⟩

/-- **Tasaki §2.5 Theorem 2.3 (Marshall–Lieb–Mattis for unbalanced sublattices), p. 42.**

Let `G` be a connected (Footnote 28, p. 33) graph on the finite vertex type `V`, bipartite with
respect to the sublattice marker `A` (every edge joins the two `A`-classes, §2.5, p. 37), with
both classes non-empty.  Let the exchange coupling `J` be real, symmetric, non-negative, vanish
within a sublattice, be strictly positive on the edges of `G`, and vanish off `G`.  In the
ordered-pair convention recorded in the module doc of `Theorem22Connected.lean` this is Tasaki's
Hamiltonian (2.5.13), p. 43, with printed exchange `2 J_{x,y}`, at spin `S = N / 2 ≥ 1 / 2`; the
printed normalisation is the instance `couplingOf G (1/2)` of
`tasaki_2_5_theorem_2_3_couplingOf_half`.  Write `S_tot = ||A| − |B|| · S`.  Then there is an
energy `μ` such that

* (K2) the ground eigenspace at `μ` has `finrank ℂ = 2 S_tot + 1 = ||A| − |B||·N + 1`, i.e. the
  ground states are `2 S_tot + 1` fold degenerate;
* (K3) every admissible magnetization sector `M` carries the expansion (2.5.4), p. 39 — the
  Marshall-signed vector `magSectorEmbedding (marshallSignS A · * v)` is an eigenvector at `μ`
  with strictly positive coefficients `v`, i.e. `c_σ > 0`, one sector per magnetization
  `σ̄ = M`;
* a ground state exists (the eigenspace is not the zero space);
* (K1) every ground state `Φ` satisfies `(Ŝ_tot)² Φ = S_tot(S_tot + 1) Φ`, i.e. carries total
  spin `S_tot`;
* `μ` is a lower bound for every eigenvalue of `heisenbergHamiltonianS J N`, which is what makes
  the four conclusions above statements about *ground* states.

**Orientation.**  Neither `|B| ≤ |A|` nor `|A| ≤ |B|` is assumed: the statement is symmetric
under exchanging the two sublattices, as the outer absolute value in `S_tot` requires, and the
proof case-splits on the orientation, running the oriented workhorse at the exchanged marker
`fun x => ! A x` in the second case (module doc above).

**Sign convention.**  As for Theorem 2.2: the marker `A` is universally quantified and every
hypothesis is invariant under `A ↦ fun x => ! A x`, so instantiating at the indicator of
Tasaki's `B` sublattice makes `marshallSignS A` literally the printed prefactor
`∏_{x ∈ B} (−1)^{σ_x − S}` of (2.5.4); instantiated at `A` the two differ by the sector-constant
factor `(−1)^{magSumS σ}`, which only rescales the expansion.

`_hJ_off` records that `J` is supported on the bonds of `G`, so that only bonds of the printed
lattice contribute.  It is carried for faithfulness to the printed model and is deliberately not
consumed (hence the leading underscore, which the unused-variable linter requires): the chain
needs only `hJ_bipartite`, which `hGbip` and `_hJ_off` together imply. -/
theorem tasaki_2_5_theorem_2_3_of_connected
    (A : V → Bool) (G : SimpleGraph V) (N : ℕ)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N)
    {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (_hJ_off : ∀ x y, ¬ G.Adj x y → J x y = 0) :
    ∃ μ : ℝ,
      finrank ℂ ↥(End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ))
          = tasaki23PredictedDegeneracy (V := V) A N ∧
      (∀ M ∈ tasaki23GroundStateSectors (V := V) A N,
        Nonempty (magConfigS V N M) →
        ∃ v : magConfigS V N M → ℝ, (∀ σ, 0 < v σ) ∧
          (heisenbergHamiltonianS J N).mulVec
              (magSectorEmbedding (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) =
            (μ : ℂ) • magSectorEmbedding
              (fun τ => (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ))) ∧
      (∃ Φ : (V → Fin (N + 1)) → ℂ, Φ ≠ 0 ∧
        (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ) ∧
      (∀ {Φ : (V → Fin (N + 1)) → ℂ},
        (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ →
        (totalSpinSSquared V N).mulVec Φ =
          ((tasaki23PredictedCasimirValue (V := V) A N : ℝ) : ℂ) • Φ) ∧
      (∀ {μM : ℝ} {φ : (V → Fin (N + 1)) → ℂ}, φ ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec φ = (μM : ℂ) • φ → μ ≤ μM) := by
  classical
  rcases le_total (Finset.univ.filter (fun x : V => (! A x) = true)).card
    (Finset.univ.filter (fun x : V => A x = true)).card with horient | horient
  · exact tasaki23_groundStates_of_connected_oriented A G N hGconn hGbip horient hcardA hcardB hN
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G
  · have hGbip' : ∀ x y, G.Adj x y → (! A x) ≠ (! A y) := by
      intro x y hadj hEq
      refine hGbip x y hadj ?_
      cases hx : A x <;> cases hy : A y <;> simp_all
    have hJbip' : ∀ x y, (! A x) = (! A y) → J x y = 0 := by
      intro x y hEq
      refine hJ_bipartite x y ?_
      cases hx : A x <;> cases hy : A y <;> simp_all
    obtain ⟨μ, hdim, hK3, hex, hcas, hmin⟩ :=
      tasaki23_groundStates_of_connected_oriented (fun x => ! A x) G N hGconn hGbip'
        (by rw [tasaki23_filter_not_not]; exact horient) hcardB
        (by rw [tasaki23_filter_not_not]; exact hcardA) hN
        hJ_real hJ_real' hJ_sym hJ_nn hJbip' hJ_pos_G
    refine ⟨μ, ?_, ?_, hex, ?_, hmin⟩
    · rw [hdim]
      exact tasaki23PredictedDegeneracy_not A N
    · intro M hM hne
      obtain ⟨v, hv_pos, hveig⟩ :=
        hK3 M (by rw [tasaki23GroundStateSectors_not]; exact hM) hne
      refine ⟨v, hv_pos, ?_⟩
      have hfun : (fun τ : magConfigS V N M =>
            (((marshallSignS (fun x => ! A x) τ.1).re * v τ : ℝ) : ℂ)) =
          ((((-1 : ℝ) ^ M : ℝ)) : ℂ) • fun τ : magConfigS V N M =>
            (((marshallSignS A τ.1).re * v τ : ℝ) : ℂ) := by
        funext τ
        have hsign : (marshallSignS (fun x => ! A x) τ.1).re
            = (-1 : ℝ) ^ M * (marshallSignS A τ.1).re := by
          have h := marshallSignS_not A τ.1
          rw [τ.2] at h
          rw [h, show ((-1 : ℂ) ^ M) = (((-1 : ℝ) ^ M : ℝ) : ℂ) by push_cast; ring,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        simp only [Pi.smul_apply, smul_eq_mul, hsign]
        push_cast
        ring
      rw [hfun, magSectorEmbedding_smul, Matrix.mulVec_smul] at hveig
      have hε : ((((-1 : ℝ) ^ M : ℝ)) : ℂ) ≠ 0 := by simp
      exact smul_right_injective _ hε (hveig.trans (smul_comm _ _ _))
    · intro Φ hΦ
      rw [← tasaki23PredictedCasimirValue_not A N]
      exact hcas hΦ

end GroundStates

end LatticeSystem.Quantum
