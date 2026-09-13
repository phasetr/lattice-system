import LatticeSystem.Quantum.SpinS.StrictHOutsideFerrimagnetic
import LatticeSystem.Quantum.SpinS.FerrimagneticLROUniversal

/-!
# Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis) at the printed generality

The Marshall–Lieb–Mattis theorem for a *connected* bipartite antiferromagnet with balanced
sublattices, concluding whole-space ground-state uniqueness, the Marshall-signed positive
ground vector, and vanishing total spin — with no magnetization-sector restriction and no
auxiliary spectral shift parameter.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020,
§2.5 Theorem 2.2, p. 39 (statement, eq. (2.5.4), p. 39; proof pp. 39–42); general exchange
couplings by the Remark and eq. (2.5.13), p. 43; connectedness is Footnote 28, p. 33; the
appendix inputs are Theorems A.16/A.17, p. 473, and A.18, p. 475.

The complete bipartite graph is **not** a hypothesis of Theorem 2.2.  It is only the bond
graph of the toy Hamiltonian (2.5.10), p. 41, which Tasaki's proof introduces as an internal
comparison witness; the hypotheses carried here are the printed ones.

The connected chain this assembles is already graph-agnostic: the strict outside-sector
ordering `tasaki23_strict_hOutside_of_connected`, the connected per-sector Perron–Frobenius
simplicity
`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected`, the
full-eigenspace engine
`heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower`, and the
irreducibility-parameterised sector lift `tasaki23_sector_lift_and_casimir_of_irreducible`,
whose predicted Casimir value vanishes on the balanced sector.
-/

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis theorem), p. 39, eq. (2.5.4).**

Let `G` be a connected (Footnote 28, p. 33) graph on the finite vertex type `V`, bipartite
with respect to the sublattice marker `A` (every edge joins the two `A`-classes, §2.5, p. 37),
with the two classes of equal cardinality (`|A| = |B|`).  Let the exchange coupling `J` be
real, symmetric, non-negative, vanish within a sublattice, be strictly positive on the edges
of `G`, and vanish off `G` — this is Tasaki's Hamiltonian (2.5.13), p. 43, at spin
`S = N / 2 ≥ 1 / 2`.  Then there is an energy `μ` such that

* (C1) the full Heisenberg eigenspace at `μ` has `finrank ℂ ≤ 1`, and `μ` is a lower bound
  for every eigenvalue of `heisenbergHamiltonianS J N` — the ground state is unique;
* (C3) the Marshall-signed vector `Φ = magSectorEmbedding (marshallSignS A · * v)` supported
  on the balanced sector `|A| * N` is an eigenvector at `μ`, which is the (2.5.4) expansion;
* (C4) its coefficients `v` are strictly positive, i.e. `c_σ > 0`;
* (C2) `Φ` is annihilated by `totalSpinSSquared`, i.e. `(Ŝ_tot)² Φ = 0`, so `S_tot = 0`.

**Sign convention (route taken: instantiation).**  Tasaki's prefactor in (2.5.4) is
`∏_{x ∈ B} (−1)^{σ_x − S}` over the sublattice `B`, while `marshallSignS A` multiplies
`(−1)^{(σ x).val}` over the `A`-marked sites.  Two facts bridge these, and neither is left
implicit.  First, per site: under the repository dictionary `σ_x = S − (σ x).val`
(`magEigenvalueS σ = |V| * N / 2 − magSumS σ`) the printed exponent is `σ_x − S = −(σ x).val`,
and `(−1)^k` depends only on the parity of `k`, so the printed per-site factor *equals* the
Lean factor `(−1)^{(σ x).val}`; there is no residual `S`-shift.  Second, the index set: the
marker `A` here is universally quantified and every hypothesis is invariant under
`A ↦ fun x => ! A x` (`hGbip` is symmetric in the two classes, `h_card_eq` is an equality
between the two class cardinalities, and `hJ_bipartite` constrains only whether `A x = A y`),
so instantiating this theorem at the indicator of
Tasaki's `B` sublattice makes `marshallSignS A` *literally* the printed prefactor and C3/C4
the printed claims.  No bridge lemma is needed on that route.  Instantiated instead at
Tasaki's `A`, the two prefactors differ by the global constant `(−1)^{magSumS σ}`, which is
fixed on the balanced sector and only rescales `Φ`.

`_hJ_off` records that `J` is supported on the bonds of `G`, which is what makes
`heisenbergHamiltonianS J N` Tasaki's bond sum (2.5.13) rather than an unrestricted pair sum.
It is carried for faithfulness to the printed model and is deliberately not consumed by the
proof (hence the leading underscore, which the unused-variable linter requires): the chain
below needs only `hJ_bipartite`, which `hGbip` and `_hJ_off` together imply. -/
theorem tasaki_2_5_theorem_2_2_of_connected
    (A : V → Bool) (G : SimpleGraph V) (N : ℕ)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
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
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS J N)) (μ : ℂ)) ≤ 1 ∧
      (∀ {μM : ℝ} {φ : (V → Fin (N + 1)) → ℂ}, φ ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec φ = (μM : ℂ) • φ → μ ≤ μM) ∧
      ∃ v : magConfigS V N
          ((Finset.univ.filter (fun x : V => A x = true)).card * N) → ℝ,
        (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS J N).mulVec
            (magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ))) =
          (μ : ℂ) •
            magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ)) ∧
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ))) = 0 := by
  classical
  have hsum : (Finset.univ.filter (fun x : V => A x = true)).card +
      (Finset.univ.filter (fun x : V => (! A x) = true)).card = Fintype.card V :=
    tasaki23_card_filter_A_add_card_notA A
  have hVpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hGconn.nonempty
  have hcardA1 : 1 ≤ (Finset.univ.filter (fun x : V => A x = true)).card := by omega
  have hcardB1 : 1 ≤ (Finset.univ.filter (fun x : V => (! A x) = true)).card := by omega
  have horient : (Finset.univ.filter (fun x : V => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : V => A x = true)).card := h_card_eq.ge
  have hsB : 0 < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) *
      (N : ℝ) / 2 := by
    have hb : (0 : ℝ) < ((Finset.univ.filter (fun x : V => (! A x) = true)).card : ℝ) := by
      exact_mod_cast hcardB1
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    positivity
  obtain ⟨c, hc⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix A J N
  obtain ⟨c_toy, hc_toy⟩ :=
    exists_strict_diag_bound_dressedHeisenbergSReMatrix A (bipartiteCoupling A) N
  obtain ⟨μ, hcommon, hstrict⟩ :=
    tasaki23_strict_hOutside_of_connected A G N c c_toy horient hsB hGconn hGbip
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G hc hc_toy hN hcardA1 hcardB1
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA1
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB1
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b with
    | false => exact ⟨b, hAb⟩
    | true => rw [hAb] at hbf; cases hbf
  have hM0_mem : (Finset.univ.filter (fun x : V => A x = true)).card * N ∈
      tasaki23GroundStateSectors (V := V) A N :=
    (tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N _ h_card_eq).mpr rfl
  haveI : Nonempty (magConfigS V N
      ((Finset.univ.filter (fun x : V => A x = true)).card * N)) :=
    magConfigS_nonempty_of_le_card_mul (tasaki23GroundStateSectors_le_card_mul A N hM0_mem)
  obtain ⟨v, hv_pos, hv_heis⟩ :=
    hcommon ((Finset.univ.filter (fun x : V => A x = true)).card * N) hM0_mem
  have hIrred : (shiftedDressedSReMatrixOnMagSector A J N c
      ((Finset.univ.filter (fun x : V => A x = true)).card * N)).IsIrreducible :=
    isIrreducible_shiftedDressedSReMatrixOnMagSector_connected A c hGconn hGbip
      hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc
  have hsec : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector J N
        ((Finset.univ.filter (fun x : V => A x = true)).card * N))) (μ : ℂ)) ≤ 1 :=
    heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
      A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc hv_pos hv_heis
  obtain ⟨hLift, hCas⟩ :=
    tasaki23_sector_lift_and_casimir_of_irreducible A c c_toy horient hsB hM0_mem
      hJ_real hc_toy hA_ne hB_ne hN hIrred hv_pos hv_heis
  refine ⟨μ, ?_, ?_, v, hv_pos, hLift, ?_⟩
  · refine heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower
      J ((Finset.univ.filter (fun x : V => A x = true)).card * N) hJ_real ?_ hsec
    intro M hM_ne _ μM φ hφ_ne hφ
    refine hstrict ?_ hφ_ne hφ
    rw [tasaki23GroundStateSectors_mem_iff_eq_of_card_eq A N M h_card_eq]
    exact hM_ne
  · intro μM φ hφ_ne hφ
    refine tasaki23_eigenvalue_ge_common A N c hJ_real hJ_real' hJ_nn hJ_sym hJ_bipartite hc
      hcommon (fun {M} hM_non {μ' φ'} hφ'_ne hφ' => ?_) hφ_ne hφ
    haveI : Nonempty (magConfigS V N M) := by
      by_contra hcon
      rw [not_nonempty_iff] at hcon
      exact hφ'_ne (funext fun τ => (hcon.false τ).elim)
    exact le_of_lt (hstrict hM_non hφ'_ne hφ')
  · have hpred0 := tasaki23PredictedCasimirValue_eq_zero_of_card_eq (V := V) A N h_card_eq
    simpa [hpred0] using hCas

end LatticeSystem.Quantum
