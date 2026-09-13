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

Summation convention.  `heisenbergHamiltonianS J N = Σ_x Σ_y J x y • Ŝ_x · Ŝ_y`
(`SpinS/HeisenbergCore.lean`) sums over **ordered** pairs, whereas Tasaki's (2.5.1), p. 37,
and (2.5.13), p. 43, sum over **unordered** bonds.  A symmetric `J` supported on the bonds of
`G` therefore yields twice the printed bond sum: the printed exchange `J_{x,y}` of (2.5.13)
is the ordered-pair coupling `J_{x,y} / 2`, each bond contributing once in each order.
Restricting the support of `J` to the bonds of `G` deletes the non-bond terms; it does not
undo that doubling, which is a property of the index set.  The doubling itself is proved in
general by `two_sum_edgeFinset_lift_eq_sum_adj` (`Lattice/Graph.lean`), applicable here
because `spinSDot` is symmetric (`spinSDot_comm`).  No conclusion depends on the
normalisation: the hypotheses below are closed under multiplying `J` by a positive constant,
and the conclusions are invariant under `Ĥ ↦ c Ĥ` because the energy `μ` is existentially
quantified.  The printed unit-weight model (2.5.1) is the instance `J = couplingOf G (1/2)`,
stated as `tasaki_2_5_theorem_2_2_couplingOf_half` below.

The connected chain this assembles is already graph-agnostic: the strict outside-sector
ordering `tasaki23_strict_hOutside_of_connected`, the connected per-sector Perron–Frobenius
simplicity
`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected`, the
full-eigenspace engine
`heisenbergHamiltonianS_full_eigenspace_finrank_le_one_of_strict_sector_lower`, and the
irreducibility-parameterised sector lift `tasaki23_sector_lift_and_casimir_of_irreducible`,
whose predicted Casimir value vanishes on the balanced sector.
-/

open LatticeSystem.Lattice

namespace LatticeSystem.Quantum

open Matrix Module

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Tasaki §2.5 Theorem 2.2 (Marshall–Lieb–Mattis theorem), p. 39, eq. (2.5.4).**

Let `G` be a connected (Footnote 28, p. 33) graph on the finite vertex type `V`, bipartite
with respect to the sublattice marker `A` (every edge joins the two `A`-classes, §2.5, p. 37),
with the two classes of equal cardinality (`|A| = |B|`).  Let the exchange coupling `J` be
real, symmetric, non-negative, vanish within a sublattice, be strictly positive on the edges
of `G`, and vanish off `G`.  In the ordered-pair convention recorded in the module doc this
is Tasaki's Hamiltonian (2.5.13), p. 43, with printed exchange `2 J_{x,y}`, at spin
`S = N / 2 ≥ 1 / 2`; the printed normalisation is the instance `couplingOf G (1/2)` of
`tasaki_2_5_theorem_2_2_couplingOf_half`.  Then there is an energy `μ` such that

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

`_hJ_off` records that `J` is supported on the bonds of `G`, so that only bonds of the
printed lattice contribute and no pair outside the bond set does; it does *not* by itself
turn the ordered double sum into an unordered bond sum, the factor two being a matter of the
index set rather than of the support.  It is carried for faithfulness to the printed model
and is deliberately not consumed by the proof (hence the leading underscore, which the
unused-variable linter requires): the chain below needs only `hJ_bipartite`, which `hGbip`
and `_hJ_off` together imply. -/
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

/-- **Tasaki §2.5 Theorem 2.2 at the printed Hamiltonian (2.5.1), p. 37.**

Theorem 2.2, p. 39, with the expansion (2.5.4), p. 39, for the model exactly as printed at
the head of §2.5: `Ĥ = Σ_{{x,y} ∈ B} Ŝ_x · Ŝ_y`, eq. (2.5.1), p. 37 — unit weight on every
bond of a connected (Footnote 28, p. 33) bipartite graph `G` with balanced sublattices, at
spin `S = N / 2 ≥ 1 / 2`.  In the ordered-pair convention of `heisenbergHamiltonianS`
(module doc above) that unit-weight bond sum is the coupling `couplingOf G (1/2)`: each bond
`{x, y}` is met twice by `Σ_x Σ_y`, once as `(x, y)` and once as `(y, x)`, so the two halves
recombine into the printed weight `1`.  The general positive exchange couplings of the
Remark and eq. (2.5.13), p. 43, are `tasaki_2_5_theorem_2_2_of_connected`, of which this is
the instance at half the printed exchange; the conclusions are its same four conjuncts.

Every hypothesis that statement places on the coupling is discharged here from `couplingOf`
itself — `couplingOf_symm`, `couplingOf_real`, and the two branches of its defining `if` —
together with bipartiteness of `G`, so the printed model assumes only connectedness,
bipartiteness, balance and `1 ≤ N`.  This is the antiferromagnetic counterpart of
`tasaki_theorem_2_1_ferromagnetic_ground_states`, which states Theorem 2.1 at the printed
ferromagnetic coupling `couplingOf G (-(1/2))` of eq. (2.4.1), p. 32. -/
theorem tasaki_2_5_theorem_2_2_couplingOf_half
    (A : V → Bool) (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    (h_card_eq : (Finset.univ.filter (fun x : V => A x = true)).card =
      (Finset.univ.filter (fun x : V => (! A x) = true)).card)
    (hN : 1 ≤ N) :
    ∃ μ : ℝ,
      finrank ℂ ↥(End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianS (couplingOf G ((1 : ℂ) / 2)) N))
          (μ : ℂ)) ≤ 1 ∧
      (∀ {μM : ℝ} {φ : (V → Fin (N + 1)) → ℂ}, φ ≠ 0 →
        (heisenbergHamiltonianS (couplingOf G ((1 : ℂ) / 2)) N).mulVec φ = (μM : ℂ) • φ →
          μ ≤ μM) ∧
      ∃ v : magConfigS V N
          ((Finset.univ.filter (fun x : V => A x = true)).card * N) → ℝ,
        (∀ σ, 0 < v σ) ∧
        (heisenbergHamiltonianS (couplingOf G ((1 : ℂ) / 2)) N).mulVec
            (magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ))) =
          (μ : ℂ) •
            magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ)) ∧
        (totalSpinSSquared V N).mulVec
            (magSectorEmbedding (fun τ => ((marshallSignS A τ.1).re * v τ : ℝ))) = 0 := by
  have hJ_real : ∀ x y : V, (couplingOf G ((1 : ℂ) / 2) x y).im = 0 := by
    intro x y
    unfold couplingOf
    by_cases h : G.Adj x y
    · rw [if_pos h]; norm_num
    · rw [if_neg h, Complex.zero_im]
  have hJ_pos_G : ∀ x y : V, G.Adj x y → 0 < (couplingOf G ((1 : ℂ) / 2) x y).re := by
    intro x y h
    unfold couplingOf
    rw [if_pos h]
    norm_num
  have hJ_off : ∀ x y : V, ¬ G.Adj x y → couplingOf G ((1 : ℂ) / 2) x y = 0 := by
    intro x y h
    unfold couplingOf
    exact if_neg h
  have hJ_nn : ∀ x y : V, 0 ≤ (couplingOf G ((1 : ℂ) / 2) x y).re := by
    intro x y
    by_cases h : G.Adj x y
    · exact (hJ_pos_G x y h).le
    · rw [hJ_off x y h, Complex.zero_re]
  have hJ_bipartite : ∀ x y : V, A x = A y → couplingOf G ((1 : ℂ) / 2) x y = 0 := by
    intro x y hxy
    unfold couplingOf
    exact if_neg fun hadj => hGbip x y hadj hxy
  exact tasaki_2_5_theorem_2_2_of_connected A G N hGconn hGbip h_card_eq hN hJ_real
    (couplingOf_real G (by norm_num)) (couplingOf_symm G ((1 : ℂ) / 2)) hJ_nn hJ_bipartite
    hJ_pos_G hJ_off

end LatticeSystem.Quantum
