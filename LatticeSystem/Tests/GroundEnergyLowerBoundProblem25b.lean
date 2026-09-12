import LatticeSystem.Quantum.SpinS.GraphLocalStarSumWrapper
import LatticeSystem.Quantum.SpinS.SpinHalfSpecializationMultiSite
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Signature pin: Tasaki Problem 2.5.b, the Anderson ground-state energy lower bound

Repository-internal regression guard for the capstone that closes Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, Springer 2020, §2.5 Problem 2.5.b (p. 38, solution
pp. 497–498, using Problem 2.5.a and Lemma A.5, p. 468): on a finite bipartite lattice
`(Λ, B)` with sublattice `A`, the ground-state energy of the printed antiferromagnetic
Heisenberg Hamiltonian `Ĥ = Σ_{{x,y}∈B} Ŝ_x·Ŝ_y` (2.5.1) satisfies
`E_GS ≥ −Σ_{x∈A} S(1 + |N(x)| S)`, `S = N/2`, with **no** minimum-degree hypothesis on `A`.

Pinned:
* R0 `tasaki_problem_2_5_b_groundEnergy_lower_bound` — the full capstone signature, no `hdeg`,
  `filter A`, coupling `1/2` (the ordered-pair-convention unit coupling per bond of (2.5.1)),
  and the `[IsAlgClosed ℂ]` binder, which the capstone keeps because the import closure of its
  own module does not provide mathlib's `Complex.isAlgClosed`. That instance is always
  satisfiable, and this fixture imports it so that the concrete controls below can discharge it.

Controls, all compiling now from existing API (none of them establishes tightness of the bound
in general; see each doc comment for what it does and does not show):
* PC1 (`isolatedVertexGraph`, `sublatticeAneOne`) — a three-site graph with a single edge `0`–`1`
  and vertex `2` isolated: `hA` holds and `¬ (1 ≤ degree 2)`, so the retired positive-degree
  wrappers could not apply here, while the capstone does.
* PC2 (`pathGraph 2`, `N = 1`, the singlet witness) — establishes
  `hermitianMinEigenvalue (H_{1/2}) ≤ -3/4` independently of the capstone, and the capstone
  application (R0-dependent) matches it as an equality (the bound attained).
* NC1–NC4 — mutation controls at the PC2 witness: dropping `hA` (NC1), dropping the `+1` (NC2),
  the `S`-halving slip `N/2 → N/4` (NC4), and the coupling slip `J = 1` (NC3) each produce a
  bound that is *not* a valid lower bound there. None of these separates "sum over `A`" from
  "sum over `univ`", nor the correct `+1` from a slightly different additive slip that happens
  to still hold at this particular witness (`N = 1`, `deg = 1`) — only R0's syntactic pin (the
  capstone's exact shape) catches those; see the design note.
* SC1 (`cycleGraph 3`) — the triangle admits **no** bipartition, so the capstone is (per the
  book's own standing assumption, §2.5, p. 37) vacuous there; this is *not* a positive control.
-/

namespace LatticeSystem.Tests.GroundEnergyLowerBoundProblem25b

open LatticeSystem.Lattice LatticeSystem.Quantum SimpleGraph Matrix

/-! ## R0: the capstone signature pin -/

/-- **R0.** Restates the exact signature of the planned capstone
`tasaki_problem_2_5_b_groundEnergy_lower_bound` as a shim `example`, so that Red fails only with
`unknown identifier` on the new name. Establishes nothing about the mathematics; it is a
syntactic pin of the capstone's exact hypotheses (no `hdeg`, `filter A`, coupling `1/2`, the
`[IsAlgClosed ℂ]` binder). -/
example {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [IsAlgClosed ℂ]
    (G : SimpleGraph Λ) [DecidableRel G.Adj] {A : Λ → Prop} [DecidablePred A]
    (hA : ∀ {x y : Λ}, G.Adj x y → A x ≠ A y) (N : ℕ) :
    ∑ x ∈ (Finset.univ : Finset Λ).filter A,
        -((N : ℝ) / 2) * ((G.degree x : ℝ) * (N : ℝ) / 2 + 1) ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian G
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) N) :=
  @tasaki_problem_2_5_b_groundEnergy_lower_bound Λ _ _ _ G _ A _ hA N

/-! ## PC1: the isolated-vertex control (`hdeg` removal is load-bearing) -/

/-- Hand-built three-site graph: the single edge `0`–`1`, with vertex `2` isolated. -/
def isolatedVertexGraph : SimpleGraph (Fin 3) where
  Adj x y := (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0)
  symm := by rintro x y (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> simp [hx, hy]
  loopless := ⟨by rintro x (⟨hx, hy⟩ | ⟨hx, hy⟩) <;> simp_all⟩

instance : DecidableRel isolatedVertexGraph.Adj := fun x y => by
  unfold isolatedVertexGraph
  infer_instance

/-- The sublattice `A := {x : x ≠ 1}`, which contains the isolated vertex `2`. -/
def sublatticeAneOne : Fin 3 → Prop := fun x => x ≠ 1

instance : DecidablePred sublatticeAneOne := fun x => by
  unfold sublatticeAneOne; infer_instance

/-- **PC1a.** `sublatticeAneOne` is a genuine bipartition of `isolatedVertexGraph` (every bond
crosses). Establishes that PC1's `hA` hypothesis of the capstone is satisfiable here; proves
nothing about eigenvalues. -/
theorem isolatedVertexGraph_isBipartite :
    ∀ {x y : Fin 3}, isolatedVertexGraph.Adj x y →
      sublatticeAneOne x ≠ sublatticeAneOne y := by
  intro x y hxy
  unfold sublatticeAneOne
  rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;> decide

/-- **PC1b.** The vertex `2 ∈ A` is isolated (`¬ (1 ≤ degree 2)`), so none of the retired
positive-degree wrappers can apply to it. Establishes that dropping `hdeg` is load-bearing
(the capstone, unlike the retired wrappers, is expected to still apply here); proves nothing
about the value of the ground energy. -/
theorem isolatedVertexGraph_degree_two_lt_one :
    ¬ (1 ≤ isolatedVertexGraph.degree (2 : Fin 3)) := by
  have hnbr : isolatedVertexGraph.neighborFinset (2 : Fin 3) = ∅ := by decide
  unfold SimpleGraph.degree
  rw [hnbr]
  simp

/-- **PC1c (R0-dependent).** The capstone instantiated at `isolatedVertexGraph`, `N = 1` gives
`-5/4 ≤ λmin`, strictly slack (the true value is `-3/4`, since the isolated vertex contributes
only slack). This does *not* establish tightness; it establishes only that the capstone applies
at an instance the retired `hdeg`-bearing wrappers could not reach. -/
example :
    ∑ x ∈ (Finset.univ : Finset (Fin 3)).filter sublatticeAneOne,
        -((1 : ℝ) / 2) * ((isolatedVertexGraph.degree x : ℝ) * (1 : ℝ) / 2 + 1) ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian isolatedVertexGraph
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) 1) := by
  exact_mod_cast tasaki_problem_2_5_b_groundEnergy_lower_bound isolatedVertexGraph
    isolatedVertexGraph_isBipartite 1

/-! ## PC2: the attained-bound control (`pathGraph 2`, spin-`1/2`, the singlet) -/

/-- The antiparallel configuration `σ 0 = 0`, `σ 1 = 1` on `Fin 2`. -/
noncomputable def sigma0 : Fin 2 → Fin 2 := ![0, 1]

/-- The singlet witness `|σ⟩ - |swap σ⟩` on the two-site chain. -/
noncomputable def psi0 : (Fin 2 → Fin 2) → ℂ :=
  basisVec sigma0 - basisVec (basisSwap sigma0 0 1)

/-- The real-valued basis vector `basisVec ρ` is fixed by `star` (its entries are `0` or `1`). -/
theorem star_basisVec_eq (ρ : Fin 2 → Fin 2) :
    star (basisVec ρ : (Fin 2 → Fin 2) → ℂ) = basisVec ρ := by
  funext τ
  simp only [Pi.star_apply, basisVec_apply]
  by_cases h : τ = ρ <;> simp [h]

/-- The singlet witness `psi0` is fixed by `star`, since each of its two basis-vector
summands is. -/
theorem star_psi0_eq : star psi0 = psi0 := by
  unfold psi0
  rw [star_sub, star_basisVec_eq, star_basisVec_eq]

/-- `⟨ψ0, ψ0⟩ = 2` (an unnormalised witness: `ψ0 = |σ⟩ - |swap σ⟩` has squared norm `1 + 1`). -/
theorem dotProduct_star_psi0_psi0 : dotProduct (star psi0) psi0 = (2 : ℂ) := by
  rw [star_psi0_eq]
  unfold psi0
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub]
  have h00 := basisVec_inner (Λ := Fin 2) sigma0 sigma0
  have h01 := basisVec_inner (Λ := Fin 2) sigma0 (basisSwap sigma0 0 1)
  have h10 := basisVec_inner (Λ := Fin 2) (basisSwap sigma0 0 1) sigma0
  have h11 := basisVec_inner (Λ := Fin 2) (basisSwap sigma0 0 1) (basisSwap sigma0 0 1)
  have hswap_ne : basisSwap sigma0 0 1 ≠ sigma0 := by
    intro h
    have := congrFun h 0
    simp [basisSwap, sigma0] at this
  unfold dotProduct at h00 h01 h10 h11 ⊢
  rw [h00, h01, h10, h11, if_neg (Ne.symm hswap_ne), if_neg hswap_ne]
  norm_num

/-- `pathGraph 2` is bipartite with `A := (· = 0)`. -/
theorem pathGraph2_isBipartite :
    ∀ {x y : Fin 2}, (SimpleGraph.pathGraph 2).Adj x y → (x = 0) ≠ (y = 0) := by
  intro x y hxy
  rw [pathGraph_adj_iff] at hxy
  rcases hxy with h | h <;> (fin_cases x <;> fin_cases y <;> simp_all)

/-- The unit-coupling graph Hamiltonian on `pathGraph 2` at `N = 1` reduces to `spinHalfDot 0 1`
via the one-sided decomposition (`pathGraph 2` bipartite with a single edge `0`–`1`). -/
theorem heisenbergHamiltonianOnGraphS_pathGraph2_eq_spinHalfDot :
    heisenbergHamiltonianOnGraphS (SimpleGraph.pathGraph 2) ((1 : ℂ) / 2) 1 =
      spinHalfDot (Λ := Fin 2) 0 1 := by
  rw [heisenbergHamiltonianOnGraphS_half_eq_sum_filter_graphLocalClusterHamiltonianS
    (SimpleGraph.pathGraph 2) pathGraph2_isBipartite 1]
  have hfilter : (Finset.univ : Finset (Fin 2)).filter (fun x => x = 0) = {0} := by decide
  rw [hfilter]
  simp only [Finset.sum_singleton]
  unfold graphLocalClusterHamiltonianS
  have hnbr : (SimpleGraph.pathGraph 2).neighborFinset (0 : Fin 2) = {1} := by decide
  rw [hnbr]
  simp only [Finset.sum_singleton]
  exact spinSDot_one_eq_spinHalfDot 0 1

/-- **PC2.** `λmin (H_{1/2}) ≤ -3/4` on `pathGraph 2` at `N = 1`, proved independently of the
capstone via the variational (Rayleigh-quotient) route at the singlet witness `psi0`.
Establishes that the printed bound is not vacuous and is sharp at least somewhere; the R0-
dependent application below is expected to match it as an equality (the bound attained).
Does *not* establish sharpness in general (Remark on Lemma A.5's commutation-freeness: the
bound is typically strict once two stars share a neighbour, which cannot happen on a single
edge). -/
theorem pathGraph2_lambdaMin_le_neg_three_quarters :
    hermitianMinEigenvalue
      (heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
        (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) 1) ≤ -(3 / 4 : ℝ) := by
  have hM' := heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
    (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) 1
  have hM : (spinHalfDot (Λ := Fin 2) 0 1).IsHermitian :=
    heisenbergHamiltonianOnGraphS_pathGraph2_eq_spinHalfDot ▸ hM'
  have heig : hermitianMinEigenvalue hM' = hermitianMinEigenvalue hM :=
    hermitianMinEigenvalue_eq_of_spectrum_eq hM' hM
      (by rw [heisenbergHamiltonianOnGraphS_pathGraph2_eq_spinHalfDot])
  rw [heig]
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hM psi0
  have hmul : (spinHalfDot (Λ := Fin 2) 0 1).mulVec psi0 = -(3 / 4 : ℂ) • psi0 := by
    unfold psi0
    exact spinHalfDot_mulVec_singlet (x := (0 : Fin 2)) (y := 1) (by decide) sigma0 (by decide)
  have hray : rayleighOnVec (spinHalfDot (Λ := Fin 2) 0 1) psi0 = -(3 / 4 : ℝ) * 2 := by
    unfold rayleighOnVec
    rw [hmul]
    simp only [dotProduct_smul, smul_eq_mul]
    rw [dotProduct_star_psi0_psi0]
    norm_num
  have hnorm : (dotProduct (star psi0) psi0).re = (2 : ℝ) := by
    rw [dotProduct_star_psi0_psi0]; norm_num
  rw [hnorm, hray] at hvar
  linarith

/-- **PC2 (R0-dependent).** The capstone applied at `pathGraph 2`, `N = 1`, `A := (· = 0)` gives
`-3/4 ≤ λmin`, which together with `pathGraph2_lambdaMin_le_neg_three_quarters` shows the bound
is *attained* (`λmin = -3/4`). -/
example :
    ∑ x ∈ (Finset.univ : Finset (Fin 2)).filter (fun x => x = 0),
        -((1 : ℝ) / 2) * (((SimpleGraph.pathGraph 2).degree x : ℝ) * (1 : ℝ) / 2 + 1) ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) 1) := by
  exact_mod_cast tasaki_problem_2_5_b_groundEnergy_lower_bound (SimpleGraph.pathGraph 2)
    pathGraph2_isBipartite 1

/-! ## NC1–NC4: mutation controls at the PC2 witness -/

/-- **NC1** (bipartiteness / `hA` load-bearing): taking `A := ∅` on `pathGraph 2` makes the
left-hand sum `0`, and `0 ≤ λmin` is false there (`pathGraph2_lambdaMin_le_neg_three_quarters`
gives `λmin ≤ -3/4 < 0`). Establishes that `hA` is load-bearing and the sum cannot be taken over
an arbitrary set; does not establish that `hA` is the weakest such hypothesis. -/
theorem nc1_not_zero_le_lambdaMin :
    ¬ (0 : ℝ) ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) 1) := by
  have := pathGraph2_lambdaMin_le_neg_three_quarters
  linarith

/-- **NC2** (the additive `+1` is load-bearing): dropping it gives the mutated closed form
`-(1/2)*(1/2) = -1/4`, which is *not* a valid lower bound at the PC2 witness, since
`-1/4 > -3/4 ≥ λmin`. -/
theorem nc2_not_dropped_plus_one_le_lambdaMin :
    ¬ -((1 : ℝ) / 2) * ((1 : ℝ) / 2) ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) 1) := by
  have := pathGraph2_lambdaMin_le_neg_three_quarters
  linarith

/-- **NC4** (the `S`-halving slip `N/2 → N/4` is load-bearing): the mutated closed form
`-(1/4)*(1/4 + 1) = -5/16` is likewise *not* a valid lower bound at the PC2 witness
(`-5/16 > -3/4 ≥ λmin`). -/
theorem nc4_not_halved_S_le_lambdaMin :
    ¬ -((1 : ℝ) / 4) * ((1 : ℝ) / 4 + 1) ≤
      hermitianMinEigenvalue
        (heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
          (by norm_num : star ((1 : ℂ) / 2) = (1 : ℂ) / 2) 1) := by
  have := pathGraph2_lambdaMin_le_neg_three_quarters
  linarith

/-- **NC3** (the coupling `J = 1/2` is load-bearing): with `J = 1`,
`H_1 = 2 • H_{1/2}` (the ordered-pair convention represents each printed unordered bond twice),
so `λmin(H_1) ≤ -3/2 < -3/4`; `J = 1` is not the printed unit coupling of (2.5.1). -/
theorem nc3_coupling_one_lambdaMin_le_neg_three_halves :
    hermitianMinEigenvalue
      (heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
        (by norm_num : star (1 : ℂ) = (1 : ℂ)) 1) ≤ -(3 / 2 : ℝ) := by
  have hone_eq_two_smul :
      heisenbergHamiltonianOnGraphS (SimpleGraph.pathGraph 2) (1 : ℂ) 1 =
        (2 : ℂ) • heisenbergHamiltonianOnGraphS (SimpleGraph.pathGraph 2) ((1 : ℂ) / 2) 1 := by
    change heisenbergHamiltonianS
        (LatticeSystem.Lattice.couplingOf (SimpleGraph.pathGraph 2) 1) 1 =
        (2 : ℂ) • heisenbergHamiltonianS
          (LatticeSystem.Lattice.couplingOf (SimpleGraph.pathGraph 2) ((1 : ℂ) / 2)) 1
    rw [← heisenbergHamiltonianS_smul]
    congr 1
    funext x y
    unfold LatticeSystem.Lattice.couplingOf
    by_cases h : (SimpleGraph.pathGraph 2).Adj x y <;> simp [h]
  have hM' := heisenbergHamiltonianOnGraphS_isHermitian (SimpleGraph.pathGraph 2)
    (by norm_num : star (1 : ℂ) = (1 : ℂ)) 1
  have hM : ((2 : ℂ) • spinHalfDot (Λ := Fin 2) 0 1).IsHermitian := by
    rw [← heisenbergHamiltonianOnGraphS_pathGraph2_eq_spinHalfDot, ← hone_eq_two_smul]
    exact hM'
  have heig : hermitianMinEigenvalue hM' = hermitianMinEigenvalue hM :=
    hermitianMinEigenvalue_eq_of_spectrum_eq hM' hM
      (by rw [hone_eq_two_smul, heisenbergHamiltonianOnGraphS_pathGraph2_eq_spinHalfDot])
  rw [heig]
  have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec hM psi0
  have hmulhalf : (spinHalfDot (Λ := Fin 2) 0 1).mulVec psi0 = -(3 / 4 : ℂ) • psi0 := by
    unfold psi0
    exact spinHalfDot_mulVec_singlet (x := (0 : Fin 2)) (y := 1) (by decide) sigma0 (by decide)
  have hray : rayleighOnVec ((2 : ℂ) • spinHalfDot (Λ := Fin 2) 0 1) psi0 =
      -(3 / 2 : ℝ) * 2 := by
    unfold rayleighOnVec
    rw [Matrix.smul_mulVec, hmulhalf]
    simp only [dotProduct_smul, smul_eq_mul]
    rw [dotProduct_star_psi0_psi0]
    norm_num
  have hnorm : (dotProduct (star psi0) psi0).re = (2 : ℝ) := by
    rw [dotProduct_star_psi0_psi0]; norm_num
  rw [hnorm, hray] at hvar
  linarith

/-! ## SC1: the triangle is not an admissible instance (negative control) -/

/-- **SC1.** `cycleGraph 3` (the triangle) admits *no* bipartition, matching the fact that §2.5
(p. 37) excludes it by standing assumption. Establishes that the capstone is vacuous on the
frustrated triangle; does *not* establish any lower bound for the triangle (deriving one would
be a different, unprinted theorem, out of scope here). -/
theorem cycleGraph3_not_bipartite :
    ¬ ∃ A : Fin 3 → Prop, ∀ {x y : Fin 3}, (cycleGraph 3).Adj x y → A x ≠ A y := by
  rintro ⟨A, hA⟩
  classical
  have h01 : (cycleGraph 3).Adj (0 : Fin 3) 1 :=
    (cycleGraph_adj_iff 1 0 1).mpr (Or.inl (by decide))
  have h12 : (cycleGraph 3).Adj (1 : Fin 3) 2 :=
    (cycleGraph_adj_iff 1 1 2).mpr (Or.inl (by decide))
  have h20 : (cycleGraph 3).Adj (2 : Fin 3) 0 :=
    (cycleGraph_adj_iff 1 2 0).mpr (Or.inl (by decide))
  have hne01 : ¬ (A 0 ↔ A 1) := fun h => hA h01 (propext h)
  have hne12 : ¬ (A 1 ↔ A 2) := fun h => hA h12 (propext h)
  have hne20 : ¬ (A 2 ↔ A 0) := fun h => hA h20 (propext h)
  by_cases h0 : A 0 <;> by_cases h1 : A 1 <;> by_cases h2 : A 2 <;> tauto

end LatticeSystem.Tests.GroundEnergyLowerBoundProblem25b
