import LatticeSystem.Quantum.SpinS.FerromagneticGroundStateTheorem21
import LatticeSystem.Quantum.SpinS.MaximalCasimirEigenvectorSpan

/-!
# Signature pin: Tasaki §2.4 Theorem 2.1, the `Ĥ`-eigenspace capstone (p. 34)

Repository-internal regression guard for the capstone declarations that close Tasaki's
Theorem 2.1 (H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer, 2020, §2.4, p. 34): on a connected, real, symmetric, edge-supported, strictly
ferromagnetic spin-`S` Heisenberg lattice (eq. (2.4.1), p. 32; standing assumption `S ≥ 1/2`,
i.e. `1 ≤ N`), the ground-state eigenspace of the Hamiltonian itself is the span of the ladder
family `ladderIterateUp`, coincides with the joint `(Ĥ, (Ŝ_tot)²)`-eigenspace, has dimension
`|V|·N + 1`, and (specialised to the printed uniform coupling `J = couplingOf G (−1/2)` of
eq. (2.4.1), p. 32) the printed ground energy is `E_GS = −|B|·S²`, which the book states in the
prose immediately below eq. (2.4.5), p. 32.

Pinned:
* C1 `heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro` — the
  `Ĥ`-eigenspace at the saturated-ferromagnet eigenvalue equals
  `span ℂ (Set.range (ladderIterateUp V N))` (this is Theorem 2.1 itself, as an eigenspace
  identity, for a general real symmetric ferromagnetic coupling).
* C2 `heisenbergHamiltonianS_eigenspace_finrank_eq_of_connected_ferro` — its dimension is
  `Fintype.card V * N + 1` (the `2S_max + 1` degeneracy count).
* C3 `heisenbergHamiltonianS_eigenspace_eq_satFerroJointEigenspace_of_connected_ferro` — the
  ground-state half of the remark after eq. (2.4.10), p. 34: the `Ĥ`-ground eigenspace coincides
  with the joint `(Ĥ, (Ŝ_tot)²)`-eigenspace, i.e. every ground state carries maximal total spin.
  The converse the book prints — that these are the *only* maximal-total-spin states — is
  `totalSpinSSquared_eigenspace_eq_span_ladderIterateUp`, pinned in its own section below, at
  the explicit value `S_max(S_max + 1)`; the maximal-eigenvalue reading is
  `totalSpinSSquared_maximal_eigenvector_mem_span_ladderIterateUp`, pinned as PIN-M below.
* C5a `saturatedFerromagnetEigenvalueS_couplingOf_neg_half` — the printed ground energy formula
  `E_GS = −|B|·S²` (p. 32, below eq. (2.4.5)) for the uniform coupling `J = couplingOf G (−1/2)`
  of eq. (2.4.1), p. 32; no hypotheses at all — it is an unconditional rewrite of
  `saturatedFerromagnetEigenvalueS`.
* C5b `tasaki_theorem_2_1_ferromagnetic_ground_states` — the printed theorem exactly, as a single
  three-conjunct statement: `Ĥ − E_GS` is `PosSemidef` (energy minimality), the `Ĥ`-eigenspace at
  `E_GS` is `span ℂ (Set.range (ladderIterateUp V N))`, and its dimension is
  `Fintype.card V * N + 1`.
* PIN-M `totalSpinSSquared_maximal_eigenvector_mem_span_ladderIterateUp` — the maximal-eigenvalue
  reading of the converse: an eigenvector of `(Ŝ_tot)²` at an eigenvalue with maximal real part
  lies in `span ℂ (Set.range (ladderIterateUp V N))`. Non-vacuity of the maximality hypothesis is
  exercised by control PC-M below.
* PIN `totalSpinSSquared_eigenspace_eq_span_ladderIterateUp` — the converse at the explicit
  value: the `(Ŝ_tot)²`-eigenspace at `S_max(S_max + 1)` equals the span of the ladder family,
  with no graph, coupling, connectivity or `1 ≤ N` hypothesis.
* PC-a — the PIN statement at `V := Fin 3`, `N := 1` with none of those hypotheses in scope.
* PC-b — the PIN statement at `N = 0`, where both sides are the whole space, so it shows only
  that `N = 0` is admitted and does not discriminate the right-hand side.
* PC-c — the finrank of the PIN's eigenspace is `4` at `V := Fin 3`, `N := 1`, which makes the
  right-hand side a proper subspace there.
* RC — the already-proved lower bound `totalSpinSSquared_eigenspace_finrank_ge_succ_card_mul_N`
  applied to the eigenspace term PC-c names.

A positive control on the triangle (`V := Fin 3`, `G := cycleGraph 3`, `N := 1`,
`J := couplingOf (cycleGraph 3) (−1/2)`) exercises C5a/C1/C2 with `|B| = 3` derived from
`cycleGraph_degree_three_le` + `SimpleGraph.sum_degrees_eq_twice_card_edges` (no `decide` on the
whole graph): spin-`1/2` on a 3-site ferromagnetic ring, ground energy `−3/4`, ground space the
`S = 3/2` quadruplet of dimension `4`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; eq. (2.4.1), p. 32; eqs. (2.4.4), (2.4.5), (2.4.9), (2.4.10),
pp. 32–34; solution of Problem 2.4.a, p. 496.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice SimpleGraph
open scoped ComplexOrder

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **C1 pin.** The `Ĥ`-eigenspace at the saturated-ferromagnet eigenvalue equals the span of the
full ladder family, on a connected graph with real, symmetric, edge-supported, strictly
ferromagnetic coupling (Tasaki §2.4 Theorem 2.1, p. 34). -/
example {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) :
    Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
      = Submodule.span ℂ (Set.range (ladderIterateUp V N)) :=
  heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro
    hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN

/-- **C2 pin.** The `Ĥ`-eigenspace at the saturated-ferromagnet eigenvalue has dimension
`|V|·N + 1` — the `2·S_max + 1` degeneracy count. -/
example {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) :
    Module.finrank ℂ
        (Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
          (saturatedFerromagnetEigenvalueS (V := V) J N))
      = Fintype.card V * N + 1 :=
  heisenbergHamiltonianS_eigenspace_finrank_eq_of_connected_ferro
    hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN

/-- **C3 pin.** The `Ĥ`-eigenspace at the saturated-ferromagnet eigenvalue equals the joint
`(Ĥ, (Ŝ_tot)²)`-eigenspace: every ground state carries maximal total spin (the ground-state half
of the remark after eq. (2.4.10), p. 34). -/
example {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) :
    Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
      = saturatedFerromagnetJointEigenspace (V := V) J N :=
  heisenbergHamiltonianS_eigenspace_eq_satFerroJointEigenspace_of_connected_ferro
    hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN

/-- **C5a pin.** The printed ground energy `E_GS = −|B|·S²` (p. 32, below eq. (2.4.5)) for the
uniform coupling `J = couplingOf G (−1/2)` of eq. (2.4.1), p. 32. Unconditional: no hypotheses on
`G` or `N` at all. -/
example (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) :
    saturatedFerromagnetEigenvalueS (V := V) (couplingOf G (-(1/2) : ℂ)) N
      = -(G.edgeFinset.card : ℂ) * ((N : ℂ) / 2) ^ 2 :=
  saturatedFerromagnetEigenvalueS_couplingOf_neg_half G N

/-- **C5b pin.** Tasaki §2.4 Theorem 2.1 as printed (p. 34): for a connected lattice with the
uniform ferromagnetic coupling `J = couplingOf G (−1/2)` and `1 ≤ N`, the shifted Hamiltonian is
positive semidefinite, its ground eigenspace is the span of the ladder family, and its dimension
is `|V|·N + 1`. -/
example (G : SimpleGraph V) [DecidableRel G.Adj] (hGconn : G.Connected) (hN : 1 ≤ N) :
    (heisenbergHamiltonianS (Λ := V) (couplingOf G (-(1/2) : ℂ)) N
        - ((-(G.edgeFinset.card : ℝ) * ((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) • 1).PosSemidef
      ∧ Module.End.eigenspace
            ((heisenbergHamiltonianS (couplingOf G (-(1/2) : ℂ)) N).mulVecLin)
            (-(G.edgeFinset.card : ℂ) * ((N : ℂ) / 2) ^ 2)
          = Submodule.span ℂ (Set.range (ladderIterateUp V N))
      ∧ Module.finrank ℂ
            (Module.End.eigenspace
              ((heisenbergHamiltonianS (couplingOf G (-(1/2) : ℂ)) N).mulVecLin)
              (-(G.edgeFinset.card : ℂ) * ((N : ℂ) / 2) ^ 2))
          = Fintype.card V * N + 1 :=
  tasaki_theorem_2_1_ferromagnetic_ground_states G hGconn hN

/-! ## Positive control: the ferromagnetic triangle (`cycleGraph 3`, spin-`1/2`)

`V := Fin 3`, `G := cycleGraph 3`, `N := 1`. `|edgeFinset| = 3`: every vertex has degree `2`
(`cycleGraph_degree_three_le` with `n := 0`), so `3 * 2 = 2 * G.edgeFinset.card` by
`SimpleGraph.sum_degrees_eq_twice_card_edges`, giving `G.edgeFinset.card = 3`. Ground energy
`−3 * (1/2)² = −3/4`; ground-space dimension `3 * 1 + 1 = 4` (the `S = 3/2` quadruplet). -/

/-- The triangle `cycleGraph 3` on `Fin 3` has three edges, from `3 * 2 = 2 * |B|`. -/
private theorem cycleGraph_three_edgeFinset_card :
    (cycleGraph 3 : SimpleGraph (Fin 3)).edgeFinset.card = 3 := by
  have hdeg : ∀ v : Fin 3, (cycleGraph 3 : SimpleGraph (Fin 3)).degree v = 2 :=
    fun v => cycleGraph_degree_three_le (n := 0)
  have hsum := (cycleGraph 3 : SimpleGraph (Fin 3)).sum_degrees_eq_twice_card_edges
  simp only [hdeg, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  omega

/-- **Positive control (C5a).** On the ferromagnetic triangle, `E_GS = −3/4`. -/
example :
    saturatedFerromagnetEigenvalueS (V := Fin 3)
        (couplingOf (cycleGraph 3) (-(1/2) : ℂ)) 1
      = -(3 : ℂ) / 4 := by
  rw [saturatedFerromagnetEigenvalueS_couplingOf_neg_half (cycleGraph 3) 1,
    cycleGraph_three_edgeFinset_card]
  norm_num

/-- **Positive control (C1).** On the ferromagnetic triangle, the ground eigenspace is the span
of the ladder family. -/
example :
    Module.End.eigenspace
        ((heisenbergHamiltonianS (Λ := Fin 3)
          (couplingOf (cycleGraph 3) (-(1/2) : ℂ)) 1).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := Fin 3)
          (couplingOf (cycleGraph 3) (-(1/2) : ℂ)) 1)
      = Submodule.span ℂ (Set.range (ladderIterateUp (Fin 3) 1)) :=
  heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro
    (show (cycleGraph 3 : SimpleGraph (Fin 3)).Connected from cycleGraph_connected (n := 2))
    (fun x y => by unfold couplingOf; by_cases h : (cycleGraph 3).Adj x y <;> simp [h])
    (couplingOf_symm (cycleGraph 3) (-(1/2) : ℂ))
    (fun x y h => by simp [couplingOf, h])
    (fun x y h => by simp [couplingOf, h])
    (le_refl 1)

/-- **Positive control (C2).** On the ferromagnetic triangle, the ground eigenspace has
dimension `4` (the `S = 3/2` quadruplet). -/
example :
    Module.finrank ℂ
        (Module.End.eigenspace
          ((heisenbergHamiltonianS (Λ := Fin 3)
            (couplingOf (cycleGraph 3) (-(1/2) : ℂ)) 1).mulVecLin)
          (saturatedFerromagnetEigenvalueS (V := Fin 3)
            (couplingOf (cycleGraph 3) (-(1/2) : ℂ)) 1))
      = 4 :=
  heisenbergHamiltonianS_eigenspace_finrank_eq_of_connected_ferro
    (show (cycleGraph 3 : SimpleGraph (Fin 3)).Connected from cycleGraph_connected (n := 2))
    (fun x y => by unfold couplingOf; by_cases h : (cycleGraph 3).Adj x y <;> simp [h])
    (couplingOf_symm (cycleGraph 3) (-(1/2) : ℂ))
    (fun x y h => by simp [couplingOf, h])
    (fun x y h => by simp [couplingOf, h])
    (le_refl 1)

/-! ## Signature pin: the converse half of the remark after eq. (2.4.10), p. 34

`totalSpinSSquared_eigenspace_eq_span_ladderIterateUp` states that the `(Ŝ_tot)²`-eigenspace at
`S_max(S_max+1)` is the span of the ladder family, with no graph, coupling, connectivity or
`1 ≤ N` hypothesis. The pins below fix that signature and exercise it at concrete `V`, `N`. -/

/-- **PIN.** The maximal-Casimir eigenspace — the `(Ŝ_tot)²`-eigenspace at
`S_max(S_max+1) = saturatedFerromagnetCasimirEigenvalueS V N` — equals the span of the ladder
family, for a finite non-empty `V` and any `N`. States only that this equality holds: no graph,
coupling, connectivity or `1 ≤ N` hypothesis is present in this pin. -/
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {N : ℕ} :
    Module.End.eigenspace ((totalSpinSSquared V N).mulVecLin)
        (saturatedFerromagnetCasimirEigenvalueS V N)
      = Submodule.span ℂ (Set.range (ladderIterateUp V N)) :=
  totalSpinSSquared_eigenspace_eq_span_ladderIterateUp

/-- **PC-a (hypothesis-free control).** The PIN statement instantiated at `V := Fin 3`, `N := 1`,
with no graph, coupling or `hN` in scope. Establishes only that the PIN's generic statement
type-checks and is usable at this concrete `V`, `N` without any of those hypotheses; it does not by
itself establish anything about the value of either side. -/
example :
    Module.End.eigenspace ((totalSpinSSquared (Fin 3) 1).mulVecLin)
        (saturatedFerromagnetCasimirEigenvalueS (Fin 3) 1)
      = Submodule.span ℂ (Set.range (ladderIterateUp (Fin 3) 1)) :=
  totalSpinSSquared_eigenspace_eq_span_ladderIterateUp

/-- **PC-b (`N = 0` control).** The PIN statement instantiated at `V := Fin 2`, `N := 0`. At
`N = 0` both sides of the PIN equality are the whole space `(V → Fin 1) → ℂ`, so on its own this
pin does not discriminate the right-hand side of the PIN statement; its purpose is only to show
that the PIN's generic statement admits `N = 0` (no `1 ≤ N` hypothesis is required). -/
example :
    Module.End.eigenspace ((totalSpinSSquared (Fin 2) 0).mulVecLin)
        (saturatedFerromagnetCasimirEigenvalueS (Fin 2) 0)
      = Submodule.span ℂ (Set.range (ladderIterateUp (Fin 2) 0)) :=
  totalSpinSSquared_eigenspace_eq_span_ladderIterateUp

/-- **PC-c (dimension control).** At `V := Fin 3`, `N := 1`, the finrank of the maximal-Casimir
eigenspace named in the PIN is `4`. Together with the ambient dimension `2³ = 8` (not pinned
here), this establishes that the PIN's right-hand side is a proper subspace at this `V`, `N`,
unlike at `N = 0` (PC-b). -/
example :
    Module.finrank ℂ
        (Module.End.eigenspace ((totalSpinSSquared (Fin 3) 1).mulVecLin)
          (saturatedFerromagnetCasimirEigenvalueS (Fin 3) 1))
      = 4 := by
  rw [totalSpinSSquared_eigenspace_eq_span_ladderIterateUp,
    finrank_span_eq_card ladderIterateUp_linearIndependent, Fintype.card_fin]
  simp

/-- **RC (already compiles at Red).** The existing lower bound
`totalSpinSSquared_eigenspace_finrank_ge_succ_card_mul_N`, instantiated at `V := Fin 3`, `N := 1`,
applied to the same eigenspace term that appears in PC-c. Establishes only that this eigenspace
term type-checks against an already-proved declaration, so that the `Unknown identifier` failures
above are isolated to the new name and are not a symptom of a malformed eigenspace term. -/
example :
    Fintype.card (Fin 3) * 1 + 1 ≤
      Module.finrank ℂ
        (Module.End.eigenspace ((totalSpinSSquared (Fin 3) 1).mulVecLin)
          (saturatedFerromagnetCasimirEigenvalueS (Fin 3) 1)) :=
  totalSpinSSquared_eigenspace_finrank_ge_succ_card_mul_N

/-! ## Signature pin: the maximal-eigenvalue reading of the remark after eq. (2.4.10), p. 34

`totalSpinSSquared_maximal_eigenvector_mem_span_ladderIterateUp` states that an eigenvector of
`(Ŝ_tot)²` whose eigenvalue is maximal — no eigenvalue with a non-zero eigenvector has a larger
real part — lies in the span of the ladder family. The pins below fix that signature and record
that the hypotheses it places on the eigenvalue are satisfiable. -/

/-- **PIN-M.** An eigenvector of `(Ŝ_tot)²` at an eigenvalue whose real part dominates the real
part of every eigenvalue of `(Ŝ_tot)²` with a non-zero eigenvector lies in the span of the
ladder family. No graph, coupling, connectivity or `1 ≤ N` hypothesis is present in this pin. -/
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {N : ℕ}
    {γ : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ≠ 0)
    (hcas : (totalSpinSSquared V N).mulVec v = γ • v)
    (hmax : ∀ (δ : ℂ) (w : (V → Fin (N + 1)) → ℂ), w ≠ 0 →
      (totalSpinSSquared V N).mulVec w = δ • w → δ.re ≤ γ.re) :
    v ∈ Submodule.span ℂ (Set.range (ladderIterateUp V N)) :=
  totalSpinSSquared_maximal_eigenvector_mem_span_ladderIterateUp hv hcas hmax

/-- **PC-M (non-vacuity control).** The three hypotheses of PIN-M are simultaneously
satisfiable: the first ladder iterate is a non-zero eigenvector of `(Ŝ_tot)²` whose eigenvalue
has maximal real part. Without this, PIN-M could hold vacuously for want of any eigenvalue
meeting its maximality hypothesis. -/
example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {N : ℕ} :
    ∃ (γ : ℂ) (v : (V → Fin (N + 1)) → ℂ), v ≠ 0 ∧
      (totalSpinSSquared V N).mulVec v = γ • v ∧
      ∀ (δ : ℂ) (w : (V → Fin (N + 1)) → ℂ), w ≠ 0 →
        (totalSpinSSquared V N).mulVec w = δ • w → δ.re ≤ γ.re := by
  have hCcast : saturatedFerromagnetCasimirEigenvalueS V N =
      ((((Fintype.card V : ℝ) * (N : ℝ) / 2) *
        ((Fintype.card V : ℝ) * (N : ℝ) / 2 + 1) : ℝ) : ℂ) := by
    unfold saturatedFerromagnetCasimirEigenvalueS
    push_cast
    ring
  have hladder := ladderIterateUp_totalSpinSSquared_hasEigenvector (V := V) (N := N) 0
  refine ⟨saturatedFerromagnetCasimirEigenvalueS V N, ladderIterateUp V N 0, hladder.2, ?_,
    fun δ w hw hδ => ?_⟩
  · have h := hladder.1
    rwa [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
  · rw [hCcast, Complex.ofReal_re]
    exact totalSpinSSquared_eigenvalue_re_le_sMax hw hδ

end LatticeSystem.Quantum
