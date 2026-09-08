import LatticeSystem.Quantum.SpinS.FerromagneticGroundStateTheorem21

/-!
# Signature pin: Tasaki §2.4 Theorem 2.1, the `Ĥ`-eigenspace capstone (p. 34)

Repository-internal regression guard for the capstone declarations that close Tasaki's
Theorem 2.1 (H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed.,
Springer, 2020, §2.4, p. 34): on a connected, real, symmetric, edge-supported, strictly
ferromagnetic spin-`S` Heisenberg lattice (eq. (2.4.1), p. 32; standing assumption `S ≥ 1/2`,
i.e. `1 ≤ N`), the ground-state eigenspace of the Hamiltonian itself is the span of the ladder
family `ladderIterateUp`, coincides with the joint `(Ĥ, (Ŝ_tot)²)`-eigenspace, has dimension
`|V|·N + 1`, and (specialised to the printed uniform coupling `J = couplingOf G (−1/2)`, eq.
(2.4.4)/(2.4.5)) the printed ground energy is `E_GS = −|B|·S²` (eq. (2.4.9)/(2.4.10)).

Pinned:
* C1 `heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro` — the
  `Ĥ`-eigenspace at the saturated-ferromagnet eigenvalue equals
  `span ℂ (Set.range (ladderIterateUp V N))` (this is Theorem 2.1 itself, as an eigenspace
  identity, for a general real symmetric ferromagnetic coupling).
* C2 `heisenbergHamiltonianS_eigenspace_finrank_eq_of_connected_ferro` — its dimension is
  `Fintype.card V * N + 1` (the `2S_max + 1` degeneracy count).
* C3 `heisenbergHamiltonianS_eigenspace_eq_satFerroJointEigenspace_of_connected_ferro` — the
  remark after eq. (2.4.10): the `Ĥ`-ground eigenspace coincides with the joint
  `(Ĥ, (Ŝ_tot)²)`-eigenspace, i.e. every ground state carries maximal total spin.
* C5a `saturatedFerromagnetEigenvalueS_couplingOf_neg_half` — the printed ground energy formula
  `E_GS = −|B|·S²` for the uniform coupling `J = couplingOf G (−1/2)` (eq. (2.4.4)/(2.4.9); no
  hypotheses at all — it is an unconditional rewrite of `saturatedFerromagnetEigenvalueS`).
* C5b `tasaki_theorem_2_1_ferromagnetic_ground_states` — the printed theorem exactly, as a single
  three-conjunct statement: `Ĥ − E_GS` is `PosSemidef` (energy minimality), the `Ĥ`-eigenspace at
  `E_GS` is `span ℂ (Set.range (ladderIterateUp V N))`, and its dimension is
  `Fintype.card V * N + 1`.

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
`(Ĥ, (Ŝ_tot)²)`-eigenspace: every ground state carries maximal total spin (the remark after eq.
(2.4.10), p. 34). -/
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

/-- **C5a pin.** The printed ground energy `E_GS = −|B|·S²` for the uniform coupling
`J = couplingOf G (−1/2)` (eq. (2.4.4)/(2.4.9), p. 32/34). Unconditional: no hypotheses on `G` or
`N` at all. -/
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

end LatticeSystem.Quantum
