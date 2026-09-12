import LatticeSystem.Quantum.SpinS.FerromagneticSectorSpan
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedFerromagnetGroundEnergy
import LatticeSystem.Lattice.Graph

/-!
# Tasaki §2.4 Theorem 2.1: the ferromagnetic ground-state eigenspace

Closes Tasaki's Theorem 2.1 (p. 34) for the spin-`S` Heisenberg model on a connected graph
carrying a real, symmetric, edge-supported, strictly ferromagnetic coupling: the eigenspace of
`Ĥ` *alone* at the saturated-ferromagnet energy is the span of the ladder family
`Φ_M = (Ŝ⁻_tot)^k Φ↑` of eq. (2.4.9), p. 33 -- which is eq. (2.4.10), p. 34 -- its dimension
is the `2 S_max + 1` degeneracy `|V|·N + 1`, and it coincides with the joint `(Ĥ, (Ŝ_tot)²)`
eigenspace, i.e. every ground state carries maximal total spin.  The remark printed after
eq. (2.4.10), p. 34, asserts that the states of eq. (2.4.10) are the *only* states of maximal
total spin; what is proved here is the ground state ⇒ maximal total spin direction alone.  The
converse direction is `totalSpinSSquared_eigenspace_eq_span_ladderIterateUp`, proved without any
graph or coupling hypothesis in `SaturatedLadderJointEigenspace`, at the explicit value
`S_max(S_max + 1)`; the maximal-eigenvalue reading is
`totalSpinSSquared_maximal_eigenvector_mem_span_ladderIterateUp` of
`MaximalCasimirEigenvectorSpan`.

Specialised to the printed uniform coupling `couplingOf G (-1/2)` of eq. (2.4.1), p. 32, the
saturated-ferromagnet energy is the printed `E_GS = -|B| S²`, and the three statements combine
into Theorem 2.1 exactly as printed, energy minimality included.

The analytic input is the per-sector Perron-Frobenius uniqueness of `FerromagneticSectorSpan`
(solution of Problem 2.4.a, p. 496); the assembly across sectors is the pointwise magnetization
decomposition of `SaturatedLadderJointEigenspace`, whose joint `(Ĥ, (Ŝ_tot)²)` analogue this
module upgrades to a statement about `Ĥ` by itself; and the minimality that makes the eigenspace
a *ground*-state space is the frustration-free bound of `SaturatedFerromagnetGroundEnergy`
(Lemma A.9, p. 469).

Two remarks on the hypotheses.  `hJ_sym` is not an assumption beyond the book: eq. (2.4.1),
p. 32, sums over *unordered* bonds, so one weight per unordered bond is the printed model, and
the repo's ordered double sum encodes exactly that when the weight function is symmetric.  And
`1 ≤ N` is the standing assumption `S ≥ 1/2` of §2.4, and it is inherited unchanged from the
two upstream lemmas this module composes, both of which assume it:
`heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_eq_span_ladderIterateUp` and
`heisenbergHamiltonianS_sub_saturatedFerromagnetEigenvalueS_posSemidef`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; eq. (2.4.1), p. 32; eq. (2.4.9), p. 33; eq. (2.4.10), p. 34;
solution of Problem 2.4.a, p. 496; Lemma A.9, p. 469.
-/

open LatticeSystem.Lattice
open scoped ComplexOrder

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **The magnetization projector preserves an `Ĥ`-eigenspace.**

`Ĥ` commutes with the pointwise magnetization projector
(`heisenbergHamiltonianS_mulVec_magProjFn_eq`, which needs no hypothesis on `J`), so projecting
an eigenvector onto a magnetization sector leaves the eigenvector equation intact.  This is the
operator form of the block decomposition `Ĥ = ⊕_M Ĥ_M` that the solution of Problem 2.4.a
(p. 496) works in.  The joint `(Ĥ, (Ŝ_tot)²)` counterpart is
`magProjFn_mem_saturatedFerromagnetJointEigenspace`; here only the `Ĥ` factor is available, and
the eigenvalue is arbitrary. -/
private theorem magProjFn_mem_heisenbergHamiltonianS_eigenspace
    {J : V → V → ℂ} {μ M : ℂ} {v : (V → Fin (N + 1)) → ℂ}
    (hv : v ∈ Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin) μ) :
    magProjFn (V := V) (N := N) M v
      ∈ Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin) μ := by
  rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hv ⊢
  rw [heisenbergHamiltonianS_mulVec_magProjFn_eq, hv, magProjFn_smul]

/-- **Tasaki §2.4 Theorem 2.1, eq. (2.4.10), p. 34**: on a connected graph with a real,
symmetric, edge-supported, strictly ferromagnetic coupling, the `Ĥ`-eigenspace at the
saturated-ferromagnet energy is exactly the span of the ladder family `Φ_M` of eq. (2.4.9),
p. 33.

`⊇` is the statement that every ladder iterate is such an eigenvector.  For `⊆`, decompose a
ground state `v = ∑_k magProjFn (m_max - k) v` (`sum_magProjFn_eq`); each summand stays in the
eigenspace by `magProjFn_mem_heisenbergHamiltonianS_eigenspace` and lands in its magnetization
subspace by `magProjFn_mem_magSubspaceS`, so the per-sector Perron-Frobenius identification
(solution of Problem 2.4.a, p. 496) turns it into a multiple of the single ladder state of that
sector.

Non-emptiness of `V` is not a hypothesis: `G.Connected` carries it.  The book's `Φ_M` is the
normalized ladder state and `ladderIterateUp` the unnormalized iterate; only their span
appears. -/
theorem heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro
    {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) :
    Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
      = Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  haveI : Nonempty V := hGconn.nonempty
  refine le_antisymm (fun v hv => ?_) ?_
  · rw [← sum_magProjFn_eq (V := V) (N := N) v]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hmem : magProjFn (V := V) (N := N)
        ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) v ∈
        Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
            (saturatedFerromagnetEigenvalueS (V := V) J N)
          ⊓ magSubspaceS V N ((Fintype.card V : ℂ) * (N : ℂ) / 2 - (k.val : ℂ)) :=
      Submodule.mem_inf.mpr
        ⟨magProjFn_mem_heisenbergHamiltonianS_eigenspace hv, magProjFn_mem_magSubspaceS _ v⟩
    rw [heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_eq_span_ladderIterateUp
      hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN k] at hmem
    exact ladderIterateUp_singleton_span_le_span_range (V := V) N k hmem
  · rw [Submodule.span_le, Set.range_subset_iff]
    exact fun k => ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace J k

/-- **The `2 S_max + 1` ground-state degeneracy** (Tasaki §2.4 Theorem 2.1, p. 34).  Under the
hypotheses of eq. (2.4.10) the ground-state eigenspace has dimension `|V|·N + 1`, which is
`2 S_max + 1` for `S_max = |V|·N/2` -- the dimension of the spin-`S_max` irreducible
representation of `SU(2)`.

The eigenspace is the span of the ladder family by
`heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro`, and that family is
linearly independent (its members are `Ŝ³_tot`-eigenvectors at pairwise distinct eigenvalues), so
`finrank_span_eq_card` counts the index type `Fin (|V|·N + 1)`. -/
theorem heisenbergHamiltonianS_eigenspace_finrank_eq_of_connected_ferro
    {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) :
    Module.finrank ℂ
        (Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
          (saturatedFerromagnetEigenvalueS (V := V) J N))
      = Fintype.card V * N + 1 := by
  haveI : Nonempty V := hGconn.nonempty
  rw [heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro
      hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN,
    finrank_span_eq_card (ladderIterateUp_linearIndependent (V := V) (N := N)),
    Fintype.card_fin]

/-- **Every ferromagnetic ground state carries maximal total spin** -- the ground-state half of
the remark following eq. (2.4.10), p. 34.

The `Ĥ`-eigenspace at the saturated-ferromagnet energy coincides with the joint
`(Ĥ, (Ŝ_tot)²)`-eigenspace at the saturated values, so the maximal-Casimir condition, which
`saturatedFerromagnetJointEigenspace` imposes as an extra constraint, is automatic for a
connected ferromagnet.  Both sides are the span of the ladder family, by eq. (2.4.10) and by
`saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp`.

What the book prints is the converse: that the states of eq. (2.4.10) are the *only* states
with maximal total spin `S_max = |Λ| S`.  That inclusion is a separate statement about
`(Ŝ_tot)²` alone, and it is `totalSpinSSquared_eigenspace_eq_span_ladderIterateUp` of
`SaturatedLadderJointEigenspace`, at the explicit value `S_max(S_max + 1)`, which this module
does not use; the maximal-eigenvalue reading is
`totalSpinSSquared_maximal_eigenvector_mem_span_ladderIterateUp` of
`MaximalCasimirEigenvectorSpan`. -/
theorem heisenbergHamiltonianS_eigenspace_eq_satFerroJointEigenspace_of_connected_ferro
    {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (hN : 1 ≤ N) :
    Module.End.eigenspace ((heisenbergHamiltonianS J N).mulVecLin)
        (saturatedFerromagnetEigenvalueS (V := V) J N)
      = saturatedFerromagnetJointEigenspace (V := V) J N := by
  haveI : Nonempty V := hGconn.nonempty
  exact (heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro
      hGconn hJ_real hJ_sym hJ_supp hJ_ferro hN).trans
    (saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp J).symm

/-- **The printed ground-state energy `E_GS = -|B| S²`** (Tasaki §2.4, p. 32, stated in the
prose immediately below eq. (2.4.5)).

For the printed uniform coupling of eq. (2.4.1) -- weight `-1/2` on every bond of `G`, which is
`Ĥ = -∑_{{x,y} ∈ B} Ŝ_x · Ŝ_y` in the repo's ordered double-sum encoding -- the
saturated-ferromagnet energy is `-|B| S²` with `|B| = #G.edgeFinset` and `S = N/2`.

Unconditional: the diagonal branch of `saturatedFerromagnetEigenvalueS_explicit` is killed by
`couplingOf_self`, and the remaining constant factors out of the ordered double sum, which
`couplingOf_sum` evaluates as `2 |B|`. -/
theorem saturatedFerromagnetEigenvalueS_couplingOf_neg_half
    (G : SimpleGraph V) [DecidableRel G.Adj] (N : ℕ) :
    saturatedFerromagnetEigenvalueS (V := V) (couplingOf G (-(1/2) : ℂ)) N
      = -(G.edgeFinset.card : ℂ) * ((N : ℂ) / 2) ^ 2 := by
  rw [saturatedFerromagnetEigenvalueS_explicit]
  have hdiag : ∀ x y : V,
      couplingOf G (-(1/2) : ℂ) x y * (if x = y then (N : ℂ) * (N + 2) / 4
          else (N : ℂ) / 2 * ((N : ℂ) / 2))
        = couplingOf G (-(1/2) : ℂ) x y * ((N : ℂ) / 2 * ((N : ℂ) / 2)) := by
    intro x y
    by_cases hxy : x = y
    · subst hxy
      rw [couplingOf_self, zero_mul, zero_mul]
    · rw [if_neg hxy]
  simp_rw [hdiag, ← Finset.sum_mul]
  rw [couplingOf_sum]
  ring

/-- **Tasaki §2.4 Theorem 2.1, p. 34, as printed.**

For the ferromagnetic spin-`S` Heisenberg model `Ĥ = -∑_{{x,y} ∈ B} Ŝ_x · Ŝ_y` of eq. (2.4.1),
p. 32, on a connected lattice with `S ≥ 1/2`: the ground-state energy is `E_GS = -|B| S²`, the
ground states are exactly the linear combinations of the ladder family `Φ_M` of eq. (2.4.9),
p. 33, and there are `2 S_max + 1 = |V|·N + 1` of them independently -- eq. (2.4.10), p. 34.

The three conjuncts are, in order, minimality of `E_GS` (`Ĥ - E_GS ≥ 0`, the frustration-free
bound of Lemma A.9, p. 469), the eigenspace identification, and the degeneracy count; the first
is what makes the second a statement about *ground* states rather than about some eigenvalue.
The book's hypotheses on the coupling are all discharged from `couplingOf`, `hJ_sym` included,
so this statement assumes only connectedness and `1 ≤ N`. -/
theorem tasaki_theorem_2_1_ferromagnetic_ground_states
    (G : SimpleGraph V) [DecidableRel G.Adj] (hGconn : G.Connected) (hN : 1 ≤ N) :
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
          = Fintype.card V * N + 1 := by
  have hJ_real : ∀ x y : V, (couplingOf G (-(1/2) : ℂ) x y).im = 0 := by
    intro x y
    unfold couplingOf
    by_cases h : G.Adj x y
    · rw [if_pos h]; norm_num
    · rw [if_neg h, Complex.zero_im]
  have hJ_supp : ∀ x y : V, ¬ G.Adj x y → couplingOf G (-(1/2) : ℂ) x y = 0 := by
    intro x y h
    unfold couplingOf
    rw [if_neg h]
  have hJ_ferro : ∀ x y : V, G.Adj x y → (couplingOf G (-(1/2) : ℂ) x y).re < 0 := by
    intro x y h
    unfold couplingOf
    rw [if_pos h]
    norm_num
  have henergy := saturatedFerromagnetEigenvalueS_couplingOf_neg_half (V := V) G N
  refine ⟨?_, ?_, ?_⟩
  · have hJ_nonpos : ∀ x y : V, (couplingOf G (-(1/2) : ℂ) x y).re ≤ 0 := by
      intro x y
      by_cases h : G.Adj x y
      · exact (hJ_ferro x y h).le
      · rw [hJ_supp x y h, Complex.zero_re]
    have hre : (saturatedFerromagnetEigenvalueS (V := V) (couplingOf G (-(1/2) : ℂ)) N).re
        = -(G.edgeFinset.card : ℝ) * ((N : ℝ) / 2) ^ 2 := by
      rw [henergy, show (-(G.edgeFinset.card : ℂ) * ((N : ℂ) / 2) ^ 2)
          = ((-(G.edgeFinset.card : ℝ) * ((N : ℝ) / 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.ofReal_re]
    rw [← hre]
    exact heisenbergHamiltonianS_sub_saturatedFerromagnetEigenvalueS_posSemidef hJ_real
      hJ_nonpos (couplingOf_self G _) hN
  · rw [← henergy]
    exact heisenbergHamiltonianS_eigenspace_eq_span_ladderIterateUp_of_connected_ferro
      hGconn hJ_real (couplingOf_symm G _) hJ_supp hJ_ferro hN
  · rw [← henergy]
    exact heisenbergHamiltonianS_eigenspace_finrank_eq_of_connected_ferro
      hGconn hJ_real (couplingOf_symm G _) hJ_supp hJ_ferro hN

end LatticeSystem.Quantum
