import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Tasaki §11.3.3: the Mielke incidence matrix and the `SᴴS` factorisation

The proof of Theorem 11.12 (the flat band of a line graph) rests on the
factorisation of the line-graph single-electron operator through the *incidence
matrix* `S` of the base lattice `(Λ̃,B̃)` (Tasaki eqs. (11.3.36)–(11.3.39)):

`S` is the `Λ̃ × B̃` matrix with `S_{x,b} = √t` if the vertex `x` is an endpoint of
the edge `b`, and `0` otherwise.  Its Gram matrix `T = SᴴS` (a `B̃ × B̃` matrix,
indexed by the edges = the vertices of the line graph) is exactly the Mielke
single-electron operator on the line graph,

`(SᴴS)_{b,b'} = t·(2·δ_{b,b'} + [b,b' share a vertex, b ≠ b'])
            = 2t·δ_{b,b'} + t·(adjacency of the line graph)`,

i.e. `mielkeSingleElectronOpOn (lineGraph) t`.  The companion matrix `T̃ = SSᴴ`
(a `Λ̃ × Λ̃` matrix) is the *signless Laplacian* of the base lattice; mathlib's
`SimpleGraph.incMatrix_mul_transpose` already identifies it.  Lemma 11.14 (`T` and
`T̃` have the same nonzero spectrum) and the bipartite zero-mode count (11.3.41)
are treated in the following PRs of this thread; this file supplies the basic
`SᴴS` identity.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.3, eqs. (11.3.36)–(11.3.39).
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Lattice SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Adjacency in the line graph is decidable: `e₁ ~ e₂` iff `e₁ ≠ e₂` and some vertex
lies in both edges, a decidable condition over a finite vertex type. -/
instance lineGraph_decidableRelAdj : DecidableRel G.lineGraph.Adj := fun _ _ =>
  decidable_of_iff _ lineGraph_adj_iff_exists.symm

/-- **The Mielke incidence matrix `S`** of a base lattice `G` (Tasaki eq. (11.3.36)):
the `V × B` matrix (`B = G.edgeSet`) with `S_{x,b} = √t` when the vertex `x` is an
endpoint of the edge `b`, and `0` otherwise.  It is `√t` times mathlib's incidence
matrix, restricted to the genuine edges as columns. -/
noncomputable def mielkeIncidence (t : ℝ) : Matrix V G.edgeSet ℂ :=
  (Real.sqrt t : ℂ) • (G.incMatrix ℂ).submatrix id (fun e : G.edgeSet => (e : Sym2 V))

omit [Fintype V] in
/-- Incidence-matrix entries (`0` or `1`) are fixed by complex conjugation. -/
private lemma incMatrix_complex_star (a : V) (e : Sym2 V) :
    star (G.incMatrix ℂ a e) = G.incMatrix ℂ a e := by
  rw [incMatrix_apply']; split_ifs <;> simp

/-- The Gram matrix of the incidence matrix, entrywise: `(SᴴS)_{e₁,e₂}` equals
`t` times the number of common endpoints of the edges `e₁`, `e₂`. -/
private lemma mielkeIncidence_conjTranspose_mul_self_apply (t : ℝ) (ht : 0 ≤ t)
    (e₁ e₂ : G.edgeSet) :
    ((mielkeIncidence G t)ᴴ * mielkeIncidence G t) e₁ e₂
      = (t : ℂ) * ∑ a, G.incMatrix ℂ a (e₁ : Sym2 V) * G.incMatrix ℂ a (e₂ : Sym2 V) := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hsq : (Real.sqrt t : ℂ) * (Real.sqrt t : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht]
  have hst : star (Real.sqrt t : ℂ) = (Real.sqrt t : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simp only [Matrix.conjTranspose_apply, mielkeIncidence, Matrix.smul_apply,
    Matrix.submatrix_apply, id_eq, smul_eq_mul, star_mul', incMatrix_complex_star, hst]
  rw [mul_mul_mul_comm, hsq]

/-- The number of common endpoints of two edges: `2` if they are equal, `1` if they
are adjacent in the line graph (share exactly one vertex), and `0` otherwise. -/
private lemma sum_incMatrix_pair (e₁ e₂ : G.edgeSet) :
    (∑ a, G.incMatrix ℂ a (e₁ : Sym2 V) * G.incMatrix ℂ a (e₂ : Sym2 V))
      = if e₁ = e₂ then 2 else if G.lineGraph.Adj e₁ e₂ then 1 else 0 := by
  by_cases heq : e₁ = e₂
  · subst heq
    rw [if_pos rfl,
      show (∑ a, G.incMatrix ℂ a (e₁ : Sym2 V) * G.incMatrix ℂ a (e₁ : Sym2 V))
        = ∑ a, G.incMatrix ℂ a (e₁ : Sym2 V) from
        Finset.sum_congr rfl fun a _ => by rw [incMatrix_apply']; split_ifs <;> simp]
    exact_mod_cast G.sum_incMatrix_apply_of_mem_edgeSet (R := ℂ) e₁.2
  · rw [if_neg heq]
    have hterm : ∀ a, G.incMatrix ℂ a (e₁ : Sym2 V) * G.incMatrix ℂ a (e₂ : Sym2 V)
        = if a ∈ (e₁ : Sym2 V) ∧ a ∈ (e₂ : Sym2 V) then 1 else 0 := by
      intro a
      rw [incMatrix_apply', incMatrix_apply']
      simp only [G.edge_mem_incidenceSet_iff]
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_boole]
    by_cases hadj : G.lineGraph.Adj e₁ e₂
    · rw [if_pos hadj]
      obtain ⟨-, v, hv₁, hv₂⟩ := lineGraph_adj_iff_exists.mp hadj
      have hcard : (Finset.univ.filter
          (fun a => a ∈ (e₁ : Sym2 V) ∧ a ∈ (e₂ : Sym2 V))).card = 1 := by
        refine le_antisymm (Finset.card_le_one.mpr ?_) (Finset.one_le_card.mpr ?_)
        · intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          by_contra hab
          exact heq (Subtype.ext (((Sym2.mem_and_mem_iff hab).mp ⟨ha.1, hb.1⟩).trans
            ((Sym2.mem_and_mem_iff hab).mp ⟨ha.2, hb.2⟩).symm))
        · exact ⟨v, by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hv₁, hv₂⟩⟩
      rw [hcard, Nat.cast_one]
    · rw [if_neg hadj, Finset.filter_false_of_mem fun a _ ha =>
        hadj (lineGraph_adj_iff_exists.mpr ⟨heq, a, ha.1, ha.2⟩),
        Finset.card_empty, Nat.cast_zero]

/-- **The Mielke `SᴴS` factorisation** (Tasaki eqs. (11.3.36)–(11.3.39)): for `t ≥ 0`,
the Gram matrix `SᴴS` of the base-lattice incidence matrix is exactly the Mielke
single-electron operator on the line graph, `2t·I + t·(adjacency of the line graph)`.
This is the algebraic core of Theorem 11.12: it presents the line-graph operator as a
manifestly positive-semidefinite Gram matrix whose kernel is `ker S`. -/
theorem mielkeIncidence_conjTranspose_mul_self (t : ℝ) (ht : 0 ≤ t) :
    (mielkeIncidence G t)ᴴ * mielkeIncidence G t
      = mielkeSingleElectronOpOn G.lineGraph t := by
  ext e₁ e₂
  rw [mielkeIncidence_conjTranspose_mul_self_apply G t ht, sum_incMatrix_pair G e₁ e₂]
  simp only [mielkeSingleElectronOpOn, Matrix.add_apply, Matrix.of_apply, couplingOf,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases heq : e₁ = e₂
  · subst heq
    rw [if_pos rfl, if_pos rfl, if_neg G.lineGraph.irrefl]
    ring
  · rw [if_neg heq, if_neg heq]
    by_cases hadj : G.lineGraph.Adj e₁ e₂ <;> simp [hadj]

open scoped ComplexOrder in
/-- **Rank–nullity for the line-graph flat band** (Tasaki §11.3.3, the rank step of
Lemma 11.14): for `t ≥ 0`, the dimension of the zero-energy (flat-band) subspace of
the line-graph single-electron operator equals the number of edges minus the rank of
the incidence matrix `S`,
`dim ker T = |B| − rank S`  (where `T = SᴴS`).
This uses the `SᴴS` factorisation together with mathlib's
`ker_mulVecLin_conjTranspose_mul_self` (`ker SᴴS = ker S`, so the kernels coincide) and
rank–nullity for `S`.  The subsequent step (PR 4) identifies `rank S = |Λ̃| − dim ker(SSᴴ)`
with `dim ker(SSᴴ) = (bipartite ? 1 : 0)` for a connected base, yielding `D(Λ̃,B̃)`. -/
theorem mielke_lineGraph_ker_finrank_eq (t : ℝ) (ht : 0 ≤ t) :
    Module.finrank ℂ (LinearMap.ker (mielkeSingleElectronOpOn G.lineGraph t).mulVecLin)
      = Fintype.card G.edgeSet - (mielkeIncidence G t).rank := by
  rw [← mielkeIncidence_conjTranspose_mul_self G t ht,
    Matrix.ker_mulVecLin_conjTranspose_mul_self]
  have hdom : Module.finrank ℂ (G.edgeSet → ℂ) = Fintype.card G.edgeSet := Module.finrank_pi ℂ
  have hrn := LinearMap.finrank_range_add_finrank_ker (mielkeIncidence G t).mulVecLin
  have hrank : (mielkeIncidence G t).rank
      = Module.finrank ℂ (LinearMap.range (mielkeIncidence G t).mulVecLin) := rfl
  rw [hdom] at hrn
  omega

end LatticeSystem.Fermion
