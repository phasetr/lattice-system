import LatticeSystem.Fermion.JordanWigner.Hubbard.MielkeTheorems
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Combinatorics.SimpleGraph.Coloring
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
`SimpleGraph.incMatrix_mul_transpose` already identifies it.  This file carries the
proof through to the flat-band dimension:

* `mielkeIncidence_conjTranspose_mul_self`: the `SᴴS` identity (eqs. (11.3.36)–(11.3.39));
* `mielke_lineGraph_ker_finrank_eq`: the rank step `dim ker T = |B| − rank S` (Lemma 11.14);
* `mielke_conjTranspose_ker_finrank`: the signless-Laplacian zero-mode count
  `dim ker(SSᴴ) = (bipartite ? 1 : 0)` for a connected base (eq. (11.3.41)), proved by
  working directly with `ker Sᴴ` (`(Sᴴ x)_b = √t(x_u + x_v)`) — bipartite gives the
  one-dimensional span of the alternating sign vector, non-bipartite the trivial kernel;
* `mielke_lineGraph_ker_finrank_eq_dim`: the assembled flat-band dimension `D(Λ̃,B)`
  (Tasaki Theorem 11.12, general base form, to be transported to the `Fin (M+1)` axiom).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), §11.3.3, eqs. (11.3.36)–(11.3.41).
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

/-! ### The signless-Laplacian zero-mode count (Tasaki eq. (11.3.41))

`SSᴴ = t·(D + A)` is the *signless graph Laplacian* of the base lattice (mathlib has
only the ordinary signed Laplacian `L = D − A`).  Rather than build the signless
Laplacian, we work directly with `ker Sᴴ`: `(Sᴴ x)_b = √t (x_u + x_v)` for the edge
`b = {u,v}`, so for `t > 0` the kernel is `{x : ∀ adjacent u,v, x_u + x_v = 0}`.  For a
connected base this kernel is the alternating `±1` sign vector of a 2-colouring
(`dim = 1`) when bipartite, and is trivial (`dim = 0`) otherwise — eq. (11.3.41). -/

/-- For an edge `{u,v}`, `Σ_a S_{a,·}·x_a` collects the two endpoints: `x u + x v`. -/
private lemma sum_incMatrix_mul_endpoints (x : V → ℂ) {u v : V} (huv : G.Adj u v) :
    (∑ a, G.incMatrix ℂ a s(u, v) * x a) = x u + x v := by
  have hne := G.ne_of_adj huv
  have hstep : ∀ a, G.incMatrix ℂ a s(u, v) * x a = if a = u ∨ a = v then x a else 0 := by
    intro a
    rw [incMatrix_apply']
    simp only [mk'_mem_incidenceSet_iff, huv, true_and]
    split_ifs <;> simp
  have hsplit : ∀ a, (if a = u ∨ a = v then x a else 0)
      = (if a = u then x a else 0) + (if a = v then x a else 0) := fun a => by
    by_cases hu : a = u <;> by_cases hv : a = v <;> simp_all
  calc (∑ a, G.incMatrix ℂ a s(u, v) * x a)
      = ∑ a, ((if a = u then x a else 0) + (if a = v then x a else 0)) :=
        Finset.sum_congr rfl fun a _ => (hstep a).trans (hsplit a)
    _ = x u + x v := by
        rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ u x,
          Finset.sum_ite_eq' Finset.univ v x, if_pos (Finset.mem_univ u),
          if_pos (Finset.mem_univ v)]

/-- The entry of `Sᴴ x` at an edge `e = {u,v}` is `√t·(x_u + x_v)`. -/
private lemma mielkeIncidence_conjTranspose_mulVec_apply (t : ℝ) (x : V → ℂ)
    (e : G.edgeSet) :
    ((mielkeIncidence G t)ᴴ *ᵥ x) e
      = (Real.sqrt t : ℂ) * ∑ a, G.incMatrix ℂ a (e : Sym2 V) * x a := by
  have hst : star (Real.sqrt t : ℂ) = (Real.sqrt t : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [show ((mielkeIncidence G t)ᴴ *ᵥ x) e = ∑ a, ((mielkeIncidence G t)ᴴ) e a * x a from rfl,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.conjTranspose_apply, mielkeIncidence, Matrix.smul_apply,
    Matrix.submatrix_apply, id_eq, smul_eq_mul, star_mul', incMatrix_complex_star, hst]
  ring

/-- **Kernel of `Sᴴ`** (for `t > 0`): `Sᴴ x = 0` iff every edge has zero endpoint sum,
`x u + x v = 0` for all adjacent `u, v`. -/
theorem mielkeIncidence_conjTranspose_mulVec_eq_zero_iff (t : ℝ) (ht : 0 < t) (x : V → ℂ) :
    (mielkeIncidence G t)ᴴ *ᵥ x = 0 ↔ ∀ u v, G.Adj u v → x u + x v = 0 := by
  have hsqrt : (Real.sqrt t : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr ht).ne'
  constructor
  · intro h u v huv
    have he : s(u, v) ∈ G.edgeSet := huv
    have := congrFun h (⟨s(u, v), he⟩ : G.edgeSet)
    rw [mielkeIncidence_conjTranspose_mulVec_apply, Pi.zero_apply] at this
    have hsum := (mul_eq_zero.mp this).resolve_left hsqrt
    rwa [sum_incMatrix_mul_endpoints G x huv] at hsum
  · intro h
    funext e
    obtain ⟨e, he⟩ := e
    induction e using Sym2.ind with
    | _ u v =>
      rw [mielkeIncidence_conjTranspose_mulVec_apply, Pi.zero_apply,
        sum_incMatrix_mul_endpoints G x (G.mem_edgeSet.mp he), h u v (G.mem_edgeSet.mp he),
        mul_zero]

/-- The `±1` alternating sign vector of a 2-colouring `C` relative to a root `r`:
`+1` on `r`'s colour class, `−1` on the other.  It is the (essentially unique)
zero-energy mode of the signless Laplacian of a connected bipartite graph. -/
private noncomputable def mielkeAlt (C : G.Coloring (Fin 2)) (r : V) : V → ℂ :=
  fun w => if C w = C r then 1 else -1

omit [Fintype V] [DecidableRel G.Adj] in
/-- In `Fin 2`, distinct colours sit on opposite sides of any reference colour. -/
private lemma fin_two_ne_iff (a b c : Fin 2) (h : a ≠ b) : (a = c ↔ b ≠ c) := by
  revert h; revert a b c; decide

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The alternating vector has zero endpoint sum across every edge. -/
private lemma mielkeAlt_endpoint_sum (C : G.Coloring (Fin 2)) (r : V) {u v : V}
    (huv : G.Adj u v) : mielkeAlt G C r u + mielkeAlt G C r v = 0 := by
  have hC : C u ≠ C v := C.valid huv
  unfold mielkeAlt
  by_cases h : C u = C r
  · rw [if_pos h, if_neg ((fin_two_ne_iff (C u) (C v) (C r) hC).mp h)]; ring
  · rw [if_neg h]
    have hv : C v = C r :=
      not_not.mp fun hv => h ((fin_two_ne_iff (C u) (C v) (C r) hC).mpr hv)
    rw [if_pos hv]; ring

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **Sign propagation along the bipartite gauge.**  If every edge has zero endpoint
sum (`y ∈ ker Sᴴ`), then along any walk `y` is tied to the alternating vector:
`y b · alt a = y a · alt b`.  Specialised at the root this gives `y = (y r) • alt`. -/
private lemma ker_reachable_alt (C : G.Coloring (Fin 2)) (r : V) {y : V → ℂ}
    (hy : ∀ u v, G.Adj u v → y u + y v = 0) :
    ∀ a b, G.Reachable a b →
      y b * mielkeAlt G C r a = y a * mielkeAlt G C r b := by
  intro a b ⟨p⟩
  induction p with
  | nil => ring
  | cons hadj _ ih =>
      have h1 := hy _ _ hadj
      have h2 := mielkeAlt_endpoint_sum G C r hadj
      rw [eq_neg_of_add_eq_zero_left h2, eq_neg_of_add_eq_zero_left h1]
      linear_combination -ih

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- **Two-valued sign propagation.**  If every edge has zero endpoint sum, then along
any walk `y b = ± y a`.  Used (contrapositively) to build a 2-colouring from a
nonzero kernel vector, ruling out flat-band modes for non-bipartite graphs. -/
private lemma ker_reachable_sign {y : V → ℂ}
    (hy : ∀ u v, G.Adj u v → y u + y v = 0) :
    ∀ a b, G.Reachable a b → y b = y a ∨ y b = - y a := by
  intro a b ⟨p⟩
  induction p with
  | nil => exact Or.inl rfl
  | cons hadj _ ih =>
      have h1 := hy _ _ hadj
      rcases ih with h | h
      · exact Or.inr (by linear_combination h + h1)
      · exact Or.inl (by linear_combination h - h1)

open Classical in
/-- **The signless-Laplacian zero-mode count** (Tasaki eq. (11.3.41)).  For a connected
base graph and `t > 0`, the flat-band dimension `dim ker(SSᴴ) = dim ker Sᴴ` is `1` if
the graph is bipartite (`Colorable 2`) and `0` otherwise.  Bipartite: the kernel is the
one-dimensional span of the alternating `±1` vector; non-bipartite: any nonzero kernel
vector would 2-colour the graph, so the kernel is trivial. -/
theorem mielke_conjTranspose_ker_finrank (t : ℝ) (ht : 0 < t) (hconn : G.Connected) :
    Module.finrank ℂ (LinearMap.ker (mielkeIncidence G t)ᴴ.mulVecLin)
      = if G.Colorable 2 then 1 else 0 := by
  have hmem : ∀ y : V → ℂ, y ∈ LinearMap.ker (mielkeIncidence G t)ᴴ.mulVecLin
      ↔ ∀ u v, G.Adj u v → y u + y v = 0 := fun y => by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      mielkeIncidence_conjTranspose_mulVec_eq_zero_iff G t ht]
  obtain ⟨r⟩ := hconn.nonempty
  by_cases hbip : G.Colorable 2
  · rw [if_pos hbip]
    obtain ⟨C⟩ := hbip
    have halt1 : mielkeAlt G C r r = 1 := by simp [mielkeAlt]
    have halt0 : mielkeAlt G C r ≠ 0 := fun h => by
      have := halt1; rw [h] at this; simp at this
    have hker_eq : LinearMap.ker (mielkeIncidence G t)ᴴ.mulVecLin = ℂ ∙ mielkeAlt G C r := by
      refine le_antisymm (fun y hy => ?_) ?_
      · rw [hmem] at hy
        rw [Submodule.mem_span_singleton]
        refine ⟨y r, funext fun w => ?_⟩
        have hkey := ker_reachable_alt G C r hy r w (hconn.preconnected r w)
        rw [halt1, mul_one] at hkey
        simp only [Pi.smul_apply, smul_eq_mul]
        exact hkey.symm
      · rw [Submodule.span_singleton_le_iff_mem, hmem]
        exact fun u v huv => mielkeAlt_endpoint_sum G C r huv
    rw [hker_eq, finrank_span_singleton halt0]
  · rw [if_neg hbip]
    have hbot : LinearMap.ker (mielkeIncidence G t)ᴴ.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [hmem] at hy
      by_contra hy0
      obtain ⟨r', hr⟩ : ∃ r', y r' ≠ 0 := by
        by_contra h
        simp only [not_exists, ne_eq, not_not] at h
        exact hy0 (funext h)
      refine hbip ⟨SimpleGraph.Coloring.mk
        (fun w => if y w = y r' then (0 : Fin 2) else 1) ?_⟩
      intro u v huv
      dsimp only
      have hsu := ker_reachable_sign G hy r' u (hconn.preconnected r' u)
      have hsv := ker_reachable_sign G hy r' v (hconn.preconnected r' v)
      have huv0 := hy u v huv
      rcases hsu with hu | hu <;> rcases hsv with hv | hv
      · exact absurd (show y r' = 0 by linear_combination (huv0 - hu - hv) / 2) hr
      · rw [if_pos hu, if_neg (fun heq => hr (show y r' = 0 by linear_combination (hv - heq) / 2))]
        decide
      · rw [if_neg (fun heq => hr (show y r' = 0 by linear_combination (hu - heq) / 2)), if_pos hv]
        decide
      · exact absurd (show y r' = 0 by linear_combination (hu + hv - huv0) / 2) hr
    rw [hbot, finrank_bot]

open Classical in
open scoped ComplexOrder in
/-- **Tasaki Theorem 11.12 (general base form)**: for a connected base graph `G` and
`t > 0`, the flat-band dimension of the line-graph single-electron operator is
`D(Λ̃,B) = |B| − (|Λ̃| − (bipartite ? 1 : 0))` (eqs. (11.3.39)/(11.3.41)).  Combines the
rank step `dim ker T = |B| − rank S` (PR3) with `rank S = |Λ̃| − dim ker(SSᴴ)`
(`rank_self_mul_conjTranspose` + rank–nullity) and the signless-Laplacian zero-mode
count `dim ker(SSᴴ) = (bipartite ? 1 : 0)`.

The closed form is written `|B| − (|Λ̃| − bip)` rather than Tasaki's `|B| − |Λ̃| + bip`
to remain sound under truncated `ℕ` subtraction: the two agree exactly when `|Λ̃| ≤ |B|`
(true once the base graph has a cycle, e.g. the relevant flat-band lattices), but the
`|B| − |Λ̃| + bip` form over-counts by `bip` for a tree (`|B| = |Λ̃| − 1`).  Since
`rank S ≤ |Λ̃|`, the form here equals `|B| − rank S` unconditionally.  The `Fin (M+1)`
realisation of `mielke_theorem_11_12` follows by transporting along the line-graph
isomorphism (PR5). -/
theorem mielke_lineGraph_ker_finrank_eq_dim (t : ℝ) (ht : 0 < t) (hconn : G.Connected) :
    Module.finrank ℂ (LinearMap.ker (mielkeSingleElectronOpOn G.lineGraph t).mulVecLin)
      = Fintype.card G.edgeSet - (Fintype.card V - (if G.Colorable 2 then 1 else 0)) := by
  have hpr3 := mielke_lineGraph_ker_finrank_eq G t ht.le
  have hcount := mielke_conjTranspose_ker_finrank G t ht hconn
  have hrn := LinearMap.finrank_range_add_finrank_ker (mielkeIncidence G t)ᴴ.mulVecLin
  have hdomV : Module.finrank ℂ (V → ℂ) = Fintype.card V := Module.finrank_pi ℂ
  rw [hdomV] at hrn
  have hrankH : (mielkeIncidence G t)ᴴ.rank
      = Module.finrank ℂ (LinearMap.range (mielkeIncidence G t)ᴴ.mulVecLin) := rfl
  have hrankeq : (mielkeIncidence G t)ᴴ.rank = (mielkeIncidence G t).rank :=
    Matrix.rank_conjTranspose _
  rw [hpr3, ← hcount]
  omega

/-- **Tasaki Theorem 11.12 (flat band in a general line graph), now a theorem.**  For a
connected base lattice `(Λ̃,B̃)` with at least as many edges as vertices (`hedge`, i.e.
the base has a cycle — automatic for any genuine flat-band lattice; a connected graph
violating it is a tree, which has no flat band), any concrete realisation `G` on
`Fin (M+1)` of its line graph has single-electron flat band of dimension exactly
`D(Λ̃,B̃) = mielkeFlatBandDim`.  This discharges the former `mielke_theorem_11_12`
axiom (§11.3.2): the kernel dimension is transported from the abstract line graph
`Gbase.lineGraph` (where `mielke_lineGraph_ker_finrank_eq_dim` computes it) to `G` along
the graph isomorphism, since reindexing a matrix by an equivalence preserves its rank
(`Matrix.rank_submatrix`) and hence its kernel dimension.  The `hedge` hypothesis is
exactly the condition under which Tasaki's `|B|−|Λ̃|+1` form equals the true dimension
`|B|−(|Λ̃|−1)` (no `ℕ`-truncation). -/
theorem mielke_theorem_11_12 {Nbase M : ℕ} (Gbase : SimpleGraph (Fin (Nbase + 1)))
    [DecidableRel Gbase.Adj] (G : SimpleGraph (Fin (M + 1))) [DecidableRel G.Adj]
    (t : ℝ) (ht : 0 < t) (hconn : Gbase.Connected)
    (hLG : Nonempty (SimpleGraph.Iso G Gbase.lineGraph))
    (hedge : Nbase + 1 ≤ Gbase.edgeFinset.card) :
    Module.finrank ℂ (LinearMap.ker (mielkeSingleElectronOp G t).mulVecLin) =
      mielkeFlatBandDim Gbase := by
  obtain ⟨e⟩ := hLG
  -- the operator on `G` is the line-graph operator reindexed by the isomorphism
  have hcorr : mielkeSingleElectronOpOn G t
      = (mielkeSingleElectronOpOn Gbase.lineGraph t).submatrix e.toEquiv e.toEquiv := by
    ext i j
    have hadj : Gbase.lineGraph.Adj (e.toEquiv i) (e.toEquiv j) ↔ G.Adj i j := e.map_adj_iff
    simp only [mielkeSingleElectronOpOn, Matrix.add_apply, Matrix.of_apply, couplingOf,
      Matrix.smul_apply, Matrix.one_apply, Matrix.submatrix_apply, smul_eq_mul,
      hadj, EmbeddingLike.apply_eq_iff_eq]
  -- reindexing preserves rank, hence (with equal cardinalities) kernel dimension
  have hrank : (mielkeSingleElectronOpOn G t).rank
      = (mielkeSingleElectronOpOn Gbase.lineGraph t).rank := by
    rw [hcorr, Matrix.rank_submatrix]
  have hcard : Fintype.card (Fin (M + 1)) = Fintype.card Gbase.edgeSet :=
    Fintype.card_congr e.toEquiv
  have key : Module.finrank ℂ (LinearMap.ker (mielkeSingleElectronOpOn G t).mulVecLin)
      = Module.finrank ℂ
          (LinearMap.ker (mielkeSingleElectronOpOn Gbase.lineGraph t).mulVecLin) := by
    have hrnG := LinearMap.finrank_range_add_finrank_ker (mielkeSingleElectronOpOn G t).mulVecLin
    have hrnLG := LinearMap.finrank_range_add_finrank_ker
      (mielkeSingleElectronOpOn Gbase.lineGraph t).mulVecLin
    rw [Module.finrank_pi ℂ] at hrnG hrnLG
    have hr1 : (mielkeSingleElectronOpOn G t).rank
        = Module.finrank ℂ (LinearMap.range (mielkeSingleElectronOpOn G t).mulVecLin) := rfl
    have hr2 : (mielkeSingleElectronOpOn Gbase.lineGraph t).rank
        = Module.finrank ℂ
            (LinearMap.range (mielkeSingleElectronOpOn Gbase.lineGraph t).mulVecLin) := rfl
    omega
  have hdimLG := mielke_lineGraph_ker_finrank_eq_dim Gbase t ht hconn
  rw [show mielkeSingleElectronOp G t = mielkeSingleElectronOpOn G t from rfl, key, hdimLG]
  unfold mielkeFlatBandDim
  rw [SimpleGraph.edgeFinset_card, Fintype.card_fin]
  rw [SimpleGraph.edgeFinset_card] at hedge
  split_ifs <;> omega

end LatticeSystem.Fermion
