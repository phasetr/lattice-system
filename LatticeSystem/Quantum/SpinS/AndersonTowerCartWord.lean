import LatticeSystem.Quantum.SpinS.AndersonTowerSphereMoment

/-!
# Tasaki §4.2.2 Proposition 4.10: Cartesian order words and the single-swap difference

The ordered product `∏_j ô^{(f j)}` of staggered axis operators appearing in the operator expansion
of the sphere average (Tasaki eq. (4.2.59), `sphereAverage_directionStaggeredOp_pow`) is repackaged
as a **Cartesian order word** `cartWord w` indexed by an axis word `w : List (Fin 3)`.  This is the
three-axis (`Fin 3`) analogue of the `Bool` ladder word `orderWordProd` used for Theorem 4.6; it
carries the same `cons`/`append` recursions and the purely algebraic **single-swap factorization**

`ô^{pre ++ α::β::suf} − ô^{pre ++ β::α::suf} = ô^{pre} · [ô^{(α)}, ô^{(β)}] · ô^{suf}`,

which begins the swap-band contraction reducing the ordered product to the grouped `(ô²)^{M/2}` main
part.  Only the operator-level identity is established here (no expectation, no telescoping); the
commutator contraction and expectation telescoping are the next step of the argument (PR-3.2b).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.2.2, eq. (4.2.59), p.108; cf. Tasaki, arXiv:1807.05847.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- The **Cartesian order word product** `ô^{w} = ∏_j ô^{(w_j)}`: the ordered product of the
axis-indexed staggered order operators `stagOpVec` along an axis word `w : List (Fin 3)`.  This is
the `Fin 3` (three-axis) analogue of the `Bool` ladder word `orderWordProd`, matching the literal
ordered product in Tasaki eq. (4.2.59) (`sphereAverage_directionStaggeredOp_pow`). -/
noncomputable def cartWord (A : Λ → Bool) (N : ℕ) (w : List (Fin 3)) : ManyBodyOpS Λ N :=
  (w.map (stagOpVec A N)).prod

/-- Cons recursion for the Cartesian word product: `ô^{α::w} = ô^{(α)} · ô^{w}`. -/
theorem cartWord_cons (A : Λ → Bool) (N : ℕ) (α : Fin 3) (w : List (Fin 3)) :
    cartWord A N (α :: w) = stagOpVec A N α * cartWord A N w := by
  rw [cartWord, cartWord, List.map_cons, List.prod_cons]

/-- Append recursion for the Cartesian word product: `ô^{w ++ w'} = ô^{w} · ô^{w'}`. -/
theorem cartWord_append (A : Λ → Bool) (N : ℕ) (w w' : List (Fin 3)) :
    cartWord A N (w ++ w') = cartWord A N w * cartWord A N w' := by
  rw [cartWord, cartWord, cartWord, List.map_append, List.prod_append]

/-- Bridge to the ordered product of Tasaki eq. (4.2.59): the Cartesian word over `List.ofFn f`
is the literal ordered product `∏_j ô^{(f j)}` of `sphereAverage_directionStaggeredOp_pow`. -/
theorem cartWord_ofFn (A : Λ → Bool) (N M : ℕ) (f : Fin M → Fin 3) :
    cartWord A N (List.ofFn f) = (List.ofFn fun j => stagOpVec A N (f j)).prod := by
  rw [cartWord, List.map_ofFn]
  rfl

/-- **Single-swap factorization** of the Cartesian order-word product difference:
`ô^{pre ++ α::β::suf} − ô^{pre ++ β::α::suf} = ô^{pre} · [ô^{(α)}, ô^{(β)}] · ô^{suf}`.  Purely
algebraic (`noncomm_ring`); the commutator `[ô^{(α)}, ô^{(β)}] = i ε_{αβγ} Ŝ^{(γ)}_tot` is
contracted in the swap-band telescoping (PR-3.2b). -/
theorem cartWord_swap_diff_eq (A : Λ → Bool) (N : ℕ) (pre suf : List (Fin 3)) (α β : Fin 3) :
    cartWord A N (pre ++ α :: β :: suf) - cartWord A N (pre ++ β :: α :: suf)
      = cartWord A N pre
        * (stagOpVec A N α * stagOpVec A N β - stagOpVec A N β * stagOpVec A N α)
        * cartWord A N suf := by
  have hexp : ∀ γ δ : Fin 3, cartWord A N (pre ++ γ :: δ :: suf)
      = cartWord A N pre * (stagOpVec A N γ * stagOpVec A N δ) * cartWord A N suf := by
    intro γ δ
    simp only [cartWord, List.map_append, List.map_cons, List.prod_append, List.prod_cons]
    noncomm_ring
  rw [hexp, hexp, ← sub_mul, ← mul_sub]

end LatticeSystem.Quantum
