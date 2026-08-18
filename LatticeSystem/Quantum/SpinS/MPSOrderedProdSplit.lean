import LatticeSystem.Quantum.SpinS.MPSTheorem76Algebra
import LatticeSystem.Quantum.SpinS.TwoSiteConfig

/-!
# Splitting an ordered MPS product at a bond

Generic matrix-product-state algebra, with no reference to any concrete model: the ordered product
`A^{σ_0} A^{σ_1} ⋯ A^{σ_{L-1}}` along an `ofFn` word factorizes at an **open** bond
`{x, x+1}` (`x.val + 1 < L`) as

`orderedProd A (ofFn σ) = P · (A^{σ_x} A^{σ_{x+1}}) · Q`,

where the prefix `P` and the suffix `Q` are the ordered products over the sites strictly left of `x`
and strictly right of `x+1`.  Together with the two congruence lemmas — gluing a two-site
configuration into the bond leaves the prefix and the suffix untouched — this is what turns a
two-site bond slice of an *open* matrix-product state into a linear functional of the two-site
tensor `A^{a_0} A^{a_1}` alone.

The periodic counterpart (a bond slice of the *trace* state is `a ↦ tr(A^{a_0}A^{a_1} R)`) lives in
`AKLTKnabe.FrustrationFreeD7c` and is proved by ring rotation instead; the open chain has no
rotation, so the split has to be done at the level of the list index, which is what this module
provides.
-/

namespace LatticeSystem.Quantum

open Matrix

variable {D N L : ℕ}

/-- **Bond split of an ordered MPS product.**  At an open bond `{x, x+1}` of the word `ofFn σ`
(`x.val + 1 < L`, so the bond does not wrap around), the ordered product factorizes into the
prefix product over the sites `< x`, the two-site tensor `A^{σ_x} A^{σ_{x+1}}`, and the suffix
product over the sites `> x + 1`. -/
theorem orderedProd_ofFn_bond_split (A : MPSMatrices D N) (σ : Fin L → Fin (N + 1))
    (x : Fin L) (hx : x.val + 1 < L) :
    orderedProd A (List.ofFn σ)
      = orderedProd A ((List.ofFn σ).take x.val)
        * (A (σ x) * A (σ ⟨x.val + 1, hx⟩))
        * orderedProd A ((List.ofFn σ).drop (x.val + 2)) := by
  have hlen : (List.ofFn σ).length = L := by simp
  have h1 : (List.ofFn σ).drop x.val
      = (List.ofFn σ)[x.val]'(by rw [hlen]; exact x.isLt) :: (List.ofFn σ).drop (x.val + 1) :=
    List.drop_eq_getElem_cons (by rw [hlen]; exact x.isLt)
  have h2 : (List.ofFn σ).drop (x.val + 1)
      = (List.ofFn σ)[x.val + 1]'(by rw [hlen]; exact hx) :: (List.ofFn σ).drop (x.val + 2) :=
    List.drop_eq_getElem_cons (by rw [hlen]; exact hx)
  have hg1 : (List.ofFn σ)[x.val]'(by rw [hlen]; exact x.isLt) = σ x := by simp
  have hg2 : (List.ofFn σ)[x.val + 1]'(by rw [hlen]; exact hx) = σ ⟨x.val + 1, hx⟩ := by simp
  have hsplit : (List.ofFn σ).take x.val
      ++ ((List.ofFn σ)[x.val]'(by rw [hlen]; exact x.isLt)
        :: (List.ofFn σ)[x.val + 1]'(by rw [hlen]; exact hx)
        :: (List.ofFn σ).drop (x.val + 2))
      = List.ofFn σ := by
    rw [← h2, ← h1, List.take_append_drop]
  conv_lhs => rw [← hsplit]
  rw [orderedProd_append]
  simp only [orderedProd, hg1, hg2, Matrix.mul_assoc]

/-- Gluing a two-site configuration into the open bond `{x, x+1}` does not change the prefix word
of the sites strictly left of `x`. -/
theorem take_ofFn_glueTwoSitesS (x : Fin L) (hx : x.val + 1 < L)
    (a : Fin 2 → Fin (N + 1)) (τ : Fin L → Fin (N + 1)) :
    (List.ofFn (glueTwoSitesS x (⟨x.val + 1, hx⟩ : Fin L) a τ)).take x.val
      = (List.ofFn τ).take x.val := by
  refine List.ext_getElem (by simp) fun i h₁ _ => ?_
  have hi : i < x.val := by
    simp only [List.length_take, List.length_ofFn, Nat.lt_min] at h₁
    exact h₁.1
  simp only [List.getElem_take, List.getElem_ofFn, glueTwoSitesS]
  rw [if_neg (by simp only [Fin.ext_iff]; omega),
    if_neg (by simp only [Fin.ext_iff]; omega)]

/-- Gluing a two-site configuration into the open bond `{x, x+1}` does not change the suffix word
of the sites strictly right of `x + 1`. -/
theorem drop_ofFn_glueTwoSitesS (x : Fin L) (hx : x.val + 1 < L)
    (a : Fin 2 → Fin (N + 1)) (τ : Fin L → Fin (N + 1)) :
    (List.ofFn (glueTwoSitesS x (⟨x.val + 1, hx⟩ : Fin L) a τ)).drop (x.val + 2)
      = (List.ofFn τ).drop (x.val + 2) := by
  refine List.ext_getElem (by simp) fun i _ _ => ?_
  simp only [List.getElem_drop, List.getElem_ofFn, glueTwoSitesS]
  rw [if_neg (by simp only [Fin.ext_iff]; omega),
    if_neg (by simp only [Fin.ext_iff]; omega)]

end LatticeSystem.Quantum
