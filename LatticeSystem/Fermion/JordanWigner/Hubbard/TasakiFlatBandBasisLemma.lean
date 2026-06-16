import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Tasaki §11.3.1: the localized-state basis of the flat-band model (Lemma 11.10)

For Tasaki's flat-band Hubbard model on the decorated hypercubic lattice `Λ = E ∪ I` (metallic sites
`E`, oxygen sites `I`), the localized single-electron states `{α_p}_{p∈E}` (centred at metallic
sites) and `{β_u}_{u∈I}` (centred at oxygen sites) together form a basis of the single-electron
space `h ≅ ℂ^{|Λ|}` (Lemma 11.10).

The mathematical content is finite-dimensional linear algebra: the `α`'s are linearly independent
(each centred at its own metallic site), the `β`'s are linearly independent, the two families are
orthogonal (`⟪α_p, β_u⟫ = 0`), and `|E| + |I| = |Λ|`.  We render this faithfully with the localized
states as abstract orthogonal linearly-independent families and **discharge it** (axiom-free): two
orthogonal linearly-independent families whose cardinalities sum to the dimension together span the
whole space.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §11.3.1, Lemma 11.10, eqs. (11.3.1)–(11.3.2), pp. 405–406.
-/

namespace LatticeSystem.Fermion

open scoped InnerProductSpace

/-- **Tasaki Lemma 11.10 (the localized-state basis).**  On the decorated lattice `Λ`, the metallic
localized states `α : ιE → ℂ^Λ` and the oxygen localized states `β : ιI → ℂ^Λ`, each family linearly
independent, mutually orthogonal (`⟪α_p, β_u⟫ = 0`), with `|ιE| + |ιI| = |Λ|`, together span the
whole single-electron space — so `{α_p} ∪ {β_u}` is a basis of `h ≅ ℂ^{|Λ|}`.

Proof: orthogonality makes the two spans disjoint, so
`finrank (span α ⊔ span β) = finrank (span α) + finrank (span β) = |ιE| + |ιI| = |Λ|`, which equals
the dimension of the whole space, forcing the join to be everything. -/
theorem tasaki_lemma_11_10 {Λ : Type*} [Fintype Λ]
    {ιE ιI : Type*} [Fintype ιE] [Fintype ιI]
    (α : ιE → EuclideanSpace ℂ Λ) (β : ιI → EuclideanSpace ℂ Λ)
    (hα : LinearIndependent ℂ α) (hβ : LinearIndependent ℂ β)
    (hortho : ∀ p u, inner ℂ (α p) (β u) = 0)
    (hcard : Fintype.card ιE + Fintype.card ιI = Fintype.card Λ) :
    Submodule.span ℂ (Set.range α) ⊔ Submodule.span ℂ (Set.range β) = ⊤ := by
  set Sα := Submodule.span ℂ (Set.range α) with hSα
  set Sβ := Submodule.span ℂ (Set.range β) with hSβ
  have hO : Sα ⟂ Sβ := by
    rw [hSα, hSβ, Submodule.isOrtho_span]
    rintro u ⟨p, rfl⟩ v ⟨q, rfl⟩
    exact hortho p q
  have hinf : Sα ⊓ Sβ = ⊥ := disjoint_iff.mp hO.disjoint
  have hfα : Module.finrank ℂ Sα = Fintype.card ιE := finrank_span_eq_card hα
  have hfβ : Module.finrank ℂ Sβ = Fintype.card ιI := finrank_span_eq_card hβ
  have hsup : Module.finrank ℂ ↥(Sα ⊔ Sβ) = Fintype.card Λ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq Sα Sβ
    rw [hinf, finrank_bot, hfα, hfβ, hcard] at h
    omega
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hsup, finrank_euclideanSpace]

end LatticeSystem.Fermion
