import LatticeSystem.Quantum.SpinS.InfiniteVolumeGroundState

/-!
# Tasaki §4.3 / §A.7: the local-support interface of the quasi-local algebra

This module provides the **graph-centric local-support interface** of the
infinite-volume spin system `InfiniteSpinSystem d A` on the hypercubic lattice
`ℤᵈ`.  It is the constructive layer between the finite-volume boxes
`Λ_n = hypercubicBox d n` (already built graph-centrically in
`LatticeSystem.Lattice.HypercubicLattice`) and the abstract quasi-local
`C*`-algebra `A` of observables (Tasaki §4.3.1, §A.7): for each finite region
`Λ ⊆ ℤᵈ` it carves out the `*`-subalgebra `A_Λ ⊆ A` of observables *supported in
`Λ`*, and assembles the increasing tower `A_{Λ_n} ⊆ A_{Λ_{n+1}} ⊆ ⋯` of
box-local algebras whose union is the local algebra `A_loc`.

The local-support assignment is carried abstractly as `LocalSupportData`: a
predicate `Supports Λ a` ("`a` acts nontrivially only on sites of `Λ`") closed
under the `*`-algebra operations and monotone in `Λ`, with the per-site spin
operator `Ŝ_x^{(α)}` supported on the singleton `{x}`.  This is the faithful
finite-support structure of the local observable net `{A_Λ}_{Λ ⋐ ℤᵈ}` (Tasaki
Definitions A.23 / A.25 / A.27) realized over the project's graph-centric boxes;
no existence theorem for the inductive-limit `C*`-algebra is asserted here (that
remains a documented axiom of the deeper operator-algebraic layer).

All declarations are proved **axiom-free**: the box-local subalgebras and their
monotone tower are finite/order facts about the support net.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1 (eqs. (4.3.1)–(4.3.5)), Appendix A.7
  (Definitions A.23, A.25, A.27), pp. 112–113, 530–533.
-/

namespace LatticeSystem.Quantum

open scoped ComplexOrder

variable {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

/-- **Local-support data for an infinite-volume spin system.**  A predicate
`Supports Λ a` recording that the observable `a` is *supported in the finite
region `Λ ⊆ ℤᵈ`* (it acts nontrivially only on sites of `Λ`), closed under the
`*`-algebra operations and monotone in `Λ`, with each per-site spin operator
`Ŝ_x^{(α)}` supported on the singleton region `{x}`.  This is the finite-support
structure of the local observable net `{A_Λ}` (Tasaki §4.3.1 / Definition A.23):
the building block of the quasi-local algebra. -/
structure LocalSupportData (S : InfiniteSpinSystem d A) where
  /-- `Supports Λ a` means the observable `a` is supported in the finite region `Λ`. -/
  Supports : Finset (Fin d → ℤ) → A → Prop
  /-- A supported observable is a local observable: `A_Λ ⊆ A_loc`. -/
  support_mem_localAlg : ∀ {Λ : Finset (Fin d → ℤ)} {a : A}, Supports Λ a → a ∈ S.localAlg
  /-- **Monotonicity**: enlarging the region preserves support, `Λ ⊆ Γ → A_Λ ⊆ A_Γ`. -/
  support_mono : ∀ {Λ Γ : Finset (Fin d → ℤ)} {a : A}, Λ ⊆ Γ → Supports Λ a → Supports Γ a
  /-- The zero observable is supported in every region. -/
  support_zero : ∀ Λ : Finset (Fin d → ℤ), Supports Λ 0
  /-- The unit observable is supported on the empty region. -/
  support_one : Supports ∅ 1
  /-- Support is closed under addition. -/
  support_add : ∀ {Λ : Finset (Fin d → ℤ)} {a b : A}, Supports Λ a → Supports Λ b → Supports Λ (a + b)
  /-- Support is closed under multiplication. -/
  support_mul : ∀ {Λ : Finset (Fin d → ℤ)} {a b : A}, Supports Λ a → Supports Λ b → Supports Λ (a * b)
  /-- Support is closed under scalar multiplication. -/
  support_smul : ∀ {Λ : Finset (Fin d → ℤ)} (c : ℂ) {a : A}, Supports Λ a → Supports Λ (c • a)
  /-- Support is closed under the `*`-operation (adjoint). -/
  support_star : ∀ {Λ : Finset (Fin d → ℤ)} {a : A}, Supports Λ a → Supports Λ (star a)
  /-- Each per-site spin operator `Ŝ_x^{(α)}` is supported on the singleton `{x}`. -/
  spin_supported_singleton : ∀ (x : Fin d → ℤ) (α : Fin 3), Supports {x} (S.spin x α)

namespace LocalSupportData

variable {S : InfiniteSpinSystem d A} (D : LocalSupportData S)

/-- The unit observable is supported in **every** region (`1 ∈ A_Λ`), since
`∅ ⊆ Λ`. -/
theorem support_one' (Λ : Finset (Fin d → ℤ)) : D.Supports Λ 1 :=
  D.support_mono (Finset.empty_subset Λ) D.support_one

/-- The **local subalgebra** `A_Λ ⊆ A` of observables supported in the finite
region `Λ ⊆ ℤᵈ` (Tasaki §4.3.1 / Definition A.23): the `*`-subalgebra cut out by
the support predicate, with the support-closure laws as its `*`-subalgebra
structure. -/
def localSubalgebra (Λ : Finset (Fin d → ℤ)) : StarSubalgebra ℂ A where
  carrier := {a | D.Supports Λ a}
  mul_mem' ha hb := D.support_mul ha hb
  one_mem' := D.support_one' Λ
  add_mem' ha hb := D.support_add ha hb
  zero_mem' := D.support_zero Λ
  algebraMap_mem' c := by
    have h := D.support_smul c (D.support_one' Λ)
    simpa [Algebra.algebraMap_eq_smul_one] using h
  star_mem' ha := D.support_star ha

/-- Membership in the local subalgebra `A_Λ` is exactly being supported in `Λ`. -/
@[simp]
theorem mem_localSubalgebra {Λ : Finset (Fin d → ℤ)} {a : A} :
    a ∈ D.localSubalgebra Λ ↔ D.Supports Λ a :=
  Iff.rfl

/-- The local subalgebra is contained in the algebra of local observables:
`A_Λ ⊆ A_loc`. -/
theorem localSubalgebra_le_localAlg (Λ : Finset (Fin d → ℤ)) :
    D.localSubalgebra Λ ≤ S.localAlg :=
  fun _ ha => D.support_mem_localAlg ha

/-- **Monotonicity of the local net**: `Λ ⊆ Γ → A_Λ ⊆ A_Γ` (Definition A.23,
the local observable net is increasing). -/
theorem localSubalgebra_mono {Λ Γ : Finset (Fin d → ℤ)} (h : Λ ⊆ Γ) :
    D.localSubalgebra Λ ≤ D.localSubalgebra Γ :=
  fun _ ha => D.support_mono h ha

/-- The **box-local subalgebra** `A_{Λ_n}` of observables supported in the
centered finite box `Λ_n = hypercubicBox d n` (side `2n`): the finite-volume
member of the increasing tower exhausting the quasi-local algebra. -/
noncomputable def boxLocalSubalgebra (n : ℕ) : StarSubalgebra ℂ A :=
  D.localSubalgebra (InfiniteSpinSystem.latticeBox d n)

/-- The box-local subalgebras form a **monotone increasing tower**
`A_{Λ_0} ⊆ A_{Λ_1} ⊆ ⋯` (the boxes are nested, Tasaki §4.3 / eq. (3.1.2)). -/
theorem boxLocalSubalgebra_mono : Monotone D.boxLocalSubalgebra := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  exact D.localSubalgebra_mono (LatticeSystem.Lattice.hypercubicBox_subset_succ n)

/-- Each box-local subalgebra is contained in the local algebra:
`A_{Λ_n} ⊆ A_loc`. -/
theorem boxLocalSubalgebra_le_localAlg (n : ℕ) :
    D.boxLocalSubalgebra n ≤ S.localAlg :=
  D.localSubalgebra_le_localAlg _

/-- A per-site spin operator at a site of the box lies in the box-local
subalgebra: `x ∈ Λ_n → Ŝ_x^{(α)} ∈ A_{Λ_n}` (the box Hamiltonian's spin factors
are box-local). -/
theorem spin_mem_boxLocalSubalgebra_of_mem {n : ℕ} {x : Fin d → ℤ} (α : Fin 3)
    (hx : x ∈ InfiniteSpinSystem.latticeBox d n) :
    S.spin x α ∈ D.boxLocalSubalgebra n := by
  refine D.support_mono ?_ (D.spin_supported_singleton x α)
  exact Finset.singleton_subset_iff.mpr hx

end LocalSupportData

end LatticeSystem.Quantum
