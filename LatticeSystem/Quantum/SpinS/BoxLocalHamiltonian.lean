import LatticeSystem.Quantum.SpinS.QuasiLocalSupport

/-!
# Tasaki §4.3.1 / §A.7: the finite-box partial Hamiltonian in the quasi-local algebra

Building on the local-support interface (`LocalSupportData`,
`QuasiLocalSupport.lean`), this module places the **finite-box antiferromagnetic
Heisenberg Hamiltonian** `Ĥ_{Λ_n}` of an infinite-volume spin system inside the
box-local subalgebra `A_{Λ_n}` of the quasi-local `C*`-algebra `A`.

For the centered box `Λ_n = hypercubicBox d n`, the partial Hamiltonian is the
sum of the bond spin–spin operators `Ŝ_x · Ŝ_y` over the nearest-neighbor bonds
of the induced box graph (Tasaki §4.3.1, the finite-volume Hamiltonian whose
`L↑∞` limit defines the infinite system; cf. Appendix A.7's partial Hamiltonian
`Ĥ_L`).  The sum is taken over **ordered** adjacent vertex pairs with a `½`
prefactor — matching the project's finite-matrix convention
`boxAFMHeisenbergHamiltonianS` — because the abstract `InfiniteSpinSystem`
provides no `Ŝ_x · Ŝ_y = Ŝ_y · Ŝ_x` symmetry to collapse unordered bonds.

The key results are proved **axiom-free**: each spin operator is supported on its
site, so a bond operator with both endpoints in `Λ` lies in `A_Λ`, and the finite
sum (with scalar) of such operators stays in the subalgebra.  No self-adjointness
or cross-site commutativity is claimed (the abstract system carries none), and no
identification of the abstract algebra with the finite-matrix model is made.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1 (eqs. (4.3.1)–(4.3.4)), Appendix A.7, pp.
  112–113, 530–533.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice

variable {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

/-- Adjacency in the finite box graph is decidable (it unfolds to a decidable
differ-in-one-coordinate existential over `Fin d`). -/
instance instDecidableBoxGraphAdj (d n : ℕ) :
    DecidableRel (hypercubicBoxGraph d n).Adj := fun _ _ =>
  decidable_of_iff _ hypercubicBoxGraph_adj.symm

/-- The **ordered nearest-neighbor bond pairs** of the finite box `Λ_n`: ordered
vertex pairs `(x, y)` of the box that are adjacent in the induced box graph. -/
noncomputable def boxOrderedBondPairs (d n : ℕ) :
    Finset (hypercubicBoxVertex d n × hypercubicBoxVertex d n) :=
  Finset.univ.filter fun p => (hypercubicBoxGraph d n).Adj p.1 p.2

/-- A pair lies in `boxOrderedBondPairs` exactly when its endpoints are adjacent
in the box graph. -/
@[simp]
theorem mem_boxOrderedBondPairs {d n : ℕ}
    {p : hypercubicBoxVertex d n × hypercubicBoxVertex d n} :
    p ∈ boxOrderedBondPairs d n ↔ (hypercubicBoxGraph d n).Adj p.1 p.2 := by
  simp [boxOrderedBondPairs]

/-- The ordered box bonds are closed under swapping endpoints (the box graph is
undirected). -/
theorem swap_mem_boxOrderedBondPairs {d n : ℕ}
    {p : hypercubicBoxVertex d n × hypercubicBoxVertex d n}
    (hp : p ∈ boxOrderedBondPairs d n) :
    (p.2, p.1) ∈ boxOrderedBondPairs d n := by
  rw [mem_boxOrderedBondPairs] at hp ⊢
  exact hp.symm

/-- The **finite-box (partial) antiferromagnetic Heisenberg Hamiltonian**
`Ĥ_{Λ_n} = ½ Σ_{(x,y) bond in Λ_n} Ŝ_x · Ŝ_y` of an infinite-volume spin system,
as an element of the quasi-local algebra `A` (Tasaki §4.3.1, finite-volume
Hamiltonian; Appendix A.7 partial Hamiltonian).  The `½` compensates for summing
over ordered pairs `(x, y)` and `(y, x)`. -/
noncomputable def boxLocalHamiltonian (S : InfiniteSpinSystem d A) (n : ℕ) : A :=
  ((1 : ℂ) / 2) •
    ∑ p ∈ boxOrderedBondPairs d n,
      InfiniteSpinSystem.spinDot S (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ)

namespace LocalSupportData

variable {S : InfiniteSpinSystem d A} (D : LocalSupportData S)

/-- A per-site spin operator at a site of `Λ` lies in the local subalgebra `A_Λ`. -/
theorem spin_mem_localSubalgebra_of_mem {Λ : Finset (Fin d → ℤ)} {x : Fin d → ℤ}
    (α : Fin 3) (hx : x ∈ Λ) :
    S.spin x α ∈ D.localSubalgebra Λ :=
  (D.mem_localSubalgebra).mpr
    (D.support_mono (Finset.singleton_subset_iff.mpr hx) (D.spin_supported_singleton x α))

/-- A **bond spin–spin operator** `Ŝ_x · Ŝ_y` whose endpoints both lie in `Λ`
belongs to the local subalgebra `A_Λ` (a finite sum of products of box-local
spin operators). -/
theorem spinDot_mem_localSubalgebra_of_mem {Λ : Finset (Fin d → ℤ)} {x y : Fin d → ℤ}
    (hx : x ∈ Λ) (hy : y ∈ Λ) :
    InfiniteSpinSystem.spinDot S x y ∈ D.localSubalgebra Λ := by
  unfold InfiniteSpinSystem.spinDot
  exact sum_mem fun α _ =>
    mul_mem (D.spin_mem_localSubalgebra_of_mem α hx) (D.spin_mem_localSubalgebra_of_mem α hy)

/-- A bond spin–spin operator whose endpoints lie in `Λ_n` belongs to the
box-local subalgebra `A_{Λ_n}`. -/
theorem spinDot_mem_boxLocalSubalgebra_of_mem {n : ℕ} {x y : Fin d → ℤ}
    (hx : x ∈ InfiniteSpinSystem.latticeBox d n)
    (hy : y ∈ InfiniteSpinSystem.latticeBox d n) :
    InfiniteSpinSystem.spinDot S x y ∈ D.boxLocalSubalgebra n :=
  D.spinDot_mem_localSubalgebra_of_mem hx hy

/-- A bond spin–spin operator between two vertices of the box `Λ_n` belongs to the
box-local subalgebra `A_{Λ_n}`. -/
theorem spinDot_mem_boxLocalSubalgebra_of_boxVertex {n : ℕ}
    (x y : hypercubicBoxVertex d n) :
    InfiniteSpinSystem.spinDot S (x : Fin d → ℤ) (y : Fin d → ℤ) ∈
      D.boxLocalSubalgebra n :=
  D.spinDot_mem_boxLocalSubalgebra_of_mem (Finset.mem_coe.mp x.2) (Finset.mem_coe.mp y.2)

/-- **The finite-box partial Hamiltonian is box-local**: `Ĥ_{Λ_n} ∈ A_{Λ_n}`
(Tasaki §4.3.1 / Appendix A.7).  It is the `½`-scaled finite sum of box-local
bond operators. -/
theorem boxLocalHamiltonian_mem_boxLocalSubalgebra (n : ℕ) :
    boxLocalHamiltonian S n ∈ D.boxLocalSubalgebra n := by
  have hsum :
      (∑ p ∈ boxOrderedBondPairs d n,
        InfiniteSpinSystem.spinDot S (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ)) ∈
        D.boxLocalSubalgebra n :=
    sum_mem fun p _ => D.spinDot_mem_boxLocalSubalgebra_of_boxVertex p.1 p.2
  rw [boxLocalHamiltonian, Algebra.smul_def]
  exact mul_mem (algebraMap_mem _ _) hsum

include D in
/-- The finite-box partial Hamiltonian is a local observable: `Ĥ_{Λ_n} ∈ A_loc`. -/
theorem boxLocalHamiltonian_mem_localAlg (n : ℕ) :
    boxLocalHamiltonian S n ∈ S.localAlg :=
  D.boxLocalSubalgebra_le_localAlg n (D.boxLocalHamiltonian_mem_boxLocalSubalgebra n)

end LocalSupportData

end LatticeSystem.Quantum
