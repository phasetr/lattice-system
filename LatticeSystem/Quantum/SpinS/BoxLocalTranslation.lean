import LatticeSystem.Quantum.SpinS.BoxLocalHamiltonian

/-!
# Tasaki §4.3.1 / §A.7: translation covariance of the local finite-box observables

Continuing the constructive infinite-volume layer (after the local-support
interface `QuasiLocalSupport.lean` and the finite-box Hamiltonian
`BoxLocalHamiltonian.lean`), this module records how the local observables of an
`InfiniteSpinSystem` transform under the translation automorphisms `τ_x`
(eq. (4.3.3)), and that the translated finite-box Hamiltonian is supported in the
**translated box** `Λ_n + x`.

The translations `τ_x` are `*`-algebra isomorphisms with the spin covariance
`τ_x(Ŝ_y^{(α)}) = Ŝ_{y+x}^{(α)}`.  By multiplicativity and additivity this lifts
to the bond operators (`τ_x(Ŝ_y · Ŝ_z) = Ŝ_{y+x} · Ŝ_{z+x}`), the bulk operators
(`τ_x Â_n = (τ_x Â)_n`), and the finite-box Hamiltonian: translating
`Ĥ_{Λ_n}` produces the partial Hamiltonian of the shifted box, which is supported
in `Λ_n + x`.  This is the translation covariance underlying the §4.3.1
infinite-volume construction (and the Appendix A.7 local-interaction picture).

Everything here is proved **axiom-free** from the `InfiniteSpinSystem` action
laws and the local-support closure; no self-adjointness or cross-site
commutativity is used.

## References

* Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
  (1st ed., Springer, 2020), §4.3.1 (eqs. (4.3.3)–(4.3.6)), Appendix A.7, pp.
  112–113, 530–533.
-/

namespace LatticeSystem.Quantum

open LatticeSystem.Lattice

variable {d : ℕ} {A : Type*} [CStarAlgebra A] [NormedSpace ℂ A] [StarModule ℂ A]

namespace InfiniteSpinSystem

/-- **Translation invariance of the bond relation**: shifting both endpoints by
`x` preserves the nearest-neighbor bond, `bond (y + x) (z + x) ↔ bond y z`. -/
theorem bond_add_right_iff (x y z : Fin d → ℤ) :
    bond (y + x) (z + x) ↔ bond y z := by
  rw [bond_iff_adj, bond_iff_adj]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨i, ?_, fun j hji => ?_⟩
    · have h : (y + x) i - (z + x) i = y i - z i := by
        simp only [Pi.add_apply]; ring
      rwa [h] at hi
    · have := hj j hji
      simp only [Pi.add_apply] at this
      omega
  · rintro ⟨i, hi, hj⟩
    refine ⟨i, ?_, fun j hji => ?_⟩
    · have h : (y + x) i - (z + x) i = y i - z i := by
        simp only [Pi.add_apply]; ring
      rwa [h]
    · simp only [Pi.add_apply, hj j hji]

/-- **Translation covariance of the bond operator**: the translation `τ_x` maps
the bond spin–spin operator `Ŝ_y · Ŝ_z` to the bond operator of the shifted
endpoints, `τ_x(Ŝ_y · Ŝ_z) = Ŝ_{y+x} · Ŝ_{z+x}` (eq. (4.3.3) lifted by
multiplicativity). -/
theorem transl_spinDot (S : InfiniteSpinSystem d A) (x y z : Fin d → ℤ) :
    S.transl x (spinDot S y z) = spinDot S (y + x) (z + x) := by
  unfold spinDot
  rw [map_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [map_mul, S.transl_spin, S.transl_spin]

/-- The **translated box** `Λ_n + x = {z + x : z ∈ Λ_n}`, the image of the
centered box under the shift by `x`. -/
noncomputable def translatedLatticeBox (d : ℕ) (x : Fin d → ℤ) (n : ℕ) :
    Finset (Fin d → ℤ) :=
  (latticeBox d n).image (· + x)

/-- Membership in the translated box: `y ∈ Λ_n + x` iff `y = z + x` for some
`z ∈ Λ_n`. -/
theorem mem_translatedLatticeBox {x y : Fin d → ℤ} {n : ℕ} :
    y ∈ translatedLatticeBox d x n ↔ ∃ z ∈ latticeBox d n, z + x = y := by
  unfold translatedLatticeBox
  rw [Finset.mem_image]

/-- **Translation covariance of the bulk operator**: `τ_x Â_n = (τ_x Â)_n`
(eq. (4.3.5)); the translations commute through the even-box average. -/
theorem transl_bulkOp (S : InfiniteSpinSystem d A) (x : Fin d → ℤ) (a : A) (n : ℕ) :
    S.transl x (bulkOp S a n) = bulkOp S (S.transl x a) n := by
  unfold bulkOp
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [S.transl_add, S.transl_add, add_comm]

end InfiniteSpinSystem

/-- The **translated finite-box Hamiltonian** `Ĥ_{Λ_n + x}`: the partial
Hamiltonian of the box shifted by `x`, summing the bond operators over the
shifted endpoints. -/
noncomputable def translatedBoxLocalHamiltonian (S : InfiniteSpinSystem d A)
    (x : Fin d → ℤ) (n : ℕ) : A :=
  ((1 : ℂ) / 2) •
    ∑ p ∈ boxOrderedBondPairs d n,
      InfiniteSpinSystem.spinDot S ((p.1 : Fin d → ℤ) + x) ((p.2 : Fin d → ℤ) + x)

/-- **Translation covariance of the finite-box Hamiltonian**: translating the
box Hamiltonian gives the partial Hamiltonian of the shifted box,
`τ_x(Ĥ_{Λ_n}) = Ĥ_{Λ_n + x}`. -/
theorem transl_boxLocalHamiltonian (S : InfiniteSpinSystem d A) (x : Fin d → ℤ)
    (n : ℕ) :
    S.transl x (boxLocalHamiltonian S n) = translatedBoxLocalHamiltonian S x n := by
  unfold boxLocalHamiltonian translatedBoxLocalHamiltonian
  rw [map_smul, map_sum]
  refine congrArg _ (Finset.sum_congr rfl (fun p _ => ?_))
  exact S.transl_spinDot x (p.1 : Fin d → ℤ) (p.2 : Fin d → ℤ)

namespace LocalSupportData

variable {S : InfiniteSpinSystem d A} (D : LocalSupportData S)

include D in
/-- The translated finite-box Hamiltonian is supported in the translated box:
`Ĥ_{Λ_n + x} ∈ A_{Λ_n + x}`. -/
theorem translatedBoxLocalHamiltonian_mem_localSubalgebra (x : Fin d → ℤ) (n : ℕ) :
    translatedBoxLocalHamiltonian S x n ∈
      D.localSubalgebra (InfiniteSpinSystem.translatedLatticeBox d x n) := by
  unfold translatedBoxLocalHamiltonian
  rw [Algebra.smul_def]
  refine mul_mem (algebraMap_mem _ _) (sum_mem (fun p _ => ?_))
  refine D.spinDot_mem_localSubalgebra_of_mem ?_ ?_
  · exact InfiniteSpinSystem.mem_translatedLatticeBox.mpr
      ⟨(p.1 : Fin d → ℤ), Finset.mem_coe.mp p.1.2, rfl⟩
  · exact InfiniteSpinSystem.mem_translatedLatticeBox.mpr
      ⟨(p.2 : Fin d → ℤ), Finset.mem_coe.mp p.2.2, rfl⟩

include D in
/-- The translated finite-box Hamiltonian is a local observable:
`Ĥ_{Λ_n + x} ∈ A_loc`. -/
theorem translatedBoxLocalHamiltonian_mem_localAlg (x : Fin d → ℤ) (n : ℕ) :
    translatedBoxLocalHamiltonian S x n ∈ S.localAlg :=
  D.localSubalgebra_le_localAlg _ (D.translatedBoxLocalHamiltonian_mem_localSubalgebra x n)

include D in
/-- The translate of the box Hamiltonian is supported in the translated box:
`τ_x(Ĥ_{Λ_n}) ∈ A_{Λ_n + x}`. -/
theorem transl_boxLocalHamiltonian_mem_localSubalgebra (x : Fin d → ℤ) (n : ℕ) :
    S.transl x (boxLocalHamiltonian S n) ∈
      D.localSubalgebra (InfiniteSpinSystem.translatedLatticeBox d x n) := by
  rw [transl_boxLocalHamiltonian]
  exact D.translatedBoxLocalHamiltonian_mem_localSubalgebra x n

include D in
/-- The translate of the box Hamiltonian is a local observable:
`τ_x(Ĥ_{Λ_n}) ∈ A_loc`. -/
theorem transl_boxLocalHamiltonian_mem_localAlg (x : Fin d → ℤ) (n : ℕ) :
    S.transl x (boxLocalHamiltonian S n) ∈ S.localAlg := by
  rw [transl_boxLocalHamiltonian]
  exact D.translatedBoxLocalHamiltonian_mem_localAlg x n

end LocalSupportData

end LatticeSystem.Quantum
