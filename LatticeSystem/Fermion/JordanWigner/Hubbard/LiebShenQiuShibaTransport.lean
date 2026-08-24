import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveBalancedGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuShibaBridge

/-!
# Shiba transport in the symmetric-attractive form (Tasaki §10.2.3, eq. (10.2.21))

Transport layer of **Tasaki Theorem 10.8** (Lieb–Shen–Qiu superconductivity; Hal Tasaki, *Physics
and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.3, p. 359).

Theorem 10.8 works with the **symmetric** attractive Hamiltonian `Ĥ^{attr,sym}(T,U)`
(eq. (10.2.21)), for which the Shiba bridge
`shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive`
(`LiebShenQiuShibaBridge.lean`) gives the conjugation `Ûᴴ Ĥ^{rep,sym} Û = Ĥ^{attr,sym}` with **no**
residual scalar.  Feeding that bridge to the reusable transport
`shibaTransport_uniqueGroundStateOn_spinZSector_of_conj`
(`LiebRepulsiveBalancedGround.lean`) therefore carries the ground energy across **unchanged**,
while the §10.2.2 face of the same transport carries the `−¼ Σ_x U_x` left over by the plain
conjugation (eq. (10.2.10)).

Keeping this instance in its own module preserves the layering of the arc: the §10.2.2
Theorem-10.4 module stays free of any dependence on the Theorem-10.8 statement layer.

## Main result

* `shibaTransport_uniqueGroundStateOn_spinZSector_symmetricAttractive` — the symmetric-attractive
  Shiba transport, at unchanged energy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §§10.2.2/10.2.3, eqs. (10.2.10)/(10.2.11)/(10.2.21), pp. 352, 359;
E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201; S.-Q. Shen, Z.-M. Qiu, G.-S. Tian,
*Phys. Rev. Lett.* **72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum LatticeSystem.Math
open scoped BigOperators

/-- **Shiba transport from the symmetric attractive model, at unchanged energy** (Tasaki §10.2.3,
eq. (10.2.21) combined with §10.2.2, eqs. (10.2.10)/(10.2.11)).  If `φ` is the unique normalized
ground state of the symmetric attractive Hamiltonian `Ĥ^{attr,sym}(T,U)` on the `N̂ = Ne` sector at
energy `E`, and `φ` is a spin singlet, then `ψ = Û φ` is the unique normalized ground state of the
symmetric repulsive Hamiltonian `Ĥ^{rep,sym}(T,U)` on the spin-`z` sector `Ŝ³ = (Ne − (N+1))/2`, at
the **same** energy `E`, and sits at half filling, `N̂ ψ = (N+1) ψ`.

The energy is unchanged because the Shiba bridge
`shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive` conjugates `Ĥ^{rep,sym}` onto
`Ĥ^{attr,sym}` with no residual scalar; feeding it as the conjugation hypothesis of
`shibaTransport_uniqueGroundStateOn_spinZSector_of_conj` is all this instance does. -/
theorem shibaTransport_uniqueGroundStateOn_spinZSector_symmetricAttractive (N Ne : ℕ)
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hT_symm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) {E : ℝ} {φ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2)}
    (hGS : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (symmetricAttractiveHubbardHamiltonian N T U) E φ)
    (hsinglet : Matrix.toEuclideanLin (fermionTotalSpinSquared N) φ = 0) :
    ∃ ψ : EuclideanSpace ℂ (Fin (2 * N + 2) → Fin 2),
      ψ.ofLp = (shibaSignedUnitary N (shibaSignFn A)).mulVec φ.ofLp ∧
      IsUniqueGroundStateOn (spinZSectorEuclidean N (((Ne : ℂ) - ((N : ℂ) + 1)) / 2))
        (symmetricRepulsiveHubbardHamiltonian N T U) E ψ ∧
      Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ :=
  shibaTransport_uniqueGroundStateOn_spinZSector_of_conj N Ne
    (shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive hT_symm hbip U) hGS hsinglet

end LatticeSystem.Fermion
