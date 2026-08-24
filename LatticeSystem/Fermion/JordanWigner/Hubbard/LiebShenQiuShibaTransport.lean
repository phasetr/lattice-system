import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveBalancedGround
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiuShibaBridge
import LatticeSystem.Math.MatrixAnalysis.SubmatrixGroundState

/-!
# Shiba transport in the symmetric-attractive form (Tasaki §10.2.3, eq. (10.2.21))

Transport layer of **Tasaki Theorem 10.8** (Lieb–Shen–Qiu superconductivity; Hal Tasaki, *Physics
and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.3, p. 359).

Theorem 10.8 works with the **symmetric** attractive Hamiltonian `Ĥ^{attr,sym}(T,U)`
(eq. (10.2.21)), whereas the Shiba transport of §10.2.2
(`shibaTransport_uniqueGroundStateOn_spinZSector`, `LiebRepulsiveBalancedGround.lean`) is phrased
for the plain attractive Hamiltonian with on-site energies shifted by `U/2` and loses the scalar
`¼ Σ_x U_x` on the way.  Composing the two with the constant-shift identity
`symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul` (`LiebShenQiuShibaBridge.lean`)
makes the two occurrences of that scalar cancel, so the symmetric-attractive form of the transport
carries the ground energy across **unchanged**.

Keeping this corollary in its own module preserves the layering of the arc: the §10.2.2
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

The energy is unchanged because the `¼ Σ_x U_x` by which the symmetric attractive Hamiltonian
differs from the shifted plain one is exactly the scalar dropped by the Shiba conjugation of the
symmetric repulsive Hamiltonian.  Concretely: rewrite `Ĥ^{attr,sym}` as the shifted plain
Hamiltonian minus that constant, read the shift backwards
(`isUniqueGroundStateOn_sub_smul_one_iff`) to get a plain-attractive ground state at energy
`E + ¼ Σ_x U_x`, and apply `shibaTransport_uniqueGroundStateOn_spinZSector`, whose output energy
subtracts the same constant again. -/
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
      Matrix.toEuclideanLin (fermionTotalNumber (2 * N + 1)) ψ = ((N : ℂ) + 1) • ψ := by
  classical
  have hκ : ((∑ x : Fin (N + 1), (U x : ℂ)) / 4)
      = (((∑ x : Fin (N + 1), U x) / 4 : ℝ) : ℂ) := by push_cast; ring
  -- Undo the constant shift: the shifted plain attractive Hamiltonian sits at `E + ¼ Σ U`.
  have hGS' : IsUniqueGroundStateOn (electronNumberSectorEuclidean N Ne)
      (attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U)
      (E + (∑ x : Fin (N + 1), U x) / 4) φ := by
    refine (isUniqueGroundStateOn_sub_smul_one_iff _ _ ((∑ x : Fin (N + 1), U x) / 4)
      (E + (∑ x : Fin (N + 1), U x) / 4) φ).mpr ?_
    rw [show E + (∑ x : Fin (N + 1), U x) / 4 - (∑ x : Fin (N + 1), U x) / 4 = E by ring]
    rwa [symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul N T U, hκ] at hGS
  obtain ⟨ψ, hψofLp, hGSrep, hnum⟩ :=
    shibaTransport_uniqueGroundStateOn_spinZSector N Ne hT_symm hbip U hGS' hsinglet
  refine ⟨ψ, hψofLp, ?_, hnum⟩
  rwa [show E + (∑ x : Fin (N + 1), U x) / 4 - (∑ x : Fin (N + 1), U x) / 4 = E by ring] at hGSrep

end LatticeSystem.Fermion
