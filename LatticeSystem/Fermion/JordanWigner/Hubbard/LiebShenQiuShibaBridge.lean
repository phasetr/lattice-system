import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebShenQiu
import LatticeSystem.Fermion.JordanWigner.Hubbard.LiebRepulsiveShibaConjugation

/-!
# The Shiba bridge onto the symmetric attractive Hamiltonian (Tasaki §10.2.3, eq. (10.2.21))

Bridge layer of **Tasaki Theorem 10.8** (Lieb–Shen–Qiu superconductivity; Hal Tasaki, *Physics and
Mathematics of Quantum Many-Body Systems*, 1st ed., Springer 2020, §10.2.3, p. 359,
eqs. (10.2.21)/(10.2.22)).

Theorem 10.8 is stated for the **symmetric** attractive Hamiltonian
`Ĥ^{attr,sym}(T,U) = Ĥhop(T) − Σ_x U_x (n̂_{x↑}−½)(n̂_{x↓}−½)` (eq. (10.2.21)), while the Shiba
conjugation of §10.2.2 (`shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive`,
eq. (10.2.10)) delivers the *plain* attractive Hamiltonian with on-site energies shifted by `U/2`,
minus the scalar `¼ Σ_x U_x`.  Reading eq. (10.2.11) in the attractive direction shows the
symmetric attractive Hamiltonian carries exactly the same scalar, so the two constants cancel.

## Main results

* `symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul` — the constant-shift identity
  `Ĥ^{attr,sym}(T,U) = Ĥ^{attr}(T + diag(U/2), U) − (¼ Σ_x U_x)·1`.
* `shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive` — the bridge
  `Ûᴴ Ĥ^{rep,sym}(T,U) Û = Ĥ^{attr,sym}(T,U)`, with **no** residual scalar: the two Hamiltonians
  are unitarily equivalent, so their spectra coincide and `Û` transports eigenvectors at
  unchanged energy.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, 1st ed., Springer
2020, §§10.2.2/10.2.3, eqs. (10.2.10)/(10.2.11)/(10.2.21), pp. 352, 359;
E. H. Lieb, *Phys. Rev. Lett.* **62** (1989) 1201; S.-Q. Shen, Z.-M. Qiu, G.-S. Tian,
*Phys. Rev. Lett.* **72** (1994) 1280.
-/

namespace LatticeSystem.Fermion

open Matrix LatticeSystem.Quantum
open scoped BigOperators

variable {N : ℕ}

/-- **The symmetric attractive Hamiltonian is a shifted plain attractive Hamiltonian**
(Tasaki eq. (10.2.11), read in the attractive direction):
`Ĥhop(T) − Ĥint'(U) = Ĥ^{attr}(T + diag(U/2), U) − (¼ Σ_x U_x)·1`.  Centring the number
operators produces the chemical potential `Σ_x (U_x/2)(n̂_{x↑}+n̂_{x↓})`, which is absorbed into
the hopping diagonal, and the constant `−¼ Σ_x U_x`. -/
theorem symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul (N : ℕ)
    (T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (U : Fin (N + 1) → ℝ) :
    symmetricAttractiveHubbardHamiltonian N T U
      = attractiveHubbardHamiltonian N (T + Matrix.diagonal (fun x => U x / 2)) U
        - ((∑ x : Fin (N + 1), (U x : ℂ)) / 4) • (1 : ManyBodyOp (Fin (2 * N + 2))) := by
  have hfun : (fun x y => ((T + Matrix.diagonal (fun z => U z / 2)) x y : ℂ))
      = (fun x y => (T x y : ℂ) + (Matrix.diagonal (fun z => (U z : ℂ) / 2)) x y) := by
    funext x y
    rw [Matrix.add_apply, Complex.ofReal_add, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos hxy]; push_cast; ring
    · rw [if_neg hxy, if_neg hxy]; push_cast; ring
  have hsplit : hubbardKinetic N (fun x y => ((T + Matrix.diagonal (fun z => U z / 2)) x y : ℂ))
      = hubbardKinetic N (fun x y => (T x y : ℂ))
        + ∑ x : Fin (N + 1),
            ((U x : ℂ) / 2) • (fermionUpNumber N x + fermionDownNumber N x) := by
    rw [hfun, hubbardKinetic_add, hubbardKinetic_diagonal]
  rw [symmetricAttractiveHubbardHamiltonian, attractiveHubbardHamiltonian, hsplit,
    sub_eq_add_neg, neg_symmetricRepulsiveInteraction_eq]
  abel

/-- **The Shiba conjugation of the symmetric repulsive Hamiltonian is the symmetric attractive
Hamiltonian** (Tasaki §10.2.3, eq. (10.2.21) combined with eq. (10.2.10)):
`Ûᴴ Ĥ^{rep,sym}(T,U) Û = Ĥ^{attr,sym}(T,U)`.  The `−¼ Σ_x U_x` left over by the conjugation
(`shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive`) is exactly the constant carried by
the symmetric attractive Hamiltonian, so no scalar survives: the two Hamiltonians are unitarily
equivalent and `Û` maps `E`-eigenvectors of one to `E`-eigenvectors of the other at the same
energy `E`. -/
theorem shibaSignedUnitary_conj_symmetricRepulsive_eq_symmetricAttractive
    {A : Finset (Fin (N + 1))} {T : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ}
    (hsymm : ∀ x y, T x y = T y x) (hbip : HoppingRespectsBipartition A T)
    (U : Fin (N + 1) → ℝ) :
    Matrix.conjTranspose (shibaSignedUnitary N (shibaSignFn A))
        * symmetricRepulsiveHubbardHamiltonian N T U
        * shibaSignedUnitary N (shibaSignFn A)
      = symmetricAttractiveHubbardHamiltonian N T U := by
  rw [shibaSignedUnitary_conj_symmetricRepulsive_eq_attractive hsymm hbip U,
    symmetricAttractiveHubbardHamiltonian_eq_attractive_sub_smul N T U]

end LatticeSystem.Fermion
