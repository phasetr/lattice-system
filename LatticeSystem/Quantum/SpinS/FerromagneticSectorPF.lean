import LatticeSystem.Quantum.SpinS.FerromagneticSectorIrreducible
import LatticeSystem.Quantum.SpinS.SaturatedLadderComponent
import LatticeSystem.Quantum.SpinS.SaturatedLadderHEigenspace
import LatticeSystem.Quantum.SpinS.SaturatedEigenvalueExplicit
import LatticeSystem.Quantum.SpinS.MagSectorEmbedding
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.ParityBlockUnshiftedFinrank
import LatticeSystem.Quantum.SpinS.RealComplexEigenspaceBridge
import LatticeSystem.Math.FiniteStrictUpperBound

/-!
# Tasaki §2.4, p. 34: Perron-Frobenius simplicity on a magnetization sector

The analytic half of the Theorem 2.1 uniqueness argument, on one magnetization sector at a time.
Tasaki's solution of Problem 2.4.a (p. 496) instructs one to apply the Perron-Frobenius theorem
(Theorem A.18, p. 475) to the matrix representation of `Ĥ` in each sector `H_M`.  The repo's
Perron-Frobenius packaging concludes simplicity from an explicit strictly positive eigenvector
rather than from a variational identification of the sectorwise minimum, and the ladder state
`Φ_M = (Ŝ⁻_tot)^k Φ↑` supplies that eigenvector: the closed form of the normalized state of
eq. (2.4.9), p. 33 -- `ladderIterateUp` is the unnormalized iterate spanning the same line -- is
a positive real multiple of a product of Clebsch-Gordan weights on its own sector.

The three steps here are: strict positivity of the restricted ladder state, its eigenvector
equation for the real-form sector matrix, and the resulting `finrank ≤ 1` for the complex sector
matrix at the saturated-ferromagnet eigenvalue.  The sector irreducibility input and its diagonal
shift come from `FerromagneticSectorIrreducible`; the shift witness itself is produced here from
`LatticeSystem.Math.exists_gt_of_finite`, so the hypotheses stay those of the book.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §2.4 Theorem 2.1, p. 34; eq. (2.4.9), p. 33; solution of Problem 2.4.a, p. 496;
Theorem A.18, p. 475.
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-- **Strict positivity of the ladder state on its own magnetization sector** (Tasaki eq. (2.4.9),
p. 33; solution of Problem 2.4.a, p. 496).

On the sector `magSumS σ = k` the closed component form of `(Ŝ⁻_tot)^k Φ↑` is the real number
`k! · ∏_x √(binom N σ_x)`, whose factors are all positive.  This is the strictly positive
Perron-Frobenius eigenvector candidate of Theorem A.18 (p. 475).  The book's `Φ_M` of eq. (2.4.9)
is this iterate normalized; `ladderIterateUp` is the unnormalized one, which spans the same line
and is positive on the same sector. -/
theorem ladderIterateUp_restriction_re_pos (k : Fin (Fintype.card V * N + 1))
    (σ : magConfigS V N k.val) :
    0 < (ladderIterateUp V N k σ.1).re := by
  unfold ladderIterateUp
  rw [totalSpinSOpMinus_pow_allAlignedStateS_zero_apply k.val σ.1, if_pos σ.2,
    Complex.ofReal_re]
  have hfac : (0 : ℝ) < (k.val.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos k.val
  have hprod : (0 : ℝ) < ∏ x : V, Real.sqrt (N.choose (σ.1 x).val) := by
    refine Finset.prod_pos fun x _ => Real.sqrt_pos.mpr ?_
    exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp (σ.1 x).isLt)
  exact mul_pos hfac hprod

/-- The saturated-ferromagnet eigenvalue is its own real part, for real coupling.  Packaging of
`saturatedFerromagnetEigenvalueS_exists_real` in the rewrite form used to feed the real-eigenvalue
interfaces of the sector matrices. -/
private theorem saturatedFerromagnetEigenvalueS_ofReal_re {J : V → V → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0) :
    (((saturatedFerromagnetEigenvalueS (V := V) J N).re : ℝ) : ℂ) =
      saturatedFerromagnetEigenvalueS (V := V) J N := by
  obtain ⟨μ, hμ⟩ := saturatedFerromagnetEigenvalueS_exists_real (V := V) (N := N) J hJ_real
  rw [← hμ, Complex.ofReal_re]

/-- **The restricted ladder state is a real sector eigenvector at the ground-state energy**
(Tasaki §2.4, p. 34; solution of Problem 2.4.a, p. 496).

`Φ_M` -- here the unnormalized `(Ŝ⁻_tot)^k Φ↑`, the book's eq. (2.4.9), p. 33, being its
normalization, which changes neither the eigenvector equation nor the span -- is an eigenvector of
the full Hamiltonian at `saturatedFerromagnetEigenvalueS J N`, which is real for real coupling;
since `Ĥ` conserves the magnetization, restricting to the sector keeps the eigenvector equation,
and taking real parts moves it to the real-form sector matrix -- the shape Theorem A.18 (p. 475)
consumes. -/
theorem heisenbergHamiltonianSReMatrixOnMagSector_mulVec_ladder_restriction
    (J : V → V → ℂ) (hJ_real : ∀ x y, (J x y).im = 0)
    (k : Fin (Fintype.card V * N + 1)) :
    (heisenbergHamiltonianSReMatrixOnMagSector J N k.val).mulVec
        (fun σ => (magSectorRestriction (M := k.val) (ladderIterateUp V N k) σ).re) =
      (saturatedFerromagnetEigenvalueS (V := V) J N).re •
        (fun σ => (magSectorRestriction (M := k.val) (ladderIterateUp V N k) σ).re) := by
  have hfull : (heisenbergHamiltonianS J N).mulVec (ladderIterateUp V N k) =
      (((saturatedFerromagnetEigenvalueS (V := V) J N).re : ℝ) : ℂ) • ladderIterateUp V N k := by
    rw [saturatedFerromagnetEigenvalueS_ofReal_re hJ_real]
    have h := ladderIterateUp_mem_heisenbergHamiltonianS_eigenspace J k
    rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at h
    exact h
  exact heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec N hJ_real
    (heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen J hfull)

/-- **Perron-Frobenius simplicity of the sector ground state** (Tasaki §2.4 Theorem 2.1, p. 34;
solution of Problem 2.4.a, p. 496; Theorem A.18, p. 475).

On a connected graph with a real, symmetric, edge-supported and strictly ferromagnetic coupling,
the eigenspace of the complex magnetization-sector matrix at the saturated-ferromagnet eigenvalue
is at most one-dimensional.  Theorem A.18 is applied to `c·1 - Ĥ|_sector`, which is non-negative
and irreducible and carries the strictly positive eigenvector supplied by the ladder state; the
diagonal shift `c` is produced here rather than assumed, so the hypotheses are the book's.

The spin hypothesis `1 ≤ N` is not used by this Perron-Frobenius step; it is carried because it is
the standing assumption `S ≥ 1/2` of §2.4 and of the Theorem 2.1 capstone this feeds. -/
theorem heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_connected_ferro
    {G : SimpleGraph V} {J : V → V → ℂ}
    (hGconn : G.Connected)
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_supp : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJ_ferro : ∀ x y, G.Adj x y → (J x y).re < 0)
    (_hN : 1 ≤ N) (k : Fin (Fintype.card V * N + 1)) :
    Module.finrank ℂ
        (Module.End.eigenspace
          (Matrix.toLin' (heisenbergHamiltonianSMatrixOnMagSector J N k.val))
          (saturatedFerromagnetEigenvalueS (V := V) J N)) ≤ 1 := by
  classical
  haveI : Nonempty (magConfigS V N k.val) :=
    magConfigS_nonempty_of_le_card_mul (Nat.lt_succ_iff.mp k.isLt)
  obtain ⟨c, hc⟩ := LatticeSystem.Math.exists_gt_of_finite
    (fun σ : V → Fin (N + 1) => heisenbergHamiltonianSReMatrix J N σ σ)
  have hshift :
      (c • (1 : Matrix (magConfigS V N k.val) (magConfigS V N k.val) ℝ)
            - heisenbergHamiltonianSReMatrixOnMagSector J N k.val).mulVec
          (fun σ => (magSectorRestriction (M := k.val) (ladderIterateUp V N k) σ).re) =
        (c - (saturatedFerromagnetEigenvalueS (V := V) J N).re) •
          fun σ => (magSectorRestriction (M := k.val) (ladderIterateUp V N k) σ).re := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      heisenbergHamiltonianSReMatrixOnMagSector_mulVec_ladder_restriction J hJ_real k, sub_smul]
  have hre := LatticeSystem.Math.PerronFrobenius.eigenspace_finrank_le_one_of_pos_eigenvec
    (isIrreducible_shiftedHeisenbergSReMatrixOnMagSector_connected_ferro
      (N := N) (M := k.val) hGconn hJ_supp hJ_ferro hJ_real hJ_sym hc)
    hshift fun σ => ladderIterateUp_restriction_re_pos k σ
  rw [eigenspace_smul_one_sub_finrank_eq, sub_sub_cancel] at hre
  have hcplx := matrix_complex_eigenspace_finrank_le_one_of_real
    (heisenbergHamiltonianSReMatrixOnMagSector J N k.val)
    (saturatedFerromagnetEigenvalueS (V := V) J N).re hre
  have hmap : (heisenbergHamiltonianSReMatrixOnMagSector J N k.val).map ((↑) : ℝ → ℂ) =
      heisenbergHamiltonianSMatrixOnMagSector J N k.val := by
    ext σ τ
    rw [Matrix.map_apply]
    exact (heisenbergHamiltonianSMatrixOnMagSector_apply_eq_ofReal N k.val hJ_real σ τ).symm
  rwa [hmap, saturatedFerromagnetEigenvalueS_ofReal_re hJ_real] at hcplx

end LatticeSystem.Quantum
