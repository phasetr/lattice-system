import LatticeSystem.Quantum.SpinS.AKLTKnabe.BondProjectionAlgebraD6b
import LatticeSystem.Quantum.SpinS.AKLTKnabe.GenericSpectralD7b
import LatticeSystem.Quantum.SpinS.AKLTKnabe.WindowReductionE4

/-!
# Gate E5: from the highest-weight blocks to the Knabe window inequality

This module (Issue #5094; Tasaki §7.1.4, Knabe's argument, pp. 188–190) carries out the block
interface and the spectral landing, on top of the Gate E4 spectral
reduction `akltWindow3H_eigenvalue_reduction_highestWeightE4`.

The chain implemented here is:

1. *self-adjointness* — `akltWindow3H` is Hermitian, since each bond projection is the real
   polynomial `½ D + ⅙ D² + ⅓` in the Hermitian bond operator `D = Ŝ_x · Ŝ_y`
   (production `spinSDot_isHermitian`).  Gate E4 did **not** need this; the spectral landing does;
2. *the block interface* — `KnabeBlockBoundE5 k` is the statement that the operator `ĥ` restricted
   to the highest-weight space `hw_k` has no eigenvalue in the open interval `(0, 2/5)`, in the
   quantitative form `0 ≤ μ² − (2/5) μ`.  The five spaces `hw_0, …, hw_4` have dimensions
   `1, 3, 6, 6, 3` (Gate E3 `finrank_highestWeightE3_window`);
3. *the block `k = 0`* — discharged here unconditionally: `hw_0 = V_0` is the line spanned by the
   all-up configuration, on which `ĥ` acts by the scalar `3`, so `μ = 3` and `9 − 6/5 ≥ 0`;
4. *the spectral landing (G)* — for an arbitrary Hermitian matrix, if every eigenvalue `μ`
   satisfies `0 ≤ μ² − γμ`, then `H² − γH ⪰ 0`.  This is the unitary diagonalisation
   `Matrix.IsHermitian.spectral_theorem` pushed through the star algebra automorphism
   `Unitary.conjStarAlgAut`, so that the whole computation happens on a diagonal matrix;
5. *the conditional capstone* — combining 1–4 with Gate E4 gives
   `Matrix.PosSemidef (akltWindow3H * akltWindow3H - ((2 : ℂ) / 5) • akltWindow3H)`
   **assuming the four remaining block bounds** `KnabeBlockBoundE5 k` for `k = 1, 2, 3, 4`.
   Those four are the only finite data left on the route (blocks of sizes `3, 6, 6, 3`); they are
   *not* proved in this gate.

No `81 × 81` entry table occurs anywhere in this file: the single matrix entry that is evaluated
is the diagonal entry of `ĥ` at the all-up configuration (`akltWindow3H_apply_upConfigE5`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.1.3 eq. (7.1.6) p. 182, §7.1.4 eq. (7.1.30) pp. 188–190; S. Knabe, *J. Stat. Phys.*
**52**, 627–638 (1988).
-/

namespace LatticeSystem.Quantum.AKLTSl2HighestWeightBoundE5

open LatticeSystem.Quantum
open LatticeSystem.Quantum.AKLTSl2SubmoduleProbeE2
open LatticeSystem.Quantum.AKLTSl2LadderSectorsE3
open LatticeSystem.Quantum.AKLTSl2WindowReductionE4
open LatticeSystem.Quantum.AKLTExactCertificateSector234Sequential
open scoped ComplexOrder

/-! ## 1. The window is Hermitian -/

/-- **The open three-bond AKLT window is Hermitian**, `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` with
`ĥᴴ = ĥ` (Tasaki eq. (7.1.30) with `ℓ = 3`, p. 189).  Each bond projection is Hermitian by the
production `bondSpin2ProjectionS_isHermitian` (Gate D6b).  This is the input of the spectral landing
(G) that Gate E4 did not need. -/
theorem akltWindow3H_isHermitianE5 : (akltWindow3H : ManyBodyOpS (Fin 4) 2).IsHermitian := by
  unfold akltWindow3H
  exact Matrix.IsHermitian.add
    (Matrix.IsHermitian.add (bondSpin2ProjectionS_isHermitian _ _)
      (bondSpin2ProjectionS_isHermitian _ _)) (bondSpin2ProjectionS_isHermitian _ _)

/-! ## 2. The block interface -/

/-- **The Knabe block bound at the highest-weight index `k`**: the window `ĥ` restricted to the
highest-weight space `hw_k = V_k ∩ ker Ŝ⁺_tot` has no eigenvalue in the open interval `(0, 2/5)`,
stated quantitatively as `0 ≤ μ² − (2/5) μ`.

Together with the Gate E4 reduction (every eigenvalue of `ĥ` is an eigenvalue on some `hw_k`,
`k ≤ 4`) these five statements are equivalent to the Knabe window inequality
`ĥ² ≥ (2/5) ĥ`; the spaces `hw_0, …, hw_4` have dimensions `1, 3, 6, 6, 3`. -/
def KnabeBlockBoundE5 (k : ℕ) : Prop :=
  ∀ (μ : ℝ) (u : ManyBodyVecE2 (Fin 4) 2), u ∈ highestWeightE2 (Fin 4) 2 k → u ≠ 0 →
    manyBodyLinE4 (Fin 4) 2 akltWindow3H u = ((μ : ℝ) : ℂ) • u → 0 ≤ μ * μ - 2 / 5 * μ

/-! ## 3. The block `k = 0` -/

/-- The all-up four-site configuration, i.e. the configuration of magnetisation index `0` in the
convention `magSumS σ = Σ_x (σ x).val`. -/
private def upConfigE5 : Fin 4 → Fin (2 + 1) := fun _ => 0

/-- The all-up configuration is the only one of magnetisation index `0`; this is what makes the
sector `V_0` (hence `hw_0 = V_0`) one-dimensional. -/
private theorem eq_upConfigE5 (σ : Fin 4 → Fin (2 + 1)) (hσ : magSumS σ = 0) :
    σ = upConfigE5 := by
  funext x
  have hsum : ∑ y : Fin 4, (σ y).val = 0 := hσ
  have hx : (σ x).val = 0 := Finset.sum_eq_zero_iff.mp hsum x (Finset.mem_univ x)
  exact Fin.ext hx

/-- **The only matrix entry of `ĥ` evaluated on the whole route**: the diagonal entry at the
all-up configuration is `3`, because each of the three bond projections acts by `1` on the aligned
two-site state (sublabel `0` of `sector2P2Entry`). -/
private theorem akltWindow3H_apply_upConfigE5 :
    akltWindow3H upConfigE5 upConfigE5 = 3 := by
  rw [akltWindow3H_apply_eq_physicalHEntry]
  norm_num [physicalHEntry, bond01Entry, bond12Entry, bond23Entry, sector2P2Entry, upConfigE5]

/-- **Gate E5, block `k = 0`, discharged.**  On the one-dimensional highest-weight space
`hw_0 = V_0` (the line spanned by the all-up configuration) the window acts by the scalar `3`, so
its only eigenvalue there is `μ = 3` and `0 ≤ 3 · 3 − (2/5) · 3 = 39/5`.

This is the `S = 4` multiplet, whose block matrix is the `1 × 1` matrix
`[39/5]`. -/
theorem knabeBlockBoundE5_zero : KnabeBlockBoundE5 0 := by
  intro μ u hu hu0 heig
  have huV : u ∈ magSectorE2 (Fin 4) 2 0 := (Submodule.mem_inf.mp hu).1
  have hsupp := (mem_magSectorE3_iff (Fin 4) 2 0 u).mp huV
  have hne : WithLp.ofLp u upConfigE5 ≠ 0 := by
    intro h
    refine hu0 (WithLp.ofLp_injective 2 (funext fun σ => ?_))
    by_cases hσ : magSumS σ = 0
    · rw [eq_upConfigE5 σ hσ, h]
      rfl
    · rw [hsupp σ hσ]
      rfl
  have hcomp := congrFun (congrArg WithLp.ofLp heig) upConfigE5
  rw [ofLp_manyBodyLinE4] at hcomp
  have hlhs : (akltWindow3H.mulVec (WithLp.ofLp u)) upConfigE5
      = akltWindow3H upConfigE5 upConfigE5 * WithLp.ofLp u upConfigE5 := by
    change ∑ τ, akltWindow3H upConfigE5 τ * WithLp.ofLp u τ
        = akltWindow3H upConfigE5 upConfigE5 * WithLp.ofLp u upConfigE5
    refine Fintype.sum_eq_single upConfigE5 fun τ hτ => ?_
    rw [hsupp τ fun hc => hτ (eq_upConfigE5 τ hc), mul_zero]
  rw [hlhs, akltWindow3H_apply_upConfigE5] at hcomp
  have hrhs : WithLp.ofLp (((μ : ℝ) : ℂ) • u) upConfigE5
      = ((μ : ℝ) : ℂ) * WithLp.ofLp u upConfigE5 := rfl
  rw [hrhs] at hcomp
  have hμ : ((μ : ℝ) : ℂ) = 3 := (mul_right_cancel₀ hne hcomp).symm
  have hμr : μ = 3 := by exact_mod_cast hμ
  rw [hμr]
  norm_num

/-! ## 4. The spectral landing -/

/-- **The spectral landing, generic form.**  If every eigenvalue `μ` of a Hermitian matrix `H`
satisfies `0 ≤ μ² − γ μ`, then `H² − γ H` is positive semidefinite.

The proof conjugates by the unitary of `Matrix.IsHermitian.spectral_theorem`: since
`Unitary.conjStarAlgAut` is a star algebra automorphism, the polynomial `X² − γX` is computed on
the *diagonal* matrix of eigenvalues, where positivity is entrywise. -/
theorem posSemidef_sq_sub_smul_of_eigenvaluesE5 {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) (γ : ℝ)
    (hev : ∀ i, 0 ≤ hH.eigenvalues i * hH.eigenvalues i - γ * hH.eigenvalues i) :
    (H * H - ((γ : ℝ) : ℂ) • H).PosSemidef := by
  have hγ : ((γ : ℝ) : ℂ) = RCLike.ofReal γ := rfl
  have hkey : H * H - ((γ : ℝ) : ℂ) • H
      = Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hH.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
              * Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)
            - ((γ : ℝ) : ℂ) • Matrix.diagonal (RCLike.ofReal ∘ hH.eigenvalues)) := by
    rw [map_sub, map_mul, map_smul, ← hH.spectral_theorem]
  have hdiag : Matrix.PosSemidef (Matrix.diagonal ((RCLike.ofReal ∘ hH.eigenvalues : n → ℂ))
        * Matrix.diagonal ((RCLike.ofReal ∘ hH.eigenvalues : n → ℂ))
      - ((γ : ℝ) : ℂ) • Matrix.diagonal ((RCLike.ofReal ∘ hH.eigenvalues : n → ℂ))) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul, Matrix.diagonal_sub]
    refine Matrix.posSemidef_diagonal_iff.mpr fun i => ?_
    change (0 : ℂ) ≤ (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ) i
        * (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ) i
      - ((γ : ℝ) : ℂ) * (RCLike.ofReal ∘ hH.eigenvalues : n → ℂ) i
    rw [Function.comp_apply, hγ, ← RCLike.ofReal_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_sub,
      RCLike.ofReal_nonneg]
    exact hev i
  rw [hkey, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  exact hdiag.mul_mul_conjTranspose_same _

/-! ## 5. The conditional capstone -/

/-- **Every eigenvalue of the window obeys the Knabe quadratic bound**, given the five block
bounds.  The eigenvector of `Matrix.IsHermitian.eigenvectorBasis` is fed into the Gate E4 spectral
reduction, which produces a nonzero highest-weight vector of index `k ≤ 4` for the same
eigenvalue. -/
theorem eigenvalues_knabe_boundE5 (hb : ∀ k, k ≤ 4 → KnabeBlockBoundE5 k)
    (i : Fin 4 → Fin (2 + 1)) :
    0 ≤ akltWindow3H_isHermitianE5.eigenvalues i * akltWindow3H_isHermitianE5.eigenvalues i
      - 2 / 5 * akltWindow3H_isHermitianE5.eigenvalues i := by
  have hvne : (akltWindow3H_isHermitianE5.eigenvectorBasis i : ManyBodyVecE2 (Fin 4) 2) ≠ 0 :=
    akltWindow3H_isHermitianE5.eigenvectorBasis.orthonormal.ne_zero i
  have heig : manyBodyLinE4 (Fin 4) 2 akltWindow3H
        (akltWindow3H_isHermitianE5.eigenvectorBasis i)
      = ((akltWindow3H_isHermitianE5.eigenvalues i : ℝ) : ℂ) •
        (akltWindow3H_isHermitianE5.eigenvectorBasis i : ManyBodyVecE2 (Fin 4) 2) := by
    refine WithLp.ofLp_injective 2 ?_
    rw [ofLp_manyBodyLinE4, WithLp.ofLp_smul]
    exact (akltWindow3H_isHermitianE5.mulVec_eigenvectorBasis i).trans
      (Complex.coe_smul _ _).symm
  obtain ⟨k, hk, u, hu, hu0, hueig⟩ :=
    akltWindow3H_eigenvalue_reduction_highestWeightE4 _ _ hvne heig
  exact hb k hk _ u hu hu0 hueig

/-- **Gate E5 capstone (conditional).**  Assuming the four remaining highest-weight block bounds
(`k = 1, 2, 3, 4`, of dimensions `3, 6, 6, 3`), the Knabe window inequality

  `ĥ² − (2/5) ĥ ≥ 0`,  i.e.  `ε₃ ≥ 2/5`,

holds for the open three-bond window `ĥ = P̂₀₁ + P̂₁₂ + P̂₂₃` of Tasaki eq. (7.1.30) with `ℓ = 3`
(pp. 188–190; Knabe 1988).  The block `k = 0` is supplied by `knabeBlockBoundE5_zero`.

The statement is the one of `akltWindow3H_knabe_posSemidef`, whose current proof goes through the
`81 × 81` rational certificate; this route replaces that certificate by the five highest-weight
blocks.

**Normalisation (pitfall R4).**  The constant `2/5` belongs to the normalisation `ĥ = Σ P̂` and to
no other: it becomes `1/10` for Tasaki's `Ĥ'` of eq. (7.1.7) and `1/5` for the (7.1.1)-normalised
`akltHamiltonianS`. -/
theorem akltWindow3H_knabe_posSemidefE5 (hb1 : KnabeBlockBoundE5 1) (hb2 : KnabeBlockBoundE5 2)
    (hb3 : KnabeBlockBoundE5 3) (hb4 : KnabeBlockBoundE5 4) :
    Matrix.PosSemidef (akltWindow3H * akltWindow3H - ((2 : ℂ) / 5) • akltWindow3H) := by
  have hb : ∀ k, k ≤ 4 → KnabeBlockBoundE5 k := by
    intro k hk
    interval_cases k
    · exact knabeBlockBoundE5_zero
    · exact hb1
    · exact hb2
    · exact hb3
    · exact hb4
  have hcast : ((2 : ℂ) / 5) = (((2 / 5 : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast]
  exact posSemidef_sq_sub_smul_of_eigenvaluesE5 akltWindow3H_isHermitianE5 (2 / 5)
    (eigenvalues_knabe_boundE5 hb)

end LatticeSystem.Quantum.AKLTSl2HighestWeightBoundE5
