import LatticeSystem.Quantum.SpinS.SaturatedCoherentAmplitude
import LatticeSystem.Quantum.SpinS.SaturatedFullLadderOrthogonality
import LatticeSystem.Quantum.SpinS.SaturatedLadderJointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Weight-sector expansion of the saturated-ferromagnet coherent state

The ground states of the saturated ferromagnet are labelled by the total magnetisation `M`, and
the normalised magnetisation-sector state is
`Φ_M = (Ŝ_tot^-)^{|Λ|S - M} Φ↑ / ‖(Ŝ_tot^-)^{|Λ|S - M} Φ↑‖`.  This module introduces the
normalisation (`saturatedLadderNorm`), the normalised sector state (`saturatedWeightVector`,
indexed by `k = |Λ|S - M`) and the coefficient `c_M(θ) = ⟪Φ_M, Ξ_{θ,0}⟫`, and proves that the
coherent state at `φ = 0` is the sum `Σ_M c_M(θ) Φ_M` with every coefficient nonzero for
`0 < θ < π`.

The expansion comes from the identification of the joint `(Ĥ, (Ŝ_tot)²)`-eigenspace with the span
of the ladder iterates, with the coefficients extracted by their pairwise orthogonality.
Nonvanishing comes from the site-product form of `Ξ_{θ,0}` together with the one-dimensionality of
each weight sector, so no closed-form coefficient is needed.

The ambient vector space stays the raw function type `(V → Fin (N + 1)) → ℂ` carrying all the
ladder and magnetisation-sector machinery; the `ℓ²` structure of `EuclideanSpace` is used only for
the two scalars — the norm in the definition of `Φ_M` and the inner product defining `c_M`.

References: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020.
The normalised sector state `Φ_M` is eq. (2.4.9), p. 33; the expansion `Φ = Σ_M c_M Φ_M` of a
saturated-ferromagnet ground state is Theorem 2.1 / eq. (2.4.10), p. 34, applied here to
`Φ = Ξ_{θ,0}`; the coherent state `Ξ_{θ,φ}` is eq. (2.4.6), p. 33 and the global rotations are
eq. (2.2.11), p. 22.  Both results feed Problem 2.4.b (statement p. 34, solution pp. 496-497,
eq. (S.17)).
-/

namespace LatticeSystem.Quantum

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## The normalised magnetisation-sector states -/

/-- **Normalisation of the `k`-th ladder iterate**: the `ℓ²` norm `‖(Ŝ_tot^-)^k Φ↑‖`, i.e. the
denominator of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.4.9), p. 33,
at `M = |Λ|S - k`.  The `EuclideanSpace` ascription is what selects the `ℓ²` norm: the raw
function type `(V → Fin (N + 1)) → ℂ` carries the supremum norm instead. -/
noncomputable def saturatedLadderNorm (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ)
    (k : Fin (Fintype.card V * N + 1)) : ℝ :=
  ‖(WithLp.toLp 2 (ladderIterateUp V N k) : EuclideanSpace ℂ (V → Fin (N + 1)))‖

/-- **Normalised magnetisation-sector state** `Φ_M` of Tasaki, *Physics and Mathematics of Quantum
Many-Body Systems*, eq. (2.4.9), p. 33, at `M = |Λ|S - k`: the `k`-th ladder iterate
`(Ŝ_tot^-)^k Φ↑` divided by its `ℓ²` norm. -/
noncomputable def saturatedWeightVector (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ)
    (k : Fin (Fintype.card V * N + 1)) : (V → Fin (N + 1)) → ℂ :=
  ((saturatedLadderNorm V N k : ℂ))⁻¹ • ladderIterateUp V N k

/-- **Coefficient** `c_M(θ) = ⟪Φ_M, Ξ_{θ,0}⟫` of `Φ_M` in the expansion of the coherent state,
i.e. the `c_M` of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, eq. (2.4.10),
p. 34, taken at `Φ = Ξ_{θ,0}` and `M = |Λ|S - k`.  The arguments are in the source order
`⟪Φ_M, Ξ_{θ,0}⟫`, so the conjugation sits on `Φ_M`. -/
noncomputable def saturatedCoherentCoeff (V : Type*) [Fintype V] [DecidableEq V] (N : ℕ)
    (θ : ℝ) (k : Fin (Fintype.card V * N + 1)) : ℂ :=
  inner ℂ (WithLp.toLp 2 (saturatedWeightVector V N k) : EuclideanSpace ℂ (V → Fin (N + 1)))
    (WithLp.toLp 2 (saturatedCoherentState V N θ 0))

/-! ## Support and self-pairing of a ladder iterate -/

/-- **Support of a ladder iterate**: `(Ŝ_tot^-)^k Φ↑` vanishes at every configuration whose
magnetisation eigenvalue differs from `|Λ|S - k`, because that iterate lies in the corresponding
magnetisation sector. -/
theorem ladderIterateUp_apply_eq_zero_of_magEigenvalueS_ne
    (k : Fin (Fintype.card V * N + 1)) {σ : V → Fin (N + 1)}
    (h : magEigenvalueS σ ≠ ladderEigenvalueUp V N k) : ladderIterateUp V N k σ = 0 :=
  magSubspaceS_apply_eq_zero_of_magEigenvalueS_ne
    (totalSpinSOpMinus_pow_allAlignedStateS_zero_mem_magSubspaceS k.val) h

/-- The normalisation of a ladder iterate is nonzero, since the iterate itself is nonzero. -/
private lemma saturatedLadderNorm_ne_zero [Nonempty V] (k : Fin (Fintype.card V * N + 1)) :
    saturatedLadderNorm V N k ≠ 0 := by
  rw [saturatedLadderNorm, norm_ne_zero_iff]
  exact fun h => (ladderIterateUp_hasEigenvector k).right ((WithLp.toLp_eq_zero 2).mp h)

/-- Self-pairing of a ladder iterate: `L_k ⬝ᵥ star L_k` is the square of its `ℓ²` norm. -/
private lemma ladderIterateUp_dotProduct_star_self (k : Fin (Fintype.card V * N + 1)) :
    ladderIterateUp V N k ⬝ᵥ star (ladderIterateUp V N k)
      = ((saturatedLadderNorm V N k : ℂ)) ^ 2 :=
  (EuclideanSpace.inner_toLp_toLp (ladderIterateUp V N k) (ladderIterateUp V N k)).symm.trans
    (inner_self_eq_norm_sq_to_K _)

/-! ## The expansion -/

/-- The coherent state at `φ = 0` lies in the span of the ladder iterates, because it is obtained
from the highest-weight state `Φ↑` by an operator commuting with both `Ĥ` and `(Ŝ_tot)²`, so it
stays inside the joint eigenspace, which is exactly that span. -/
private lemma saturatedCoherentState_zero_mem_span [Nonempty V] (θ : ℝ) :
    saturatedCoherentState V N θ 0 ∈ Submodule.span ℂ (Set.range (ladderIterateUp V N)) := by
  classical
  set J : V → V → ℂ := fun _ _ => 0 with hJ
  rw [← saturatedFerromagnetJointEigenspace_eq_span_ladderIterateUp J]
  have hL0 : ladderIterateUp V N 0 = allAlignedStateS V N (0 : Fin (N + 1)) := by
    simp [ladderIterateUp]
  obtain ⟨hH, hC⟩ :=
    ladderIterateUp_mem_saturatedFerromagnetJointEigenspace (V := V) (N := N) J 0
  simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply, hL0] at hH hC
  have hcH : Commute (heisenbergHamiltonianS J N) (saturatedGlobalRot2 V N θ) := by
    rw [saturatedGlobalRot2]
    exact (((heisenbergHamiltonianS_commute_totalSpinSOp2 (N := N) J).smul_right
      (-Complex.I)).smul_right θ).exp_right
  have hcC : Commute (totalSpinSSquared V N) (saturatedGlobalRot2 V N θ) := by
    rw [saturatedGlobalRot2]
    exact (((totalSpinSSquared_commute_totalSpinSOp2 (V := V) (N := N)).smul_right
      (-Complex.I)).smul_right θ).exp_right
  rw [saturatedCoherentState_zero_eq_globalRot2]
  refine ⟨?_, ?_⟩
  · simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact mulVec_preserves_eigenvalue_of_commuteS hcH hH
  · simp only [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
    exact mulVec_preserves_eigenvalue_of_commuteS hcC hC

/-- **Expansion of the coherent state into magnetisation sectors.**  At `φ = 0` the
saturated-ferromagnet coherent state is `Ξ_{θ,0} = Σ_M c_M(θ) Φ_M`.  This is the
`Φ = Ξ_{θ,0}` instance of Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Theorem 2.1 / eq. (2.4.10), p. 34, with `Φ_M` as in eq. (2.4.9), p. 33.

The coherent state lies in the joint `(Ĥ, (Ŝ_tot)²)`-eigenspace, which is spanned by the ladder
iterates; pairing the resulting expansion with a single iterate and using their orthogonality
identifies each expansion scalar as `c_M(θ)` divided by the normalisation. -/
theorem saturatedCoherentState_zero_eq_sum [Nonempty V] (θ : ℝ) :
    saturatedCoherentState V N θ 0
      = ∑ k, saturatedCoherentCoeff V N θ k • saturatedWeightVector V N k := by
  classical
  obtain ⟨b, hb⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp
      (saturatedCoherentState_zero_mem_span (V := V) (N := N) θ)
  have key : ∀ k, saturatedCoherentCoeff V N θ k • saturatedWeightVector V N k
      = b k • ladderIterateUp V N k := by
    intro k
    have hnorm0 : saturatedLadderNorm V N k ≠ 0 :=
      saturatedLadderNorm_ne_zero (V := V) (N := N) k
    have hnorm : (saturatedLadderNorm V N k : ℂ) ≠ 0 := by exact_mod_cast hnorm0
    have hcoeff : saturatedCoherentCoeff V N θ k = b k * (saturatedLadderNorm V N k : ℂ) := by
      rw [saturatedCoherentCoeff, EuclideanSpace.inner_toLp_toLp, ← hb, saturatedWeightVector,
        star_smul, sum_dotProduct]
      rw [Finset.sum_eq_single k]
      · rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_dotProduct, dotProduct_smul,
          ladderIterateUp_dotProduct_star_self, smul_eq_mul, smul_eq_mul, pow_two,
          inv_mul_cancel_left₀ hnorm]
      · intro j _ hjk
        rw [smul_dotProduct, dotProduct_smul, dotProduct_comm,
          ladderIterateUp_orthogonal (Ne.symm hjk), smul_zero, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ k) h
    rw [hcoeff, saturatedWeightVector, smul_smul, mul_assoc, mul_inv_cancel₀ hnorm, mul_one]
  rw [← hb]
  exact Finset.sum_congr rfl fun k _ => (key k).symm

/-! ## Nonvanishing of the coefficients -/

/-- **Every coefficient is nonzero.**  For `0 < θ < π` and every magnetisation sector `M`, the
coefficient `c_M(θ) = ⟪Φ_M, Ξ_{θ,0}⟫` of Tasaki, *Physics and Mathematics of Quantum Many-Body
Systems*, eq. (2.4.10), p. 34, is nonzero.

At a configuration `σ` where the `k`-th ladder iterate does not vanish, every other sector's
contribution to the expansion vanishes because the sectors have disjoint supports, so `Ξ_{θ,0} σ`
is a nonzero multiple of `c_M(θ)`; and `Ξ_{θ,0} σ` is a product of one-site amplitudes, each
nonzero on `0 < θ < π`.  This is the input that Problem 2.4.b (statement p. 34, solution
pp. 496-497) needs in order to invert the expansion. -/
theorem saturatedCoherentCoeff_ne_zero [Nonempty V] {θ : ℝ}
    (hθ₀ : 0 < θ) (hθπ : θ < Real.pi) (k : Fin (Fintype.card V * N + 1)) :
    saturatedCoherentCoeff V N θ k ≠ 0 := by
  classical
  obtain ⟨σ, hσ⟩ : ∃ σ, ladderIterateUp V N k σ ≠ 0 := by
    by_contra h
    exact (ladderIterateUp_hasEigenvector k).right (funext fun σ => not_not.mp (not_exists.mp h σ))
  have hmag : magEigenvalueS σ = ladderEigenvalueUp V N k := by
    by_contra h
    exact hσ (ladderIterateUp_apply_eq_zero_of_magEigenvalueS_ne k h)
  have hΞ := congrFun (saturatedCoherentState_zero_eq_sum (V := V) (N := N) θ) σ
  rw [Finset.sum_apply, Finset.sum_eq_single k] at hΞ
  · have hprod : saturatedCoherentState V N θ 0 σ ≠ 0 := by
      rw [saturatedCoherentState_zero_apply]
      exact Finset.prod_ne_zero_iff.mpr fun x _ => saturatedCoherentAmp_ne_zero N hθ₀ hθπ (σ x)
    intro hc
    rw [hc] at hΞ
    exact hprod (by simpa using hΞ)
  · intro j _ hjk
    have hne : magEigenvalueS σ ≠ ladderEigenvalueUp V N j := by
      rw [hmag]
      exact fun h => hjk (ladderEigenvalueUp_injective h.symm)
    simp [saturatedWeightVector, ladderIterateUp_apply_eq_zero_of_magEigenvalueS_ne j hne]
  · intro h
    exact absurd (Finset.mem_univ k) h

end LatticeSystem.Quantum
