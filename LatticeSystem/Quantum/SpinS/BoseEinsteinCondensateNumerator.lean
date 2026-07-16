import LatticeSystem.Quantum.SpinS.BoseEinsteinCondensateAlgebra
import LatticeSystem.Quantum.SpinS.AndersonTowerLocality

/-!
# Tasaki §5.3 Theorem 5.2 (BEC low-lying tower states): μ-term numerator algebra (PR-3)

This file supplies the **exact variational-numerator algebra** of the Bose–Einstein-condensation
tower discharge (`tasaki_5_2_bec_tower`, Tasaki §5.3, eq. (5.3.4)): the double commutator of the
chemical-potential XY Hamiltonian `Ĥ_μ = 2 Ĥ_XY − μ Ŝ_tot^{(3)}` (eq. (5.3.2)) with the tower
operator splits exactly into the pure XY double commutator and a single `−μ M` linear term, and
the corresponding variational numerator `⟨Φ, [Aᴴ, [Ĥ_μ, A]] Φ⟩` (the right-hand side of the
Hamiltonian-agnostic gap bound `variational_gap_le_double_commutator`) has the exact real-part
expression `⟨Φ, [Aᴴ, [2 Ĥ_XY, A]] Φ⟩ − μ M (‖AΦ‖² − ‖AᴴΦ‖²)` (§4-b/§4-c of the design note).

Only the *exact algebra* of the numerator is proved here.  The quantitative XY-planar bound on the
pure XY double commutator and the eventual absorption of the residual first-order `−μ M`
moment-difference term into the cubic budget (localized to a `BECSectorCurvatureBound` predicate)
belong to the later PRs of the arc; the μ = 0 half-filling core is the special case of
`chemicalPotential_numerator_muTerm` at `μ = 0`, where the moment-difference term vanishes.

The lemmas are stated for a generic pair `Hxy` (the XY term) and `S` (the total `Ŝ^{(3)}`) with the
single algebraic input `S A − A S = M • A`; for the tower application that input is exactly PR-1's
`totalSpinSOp3_commutator_towerPow` (§4-a), `Hxy := xyHamiltonianS d L`,
`S := totalSpinSOp3 (HypercubicTorus d L) 1`, and then `2 • Hxy − μ • S = Ĥ_μ`
(`xyChemicalPotentialHamiltonianS`) by definition.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §5.3, Theorem 5.2, eqs. (5.3.2)/(5.3.4), pp. 140–141 (Koma–Tasaki [21]); the variational
double-commutator engine is `variational_gap_le_double_commutator` (Anderson-tower Theorem 4.6).
-/

namespace LatticeSystem.Quantum

open Matrix

/-- **Chemical-potential double-commutator decomposition** (§4-b of the design note).  For the
chemical-potential Hamiltonian `H = 2 Hxy − μ S` and any operator `A` that is an eigenoperator of
the adjoint action of `S` with eigenvalue `M` (`S A − A S = M • A`), the symmetric double
commutator with `Aᴴ` splits exactly into the pure XY double commutator and the single first-order
chemical-potential term:
`[Aᴴ, [H, A]] = [Aᴴ, [2 Hxy, A]] − (μ M) • [Aᴴ, A]`.
For the Theorem 5.2 tower operator `A = (Ô_L^{sgn M})^{|M|}` the eigenvalue hypothesis is PR-1's
`totalSpinSOp3_commutator_towerPow`, and `2 Hxy − μ S = Ĥ_μ` (`xyChemicalPotentialHamiltonianS`)
definitionally.  This is the exact algebraic content of the `−μ Ŝ_tot^{(3)}` contribution to the
variational numerator of eq. (5.3.4). -/
theorem chemicalPotential_double_commutator_muTerm {ι : Type*} [Fintype ι]
    (Hxy S Aop : Matrix ι ι ℂ) (μ : ℝ) (M : ℤ)
    (hS : S * Aop - Aop * S = (M : ℂ) • Aop) :
    Matrix.conjTranspose Aop
        * (((2 : ℂ) • Hxy - (μ : ℂ) • S) * Aop - Aop * ((2 : ℂ) • Hxy - (μ : ℂ) • S))
      - (((2 : ℂ) • Hxy - (μ : ℂ) • S) * Aop - Aop * ((2 : ℂ) • Hxy - (μ : ℂ) • S))
        * Matrix.conjTranspose Aop
      = (Matrix.conjTranspose Aop * ((2 : ℂ) • Hxy * Aop - Aop * ((2 : ℂ) • Hxy))
          - ((2 : ℂ) • Hxy * Aop - Aop * ((2 : ℂ) • Hxy)) * Matrix.conjTranspose Aop)
        - ((μ : ℂ) * (M : ℂ))
          • (Matrix.conjTranspose Aop * Aop - Aop * Matrix.conjTranspose Aop) := by
  have hcomm : ((2 : ℂ) • Hxy - (μ : ℂ) • S) * Aop - Aop * ((2 : ℂ) • Hxy - (μ : ℂ) • S)
      = ((2 : ℂ) • Hxy * Aop - Aop * ((2 : ℂ) • Hxy)) - ((μ : ℂ) * (M : ℂ)) • Aop := by
    have hmid : ((μ : ℂ) • S) * Aop - Aop * ((μ : ℂ) • S) = ((μ : ℂ) * (M : ℂ)) • Aop := by
      rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, hS, smul_smul]
    rw [sub_mul, mul_sub, ← hmid]; abel
  rw [hcomm]
  generalize (2 : ℂ) • Hxy * Aop - Aop * ((2 : ℂ) • Hxy) = P
  generalize (μ : ℂ) * (M : ℂ) = q
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel

/-- **Chemical-potential variational numerator, exact `−μ M` term** (§4-c of the design note).  The
real-part variational numerator `⟨Φ, [Aᴴ, [Ĥ_μ, A]] Φ⟩` for `Ĥ_μ = 2 Hxy − μ S` and an
eigenoperator `A` with `S A − A S = M • A` equals the pure XY numerator minus the first-order
chemical-potential term `μ M (‖AΦ‖² − ‖AᴴΦ‖²)`:
`⟨Φ, [Aᴴ, [Ĥ_μ, A]] Φ⟩ = ⟨Φ, [Aᴴ, [2 Hxy, A]] Φ⟩ − μ M (‖AΦ‖² − ‖AᴴΦ‖²)`.
This is the exact right-hand side of `variational_gap_le_double_commutator` for `Ĥ_μ`; the
moment-difference `‖AΦ‖² − ‖AᴴΦ‖²` is the residual first-order term whose cubic absorption is
localized to the later `BECSectorCurvatureBound` predicate. -/
theorem chemicalPotential_numerator_muTerm {ι : Type*} [Fintype ι]
    (Hxy S Aop : Matrix ι ι ℂ) (μ : ℝ) (M : ℤ) (Φ : ι → ℂ)
    (hS : S * Aop - Aop * S = (M : ℂ) • Aop) :
    (star Φ ⬝ᵥ (Matrix.conjTranspose Aop
          * (((2 : ℂ) • Hxy - (μ : ℂ) • S) * Aop - Aop * ((2 : ℂ) • Hxy - (μ : ℂ) • S))
        - (((2 : ℂ) • Hxy - (μ : ℂ) • S) * Aop - Aop * ((2 : ℂ) • Hxy - (μ : ℂ) • S))
          * Matrix.conjTranspose Aop).mulVec Φ).re
      = (star Φ ⬝ᵥ (Matrix.conjTranspose Aop * ((2 : ℂ) • Hxy * Aop - Aop * ((2 : ℂ) • Hxy))
          - ((2 : ℂ) • Hxy * Aop - Aop * ((2 : ℂ) • Hxy))
            * Matrix.conjTranspose Aop).mulVec Φ).re
        - μ * (M : ℝ) * ((star (Aop.mulVec Φ) ⬝ᵥ Aop.mulVec Φ).re
            - (star ((Matrix.conjTranspose Aop).mulVec Φ)
                ⬝ᵥ (Matrix.conjTranspose Aop).mulVec Φ).re) := by
  have hB : star Φ ⬝ᵥ (Matrix.conjTranspose Aop * Aop
        - Aop * Matrix.conjTranspose Aop).mulVec Φ
      = star (Aop.mulVec Φ) ⬝ᵥ Aop.mulVec Φ
        - star ((Matrix.conjTranspose Aop).mulVec Φ) ⬝ᵥ (Matrix.conjTranspose Aop).mulVec Φ := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    congr 1
    · rw [← Matrix.mulVec_mulVec, star_dotProduct_mulVec_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    · rw [← Matrix.mulVec_mulVec, star_dotProduct_mulVec_conjTranspose]
  have hμc : (μ : ℂ) * (M : ℂ) = ((μ * (M : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [chemicalPotential_double_commutator_muTerm Hxy S Aop μ M hS, Matrix.sub_mulVec,
    dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.sub_re, hB,
    hμc, Complex.re_ofReal_mul, Complex.sub_re]

end LatticeSystem.Quantum
