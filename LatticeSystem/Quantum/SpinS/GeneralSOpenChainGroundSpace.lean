import LatticeSystem.Quantum.SpinS.GeneralSCasimirSpectrum
import LatticeSystem.Quantum.SpinS.AKLTOpenChain
import LatticeSystem.Math.FrustrationFree
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Tasaki §8.3.1: the ground space of the general-`S` open AKLT chain is the joint bond kernel

The general-`S` open-chain Hamiltonian `Ĥ = Σ_{x ∈ openBonds L} ĥ_x` (`openAKLTHamiltonianGeneralS`)
is a sum of positive-semidefinite bond terms (`bondCasimirPenaltyS_posSemidef`), hence itself
positive semidefinite, and its zero-energy space is *frustration-free*: a state has zero energy
iff it is annihilated by every bond term separately (Tasaki Appendix Lemmas A.9/A.10,
`Math/FrustrationFree`).  Composed with the prime-power bond divisibility of
`GeneralSOpenChainBondTerm` and the boundary shape of `AKLTOpenChainWeylFactorization`, this pins
the Weyl image of every ground state to the `(S+1)²` boundary multidegrees of §8.3.1, p. 252
(`weylMap_groundSpaceGeneralS_eq_boundary_mul_prod`).

Read in the opposite direction the same characterisation *constructs* ground states: the `(S+1)²`
explicit polynomials `X^{boundaryDeg m S ab} · ∏_x f_x^S` are Weyl images
(`openVBSStateGeneralS`), each is annihilated by every bond term, and they are linearly
independent, which gives the lower half `(S+1)² ≤ dim` of Tasaki's edge degeneracy
(`succ_sq_le_finrank_openAKLTGroundSpaceGeneralS`) and, as a by-product, the attainment of the
ground energy `0` (`isGroundEnergy_openAKLTHamiltonianGeneralS`).  The matching upper bound is not
proved here.

The Hamiltonian is already normalised to ground energy `0` (unlike the `S = 1` open chain
`openProjHamiltonianS`, which needs an affine shift), so the frustration-free argument here carries
every local energy `0` with no shift, mirroring `openGroundSpace_isVBSGroundForm`.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §7.2.3, eq. (7.2.46), p. 205; §8.3.1, p. 252; Appendix A.2.3, Lemmas A.9–A.10, pp. 469–470.
-/

open Matrix
open scoped ComplexOrder

namespace LatticeSystem.Quantum

open LatticeSystem.Math LatticeSystem.Quantum.AKLTUniqueness MvPolynomial

/-- The **zero-energy space of the general-`S` open chain**: the eigenspace of the Hamiltonian's
linear map at eigenvalue `0`.  For `2 ≤ L` and `S ≠ 0` the Hamiltonian is positive semidefinite
(`openAKLTHamiltonianGeneralS_posSemidef`) and `0` really is its ground energy, the boundary states
`openVBSStateGeneralS` being explicit nonzero zero modes
(`isGroundEnergy_openAKLTHamiltonianGeneralS`); the definition itself assumes neither. -/
noncomputable def openAKLTGroundSpaceGeneralS (L S : ℕ) :
    Submodule ℂ ((Fin L → Fin (2 * S + 1)) → ℂ) :=
  Module.End.eigenspace (Matrix.mulVecLin (openAKLTHamiltonianGeneralS L S)) 0

/-- **The zero-energy space is the kernel of the Hamiltonian.** -/
theorem openAKLTGroundSpaceGeneralS_eq_ker (L S : ℕ) :
    openAKLTGroundSpaceGeneralS L S
      = LinearMap.ker (Matrix.mulVecLin (openAKLTHamiltonianGeneralS L S)) := by
  ext Φ
  rw [openAKLTGroundSpaceGeneralS, Module.End.mem_eigenspace_iff, zero_smul, LinearMap.mem_ker]

/-- **`Ĥ ≥ 0`**, so `0` lower-bounds the energy: each bond term is positive semidefinite
(`bondCasimirPenaltyS_posSemidef`), and a sum of positive-semidefinite matrices is
positive semidefinite. -/
theorem openAKLTHamiltonianGeneralS_posSemidef {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) :
    (openAKLTHamiltonianGeneralS L S).PosSemidef := by
  rw [openAKLTHamiltonianGeneralS]
  exact Finset.sum_induction _ _ (fun _ _ => Matrix.PosSemidef.add) Matrix.PosSemidef.zero
    fun x _ => bondCasimirPenaltyS_posSemidef (ne_ringSucc (by omega) x) hS

/-- **Headline: the zero-energy space is the joint bond kernel** (frustration-freeness).  A state
has zero energy iff it is annihilated by every open-bond Casimir penalty term separately. -/
theorem mem_openAKLTGroundSpaceGeneralS_iff {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0)
    (Φ : (Fin L → Fin (2 * S + 1)) → ℂ) :
    Φ ∈ openAKLTGroundSpaceGeneralS L S
      ↔ ∀ x ∈ openBonds L, (bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ = 0 := by
  have hlb : ∀ x ∈ openBonds L,
      (bondCasimirPenaltyS x (ringSucc x) S
        - ((0 : ℝ) : ℂ) • (1 : ManyBodyOpS (Fin L) (2 * S))).PosSemidef := fun x _ => by
    simpa using bondCasimirPenaltyS_posSemidef (ne_ringSucc (by omega) x) hS
  rw [openAKLTGroundSpaceGeneralS_eq_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    openAKLTHamiltonianGeneralS]
  refine ⟨fun h x hx => ?_, fun h => ?_⟩
  · have hgs : (∑ x ∈ openBonds L, bondCasimirPenaltyS x (ringSucc x) S).mulVec Φ
        = ((∑ _x ∈ openBonds L, (0 : ℝ) : ℝ) : ℂ) • Φ := by simpa using h
    simpa using frustration_free_local_eigen (openBonds L)
      (fun x : Fin L => bondCasimirPenaltyS x (ringSucc x) S) (fun _ => (0 : ℝ)) Φ hlb hgs x hx
  · rw [Matrix.sum_mulVec]
    exact Finset.sum_eq_zero h

/-- **Boundary shape of the general-`S` open-chain ground states** (Tasaki §8.3.1, p. 252).  The
Weyl image of any zero-energy state factors as the product `∏_x f_x^S` of the `S`-th powers of the
open bond factors times a boundary form: a linear combination of the `(S+1)²` monomials
`X^{boundaryDeg m S ab}`, which involve only the two end sites and record Tasaki's two free
effective spin-`S/2` edge spins.

Proof: frustration-freeness (`mem_openAKLTGroundSpaceGeneralS_iff`) turns membership into
annihilation by every bond term, which yields the prime-power divisibility
`prod_fBond_pow_dvd_weylMap_of_annihilated`; the per-site degree input is the weighted homogeneity
of the Weyl image, and `exists_boundary_factorization` supplies the shape. -/
theorem weylMap_groundSpaceGeneralS_eq_boundary_mul_prod {m S : ℕ} (hS : S ≠ 0)
    {Φ : (Fin (m + 2) → Fin (2 * S + 1)) → ℂ}
    (hΦ : Φ ∈ openAKLTGroundSpaceGeneralS (m + 2) S) :
    ∃ c : Fin (S + 1) × Fin (S + 1) → ℂ,
      weylMap Φ
        = (∑ ab : Fin (S + 1) × Fin (S + 1), monomial (boundaryDeg m S ab) (c ab))
            * ∏ x ∈ openBonds (m + 2), fBond x ^ S :=
  exists_boundary_factorization (weylMap_isWeightedHomogeneous Φ)
    (prod_fBond_pow_dvd_weylMap_of_annihilated (by omega) S Φ
      ((mem_openAKLTGroundSpaceGeneralS_iff (by omega) hS Φ).mp hΦ))

/-! ## The `(S+1)²` boundary states and the lower bound on the ground-space dimension -/

/-- **The boundary form times the bond product has the per-site degrees of a Weyl image.**  The
boundary monomial `X^{boundaryDeg m S ab}` carries degree `S` at each of the two end sites, and the
bond product `∏_x f_x^S` carries `S` at each end and `2S` in the bulk, so the product carries `2S`
at every site — exactly the per-site degree of a Weyl image
(`weylMap_isWeightedHomogeneous` at `N = 2S`).  This is what makes the polynomial a Weyl image at
all. -/
theorem boundaryMonomial_mul_prod_isWeightedHomogeneous (m S : ℕ)
    (ab : Fin (S + 1) × Fin (S + 1)) :
    ((monomial (boundaryDeg m S ab) 1 : MvPolynomial (Fin (m + 2) × Fin 2) ℂ)
        * ∏ x ∈ openBonds (m + 2), fBond x ^ S).IsWeightedHomogeneous
      (siteWeight (L := m + 2)) (∑ x : Fin (m + 2), Finsupp.single x (2 * S)) := by
  have hmono : (monomial (boundaryDeg m S ab) 1
      : MvPolynomial (Fin (m + 2) × Fin 2) ℂ).IsWeightedHomogeneous (siteWeight (L := m + 2))
        (Finsupp.single (0 : Fin (m + 2)) S + Finsupp.single (Fin.last (m + 1)) S) :=
    isWeightedHomogeneous_monomial _ _ _ (by
      rw [boundaryDeg, map_add, weight_siteWeight_mdSite, weight_siteWeight_mdSite])
  have hdeg : (Finsupp.single (0 : Fin (m + 2)) S + Finsupp.single (Fin.last (m + 1)) S)
      + S • (∑ x ∈ openBonds (m + 2), (Finsupp.single x 1 + Finsupp.single (ringSucc x) 1))
      = ∑ x : Fin (m + 2), Finsupp.single x (2 * S) := by
    have hz : (⟨0, by omega⟩ : Fin (m + 2)) = (0 : Fin (m + 2)) := Fin.ext (by simp)
    have hl : (⟨m + 2 - 1, by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext (by simp)
    have hfst := prodWeight_apply_first (L := m + 2) (by omega)
    have hlst := prodWeight_apply_last (L := m + 2) (by omega)
    have hne : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by simp [Fin.ext_iff]
    rw [hz] at hfst
    rw [hl] at hlst
    ext y
    rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      Finsupp.smul_apply, smul_eq_mul, weylMapWeight_apply]
    by_cases hy0 : y = 0
    · subst hy0
      rw [if_pos rfl, if_neg (Ne.symm hne), hfst]
      omega
    · by_cases hyl : y = Fin.last (m + 1)
      · subst hyl
        rw [if_neg hne, if_pos rfl, hlst]
        omega
      · have h0 : 0 < y.val := Nat.pos_of_ne_zero fun h => hy0 (Fin.ext (by simp [h]))
        have hlt : y.val ≠ m + 1 := fun h => hyl (Fin.ext (by simp [h]))
        have h1 : y.val + 1 < m + 2 := by have := y.isLt; omega
        rw [if_neg (fun h => hy0 h.symm), if_neg (fun h => hyl h.symm),
          prodWeight_apply_of_interior h0 h1]
        omega
  rw [← hdeg]
  exact hmono.mul (prod_openBonds_fBond_pow_isWeightedHomogeneous (L := m + 2) S)

/-- The **general-`S` open VBS boundary states** `Φ_{ab}` (Tasaki §8.3.1, p. 252): the state whose
Weyl image is `u_1^{S−a} v_1^a · u_L^{S−b} v_L^b · ∏_x f_x^S`, i.e. `S` valence bonds on every link
of the open chain together with the two free effective spin-`S/2` edge spins `a, b ∈ {0, …, S}`.
The `(S+1)²` of them are the zero modes that force the ground-space dimension up to `(S+1)²`.

The state is defined as the Weyl preimage of that polynomial rather than as an explicit matrix
product: the polynomial is what the bond kernel
(`bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd`) and the boundary shape (`boundaryDeg`) are
both stated against, so membership and independence are both read off the polynomial layer. -/
noncomputable def openVBSStateGeneralS (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    (Fin (m + 2) → Fin (2 * S + 1)) → ℂ :=
  weylPreimage (N := 2 * S)
    (monomial (boundaryDeg m S ab) 1 * ∏ x ∈ openBonds (m + 2), fBond x ^ S)

/-- **The boundary states realise their defining polynomials.**  The Weyl map is onto its per-site
graded piece (`weylMap_weylPreimage`), and the defining polynomial lies in that piece
(`boundaryMonomial_mul_prod_isWeightedHomogeneous`), so `Φ_{ab}` really is the state whose Weyl
image is the boundary monomial times `∏_x f_x^S`. -/
theorem weylMap_openVBSStateGeneralS (m S : ℕ) (ab : Fin (S + 1) × Fin (S + 1)) :
    weylMap (openVBSStateGeneralS m S ab)
      = monomial (boundaryDeg m S ab) 1 * ∏ x ∈ openBonds (m + 2), fBond x ^ S :=
  weylMap_weylPreimage (boundaryMonomial_mul_prod_isWeightedHomogeneous m S ab)

/-- **Every boundary state is a ground state.**  Frustration-freeness reduces membership to
annihilation by each bond term (`mem_openAKLTGroundSpaceGeneralS_iff`), which is
`f_x^S`-divisibility of the Weyl image
(`bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd`); that divisibility is immediate because
`f_x^S` is one factor of the product the state is built from. -/
theorem openVBSStateGeneralS_mem_openAKLTGroundSpaceGeneralS {m S : ℕ} (hS : S ≠ 0)
    (ab : Fin (S + 1) × Fin (S + 1)) :
    openVBSStateGeneralS m S ab ∈ openAKLTGroundSpaceGeneralS (m + 2) S := by
  rw [mem_openAKLTGroundSpaceGeneralS_iff (by omega) hS]
  intro x hx
  rw [bondCasimirPenaltyS_mulVec_eq_zero_iff_fBond_pow_dvd (by omega) x S,
    weylMap_openVBSStateGeneralS]
  exact (Finset.dvd_prod_of_mem (fun z => fBond z ^ S) hx).mul_left _

/-- **The `(S+1)²` boundary states are linearly independent** (Tasaki §8.3.1, p. 252).  The Weyl map
is linear, so independence of the images already forces independence of the states themselves
(`LinearIndependent.of_comp`; injectivity of the Weyl map is not needed).  Those images are the
pairwise distinct monomials `X^{boundaryDeg m S ab}` (`boundaryDeg_injective`) — a subfamily of the
monomial basis — multiplied by the single nonzero polynomial `∏_x f_x^S`, and multiplication by a
nonzero polynomial is injective in the polynomial domain. -/
theorem openVBSStateGeneralS_linearIndependent (m S : ℕ) :
    LinearIndependent ℂ fun ab : Fin (S + 1) × Fin (S + 1) => openVBSStateGeneralS m S ab := by
  refine LinearIndependent.of_comp (weylMap (L := m + 2) (N := 2 * S)) ?_
  have hmono : LinearIndependent ℂ fun ab : Fin (S + 1) × Fin (S + 1) =>
      (monomial (boundaryDeg m S ab) 1 : MvPolynomial (Fin (m + 2) × Fin 2) ℂ) := by
    have h := (basisMonomials (Fin (m + 2) × Fin 2) ℂ).linearIndependent.comp
      (boundaryDeg m S) boundaryDeg_injective
    simpa [Function.comp_def, coe_basisMonomials] using h
  have hker : LinearMap.ker
      (LinearMap.mulRight ℂ (∏ x ∈ openBonds (m + 2), fBond x ^ S)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro p q hpq
    exact mul_right_cancel₀ (prod_openBonds_fBond_pow_ne_zero (by omega) S) hpq
  have hmul := hmono.map' (LinearMap.mulRight ℂ (∏ x ∈ openBonds (m + 2), fBond x ^ S)) hker
  simpa [Function.comp_def, weylMap_openVBSStateGeneralS] using hmul

/-- **Tasaki §8.3.1, p. 252, the lower half of the `(S+1)²` edge degeneracy.**  The ground space of
the general-`S` open AKLT chain has complex dimension at least `(S+1)²`: the `(S+1)²` independent
boundary states `Φ_{ab}` all sit in it, one for each pair of effective spin-`S/2` edge spins.  At
`S = 1` this is the `4 ≤ dim` bound of Problem 7.2.3.a; the matching upper bound is not proved
here. -/
theorem succ_sq_le_finrank_openAKLTGroundSpaceGeneralS {m S : ℕ} (hS : S ≠ 0) :
    (S + 1) ^ 2 ≤ Module.finrank ℂ (openAKLTGroundSpaceGeneralS (m + 2) S) := by
  have hle : Submodule.span ℂ
      (Set.range fun ab : Fin (S + 1) × Fin (S + 1) => openVBSStateGeneralS m S ab)
      ≤ openAKLTGroundSpaceGeneralS (m + 2) S := by
    rw [Submodule.span_le]
    rintro v ⟨ab, rfl⟩
    exact openVBSStateGeneralS_mem_openAKLTGroundSpaceGeneralS hS ab
  have hrank : Module.finrank ℂ (Submodule.span ℂ
      (Set.range fun ab : Fin (S + 1) × Fin (S + 1) => openVBSStateGeneralS m S ab))
      = (S + 1) ^ 2 := by
    rw [finrank_span_eq_card (openVBSStateGeneralS_linearIndependent m S), Fintype.card_prod,
      Fintype.card_fin, sq]
  rw [← hrank]
  exact Submodule.finrank_mono hle

/-- **The ground energy of the general-`S` open AKLT chain is `0`.**  The Hamiltonian is already
normalised (no affine shift is needed, unlike the `S = 1` chain): it is positive semidefinite, so
`0` lower-bounds its real spectrum, and the boundary state `Φ_{0,0}` is a nonzero zero mode, so `0`
is attained. -/
theorem isGroundEnergy_openAKLTHamiltonianGeneralS {L S : ℕ} (hL : 2 ≤ L) (hS : S ≠ 0) :
    IsGroundEnergy (openAKLTHamiltonianGeneralS L S) 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 2 := ⟨L - 2, by omega⟩
  refine ⟨⟨openVBSStateGeneralS m S (0, 0),
    (openVBSStateGeneralS_linearIndependent m S).ne_zero (0, 0), ?_⟩, fun E hE => ?_⟩
  · have hmem := openVBSStateGeneralS_mem_openAKLTGroundSpaceGeneralS (m := m) hS (0, 0)
    rw [openAKLTGroundSpaceGeneralS_eq_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hmem
    rw [hmem]
    simp
  · exact realSpectrum_nonneg_of_posSemidef
      (openAKLTHamiltonianGeneralS_posSemidef (by omega) hS) hE

end LatticeSystem.Quantum
