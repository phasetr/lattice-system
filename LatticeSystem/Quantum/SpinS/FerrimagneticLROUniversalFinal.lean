import LatticeSystem.Quantum.SpinS.FerrimagneticLROUniversal
import LatticeSystem.Quantum.SpinS.ConnectedFerrimagneticLRO
import LatticeSystem.Quantum.SpinS.ConnectedTheorem23
import LatticeSystem.Quantum.SpinS.StrictHOutsideFerrimagnetic
import LatticeSystem.Quantum.SpinS.SU2ExpectationLadderIterated
import LatticeSystem.Quantum.SpinS.ConnectedSectorFinrankLeOne
import LatticeSystem.Quantum.SpinS.SectorRestrictionComplexEigval
import LatticeSystem.Quantum.SpinS.DressedMatrixOnMagSectorEigenvalueUnique
import LatticeSystem.Quantum.SpinS.Theorem23Local
import LatticeSystem.Quantum.SpinS.Theorem23Sectors
import LatticeSystem.Quantum.SpinS.FerrimagneticLROCapstone
import LatticeSystem.Quantum.SpinS.EigenspaceFinrankLeOneTransfer
import LatticeSystem.Quantum.SpinS.SubmatrixEigenvalueReal

/-!
# Tasaki §4.1 Theorem 4.4 (Shen–Qiu–Tian): discharge of `shenQiuTian_ferrimagnetic_lro`

This file discharges the documented axiom `shenQiuTian_ferrimagnetic_lro`
(`FerrimagneticLRO.lean`) as a **theorem** with identical signature, for *every*
normalized ground state `Φ` of the connected bipartite antiferromagnetic spin-`S`
Heisenberg model (Issue #4604).

## Strategy (Tasaki chain (4.1.16), assembled over magnetization sectors)

The squared staggered order operator `Ô² = staggeredCasimirOpS A N` is `SU(2)`
invariant, hence commutes with `Ŝ_tot^{(3)}`, `Ŝ⁺_tot`, `Ŝ⁻_tot`.  Both the
expectation `⟨Φ, Ô² Φ⟩.re` and the squared norm `‖Φ‖²` split as finite sums over
magnetization sectors `M` of the diagonal quantities on the weight components
`Φ_M := magSectorEmbedding (magSectorRestriction Φ)`
(`weightPreserving_expectation_eq_sum_sector`, `star_dotProduct_self_eq_sum_sector`).

The per-sector bound is
`S_tot² ‖Φ_M‖² ≤ ⟨Φ_M, Ô² Φ_M⟩.re`,
proved (oriented `|¬A| ≤ |A|`) as follows.  Either `Φ_M = 0` (outside sectors,
forced by the strict outside-sector energy separation
`tasaki23_strict_hOutside_of_connected`), or `Φ_M` lies in an admissible sector
where the bare Heisenberg eigenspace is one-dimensional
(`heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected`),
so `Φ_M` is proportional to the Marshall ground vector `w_M`.  The real Rayleigh
ratio `⟨w_M, Ô² w_M⟩.re / ‖w_M‖²` is `SU(2)`-ladder invariant
(`su2_expectationRatioRe_ladder_iterate_invariant`), so it agrees with the ratio
at a near-central admissible sector, where Tasaki's chain bound
`chain_bound_marshall_sector` gives `γ − m² ≥ S_tot²`.

Summing over sectors collapses `Σ_M ‖Φ_M‖² = ‖Φ‖² = 1` and rewrites `S_tot²` to
the coefficient `(N/2)² (|A| − |B|)²` (`tasaki23PredictedTotalSpin_sq_eq`).

The orientation `by_cases` reduces the general case to the oriented one, using the
sublattice-flip invariance `staggeredCasimirOpS_compl` and the symmetry of the
coefficient under `A ↦ ¬A`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4.1 Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78
(Shen, Qiu, Tian [59]); §2.5 Theorem 2.3, p. 42.
-/

namespace LatticeSystem.Quantum

open Matrix Module

open scoped ComplexOrder

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-- **Scalar scaling of a real expectation.** For any operator `O`, vector `u`, and
scalar `s : ℂ`, `⟨s • u, O (s • u)⟩.re = ‖s‖² ⟨u, O u⟩.re`. -/
private theorem star_smul_dotProduct_mulVec_smul_re
    (O : ManyBodyOpS Λ N) (s : ℂ) (u : (Λ → Fin (N + 1)) → ℂ) :
    (star (s • u) ⬝ᵥ (O.mulVec (s • u))).re =
      Complex.normSq s * (star u ⬝ᵥ (O.mulVec u)).re := by
  rw [Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul,
    smul_eq_mul, ← mul_assoc]
  have hmul : s * star s = (Complex.normSq s : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj]
  rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Real Rayleigh quotient is scale-invariant.** If `Ψ = s • Φ` with `s ≠ 0`,
then the real ratios `⟨·, O ·⟩.re / ‖·‖²` of `Ψ` and `Φ` agree. -/
private theorem ratioRe_eq_of_smul
    (O : ManyBodyOpS Λ N) {s : ℂ} {Φ Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hs : s ≠ 0) (hΨ_eq : Ψ = s • Φ) :
    (star Ψ ⬝ᵥ (O.mulVec Ψ)).re / (star Ψ ⬝ᵥ Ψ).re =
      (star Φ ⬝ᵥ (O.mulVec Φ)).re / (star Φ ⬝ᵥ Φ).re := by
  subst hΨ_eq
  have hO := star_smul_dotProduct_mulVec_smul_re O s Φ
  have hid := star_smul_dotProduct_mulVec_smul_re (1 : ManyBodyOpS Λ N) s Φ
  simp only [Matrix.one_mulVec] at hid
  have hns : Complex.normSq s ≠ 0 := fun hzero => hs (Complex.normSq_eq_zero.mp hzero)
  rw [hO, hid, mul_div_mul_left _ _ hns]

/-- **Sector eigenvector proportionality from `finrank ≤ 1`.** If the bare complex
Heisenberg sector matrix at `M` has `μ`-eigenspace `finrank ≤ 1`, and `Φ0`, `Ψ` are
both `μ`-eigenvectors of the full Heisenberg Hamiltonian lying in the centered
sector `magSubspaceS (card·N/2 − M)`, with `Φ0 ≠ 0`, then `Ψ = s • Φ0` for some
`s : ℂ`.  This is the proportionality extraction underlying the per-sector ratio
identification. -/
private theorem sector_eigenvec_proportional_of_finrank_le_one
    (J : Λ → Λ → ℂ) (M : ℕ) (μ : ℂ)
    {Φ0 Ψ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ0_ne : Φ0 ≠ 0)
    (hΦ0_eig : (heisenbergHamiltonianS J N).mulVec Φ0 = μ • Φ0)
    (hΦ0_mem : Φ0 ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (hΨ_eig : (heisenbergHamiltonianS J N).mulVec Ψ = μ • Ψ)
    (hΨ_mem : Ψ ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ)))
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M)) μ) ≤ 1) :
    ∃ s : ℂ, Ψ = s • Φ0 := by
  classical
  set E := End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J N)) μ
    with hEdef
  set Asub :=
    magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) with hAdef
  have hline : finrank ℂ ↥(E ⊓ Asub) ≤ 1 := by
    subst E
    subst Asub
    exact heisenbergHamiltonianS_eigenspace_inf_magSubspaceS_finrank_le_one_of_sector
      (Λ := Λ) (N := N) J M μ h_sector_pf
  have hΦ0_in : Φ0 ∈ E ⊓ Asub := by
    refine ⟨?_, hΦ0_mem⟩
    change Φ0 ∈ End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J N)) μ
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΦ0_eig
  have hΨ_in : Ψ ∈ E ⊓ Asub := by
    refine ⟨?_, hΨ_mem⟩
    change Ψ ∈ End.eigenspace (Matrix.toLin' (heisenbergHamiltonianS (Λ := Λ) J N)) μ
    rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hΨ_eig
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hline
  obtain ⟨a, ha⟩ := hv ⟨Φ0, hΦ0_in⟩
  obtain ⟨b, hb⟩ := hv ⟨Ψ, hΨ_in⟩
  have ha' : a • (v : (Λ → Fin (N + 1)) → ℂ) = Φ0 := by
    have h := congrArg ((↑) : ↥(E ⊓ Asub) → (Λ → Fin (N + 1)) → ℂ) ha
    simpa using h
  have hb' : b • (v : (Λ → Fin (N + 1)) → ℂ) = Ψ := by
    have h := congrArg ((↑) : ↥(E ⊓ Asub) → (Λ → Fin (N + 1)) → ℂ) hb
    simpa using h
  have ha_ne : a ≠ 0 := by
    intro h0; apply hΦ0_ne; rw [← ha', h0, zero_smul]
  refine ⟨b * a⁻¹, ?_⟩
  rw [← hb', ← ha', smul_smul]
  congr 1
  rw [mul_assoc, inv_mul_cancel₀ ha_ne, mul_one]

/-- **Chain ratio bound at a Marshall sector vector.** For a Marshall ground vector
`w = magSectorEmbedding (marshallSignS A · * v)` (`v > 0`) at sector `M`, a joint
`(Ŝ_tot)²`-eigenvector at `γ` and `Ŝ_tot^{(3)}`-eigenvector at the real weight `m`,
the real Rayleigh quotient of `Ô²` is at least `γ − m²`.  Direct corollary of
`chain_bound_marshall_sector` divided by the positive squared norm. -/
private theorem ratioRe_marshall_ge_chain
    (A : Λ → Bool) {M : ℕ} {v : magConfigS Λ N M → ℝ} (hv_pos : ∀ σ, 0 < v σ)
    [Nonempty (magConfigS Λ N M)] {γ m : ℝ}
    (hcas : (totalSpinSSquared Λ N).mulVec
        (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        ((γ : ℝ) : ℂ) • magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))
    (hweight : (totalSpinSOp3 Λ N).mulVec
        (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) =
        ((m : ℝ) : ℂ) • magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) :
    γ - m ^ 2 ≤
      (star (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ⬝ᵥ
        (staggeredCasimirOpS A N).mulVec
          (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)))).re /
      (star (magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))) ⬝ᵥ
        magSectorEmbedding (fun σ : magConfigS Λ N M =>
          (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ))).re := by
  set w : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS Λ N M =>
      (((marshallSignS A σ.1).re * v σ : ℝ) : ℂ)) with hwdef
  have hw_ne : w ≠ 0 := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hv_pos
  have hpos : (0 : ℂ) < star w ⬝ᵥ w := Matrix.dotProduct_star_self_pos_iff.mpr hw_ne
  have hnrm_pos : 0 < (star w ⬝ᵥ w).re := (Complex.lt_def.mp hpos).1
  have hchain := chain_bound_marshall_sector A hv_pos hcas hweight
  rw [le_div_iff₀ hnrm_pos]
  exact hchain

/-- **Casimir avoids the lowering kernel inside the band (real form).** For a real
weight `x` with `−S < x ≤ S`, the Casimir value `S(S+1)` is never the
lowering-kernel value `x(x−1)`: factoring, `x(x−1) − S(S+1) = (x−S−1)(x+S)`, whose
factors have strict signs `x − S − 1 < 0` and `x + S > 0`. -/
private theorem predictedCasimir_ne_kernel_real
    {S x : ℝ} (hlt : -S < x) (hle : x ≤ S) :
    S * (S + 1) ≠ x * (x - 1) := by
  intro heq
  nlinarith [hlt, hle, heq]

/-- **Marshall sector ratio equals the left-edge hub ratio.** Let `w_L` be the
left-edge hub: a non-zero joint `Ŝ_tot^{(3)}`-eigenvector at the maximal weight
`m_L = S` and `(Ŝ_tot)²`-eigenvector at `γ = S(S+1)`, also a full-Heisenberg
`μ`-eigenvector lying in the centered weight `card·N/2 − L`.  Let `w_M` be a
Marshall ground vector at admissible sector `M = L + k`, a non-zero full
`μ`-eigenvector whose bare sector `μ`-eigenspace is one-dimensional.  If every
intermediate lowering weight `m_L − j` (`j < k`) stays in the open band `(−S, S]`,
then the real Rayleigh ratios of `Ô²` on `w_M` and `w_L` coincide.

The `k`-fold lowering `(Ŝ⁻_tot)^k w_L` is non-zero (Casimir avoids the band kernel),
a full `μ`-eigenvector in sector `M`, hence proportional to `w_M` by `finrank ≤ 1`;
scale-invariance of the ratio plus the SU(2)-ladder ratio invariance close it. -/
private theorem ratioRe_marshall_eq_left_edge
    (A : Λ → Bool) (J : Λ → Λ → ℂ) (L k : ℕ) {μ S γ : ℝ}
    {w_L w_M : (Λ → Fin (N + 1)) → ℂ}
    (hSγ : γ = S * (S + 1))
    (hw_L_ne : w_L ≠ 0)
    (hw_L_mem : w_L ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)))
    (hw_L_weight : (totalSpinSOp3 Λ N).mulVec w_L = (S : ℂ) • w_L)
    (hw_L_cas : (totalSpinSSquared Λ N).mulVec w_L = (γ : ℂ) • w_L)
    (hw_L_eig : (heisenbergHamiltonianS J N).mulVec w_L = (μ : ℂ) • w_L)
    (hw_M_ne : w_M ≠ 0)
    (hw_M_eig : (heisenbergHamiltonianS J N).mulVec w_M = (μ : ℂ) • w_M)
    (hw_M_mem : w_M ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - ((L + k : ℕ) : ℂ)))
    (h_sector_pf : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
      (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N (L + k))) (μ : ℂ)) ≤ 1)
    (hweight_mLre : (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)).re = S)
    (hband : ∀ j : ℕ, j < k → -S < S - (j : ℝ) ∧ S - (j : ℝ) ≤ S) :
    (star w_M ⬝ᵥ ((staggeredCasimirOpS A N).mulVec w_M)).re / (star w_M ⬝ᵥ w_M).re =
      (star w_L ⬝ᵥ ((staggeredCasimirOpS A N).mulVec w_L)).re / (star w_L ⬝ᵥ w_L).re := by
  classical
  set lw : (Λ → Fin (N + 1)) → ℂ := ((totalSpinSOpMinus Λ N) ^ k).mulVec w_L with hlwdef
  -- The hub's centered weight has real part `S`.
  have hw_L_weight' : w_L ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)) := hw_L_mem
  -- Kernel-avoidance: Casimir `γ = S(S+1)` differs from the lowering kernel value.
  have hγ_ne : ∀ j : ℕ, j < k →
      (γ : ℂ) ≠ ((((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)) - (j : ℂ)) *
        (((((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)) - (j : ℂ)) - 1) := by
    intro j hj
    obtain ⟨hlt, hle⟩ := hband j hj
    have hne_real := predictedCasimir_ne_kernel_real (S := S) (x := S - (j : ℝ)) hlt hle
    intro heq
    apply hne_real
    -- Reduce the complex equality to its real part.
    have hxre : ((((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)) - (j : ℂ)) =
        ((S - (j : ℝ) : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.sub_re, hweight_mLre, Complex.natCast_re, Complex.ofReal_re]
      · rw [Complex.sub_im, Complex.natCast_im, sub_zero, Complex.ofReal_im]
        simp [Complex.sub_im, Complex.mul_im]
    rw [hxre] at heq
    rw [hSγ] at heq
    have hceq : ((S * (S + 1) : ℝ) : ℂ) =
        (((S - (j : ℝ)) * ((S - (j : ℝ)) - 1) : ℝ) : ℂ) := by
      push_cast at heq ⊢
      linear_combination heq
    exact_mod_cast hceq
  -- The lowering iterate is non-zero.
  have hlw_ne : lw ≠ 0 := by
    rw [hlwdef]
    exact totalSpinSOpMinus_pow_mulVec_ne_zero_of_casimir_ne_kernel_values
      (V := Λ) (N := N) k hw_L_weight' hw_L_cas hw_L_ne hγ_ne
  -- The lowering iterate is a full Heisenberg `μ`-eigenvector.
  have hlw_eig : (heisenbergHamiltonianS J N).mulVec lw = (μ : ℂ) • lw := by
    rw [hlwdef]
    exact heisenbergHamiltonianS_mulVec_totalSpinSOpMinus_pow_of_eigenvec J N k hw_L_eig
  -- The lowering iterate lives in sector `L + k`.
  have hlw_mem : lw ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - ((L + k : ℕ) : ℂ)) := by
    have hmem := totalSpinSOpMinus_pow_mulVec_mem_magSubspaceS_of_mem
      (V := Λ) (N := N) k hw_L_mem
    have hidx : ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ) - (k : ℂ) =
        ((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - ((L + k : ℕ) : ℂ) := by push_cast; ring
    rw [hidx] at hmem
    rwa [hlwdef]
  -- `w_M` is proportional to `lw` (sector `finrank ≤ 1`).
  obtain ⟨s, hs⟩ := sector_eigenvec_proportional_of_finrank_le_one
    (Λ := Λ) (N := N) J (L + k) (μ : ℂ) hlw_ne hlw_eig hlw_mem hw_M_eig hw_M_mem h_sector_pf
  have hs_ne : s ≠ 0 := by
    intro h0; apply hw_M_ne; rw [hs, h0, zero_smul]
  -- Ratio scale invariance: ratio(w_M) = ratio(lw).
  have hratio1 := ratioRe_eq_of_smul (staggeredCasimirOpS A N) hs_ne hs
  -- SU(2) ladder invariance: ratio(lw) = ratio(w_L).
  have hladder := su2_expectationRatioRe_ladder_iterate_invariant (staggeredCasimirOpS A N)
    (staggeredCasimirOpS_commute_totalSpinSOpPlus A N)
    (staggeredCasimirOpS_commute_totalSpinSOpMinus A N)
    hw_L_weight hw_L_cas k (by rw [← hlwdef]; exact hlw_ne)
  rw [hratio1]
  rw [← hlwdef] at hladder
  exact hladder

set_option maxHeartbeats 1600000 in
-- This per-sector assembly chains the connected Theorem 2.3 data, the strict
-- outside-sector separation, the left-edge ladder hub, and the near-central chain
-- bound; the resulting elaboration exceeds the default heartbeat budget.
/-- **Per-sector ferrimagnetic LRO bound (oriented).** For a connected bipartite
antiferromagnetic coupling `J` (oriented so `|¬A| ≤ |A|`), a global-minimum
Heisenberg `μ`-eigenvector `Φ`, and any magnetization sector `M`, the weight
component `Φ_M := magSectorEmbedding (magSectorRestriction Φ)` satisfies Tasaki's
ferrimagnetic bound `S_tot² ‖Φ_M‖² ≤ ⟨Φ_M, Ô² Φ_M⟩.re`.

Outside the admissible band `Φ_M = 0` (strict outside-sector separation forces it);
inside the band `Φ_M` is proportional to a Marshall ground vector whose ladder ratio
equals that of the near-central admissible sector, where `chain_bound_marshall_sector`
gives `γ − m² ≥ S_tot²`. -/
private theorem staggeredCasimir_weightComponent_bound_oriented
    (A : Λ → Bool) (G : SimpleGraph Λ) (c c_toy : ℝ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hc_strict : ∀ σ, dressedHeisenbergSReMatrix A J N σ σ < c)
    (hc_strict_toy : ∀ σ,
      dressedHeisenbergSReMatrix A (bipartiteCoupling A) N σ σ < c_toy)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {μ : ℝ} {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0)
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ)
    (hΦ_min : ∀ {μ' : ℝ} {Ψ' : (Λ → Fin (N + 1)) → ℂ}, Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' → μ ≤ μ')
    (M : ℕ) :
    tasaki23PredictedTotalSpin (V := Λ) A N ^ 2 *
        (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          magSectorEmbedding (magSectorRestriction (M := M) Φ)).re ≤
      (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
        (staggeredCasimirOpS A N).mulVec
          (magSectorEmbedding (magSectorRestriction (M := M) Φ))).re := by
  classical
  set cA := (Finset.univ.filter (fun x : Λ => A x = true)).card with hcA
  set cB := (Finset.univ.filter (fun x : Λ => (! A x) = true)).card with hcB
  haveI : Nonempty Λ := ⟨(Finset.card_pos.mp hcardA).choose⟩
  set S := tasaki23PredictedTotalSpin (V := Λ) A N with hSdef
  set γ := tasaki23PredictedCasimirValue (V := Λ) A N with hγdef
  set ΦM : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (magSectorRestriction (M := M) Φ) with hΦMdef
  have hSγ : γ = S * (S + 1) := rfl
  have hsB : 0 < ((Finset.univ.filter (fun x : Λ => (! A x) = true)).card : ℝ) * (N : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ (cB : ℝ) := by exact_mod_cast hcardB
    have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    rw [← hcB]; positivity
  have hA_ne : ∃ a, A a = true := by
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcardA
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hB_ne : ∃ b, A b = false := by
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hcardB
    have hbf := (Finset.mem_filter.mp hb).2
    cases hAb : A b with
    | false => exact ⟨b, hAb⟩
    | true => rw [hAb] at hbf; cases hbf
  -- Oriented: `min cA cB = cB`, `max cA cB = cA`.
  have hmin_eq : min cA cB = cB := min_eq_right horient
  have hmax_eq : max cA cB = cA := max_eq_left horient
  have hsum : cA + cB = Fintype.card Λ := tasaki23_card_filter_A_add_card_notA A
  -- The connected per-sector irreducibility witnesses.
  have hIrred : ∀ (M : ℕ) [Nonempty (magConfigS Λ N M)],
      (shiftedDressedSReMatrixOnMagSector A J N c M).IsIrreducible := by
    intro M _
    exact isIrreducible_shiftedDressedSReMatrixOnMagSector_connected
      (N := N) (M := M) A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite hc_strict
  -- The global Theorem 2.3 data: common energy `μd`, per-admissible-sector Marshall
  -- ground vectors with a sector-supported uniqueness clause, and global minimality.
  obtain ⟨μd, hper, hmin⟩ :=
    tasaki_2_5_theorem_2_3_data_of_connected A G N c c_toy horient hsB hGconn hGbip
      hc_strict_toy hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G hc_strict hN hcardA hcardB
  -- Strict outside-sector separation at the (same) common energy `μs`.
  obtain ⟨μs, hcommon_s, hstrict⟩ :=
    tasaki23_strict_hOutside_of_connected A G N c c_toy horient hsB hGconn hGbip
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G hc_strict hc_strict_toy hN hcardA hcardB
  -- Left band edge `L = cB·N` is admissible and nonempty.
  set L := cB * N with hLdef
  have hmax_le_card : max cA cB ≤ Fintype.card Λ := by
    rw [← hsum]; exact max_le (Nat.le_add_right _ _) (Nat.le_add_left _ _)
  have hL_mem : L ∈ tasaki23GroundStateSectors (V := Λ) A N := by
    have := tasaki23GroundStateSectors_left_mem A N
    rw [hmin_eq] at this; rwa [hLdef]
  haveI hLNe : Nonempty (magConfigS Λ N L) :=
    magConfigS_nonempty_of_le_card_mul (by
      rw [hLdef]
      calc cB * N ≤ cA * N := Nat.mul_le_mul_right N horient
        _ ≤ Fintype.card Λ * N := Nat.mul_le_mul_right N (by rw [← hsum]; omega))
  -- The hub Marshall ground vector at the left edge (strict-theorem ReMatrix form, energy `μs`).
  obtain ⟨vL, hvL_pos, hReEig_L⟩ := hcommon_s L hL_mem
  set wL : (Λ → Fin (N + 1)) → ℂ :=
    magSectorEmbedding (fun σ : magConfigS Λ N L => (((marshallSignS A σ.1).re * vL σ : ℝ) : ℂ))
    with hwLdef
  have hwL_ne : wL ≠ 0 := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvL_pos
  obtain ⟨hwL_eig, hwL_cas⟩ :=
    tasaki23_sector_lift_and_casimir_of_irreducible (N := N) (M := L)
      A c c_toy horient hsB hL_mem hJ_real hc_strict_toy hA_ne hB_ne hN
      (hIrred L) hvL_pos hReEig_L
  have hwL_mem : wL ∈
      magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)) := by
    rw [hwLdef]; exact magSectorEmbedding_mem_magSubspaceS _
  -- `μ = μs`: the hub is a nonzero global-minimum-energy eigenvector at `μs`, and `μs = μd`
  -- (the strict common energy equals the data common energy) via the data uniqueness clause.
  obtain ⟨vd, _hμd_lt, hvd_pos, _hHd, huniq_L⟩ := hper L hL_mem
  have hμs_eq_μd : μs = μd := by
    refine (huniq_L hwL_eig ?_ ?_).1
    · intro σ hσ
      exact magSectorEmbedding_apply_of_not_mem _ hσ
    · intro τ
      rw [magSectorEmbedding_apply_subtype
        (fun σ : magConfigS Λ N L => (((marshallSignS A σ.1).re * vL σ : ℝ) : ℂ)) τ,
        Complex.ofReal_re]
      have hsq : (marshallSignS A τ.1).re * (marshallSignS A τ.1).re = 1 :=
        marshallSignS_re_sq A τ.1
      nlinarith [hvL_pos τ, hsq]
  have hμ_le_μs : μ ≤ μs := hΦ_min hwL_ne hwL_eig
  have hμd_le_μ : μd ≤ μ := hmin hΦ_ne hΦ_eig
  have hμ_eq : μ = μs := le_antisymm hμ_le_μs (by rw [hμs_eq_μd]; exact hμd_le_μ)
  -- The hub's centered weight has real part `S` (the left edge is the highest weight).
  have hweight_Lre : (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)).re = S := by
    have hre : (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)).re =
        (Fintype.card Λ : ℝ) * (N : ℝ) / 2 - (L : ℝ) := by
      simp [Complex.sub_re, Complex.mul_re, Complex.natCast_re,
        Complex.natCast_im]
    rw [hre, hSdef, tasaki23PredictedTotalSpin, ← hcA, ← hcB, hLdef]
    have hcardR : (Fintype.card Λ : ℝ) = (cA : ℝ) + (cB : ℝ) := by
      rw [← hsum]; push_cast; ring
    rw [abs_of_nonneg (by
      have : (cB : ℝ) ≤ (cA : ℝ) := by exact_mod_cast horient
      linarith)]
    push_cast [hcardR]
    ring
  -- The centered weight at `L` equals `(S : ℂ)`.
  have hLweight_cast : (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (L : ℂ)) = (S : ℂ) := by
    apply Complex.ext
    · rw [hweight_Lre, Complex.ofReal_re]
    · rw [Complex.ofReal_im]
      simp [Complex.sub_im, Complex.mul_im]
  have hwL_weight : (totalSpinSOp3 Λ N).mulVec wL = (S : ℂ) • wL := by
    have hmem := hwL_mem
    rw [mem_magSubspaceS_iff] at hmem
    rwa [hLweight_cast] at hmem
  -- The hub's energy expressed at `μ`.
  have hwL_eig_μ : (heisenbergHamiltonianS J N).mulVec wL = (μ : ℂ) • wL := by
    rw [hμ_eq]; exact hwL_eig
  -- `S ≥ 0`.
  have hS_nn : 0 ≤ S := by rw [hSdef, tasaki23PredictedTotalSpin]; positivity
  -- A reusable builder: for an admissible sector `M'`, the Marshall ground vector `w_{M'}` has
  -- the same `Ô²` ratio as the hub.  Packaged as the per-sector ratio at `M'`.
  -- We instantiate it both at the near-central `M₀` (to get `ratio ≥ S²`) and at the goal `M`.
  -- First, the near-central sector `M₀`.
  set M0 : ℕ := (cA + cB) * N / 2 with hM0def
  have hcard_mul : (cA + cB) * N = Fintype.card Λ * N := by rw [hsum]
  -- `M₀` lies in `[cB·N, cA·N]`.
  have hM0_lo : cB * N ≤ M0 := by
    rw [hM0def]
    have h2 : 2 * (cB * N) ≤ (cA + cB) * N := by
      have : 2 * cB ≤ cA + cB := by omega
      calc 2 * (cB * N) = (2 * cB) * N := by ring
        _ ≤ (cA + cB) * N := Nat.mul_le_mul_right N this
    omega
  have hM0_hi : M0 ≤ cA * N := by
    rw [hM0def]
    have h2 : (cA + cB) * N ≤ 2 * (cA * N) := by
      have : cA + cB ≤ 2 * cA := by omega
      calc (cA + cB) * N ≤ (2 * cA) * N := Nat.mul_le_mul_right N this
        _ = 2 * (cA * N) := by ring
    omega
  have hM0_mem : M0 ∈ tasaki23GroundStateSectors (V := Λ) A N := by
    rw [tasaki23GroundStateSectors_mem_iff, hmin_eq, hmax_eq]
    exact ⟨hM0_lo, hM0_hi⟩
  haveI hM0Ne : Nonempty (magConfigS Λ N M0) :=
    magConfigS_nonempty_of_le_card_mul (le_trans hM0_hi
      (Nat.mul_le_mul_right N (by rw [← hsum]; omega)))
  -- For any admissible sector `M'` (with `cB·N ≤ M' ≤ cA·N`), the Marshall ground vector
  -- `w_{M'}` has the same `Ô²` Rayleigh ratio as the hub.
  have hwM_ratio : ∀ (M' : ℕ), cB * N ≤ M' → M' ≤ cA * N →
      ∃ (wM' : (Λ → Fin (N + 1)) → ℂ),
        wM' ≠ 0 ∧
        (heisenbergHamiltonianS J N).mulVec wM' = (μ : ℂ) • wM' ∧
        wM' ∈ magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M' : ℂ)) ∧
        finrank ℂ ↥(End.eigenspace (Matrix.toLin'
          (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M')) (μ : ℂ)) ≤ 1 ∧
        (star wM' ⬝ᵥ ((staggeredCasimirOpS A N).mulVec wM')).re / (star wM' ⬝ᵥ wM').re =
          (star wL ⬝ᵥ ((staggeredCasimirOpS A N).mulVec wL)).re / (star wL ⬝ᵥ wL).re := by
    intro M' hlo hhi
    have hM'_mem : M' ∈ tasaki23GroundStateSectors (V := Λ) A N := by
      rw [tasaki23GroundStateSectors_mem_iff, hmin_eq, hmax_eq]; exact ⟨hlo, hhi⟩
    haveI hM'Ne : Nonempty (magConfigS Λ N M') :=
      magConfigS_nonempty_of_le_card_mul (le_trans hhi
        (Nat.mul_le_mul_right N (by rw [← hsum]; omega)))
    obtain ⟨vM', hvM'_pos, hReEig_M'⟩ := hcommon_s M' hM'_mem
    set wM' : (Λ → Fin (N + 1)) → ℂ :=
      magSectorEmbedding
        (fun σ : magConfigS Λ N M' => (((marshallSignS A σ.1).re * vM' σ : ℝ) : ℂ))
      with hwM'def
    have hwM'_ne : wM' ≠ 0 := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvM'_pos
    obtain ⟨hwM'_eig_μs, _hwM'_cas⟩ :=
      tasaki23_sector_lift_and_casimir_of_irreducible (N := N) (M := M')
        A c c_toy horient hsB hM'_mem hJ_real hc_strict_toy hA_ne hB_ne hN
        (hIrred M') hvM'_pos hReEig_M'
    have hwM'_eig : (heisenbergHamiltonianS J N).mulVec wM' = (μ : ℂ) • wM' := by
      rw [hμ_eq]; exact hwM'_eig_μs
    have hwM'_mem : wM' ∈
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M' : ℂ)) := by
      rw [hwM'def]; exact magSectorEmbedding_mem_magSubspaceS _
    have hpf_M' : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N M')) (μ : ℂ)) ≤ 1 := by
      rw [hμ_eq]
      exact heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
        (N := N) (M := M') A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite
        hc_strict hvM'_pos hReEig_M'
    -- `M' = L + k` with `k = M' − L`; band condition on the lowering weights.
    have hk : M' = L + (M' - L) := by rw [hLdef]; omega
    have hwM'_mem' : wM' ∈
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - ((L + (M' - L) : ℕ) : ℂ)) := by
      rw [show (L + (M' - L) : ℕ) = M' by rw [hLdef]; omega]; exact hwM'_mem
    have hpf_M'' : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N (L + (M' - L)))) (μ : ℂ)) ≤ 1 := by
      rw [show (L + (M' - L) : ℕ) = M' by rw [hLdef]; omega]; exact hpf_M'
    have hband : ∀ j : ℕ, j < (M' - L) → -S < S - (j : ℝ) ∧ S - (j : ℝ) ≤ S := by
      intro j hj
      refine ⟨?_, by linarith [Nat.cast_nonneg (α := ℝ) j]⟩
      -- `j < M' − L ≤ cA·N − cB·N = 2S`.
      have hk_le : M' - L ≤ cA * N - cB * N := by rw [hLdef]; omega
      have hcBcA : (cB : ℝ) ≤ (cA : ℝ) := by exact_mod_cast horient
      have hSval : S = ((cA : ℝ) - (cB : ℝ)) * ((N : ℝ) / 2) := by
        rw [hSdef, tasaki23PredictedTotalSpin, ← hcA, ← hcB,
          abs_of_nonneg (by linarith)]
      have hjr : (j : ℝ) < (cA * N - cB * N : ℕ) := by
        have : (j : ℝ) < ((M' - L : ℕ) : ℝ) := by exact_mod_cast hj
        have hle2 : ((M' - L : ℕ) : ℝ) ≤ ((cA * N - cB * N : ℕ) : ℝ) := by exact_mod_cast hk_le
        linarith
      have hcast : ((cA * N - cB * N : ℕ) : ℝ) = (cA : ℝ) * (N : ℝ) - (cB : ℝ) * (N : ℝ) := by
        have hsub : cB * N ≤ cA * N := Nat.mul_le_mul_right N horient
        push_cast [Nat.cast_sub hsub]; ring
      rw [hcast] at hjr
      rw [hSval]; nlinarith [hjr]
    refine ⟨wM', hwM'_ne, hwM'_eig, hwM'_mem, hpf_M', ?_⟩
    exact ratioRe_marshall_eq_left_edge A J L (M' - L) hSγ hwL_ne hwL_mem hwL_weight
      hwL_cas hwL_eig_μ hwM'_ne hwM'_eig hwM'_mem' hpf_M'' hweight_Lre hband
  -- `S² ≤ ratio(wL)` via the near-central sector `M₀`, where the chain bound applies.
  have hratioL_ge : S ^ 2 ≤
      (star wL ⬝ᵥ ((staggeredCasimirOpS A N).mulVec wL)).re / (star wL ⬝ᵥ wL).re := by
    -- Build the near-central Marshall ground vector with full Casimir / weight structure.
    obtain ⟨vM0, hvM0_pos, hReEig_M0⟩ := hcommon_s M0 hM0_mem
    set wM0 : (Λ → Fin (N + 1)) → ℂ :=
      magSectorEmbedding
        (fun σ : magConfigS Λ N M0 => (((marshallSignS A σ.1).re * vM0 σ : ℝ) : ℂ))
      with hwM0def
    obtain ⟨hwM0_eig_μs, hwM0_cas⟩ :=
      tasaki23_sector_lift_and_casimir_of_irreducible (N := N) (M := M0)
        A c c_toy horient hsB hM0_mem hJ_real hc_strict_toy hA_ne hB_ne hN
        (hIrred M0) hvM0_pos hReEig_M0
    have hwM0_ne : wM0 ≠ 0 := tasaki23_marshallPositive_magSectorEmbedding_ne_zero A hvM0_pos
    have hwM0_eig : (heisenbergHamiltonianS J N).mulVec wM0 = (μ : ℂ) • wM0 := by
      rw [hμ_eq]; exact hwM0_eig_μs
    have hwM0_mem : wM0 ∈
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ)) := by
      rw [hwM0def]; exact magSectorEmbedding_mem_magSubspaceS _
    -- The near-central weight `m₀ = card·N/2 − M₀` and its real part.
    set m0 : ℝ := (Fintype.card Λ : ℝ) * (N : ℝ) / 2 - (M0 : ℝ) with hm0def
    have hm0_cast : (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M0 : ℂ)) = ((m0 : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [hm0def, Complex.ofReal_re]
        simp [Complex.sub_re, Complex.mul_re, Complex.natCast_re,
          Complex.natCast_im]
      · rw [Complex.ofReal_im]
        simp [Complex.sub_im, Complex.mul_im]
    have hwM0_weight : (totalSpinSOp3 Λ N).mulVec wM0 = ((m0 : ℝ) : ℂ) • wM0 := by
      have hmem := hwM0_mem
      rw [mem_magSubspaceS_iff] at hmem
      rwa [hm0_cast] at hmem
    -- The chain bound at `M₀`: `γ − m₀² ≤ ratio(wM0)`.
    have hchain := ratioRe_marshall_ge_chain A hvM0_pos (γ := γ) (m := m0) hwM0_cas hwM0_weight
    -- `ratio(wM0) = ratio(wL)` via the ladder hub transfer.
    have hk0 : M0 = L + (M0 - L) := by rw [hLdef]; omega
    have hwM0_mem' : wM0 ∈
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - ((L + (M0 - L) : ℕ) : ℂ)) := by
      rw [show (L + (M0 - L) : ℕ) = M0 by rw [hLdef]; omega]; exact hwM0_mem
    have hpf_M0 : finrank ℂ ↥(End.eigenspace (Matrix.toLin'
        (heisenbergHamiltonianSMatrixOnMagSector (V := Λ) J N (L + (M0 - L)))) (μ : ℂ)) ≤ 1 := by
      rw [show (L + (M0 - L) : ℕ) = M0 by rw [hLdef]; omega, hμ_eq]
      exact heisenbergHamiltonianSMatrixOnMagSector_finrank_le_one_of_marshall_positive_connected
        (N := N) (M := M0) A c hGconn hGbip hJ_real hJ_pos_G hJ_nn hJ_sym hJ_bipartite
        hc_strict hvM0_pos hReEig_M0
    have hcBcA : (cB : ℝ) ≤ (cA : ℝ) := by exact_mod_cast horient
    have hSval : S = ((cA : ℝ) - (cB : ℝ)) * ((N : ℝ) / 2) := by
      rw [hSdef, tasaki23PredictedTotalSpin, ← hcA, ← hcB, abs_of_nonneg (by linarith)]
    have hband0 : ∀ j : ℕ, j < (M0 - L) → -S < S - (j : ℝ) ∧ S - (j : ℝ) ≤ S := by
      intro j hj
      refine ⟨?_, by linarith [Nat.cast_nonneg (α := ℝ) j]⟩
      have hk_le : M0 - L ≤ cA * N - cB * N := by rw [hLdef]; omega
      have hjr : (j : ℝ) < (cA * N - cB * N : ℕ) := by
        have h1 : (j : ℝ) < ((M0 - L : ℕ) : ℝ) := by exact_mod_cast hj
        have h2 : ((M0 - L : ℕ) : ℝ) ≤ ((cA * N - cB * N : ℕ) : ℝ) := by exact_mod_cast hk_le
        linarith
      have hcast : ((cA * N - cB * N : ℕ) : ℝ) = (cA : ℝ) * (N : ℝ) - (cB : ℝ) * (N : ℝ) := by
        have hsub : cB * N ≤ cA * N := Nat.mul_le_mul_right N horient
        push_cast [Nat.cast_sub hsub]; ring
      rw [hcast] at hjr
      rw [hSval]; nlinarith [hjr]
    have hratio_eq := ratioRe_marshall_eq_left_edge A J L (M0 - L) hSγ hwL_ne hwL_mem
      hwL_weight hwL_cas hwL_eig_μ hwM0_ne hwM0_eig hwM0_mem' hpf_M0 hweight_Lre hband0
    -- `γ − m₀² ≥ S²` from `|m₀| ≤ 1/2 ≤ S`.
    have hm0_bound : m0 ^ 2 ≤ S := by
      -- `m₀ = r/2` where `r = (cA+cB)·N % 2 ∈ {0, 1}`.
      obtain ⟨r, hr01, hdivmod⟩ : ∃ r, (r = 0 ∨ r = 1) ∧ (cA + cB) * N = 2 * M0 + r := by
        refine ⟨(cA + cB) * N % 2, by omega, ?_⟩
        have hdm := Nat.div_add_mod ((cA + cB) * N) 2
        rw [hM0def]; omega
      have hcardR : (Fintype.card Λ : ℝ) = (cA : ℝ) + (cB : ℝ) := by
        rw [← hsum]; push_cast; ring
      have hm0_eq : m0 = (r : ℝ) / 2 := by
        rw [hm0def, hcardR]
        have hc : (((cA + cB) * N : ℕ) : ℝ) = ((2 * M0 + r : ℕ) : ℝ) := by exact_mod_cast hdivmod
        push_cast at hc; linarith
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      rcases hr01 with hr | hr
      · rw [hm0_eq, hr]
        norm_num
        exact hS_nn
      · -- `r = 1`: `(cA+cB)·N` odd, so `cA ≠ cB`, hence `cA > cB` and `S ≥ 1/2`.
        have hne : cA ≠ cB := by
          intro heq
          have heven : (cA + cB) * N = 2 * (cB * N) := by rw [heq]; ring
          omega
        have hgt : cB < cA := lt_of_le_of_ne horient (fun h => hne h.symm)
        have hScA : (1 : ℝ) ≤ (cA : ℝ) - (cB : ℝ) := by
          have : (cB : ℝ) + 1 ≤ (cA : ℝ) := by exact_mod_cast hgt
          linarith
        have hS_half : (1 : ℝ) / 2 ≤ S := by rw [hSval]; nlinarith [hScA, hN1]
        rw [hm0_eq, hr]
        norm_num
        nlinarith [hS_half]
    have hge : S ^ 2 ≤ γ - m0 ^ 2 := by
      rw [hSγ]; nlinarith [hm0_bound]
    rw [← hratio_eq]
    linarith [hchain, hge]
  -- The goal at sector `M`.
  by_cases hΦM_zero : ΦM = 0
  · rw [hΦM_zero]
    simp only [Matrix.mulVec_zero, dotProduct_zero, Complex.zero_re, mul_zero, le_refl]
  · -- `ΦM ≠ 0`: it is a nonzero `μ`-eigenvector in the centered sector `card·N/2 − M`.
    have hΦM_eig : (heisenbergHamiltonianS J N).mulVec ΦM = (μ : ℂ) • ΦM := by
      rw [hΦMdef]; exact heisenbergHamiltonianS_magSectorProjection_eigen J M hΦ_eig
    have hΦM_mem : ΦM ∈
        magSubspaceS Λ N (((Fintype.card Λ : ℂ) * (N : ℂ)) / 2 - (M : ℂ)) := by
      rw [hΦMdef]; exact magSectorEmbedding_mem_magSubspaceS _
    -- The sector restriction is nonzero.
    have hWrestr_ne : magSectorRestriction (M := M) Φ ≠ 0 := by
      intro h0
      apply hΦM_zero
      rw [hΦMdef, h0, magSectorEmbedding_zero]
    have hpos : (0 : ℂ) < star ΦM ⬝ᵥ ΦM := Matrix.dotProduct_star_self_pos_iff.mpr hΦM_zero
    have hnrm_pos : 0 < (star ΦM ⬝ᵥ ΦM).re := (Complex.lt_def.mp hpos).1
    by_cases hadm : cB * N ≤ M ∧ M ≤ cA * N
    · -- Admissible: `ΦM` is proportional to the Marshall ground vector `w_M`.
      obtain ⟨wM, hwM_ne, hwM_eig, hwM_mem, hpf_M, hwM_ratioL⟩ :=
        hwM_ratio M hadm.1 hadm.2
      obtain ⟨s, hs⟩ := sector_eigenvec_proportional_of_finrank_le_one
        (Λ := Λ) (N := N) J M (μ : ℂ) hwM_ne hwM_eig hwM_mem hΦM_eig hΦM_mem hpf_M
      have hs_ne : s ≠ 0 := by intro h0; apply hΦM_zero; rw [hs, h0, zero_smul]
      have hΦM_ratio := ratioRe_eq_of_smul (staggeredCasimirOpS A N) hs_ne hs
      -- `ratio(ΦM) = ratio(wM) = ratio(wL) ≥ S²`.
      have hΦM_ge : S ^ 2 ≤
          (star ΦM ⬝ᵥ ((staggeredCasimirOpS A N).mulVec ΦM)).re / (star ΦM ⬝ᵥ ΦM).re := by
        rw [hΦM_ratio, hwM_ratioL]; exact hratioL_ge
      rw [le_div_iff₀ hnrm_pos] at hΦM_ge
      linarith [hΦM_ge]
    · -- Not admissible: `M ∉ tasaki23GroundStateSectors`, so `ΦM = 0`, contradicting `hΦM_zero`.
      exfalso
      have hM_non : M ∉ tasaki23GroundStateSectors (V := Λ) A N := by
        rw [tasaki23GroundStateSectors_mem_iff, hmin_eq, hmax_eq]
        push Not
        intro h1; omega
      haveI hMNe : Nonempty (magConfigS Λ N M) := ⟨(Function.ne_iff.mp hWrestr_ne).choose⟩
      -- The sector restriction is a complex `μ`-eigenvector of the sector matrix.
      have hWcomplex :
          (heisenbergHamiltonianSMatrixOnMagSector J N M).mulVec
            (magSectorRestriction (M := M) Φ) =
            (μ : ℂ) • magSectorRestriction (M := M) Φ :=
        heisenbergHamiltonianSMatrixOnMagSector_mulVec_magSectorRestriction_of_full_eigen_complex
          J hΦ_eig
      -- Its real and imaginary parts are real sector eigenvectors at `μ`.
      have hWre := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_re_of_complex_eigenvec
        (J := J) N hJ_real (W := magSectorRestriction (M := M) Φ) hWcomplex
      have hWim := heisenbergHamiltonianSReMatrixOnMagSector_mulVec_im_of_complex_eigenvec
        (J := J) N hJ_real (W := magSectorRestriction (M := M) Φ) hWcomplex
      -- `W ≠ 0` ⟹ its real or imaginary part is nonzero.
      obtain ⟨τ0, hτ0⟩ := Function.ne_iff.mp hWrestr_ne
      have hμlt : μs < μ := by
        by_cases hre0 : (fun σ => (magSectorRestriction (M := M) Φ σ).re) = 0
        · -- The real part vanishes, so the imaginary part is nonzero.
          have him_ne : (fun σ => (magSectorRestriction (M := M) Φ σ).im) ≠ 0 := by
            intro h0
            apply hτ0
            apply Complex.ext
            · exact congrFun hre0 τ0
            · exact congrFun h0 τ0
          exact hstrict (M := M) hM_non him_ne hWim
        · exact hstrict (M := M) hM_non hre0 hWre
      linarith [hμ_le_μs, hμlt]

/-- **Ferrimagnetic LRO sum assembly (oriented).** Summing the per-sector bound
`staggeredCasimir_weightComponent_bound_oriented` over all magnetization sectors and
collapsing `Σ_M ‖Φ_M‖² = ‖Φ‖² = 1` (`star_dotProduct_self_eq_sum_sector`,
`weightPreserving_expectation_eq_sum_sector`) yields the normalized ferrimagnetic
bound for the oriented case `|¬A| ≤ |A|`. -/
private theorem ferrimagnetic_lro_oriented
    (A : Λ → Bool) (G : SimpleGraph Λ)
    (horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hGconn : G.Connected)
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y)
    {J : Λ → Λ → ℂ}
    (hJ_real : ∀ x y, (J x y).im = 0)
    (hJ_real' : ∀ x y, star (J x y) = J x y)
    (hJ_sym : ∀ x y, J x y = J y x)
    (hJ_nn : ∀ x y, 0 ≤ (J x y).re)
    (hJ_bipartite : ∀ x y, A x = A y → J x y = 0)
    (hJ_pos_G : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hN : 1 ≤ N)
    (hcardA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card)
    {μ : ℝ} {Φ : (Λ → Fin (N + 1)) → ℂ}
    (hΦ_ne : Φ ≠ 0) (hnorm : star Φ ⬝ᵥ Φ = 1)
    (hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ)
    (hΦ_min : ∀ {μ' : ℝ} {Ψ' : (Λ → Fin (N + 1)) → ℂ}, Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' → μ ≤ μ') :
    tasaki23PredictedTotalSpin (V := Λ) A N ^ 2 ≤
      (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re := by
  classical
  haveI : Nonempty Λ := ⟨(Finset.card_pos.mp hcardA).choose⟩
  obtain ⟨c, hc_strict⟩ := exists_strict_diag_bound_dressedHeisenbergSReMatrix A J N
  obtain ⟨c_toy, hc_strict_toy⟩ :=
    exists_strict_diag_bound_dressedHeisenbergSReMatrix A (bipartiteCoupling A) N
  set S := tasaki23PredictedTotalSpin (V := Λ) A N with hSdef
  -- Per-sector bound, summed.
  have hper : ∀ M ∈ Finset.range (Fintype.card Λ * N + 1),
      S ^ 2 * (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          magSectorEmbedding (magSectorRestriction (M := M) Φ)).re ≤
        (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          (staggeredCasimirOpS A N).mulVec
            (magSectorEmbedding (magSectorRestriction (M := M) Φ))).re := by
    intro M _
    exact staggeredCasimir_weightComponent_bound_oriented A G c c_toy horient hGconn hGbip
      hJ_real hJ_real' hJ_sym hJ_nn hJ_bipartite hJ_pos_G hc_strict hc_strict_toy hN hcardA hcardB
      hΦ_ne hΦ_eig (fun {μ'} {Ψ'} => hΦ_min) M
  -- Expectation sum decomposition.
  have hexp := weightPreserving_expectation_eq_sum_sector (staggeredCasimirOpS A N)
    (staggeredCasimirOpS_commute_op3' A N) Φ
  have hexpre : (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re =
      ∑ M ∈ Finset.range (Fintype.card Λ * N + 1),
        (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
          (staggeredCasimirOpS A N).mulVec
            (magSectorEmbedding (magSectorRestriction (M := M) Φ))).re := by
    rw [hexp, Complex.re_sum]
  -- Norm sum decomposition: `Σ_M ‖Φ_M‖² = ‖Φ‖² = 1`.
  have hnormsum := star_dotProduct_self_eq_sum_sector Φ
  have hnorm_one : ∑ M ∈ Finset.range (Fintype.card Λ * N + 1),
      (star (magSectorEmbedding (magSectorRestriction (M := M) Φ)) ⬝ᵥ
        magSectorEmbedding (magSectorRestriction (M := M) Φ)).re = 1 := by
    rw [← hnormsum, hnorm, Complex.one_re]
  -- Sum the per-sector bounds.
  have hsum_le := Finset.sum_le_sum hper
  rw [← Finset.mul_sum, hnorm_one, mul_one] at hsum_le
  rw [hexpre]
  exact hsum_le

-- The `[DecidableRel G.Adj]` instance is part of the discharged axiom's signature but is
-- not used in the statement's type; the scoped linter disable keeps signature parity.
set_option linter.unusedDecidableInType false in
/-- **Tasaki Theorem 4.4 (Shen–Qiu–Tian ferrimagnetic long-range order).**  Discharge
of the documented axiom `shenQiuTian_ferrimagnetic_lro`: for the spin-`S` (`S = N/2`)
antiferromagnetic Heisenberg model on a connected bipartite lattice (modeled by a
connected bipartite graph `G`, real symmetric edge-supported strictly
antiferromagnetic coupling `J`, both sublattices nonempty), *any* normalized ground
state `Φ` obeys the ferrimagnetic bound (4.1.13)
`(N/2)² (|A| − |B|)² ≤ ⟨Φ, (Ô_Λ)² Φ⟩.re`.

The proof reduces (via the global sublattice-flip invariance `staggeredCasimirOpS_compl`
and coefficient symmetry) to the oriented assembly `ferrimagnetic_lro_oriented`, after
extracting the real ground energy `μ = E₀.re` (Hermitian eigenvalue) and handling the
trivial-spin case `N = 0`.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*,
Springer 2020, §4.1 Theorem 4.4, eqs. (4.1.12)–(4.1.16), pp. 77–78. -/
theorem shenQiuTian_ferrimagnetic_lro (A : Λ → Bool) (J : Λ → Λ → ℂ) (N : ℕ)
    (G : SimpleGraph Λ) [DecidableRel G.Adj]
    (hGbip : ∀ x y, G.Adj x y → A x ≠ A y) (hGconn : G.Connected)
    (hreal : ∀ x y, (J x y).im = 0) (hsym : ∀ x y, J x y = J y x)
    (hJoff : ∀ x y, ¬ G.Adj x y → J x y = 0)
    (hJon : ∀ x y, G.Adj x y → 0 < (J x y).re)
    (hA : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = true)).card)
    (hB : 1 ≤ (Finset.univ.filter (fun x : Λ => A x = false)).card)
    (Φ : (Λ → Fin (N + 1)) → ℂ) (hnorm : star Φ ⬝ᵥ Φ = 1)
    (hgs : ∃ E₀ : ℂ, (heisenbergHamiltonianS J N).mulVec Φ = E₀ • Φ ∧
      (∀ E : ℂ, ∀ Ψ : (Λ → Fin (N + 1)) → ℂ, Ψ ≠ 0 →
        (heisenbergHamiltonianS J N).mulVec Ψ = E • Ψ → E₀.re ≤ E.re) ∧ Φ ≠ 0) :
    ((N : ℝ) / 2) ^ 2 *
        (((Finset.univ.filter (fun x : Λ => A x = true)).card : ℤ) -
          ((Finset.univ.filter (fun x : Λ => A x = false)).card : ℤ) : ℝ) ^ 2 ≤
      (star Φ ⬝ᵥ (staggeredCasimirOpS A N).mulVec Φ).re := by
  classical
  -- `N = 0`: both sides vanish.
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [staggeredCasimirOpS_N_zero A, Matrix.zero_mulVec, dotProduct_zero, Complex.zero_re]
    norm_num
  -- Real ground energy.
  obtain ⟨E₀, hE_eig, hE_min, hΦ_ne⟩ := hgs
  have hreal' : ∀ x y, star (J x y) = J x y := by
    intro x y; rw [Complex.star_def, Complex.conj_eq_iff_im]; exact hreal x y
  have hE_im : E₀.im = 0 := by
    have hstar := isHermitian_eigenvalue_star_eq
      (heisenbergHamiltonianS_isHermitian_of_real hreal' N) hE_eig hΦ_ne
    rw [Complex.star_def, Complex.conj_eq_iff_im] at hstar; exact hstar
  set μ : ℝ := E₀.re with hμdef
  have hE_cast : E₀ = (μ : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]
    · rw [Complex.ofReal_im, hE_im]
  have hΦ_eig : (heisenbergHamiltonianS J N).mulVec Φ = (μ : ℂ) • Φ := by
    rw [← hE_cast]; exact hE_eig
  have hΦ_min : ∀ {μ' : ℝ} {Ψ' : (Λ → Fin (N + 1)) → ℂ}, Ψ' ≠ 0 →
      (heisenbergHamiltonianS J N).mulVec Ψ' = (μ' : ℂ) • Ψ' → μ ≤ μ' := by
    intro μ' Ψ' hΨ'_ne hΨ'
    have := hE_min (μ' : ℂ) Ψ' hΨ'_ne hΨ'
    rwa [Complex.ofReal_re] at this
  -- `J` is non-negative on the reals and vanishes within a sublattice.
  have hJ_nn : ∀ x y, 0 ≤ (J x y).re := by
    intro x y
    by_cases h : G.Adj x y
    · exact le_of_lt (hJon x y h)
    · rw [hJoff x y h, Complex.zero_re]
  have hJ_bipartite : ∀ x y, A x = A y → J x y = 0 := by
    intro x y hAxy
    apply hJoff
    intro hadj
    exact hGbip x y hadj hAxy
  -- `B`-cardinality in the `(! A x) = true` fiber form used by the oriented assembly.
  have hcardB : 1 ≤ (Finset.univ.filter (fun x : Λ => (! A x) = true)).card := by
    rw [← card_filter_A_false_eq_card_filter_notA]; exact hB
  -- Orientation split.
  by_cases horient : (Finset.univ.filter (fun x : Λ => (! A x) = true)).card ≤
      (Finset.univ.filter (fun x : Λ => A x = true)).card
  · -- Oriented `|¬A| ≤ |A|`: apply the oriented assembly directly.
    have hbound := ferrimagnetic_lro_oriented A G horient hGconn hGbip hreal hreal' hsym
      hJ_nn hJ_bipartite hJon hN hA hcardB hΦ_ne hnorm hΦ_eig (fun {μ'} {Ψ'} => hΦ_min)
    rw [tasaki23PredictedTotalSpin_sq_eq A N] at hbound
    exact hbound
  · -- Reversed `|A| < |¬A|`: apply the oriented assembly to `A' := ¬A`.
    push Not at horient
    -- Cardinalities under the flip `A' = ¬A`.
    have hflip_notA : (Finset.univ.filter (fun x : Λ => (! (fun x => ! A x) x) = true)).card =
        (Finset.univ.filter (fun x : Λ => A x = true)).card := by
      congr 1
      apply Finset.filter_congr
      intro x _
      simp only [Bool.not_not]
    -- The flipped bipartite / cardinality hypotheses.
    have hGbip' : ∀ x y, G.Adj x y → (fun x => ! A x) x ≠ (fun x => ! A x) y := by
      intro x y hadj h
      simp only [Bool.not_inj_iff] at h
      exact hGbip x y hadj h
    have horient' :
        (Finset.univ.filter (fun x : Λ => (! (fun x => ! A x) x) = true)).card ≤
          (Finset.univ.filter (fun x : Λ => (fun x => ! A x) x = true)).card := by
      rw [hflip_notA]
      change (Finset.univ.filter (fun x : Λ => A x = true)).card ≤
        (Finset.univ.filter (fun x : Λ => (! A x) = true)).card
      omega
    have hcardA' : 1 ≤ (Finset.univ.filter (fun x : Λ => (fun x => ! A x) x = true)).card :=
      hcardB
    have hcardB' : 1 ≤
        (Finset.univ.filter (fun x : Λ => (! (fun x => ! A x) x) = true)).card := by
      rw [hflip_notA]; exact hA
    have hJ_bipartite' : ∀ x y, (fun x => ! A x) x = (fun x => ! A x) y → J x y = 0 := by
      intro x y h
      apply hJ_bipartite
      simp only [Bool.not_inj_iff] at h
      exact h
    have hbound := ferrimagnetic_lro_oriented (fun x => ! A x) G horient' hGconn hGbip'
      hreal hreal' hsym hJ_nn hJ_bipartite' hJon hN hcardA' hcardB' hΦ_ne hnorm hΦ_eig
      (fun {μ'} {Ψ'} => hΦ_min)
    -- Transfer to `A`: `Ô²(¬A) = Ô²(A)` and the predicted spin is flip-symmetric.
    rw [staggeredCasimirOpS_compl A N] at hbound
    have hspin_eq : tasaki23PredictedTotalSpin (V := Λ) (fun x => ! A x) N =
        tasaki23PredictedTotalSpin (V := Λ) A N := by
      rw [tasaki23PredictedTotalSpin, tasaki23PredictedTotalSpin, hflip_notA]
      rw [mul_eq_mul_right_iff]
      left
      rw [abs_sub_comm]
    rw [hspin_eq, tasaki23PredictedTotalSpin_sq_eq A N] at hbound
    exact hbound

end LatticeSystem.Quantum
