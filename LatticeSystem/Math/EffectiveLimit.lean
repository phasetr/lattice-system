import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Algebra.Order.Field
import LatticeSystem.Math.PosSemidef.Kernel

/-!
# Tasaki Appendix A.2.3: the strong-coupling effective Hamiltonian (Theorem A.12)

Tasaki's Theorem A.12, "widely used in the physics literature" (and used in §5.1 and §11.2,
and the basis of the §11.5 metallic-ferromagnetism limit): for a Hamiltonian
`Ĥ_v = Ĥ₀ + v V̂` with `Ĥ₀` self-adjoint, `V̂ ≥ 0`, and a parameter `v ≥ 0`, the eigenstates
whose energy stays finite as `v ↑ ∞` are governed by the *effective Schrödinger equation*
`P̂₀ Ĥ₀ |Φ⟩ = E |Φ⟩` on the subspace `H₀ = { Φ : V̂ Φ = 0 }` (`P̂₀` the orthogonal projection
onto `H₀`).

We state it for finite complex matrices without an explicit projection matrix, in the
non-vacuous "finite-energy ⇒ effective" direction: if a family `Φ_v` of `Ĥ_v`-eigenstates
converges as `v ↑ ∞` to a nonzero `Φ` with energy converging to a finite `E`, then `Φ ∈ H₀`
(`V̂ Φ = 0`) and `Φ` solves the effective equation `P̂₀ Ĥ₀ Φ = E Φ`, rendered by its weak
(variational) form `⟨ψ | Ĥ₀ | Φ⟩ = E ⟨ψ | Φ⟩` for every `ψ ∈ H₀` (equivalently
`P̂₀(Ĥ₀ Φ − E Φ) = 0`).  This rests on a continuity/limit argument (Theorem A.12's proof) and
was initially recorded as a documented axiom and is **now proved (axiom-free)**: the weak
equation follows by transposing `V̂` onto `ψ ∈ ker V̂` (Hermitian) and passing the eigenvalue
relation to the limit; the kernel condition follows because the eigenvalue relation forces
`⟨Φ_v|V̂|Φ_v⟩ = (E_v − ⟨Φ_v|Ĥ₀|Φ_v⟩)·v⁻¹·‖Φ_v‖²`-style decay, so the limiting quadratic form
vanishes and Lemma A.11 (`posSemidef_mulVec_eq_zero_of_inner_zero`) kills `V̂ Φ`.  It underlies
the §11.5 effective-theory constructions (`ttDKernel` / `ttEffectiveHamiltonian`).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*
(1st ed.), Appendix A.2.3, Theorem A.12, p. 470.
-/

namespace LatticeSystem.Math

open Matrix Filter Topology
open scoped ComplexOrder

section EffectiveLimit

variable {n : Type*} [Fintype n]

/-- Convergence of states gives convergence of the sesquilinear pairings
`⟨f v | A | g v⟩ → ⟨F | A | G⟩` (coordinatewise products of finitely many converging
coordinates). -/
private theorem tendsto_star_dot_mulVec (A : Matrix n n ℂ) {f g : ℝ → (n → ℂ)} {F G : n → ℂ}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G)) :
    Tendsto (fun v => star (f v) ⬝ᵥ A.mulVec (g v)) atTop (𝓝 (star F ⬝ᵥ A.mulVec G)) := by
  have hgA : ∀ i, Tendsto (fun v => A.mulVec (g v) i) atTop (𝓝 (A.mulVec G i)) := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    exact tendsto_finset_sum _ fun j _ =>
      tendsto_const_nhds.mul (tendsto_pi_nhds.mp hg j)
  simp only [dotProduct, Pi.star_apply]
  exact tendsto_finset_sum _ fun i _ =>
    ((tendsto_pi_nhds.mp hf i).star).mul (hgA i)

/-- Convergence of states gives convergence of the plain pairings `⟨f v | g v⟩ → ⟨F | G⟩`. -/
private theorem tendsto_star_dot {f g : ℝ → (n → ℂ)} {F G : n → ℂ}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G)) :
    Tendsto (fun v => star (f v) ⬝ᵥ g v) atTop (𝓝 (star F ⬝ᵥ G)) := by
  simp only [dotProduct, Pi.star_apply]
  exact tendsto_finset_sum _ fun i _ =>
    ((tendsto_pi_nhds.mp hf i).star).mul (tendsto_pi_nhds.mp hg i)

/-- Hermitian matrices transpose across the pairing: `⟨ψ|A|χ⟩ = ⟨Aψ|χ⟩`. -/
private theorem star_dot_mulVec_of_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (ψ χ : n → ℂ) : star ψ ⬝ᵥ A.mulVec χ = star (A.mulVec ψ) ⬝ᵥ χ := by
  rw [dotProduct_mulVec, Matrix.star_mulVec, hA.eq]

/-- **Tasaki Theorem A.12 (strong-coupling effective Hamiltonian), PROVED.**  For
`Ĥ_v = Ĥ₀ + v V̂` with `Ĥ₀` Hermitian and `V̂` positive-semidefinite, the eigenstates whose
energy stays finite as `v ↑ ∞` are governed by the effective Schrödinger equation
`P̂₀ Ĥ₀ |Φ⟩ = E |Φ⟩` on `H₀ = ker V̂`.  Concretely (the "finite-energy ⇒ effective" direction,
which is non-vacuous): if `Φ_v` is a family of `Ĥ_v`-eigenstates with eigenvalue `E_v`, and as
`v ↑ ∞` the states converge to a nonzero `Φ` and the energies to a finite `E`, then the limit
state lies in `H₀` (`V̂ Φ = 0`) and solves the effective equation in weak form,
`⟨ψ|Ĥ₀|Φ⟩ = E ⟨ψ|Φ⟩` for every `ψ ∈ H₀` (i.e. `P̂₀ Ĥ₀ Φ = E Φ`).

*Proof.*  Pairing the eigenvalue relation with `Φ_v` gives
`v·⟨Φ_v|V̂|Φ_v⟩ = E_v⟨Φ_v|Φ_v⟩ − ⟨Φ_v|Ĥ₀|Φ_v⟩`; the right side converges, so multiplying by
`v⁻¹ → 0` shows `⟨Φ_v|V̂|Φ_v⟩ → 0`, while continuity gives `⟨Φ_v|V̂|Φ_v⟩ → ⟨Φ|V̂|Φ⟩`; hence
`⟨Φ|V̂|Φ⟩ = 0` and Lemma A.11 yields `V̂ Φ = 0`.  Pairing instead with a fixed `ψ ∈ ker V̂`
kills the `v V̂` term outright (`V̂` Hermitian), so `⟨ψ|Ĥ₀|Φ_v⟩ = E_v⟨ψ|Φ_v⟩` for all `v ≥ 0`,
and the limit is the weak effective equation. -/
theorem effectiveHamiltonian_strongCoupling_limit {n : Type*} [Fintype n]
    (H0 V : Matrix n n ℂ) (_hH0 : H0.IsHermitian) (hV : V.PosSemidef)
    (Φv : ℝ → (n → ℂ)) (Ev : ℝ → ℝ) (Φ : n → ℂ) (E : ℝ)
    (heig : ∀ v : ℝ, 0 ≤ v → (H0 + (v : ℂ) • V).mulVec (Φv v) = (Ev v : ℂ) • (Φv v))
    (hΦlim : Tendsto Φv atTop (𝓝 Φ)) (hElim : Tendsto Ev atTop (𝓝 E)) (_hΦ : Φ ≠ 0) :
    V.mulVec Φ = 0 ∧
      ∀ ψ : n → ℂ, V.mulVec ψ = 0 → star ψ ⬝ᵥ H0.mulVec Φ = (E : ℂ) * (star ψ ⬝ᵥ Φ) := by
  -- the complexified energies converge
  have hElimC : Tendsto (fun v => ((Ev v : ℝ) : ℂ)) atTop (𝓝 (E : ℂ)) :=
    (Complex.continuous_ofReal.tendsto E).comp hElim
  constructor
  · -- kernel condition: the limiting quadratic form vanishes
    -- the eigenvalue relation paired with `Φ_v` itself
    have hpair : ∀ v : ℝ, 0 ≤ v →
        (v : ℂ) * (star (Φv v) ⬝ᵥ V.mulVec (Φv v))
          = (Ev v : ℂ) * (star (Φv v) ⬝ᵥ Φv v) - star (Φv v) ⬝ᵥ H0.mulVec (Φv v) := by
      intro v hv
      have h := congrArg (fun w => star (Φv v) ⬝ᵥ w) (heig v hv)
      simp only [Matrix.add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
        smul_eq_mul] at h
      linear_combination h
    -- the right side converges, so `⟨Φ_v|V̂|Φ_v⟩ = (RHS)·v⁻¹ → 0`
    have hQlim0 : Tendsto (fun v => star (Φv v) ⬝ᵥ V.mulVec (Φv v)) atTop (𝓝 0) := by
      have hR : Tendsto
          (fun v => (Ev v : ℂ) * (star (Φv v) ⬝ᵥ Φv v) - star (Φv v) ⬝ᵥ H0.mulVec (Φv v))
          atTop (𝓝 ((E : ℂ) * (star Φ ⬝ᵥ Φ) - star Φ ⬝ᵥ H0.mulVec Φ)) :=
        (hElimC.mul (tendsto_star_dot hΦlim hΦlim)).sub
          (tendsto_star_dot_mulVec H0 hΦlim hΦlim)
      have hinv : Tendsto (fun v : ℝ => ((v : ℂ))⁻¹) atTop (𝓝 0) := by
        have h1 : Tendsto (fun v : ℝ => v⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
        simp only [Complex.ofReal_zero] at h2
        exact h2.congr fun v => by rw [Function.comp_apply, Complex.ofReal_inv]
      have hmul : Tendsto
          (fun v : ℝ => ((v : ℂ))⁻¹
            * ((Ev v : ℂ) * (star (Φv v) ⬝ᵥ Φv v) - star (Φv v) ⬝ᵥ H0.mulVec (Φv v)))
          atTop (𝓝 0) := by
        simpa using hinv.mul hR
      refine hmul.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with v hv
      have hv0 : (v : ℂ) ≠ 0 := by
        simpa using ne_of_gt hv
      rw [← hpair v hv.le]
      field_simp
    -- continuity identifies the limit with the quadratic form at `Φ`
    have hQlim : Tendsto (fun v => star (Φv v) ⬝ᵥ V.mulVec (Φv v)) atTop
        (𝓝 (star Φ ⬝ᵥ V.mulVec Φ)) := tendsto_star_dot_mulVec V hΦlim hΦlim
    have hzero : star Φ ⬝ᵥ V.mulVec Φ = 0 := tendsto_nhds_unique hQlim hQlim0
    exact posSemidef_mulVec_eq_zero_of_inner_zero hV hzero
  · -- weak effective equation: pair with a fixed `ψ ∈ ker V̂`
    intro ψ hψ
    -- for every `v ≥ 0` the pairing kills the `v V̂` term
    have hpair : ∀ v : ℝ, 0 ≤ v →
        star ψ ⬝ᵥ H0.mulVec (Φv v) = (Ev v : ℂ) * (star ψ ⬝ᵥ Φv v) := by
      intro v hv
      have h := congrArg (fun w => star ψ ⬝ᵥ w) (heig v hv)
      simp only [Matrix.add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
        smul_eq_mul] at h
      rwa [star_dot_mulVec_of_isHermitian hV.isHermitian ψ (Φv v), hψ, star_zero,
        zero_dotProduct, mul_zero, add_zero] at h
    -- pass to the limit on both sides
    have hL : Tendsto (fun v => star ψ ⬝ᵥ H0.mulVec (Φv v)) atTop
        (𝓝 (star ψ ⬝ᵥ H0.mulVec Φ)) := tendsto_star_dot_mulVec H0 tendsto_const_nhds hΦlim
    have hRt : Tendsto (fun v => (Ev v : ℂ) * (star ψ ⬝ᵥ Φv v)) atTop
        (𝓝 ((E : ℂ) * (star ψ ⬝ᵥ Φ))) :=
      hElimC.mul (tendsto_star_dot tendsto_const_nhds hΦlim)
    refine tendsto_nhds_unique (hL.congr' ?_) hRt
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with v hv
    exact hpair v hv

end EffectiveLimit

end LatticeSystem.Math
