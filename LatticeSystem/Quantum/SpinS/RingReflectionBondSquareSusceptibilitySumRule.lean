/-
Susceptibility sum rule on the even ring (Tasaki §4.1 Theorem 4.2, eq. (4.1.41), book p. 84,
issue #4777, PR-χ2b).

The ground-state energy uniform-field bound `E_GS(λh) ≥ E_GS(0)` (χ1,
`ringBondSquareFieldHamiltonian_hermitianMinEigenvalue_ge_field_zero`), expanded to second order in
the field strength `λ`, yields Tasaki's susceptibility sum rule.  Writing the bond-square field
Hamiltonian at the scaled field `λh` as the proved operator identity
`Ĥ_λ = H₀ + λ·V + (λ²·C(h))·1` (`ringBondSquareFieldHamiltonian_smulField_eq`), with
`H₀ = ringFieldHamiltonian n N 0` the field-free ring Heisenberg Hamiltonian, `V = Σ_z (kOf h)_z·
Ŝ³_z` the Zeeman perturbation (Tasaki's `−Ô_b`, (4.1.38)), and `C(h) = ½Σ(f_x+f_{x+1})²` the scalar
constant, the trial state `ψ_λ = Φ − λ·y` (`y` the pseudoinverse potential `(H₀−E₀)y = VΦ`,
`y ⊥ Φ`) makes the variational lower bound `E_GS(λh)·⟨ψ_λ|ψ_λ⟩ ≤ ⟨ψ_λ|Ĥ_λ|ψ_λ⟩` into a
`λ`-polynomial whose `λ²`-coefficient, after the `λ → 0⁺` limit, gives the susceptibility
`χ_b = Re⟨y, VΦ⟩ ≤ C(h)`.  The first-order term drops because `⟨Φ|V|Φ⟩ = 0`
(`ringBondSquareLinFieldOp_groundState_expectation_zero`, χ2a).

The capstone `ringBondSquareField_susceptibility_sum_rule` is phrased in the `hsusc` shape of
`no_long_range_order_1d_of_susceptibility` (`(Ĥ−E₀)y = VΦ ∧ Re⟨y, VΦ⟩ ≤ RHS`), for a general field
`h` with `RHS = C(h)`.  The staggered specialisation and the Green-function `≤ C·L` bound are the
next stage (χ3); this file stops at the general-field sum rule.

Reference: H. Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Springer 2020, §4.1,
eqs. (4.1.38)–(4.1.41), book p. 84.  See
`.self-local/docs/math-tasaki-4-1-41-susceptibility-sum-rule.md`.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareSusceptibility
import LatticeSystem.Quantum.SpinS.RingReflectionBondSquareGroundEnergy
import LatticeSystem.Quantum.SpinS.HermitianSubMinPosSemidef
import LatticeSystem.Quantum.SpinS.HermitianMinSimilarInvariance
import LatticeSystem.Math.MatrixAnalysis.HermitianPseudoinverse
import Mathlib.Topology.Order.DenselyOrdered

namespace LatticeSystem.Quantum

open Matrix Module
open scoped ComplexOrder

variable {n N : ℕ}

/-- **A quadratic real polynomial nonnegative on `(0, ∞)` has a nonnegative constant term.**  If
`a + λb + λ²c ≥ 0` for every `λ > 0`, then `0 ≤ a`: the polynomial is continuous, so its value at
the boundary point `0` (which is `a`) is a limit of nonnegative values along `𝓝[>] 0`.  This is the
`λ → 0⁺` step of Tasaki's susceptibility sum rule. -/
private lemma le_of_forall_pos_poly (a b c : ℝ)
    (H : ∀ lam : ℝ, 0 < lam → 0 ≤ a + lam * b + lam ^ 2 * c) : 0 ≤ a := by
  have hcont : Continuous (fun lam : ℝ => a + lam * b + lam ^ 2 * c) := by fun_prop
  have htend : Filter.Tendsto (fun lam : ℝ => a + lam * b + lam ^ 2 * c)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds a) := by
    have h := hcont.tendsto 0
    rw [show a + (0 : ℝ) * b + (0 : ℝ) ^ 2 * c = a by ring] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  exact H lam hlam

/-- **Real-part symmetry of a Hermitian quadratic cross form**: `Re⟨a, M b⟩ = Re⟨b, M a⟩` for
Hermitian `M`.  Since `M` is self-adjoint, `⟨a, M b⟩ = conj⟨b, M a⟩`, so the real parts agree.
Used to identify the cross term `Re⟨Φ, V y⟩` with the susceptibility `Re⟨y, V Φ⟩`. -/
private theorem isHermitian_dotProduct_mulVec_re_comm {m : Type*} [Fintype m]
    {M : Matrix m m ℂ} (hM : M.IsHermitian) (a b : m → ℂ) :
    (star a ⬝ᵥ M.mulVec b).re = (star b ⬝ᵥ M.mulVec a).re := by
  have hconj : star (star a ⬝ᵥ M.mulVec b) = star b ⬝ᵥ M.mulVec a := by
    rw [← Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hM.eq]
  calc (star a ⬝ᵥ M.mulVec b).re
      = ((starRingEnd ℂ) (star a ⬝ᵥ M.mulVec b)).re := (Complex.conj_re _).symm
    _ = (star b ⬝ᵥ M.mulVec a).re := by rw [starRingEnd_apply, hconj]

/-- **Scaling of the staggered field**: `f_x(λh) = λ·f_x(h)`, since `f_x = (−1)ˣ h_x` is field
linear. -/
theorem ringBondSquareStagField_smul (lam : ℝ) (h : Fin (2 * n) → ℝ) (x : Fin (2 * n)) :
    ringBondSquareStagField (fun y => lam * h y) x = lam * ringBondSquareStagField h x := by
  simp only [ringBondSquareStagField]; ring

/-- **Scaling of the per-site linear field**: `kOf(λh) = λ·kOf(h)`.  Each of the four staggered
slots of `kOf` scales by `λ` (`ringBondSquareStagField_smul`), so the whole real linear combination
does. -/
theorem ringBondSquareLinField_smul (n : ℕ) [NeZero n] (lam : ℝ) (h : Fin (2 * n) → ℝ) :
    ringBondSquareLinField n (fun y => lam * h y)
      = fun z => lam * ringBondSquareLinField n h z := by
  funext z
  simp only [ringBondSquareLinField, ringBondSquareStagField_smul]
  ring

/-- **Quadratic scaling of the scalar constant**: `C(λh) = λ²·C(h)`.  `C(h) = ½Σ(f_x+f_{x+1})²` is a
sum of squared bond sums, each of which scales by `λ²` under the linear field scaling
(`ringBondSquareStagField_smul`). -/
theorem ringBondSquareConst_smul (n : ℕ) [NeZero n] (lam : ℝ) (h : Fin (2 * n) → ℝ) :
    ringBondSquareConst n (fun y => lam * h y) = lam ^ 2 * ringBondSquareConst n h := by
  simp only [ringBondSquareConst, ringBondSquareStagField_smul]
  have hterm : ∀ x : Fin (2 * n),
      (lam * ringBondSquareStagField h x
          + lam * ringBondSquareStagField h (ringBondSucc n x)) ^ 2
        = lam ^ 2 * (ringBondSquareStagField h x
          + ringBondSquareStagField h (ringBondSucc n x)) ^ 2 := fun x => by ring
  rw [Finset.sum_congr rfl (fun x _ => hterm x), ← Finset.mul_sum]
  ring

/-- **Scaling of the linear-core field Hamiltonian in the field**: `Ĥ_field(λk) = H₀ + λ·(Σ_z k_z·
Ŝ³_z)`.  The Zeeman sum is linear in the field `k`, and the field-free part is `H₀ =
ringFieldHamiltonian n N 0` (`ringFieldHamiltonian_zero`). -/
theorem ringFieldHamiltonian_smul_field (n N : ℕ) (lam : ℝ) (k : Fin (2 * n) → ℝ) :
    ringFieldHamiltonian n N (fun z => lam * k z)
      = ringFieldHamiltonian n N 0
        + (lam : ℂ) • ∑ z, (k z : ℂ) • onSiteS z (spinSOp3 N) := by
  rw [ringFieldHamiltonian, ringFieldHamiltonian_zero, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [smul_smul, ← Complex.ofReal_mul]

/-- **`λ`-parametrised operator identity** (Tasaki §4.1 (4.1.37)/(4.1.38), book p. 84): the
bond-square field Hamiltonian at the scaled field `λh` is `Ĥ_λ = H₀ + λ·V + (λ²·C(h))·1`, with
`H₀ = ringFieldHamiltonian n N 0` the field-free ring Heisenberg Hamiltonian, `V = Σ_z (kOf h)_z·
Ŝ³_z` the Zeeman perturbation and `C(h) = ringBondSquareConst n h` the scalar constant.  Combines
the reduction `(★)` (`ringBondSquareFieldHamiltonian_eq`) with the three scaling lemmas. -/
theorem ringBondSquareFieldHamiltonian_smulField_eq (n N : ℕ) [NeZero n] (lam : ℝ)
    (h : Fin (2 * n) → ℝ) :
    ringBondSquareFieldHamiltonian n N (fun x => lam * h x)
      = ringFieldHamiltonian n N 0
        + (lam : ℂ) • (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N))
        + ((lam ^ 2 * ringBondSquareConst n h : ℝ) : ℂ) • 1 := by
  rw [ringBondSquareFieldHamiltonian_eq, ringBondSquareLinField_smul,
    ringFieldHamiltonian_smul_field n N lam (ringBondSquareLinField n h), ringBondSquareConst_smul]

/-- **Susceptibility sum rule** (Tasaki §4.1 Theorem 4.2, eq. (4.1.41), book p. 84): for a unique
ground state `Φ` of the field-free ring Heisenberg Hamiltonian `H₀ = ringFieldHamiltonian n N 0`
(eigenvalue `E₀ = hermitianMinEigenvalue`, `finrank ≤ 1` eigenspace), there is a pseudoinverse
potential `y` with `(H₀ − E₀)y = VΦ` for the Zeeman perturbation `V = Σ_z (kOf h)_z·Ŝ³_z` whose
susceptibility is bounded by the scalar constant, `Re⟨y, VΦ⟩ ≤ C(h) = ½Σ(f_x+f_{x+1})²`.  Proved by
expanding χ1's ground-energy bound `E_GS(λh) ≥ E_GS(0)` to second order at the trial state
`ψ_λ = Φ − λ·y`: the variational lower bound and the operator identity
`ringBondSquareFieldHamiltonian_smulField_eq` make `E_GS(λh) ≤ ⟨ψ_λ|Ĥ_λ|ψ_λ⟩/⟨ψ_λ|ψ_λ⟩` a
`λ`-polynomial with vanishing first order (`⟨Φ|V|Φ⟩ = 0`, χ2a), whose `λ → 0⁺` limit is the sum
rule.  This is the `hsusc` shape of `no_long_range_order_1d_of_susceptibility` for a general
field. -/
theorem ringBondSquareField_susceptibility_sum_rule
    (G : AxisTwoPiRotS N) (n : ℕ) [NeZero n] (hn : 1 ≤ n) (h : Fin (2 * n) → ℝ)
    {Φ : (Fin (2 * n) → Fin (N + 1)) → ℂ} (hΦnorm : star Φ ⬝ᵥ Φ = 1)
    (huniq : finrank ℂ
        ↥(End.eigenspace (Matrix.toLin' (ringFieldHamiltonian n N 0))
          (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ)) ≤ 1)
    (hgs : (ringFieldHamiltonian n N 0).mulVec Φ
        = (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) • Φ) :
    ∃ y, (ringFieldHamiltonian n N 0
            - (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) • 1).mulVec y
          = (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ
        ∧ (star y ⬝ᵥ
            (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ).re
            ≤ ringBondSquareConst n h := by
  classical
  have hΦne : Φ ≠ 0 := by
    intro h0; rw [h0] at hΦnorm; simp at hΦnorm
  -- first-order vanishing `⟨Φ|V|Φ⟩ = 0` (χ2a)
  have hvanish : star Φ ⬝ᵥ
      (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ = 0 :=
    ringBondSquareLinFieldOp_groundState_expectation_zero n N h hΦne huniq hgs
  -- `A Φ = 0` for `A = H₀ − E₀·1`
  have hAΦ : (ringFieldHamiltonian n N 0
        - (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) • 1).mulVec Φ
      = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hgs, sub_self]
  -- `VΦ ⊥ ker A`: a kernel vector is `∝ Φ` (unique ground state) and `⟨Φ|VΦ⟩ = 0`
  have hker : ∀ u, (ringFieldHamiltonian n N 0
        - (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) • 1).mulVec u = 0 →
      star u ⬝ᵥ
        (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ = 0 := by
    intro u hu
    have hHu : (ringFieldHamiltonian n N 0).mulVec u
        = (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) • u := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hu
      exact sub_eq_zero.mp hu
    have hΦmem : Φ ∈ End.eigenspace (Matrix.toLin' (ringFieldHamiltonian n N 0))
        (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) := by
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hgs
    have hu_mem : u ∈ End.eigenspace (Matrix.toLin' (ringFieldHamiltonian n N 0))
        (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) := by
      rw [End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact hHu
    obtain ⟨c, hc⟩ :=
      LatticeSystem.Math.exists_smul_of_mem_finrank_le_one huniq hΦmem hΦne hu_mem
    rw [hc, star_smul, smul_dotProduct, smul_eq_mul, hvanish, mul_zero]
  -- pseudoinverse potential `y`
  obtain ⟨y, hAy, hyperp⟩ :=
    LatticeSystem.Math.hermitian_posSemidef_exists_orthogonal_potential
      (hermitianSubMin_posSemidef (ringFieldHamiltonian_isHermitian n N 0))
      ((∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ) hker
  have hstarΦy : star Φ ⬝ᵥ y = 0 := hyperp Φ hAΦ
  have hstaryΦ : star y ⬝ᵥ Φ = 0 := by
    rw [Matrix.star_dotProduct, hstarΦy, star_zero]
  -- `H₀ y = VΦ + E₀ y`
  have hH0y : (ringFieldHamiltonian n N 0).mulVec y
      = (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ
        + (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℂ) • y := by
    have hy := hAy
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_iff_eq_add] at hy
    exact hy
  -- Hermiticity of `V`
  have hVherm :
      (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).IsHermitian := by
    refine Matrix.isHermitian_sum _ (fun z _ => ?_)
    refine (onSiteS_isHermitian z (spinSOp3_isHermitian N)).smul ?_
    rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]
  have hd : 0 ≤ (star y ⬝ᵥ y).re := (Complex.le_def.mp (dotProduct_star_self_nonneg y)).1
  -- cross-term identity `Re⟨Φ, V y⟩ = Re⟨y, V Φ⟩`
  have hpχ : (star Φ ⬝ᵥ
        (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re
      = (star y ⬝ᵥ
        (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ).re :=
    isHermitian_dotProduct_mulVec_re_comm hVherm Φ y
  -- `E₀` is the ground energy of the bond-square Hamiltonian at zero field
  have hE0 : hermitianMinEigenvalue
        (ringBondSquareFieldHamiltonian_isHermitian n N (0 : Fin (2 * n) → ℝ))
      = hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) := by
    refine hermitianMinEigenvalue_eq_of_spectrum_eq
      (ringBondSquareFieldHamiltonian_isHermitian n N (0 : Fin (2 * n) → ℝ))
      (ringFieldHamiltonian_isHermitian n N 0) ?_
    have hbs0 : ringBondSquareFieldHamiltonian n N (0 : Fin (2 * n) → ℝ)
        = ringFieldHamiltonian n N 0 := ringBondSquareFieldHamiltonian_const n N 0
    rw [hbs0]
  refine ⟨y, hAy, ?_⟩
  -- per-`λ` inequality `0 ≤ (C − χ) + λ·q + λ²·(C·d)` from the variational squeeze
  have hforall : ∀ lam : ℝ, 0 < lam →
      0 ≤ (ringBondSquareConst n h - (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ).re)
          + lam * (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re
          + lam ^ 2 * (ringBondSquareConst n h * (star y ⬝ᵥ y).re) := by
    intro lam hlam
    set ψ : (Fin (2 * n) → Fin (N + 1)) → ℂ := Φ - (lam : ℂ) • y with hψ
    have hslam : star (lam : ℂ) = (lam : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    -- `Ĥ_λ ψ = E'·ψ − λ²·(V y)` with `E' = E₀ + λ²·C`
    have hHmul : (ringBondSquareFieldHamiltonian n N (fun x => lam * h x)).mulVec ψ
        = (((hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0))
              + lam ^ 2 * ringBondSquareConst n h : ℝ) : ℂ) • ψ
          - ((lam ^ 2 : ℝ) : ℂ)
              • (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y := by
      rw [ringBondSquareFieldHamiltonian_smulField_eq, hψ]
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_smul, hgs, hH0y]
      push_cast
      module
    -- numerator as a complex bilinear expression
    have hNumc : star ψ ⬝ᵥ ((ringBondSquareFieldHamiltonian n N (fun x => lam * h x)).mulVec ψ)
        = (((hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0))
              + lam ^ 2 * ringBondSquareConst n h : ℝ) : ℂ) * (star ψ ⬝ᵥ ψ)
          - ((lam ^ 2 : ℝ) : ℂ) * (star ψ ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y) := by
      rw [hHmul, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hNumre :
        (star ψ ⬝ᵥ ((ringBondSquareFieldHamiltonian n N (fun x => lam * h x)).mulVec ψ)).re
        = ((hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0))
              + lam ^ 2 * ringBondSquareConst n h) * (star ψ ⬝ᵥ ψ).re
          - lam ^ 2 * (star ψ ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re := by
      rw [hNumc, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    -- the `⟨ψ, V y⟩` cross factor
    have hcross : star ψ ⬝ᵥ
          (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y
        = (star Φ ⬝ᵥ (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y)
          - (lam : ℂ) * (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y) := by
      rw [hψ, star_sub, star_smul, hslam, sub_dotProduct, smul_dotProduct, smul_eq_mul]
    have hcrossre : (star ψ ⬝ᵥ
          (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re
        = (star Φ ⬝ᵥ (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re
          - lam * (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re := by
      rw [hcross, Complex.sub_re, Complex.re_ofReal_mul]
    -- denominator `⟨ψ, ψ⟩`
    have hDenc : star ψ ⬝ᵥ ψ = 1 + ((lam ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ y) := by
      rw [hψ]
      simp only [star_sub, star_smul, hslam, sub_dotProduct, dotProduct_sub, smul_dotProduct,
        dotProduct_smul, smul_eq_mul, hΦnorm, hstarΦy, hstaryΦ]
      push_cast; ring
    have hDenre : (star ψ ⬝ᵥ ψ).re = 1 + lam ^ 2 * (star y ⬝ᵥ y).re := by
      rw [hDenc, Complex.add_re, Complex.one_re, Complex.re_ofReal_mul]
    -- variational lower bound at `ψ`
    have hvar := hermitianMinEigenvalue_mul_dotProduct_re_le_rayleighOnVec
      (ringBondSquareFieldHamiltonian_isHermitian n N (fun x => lam * h x)) ψ
    rw [rayleighOnVec, hNumre, hcrossre, hDenre, hpχ] at hvar
    -- χ1: `E₀ ≤ E_GS(λh)`
    have hχ1 : (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℝ)
        ≤ hermitianMinEigenvalue
            (ringBondSquareFieldHamiltonian_isHermitian n N (fun x => lam * h x)) := by
      rw [← hE0]
      exact ringBondSquareFieldHamiltonian_hermitianMinEigenvalue_ge_field_zero G n hn
        (fun x => lam * h x)
    have hDenpos : 0 < 1 + lam ^ 2 * (star y ⬝ᵥ y).re := by
      have := mul_nonneg (sq_nonneg lam) hd; linarith
    have step1 : (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℝ)
          * (1 + lam ^ 2 * (star y ⬝ᵥ y).re)
        ≤ hermitianMinEigenvalue
            (ringBondSquareFieldHamiltonian_isHermitian n N (fun x => lam * h x))
          * (1 + lam ^ 2 * (star y ⬝ᵥ y).re) :=
      mul_le_mul_of_nonneg_right hχ1 hDenpos.le
    have hid : lam ^ 2 * ((ringBondSquareConst n h - (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ).re)
          + lam * (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re
          + lam ^ 2 * (ringBondSquareConst n h * (star y ⬝ᵥ y).re))
        = (((hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0))
              + lam ^ 2 * ringBondSquareConst n h) * (1 + lam ^ 2 * (star y ⬝ᵥ y).re)
            - lam ^ 2 * ((star y ⬝ᵥ
                (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ).re
              - lam * (star y ⬝ᵥ
                (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re))
          - (hermitianMinEigenvalue (ringFieldHamiltonian_isHermitian n N 0) : ℝ)
              * (1 + lam ^ 2 * (star y ⬝ᵥ y).re) := by ring
    have step3 : 0 ≤ lam ^ 2 * ((ringBondSquareConst n h - (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ).re)
          + lam * (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re
          + lam ^ 2 * (ringBondSquareConst n h * (star y ⬝ᵥ y).re)) := by
      rw [hid]; linarith [le_trans step1 hvar]
    have hlam2 : (0 : ℝ) < lam ^ 2 := pow_pos hlam 2
    have hmul0 : lam ^ 2 * 0 ≤ lam ^ 2 * ((ringBondSquareConst n h - (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec Φ).re)
          + lam * (star y ⬝ᵥ
              (∑ z, (ringBondSquareLinField n h z : ℂ) • onSiteS z (spinSOp3 N)).mulVec y).re
          + lam ^ 2 * (ringBondSquareConst n h * (star y ⬝ᵥ y).re)) := by
      rw [mul_zero]; exact step3
    exact le_of_mul_le_mul_left hmul0 hlam2
  have h0 := le_of_forall_pos_poly _ _ _ hforall
  linarith

end LatticeSystem.Quantum
