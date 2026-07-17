import LatticeSystem.Quantum.SpinS.LiebSchultzMattisGeneral
import LatticeSystem.Quantum.SpinS.LiebSchultzMattisProof
import LatticeSystem.Quantum.SpinS.LagrangeFormula
import LatticeSystem.Quantum.SpinS.Problem25cZAxisRotationCommutation

/-!
# Tasaki §6.2 Lemma 6.4 (CRUX A): the global→local twist reduction (eq. (6.2.27))

The generalized Lieb–Schultz–Mattis variational bound (Lemma 6.4) reduces the conjugation of each
local term `ĥ_x` by the *global* twist `Û_LSM = exp(−i Σ_y θ_y Ŝ_y^{(3)})` (`θ_y = 2π(y+1)/L`) to a
conjugation by the *centered local* twist generated only on the range-`r` window `W_x` of `x`:

`Û_LSM† ĥ_x Û_LSM = exp(+i M̂_x) ĥ_x exp(−i M̂_x)`  (★),
where `M̂_x = Σ_{y∈W_x} (2π/L) δ(x,y) Ŝ_y^{(3)}`

(the `Û ↔ Û†` mirror is the companion identity), with `δ(x,y)` the ring-distance-centered signed
displacement (`signedRingDisp`).  This is Tasaki eq. (6.2.27), p. 164.

**Proof (diagonal / matrix-entry form).**  Both the global generator `Σ_y θ_y Ŝ_y^{(3)}` and the
local generator `M̂_x` are diagonal in the computational basis, so `Û_LSM`, `Û_LSM†`,
`exp(±i M̂_x)` are all diagonal; conjugation acts on the `(σ',σ)` entry of `ĥ_x` by the scalar
`exp(±i (φ_σ' − φ_σ))`.  Whenever the entry `ĥ_x[σ',σ] ≠ 0` two facts hold:

* **Locality** (`IsLocalRangeR`, PR-1 commutant form): `ĥ_x` commutes with every far single-site
  `Ŝ_y^{(3)}`, so its off-diagonal entries preserve every far occupation: `σ'_y = σ_y` for
  `y ∉ W_x`.
* **`U(1)`-invariance** (`u1_comm`): `ĥ_x` commutes with `Ŝ_tot^{(3)}`, so entries preserve total
  magnetization, `Σ_y (σ_y − σ'_y) = 0`.

The global and local phase differences then agree **modulo `2π`**: their gap is
`θ_x · Σ_{y∈W_x}(σ_y − σ'_y) + 2π · (integer) = 2π · (integer)` — the mean-angle term vanishes by
`U(1)`-invariance, and the residual is an integer multiple of `2π` coming from the periodic-seam
winding of the linear angle `θ_y` relative to the ring-centered `δ(x,y)` (the spinor two-valued
`exp(±i 2π Ŝ^{(3)}) = ±1` global scalar of the book, here an exact `exp(2πi·m) = 1`).  Hence the two
conjugation phases coincide, giving (★).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §6.2, Lemma 6.4, eqs. (6.2.26)–(6.2.27), pp. 163–164.
-/

namespace LatticeSystem.Quantum

open Matrix

/-! ## Diagonal form of a single-site `Ŝ^{(3)}` and the two commutant support facts -/

/-- The single-site operator `Ŝ_y^{(3)}` is diagonal with entry `spinSOp3Eigen N (σ y) = N/2 − σ_y`
at the configuration `σ` (its site-`y` occupation). -/
theorem spinSSiteOp3_eq_diagonal {L : ℕ} (y : Fin L) (N : ℕ) :
    (spinSSiteOp3 y N : ManyBodyOpS (Fin L) N)
      = Matrix.diagonal (fun σ => spinSOp3Eigen N (σ y)) := by
  rw [spinSSiteOp3_def, spinSOp3_eq_diagonal_eigen, onSiteS_diagonal]

/-- **Far single-site commutation** extracted from the locality predicate (`IsLocalRangeR`,
commutant form): a range-`r`-local operator at `x` commutes with `Ŝ_y^{(3)}` for every site `y`
strictly farther than `r` from `x`.  Special case `A = Ŝ^{(3)}` of the predicate. -/
theorem isLocalRangeR_commute_spinSSiteOp3 {L N r : ℕ} {x : Fin L}
    {op : ManyBodyOpS (Fin L) N} (hloc : IsLocalRangeR L N r x op)
    {y : Fin L} (hy : r < ringDist L x y) :
    Commute op (spinSSiteOp3 y N) := by
  rw [spinSSiteOp3_def]
  exact hloc y hy (spinSOp3 N)

/-- **Locality kills far off-diagonal entries.**  If `op` is range-`r`-local at `x` and its
`(σ',σ)` matrix element is nonzero-compatible, then for every far site `y` (`ringDist > r`) the two
configurations must agree at `y`; contrapositively, disagreement at a far site forces the entry to
vanish.  This is the matrix-entry form of the commutant locality, using that `Ŝ^{(3)}` has distinct
eigenvalues. -/
theorem isLocalRangeR_apply_eq_zero_of_far {L N r : ℕ} {x : Fin L}
    {op : ManyBodyOpS (Fin L) N} (hloc : IsLocalRangeR L N r x op)
    {y : Fin L} (hy : r < ringDist L x y) {σ' σ : Fin L → Fin (N + 1)}
    (hne : σ' y ≠ σ y) : op σ' σ = 0 := by
  have hcomm := isLocalRangeR_commute_spinSSiteOp3 hloc hy
  have hentry := congrFun (congrFun hcomm σ') σ
  rw [spinSSiteOp3_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have hne' : spinSOp3Eigen N (σ y) ≠ spinSOp3Eigen N (σ' y) := fun heq =>
    hne (spinSOp3Eigen_injOn N (Finset.mem_univ _) (Finset.mem_univ _) heq).symm
  have h0 : op σ' σ * (spinSOp3Eigen N (σ y) - spinSOp3Eigen N (σ' y)) = 0 := by
    rw [mul_sub, hentry]; ring
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h) hne'

/-- **`U(1)`-invariance kills magnetization-changing entries.**  If `op` commutes with the total
`Ŝ_tot^{(3)}` then its `(σ',σ)` entry vanishes whenever the two configurations have different total
magnetization eigenvalues. -/
theorem commute_totalSpinSOp3_apply_eq_zero_of_mag_ne {L N : ℕ}
    {op : ManyBodyOpS (Fin L) N} (hu1 : Commute op (totalSpinSOp3 (Fin L) N))
    {σ' σ : Fin L → Fin (N + 1)} (hmag : magEigenvalueS σ' ≠ magEigenvalueS σ) :
    op σ' σ = 0 := by
  have hentry := congrFun (congrFun hu1 σ') σ
  rw [totalSpinSOp3_eq_diagonal_magEigenvalueS, Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
  have h0 : op σ' σ * (magEigenvalueS σ - magEigenvalueS σ') = 0 := by
    rw [mul_sub, hentry]; ring
  rcases mul_eq_zero.mp h0 with h | h
  · exact h
  · exact absurd (sub_eq_zero.mp h).symm hmag

/-! ## The centered local twist phase and its diagonal exponential -/

/-- The **centered local twist phase** `φ_x(σ) := Σ_{y∈W_x} (2π/L) δ(x,y) · (N/2 − σ_y)`: the
diagonal entry of the centered local twist generator `M̂_x = localTwistGen L N r x` at the
configuration `σ` (Tasaki eq. (6.2.27)).  Here `W_x = window L r x` and
`δ(x,y) = signedRingDisp`. -/
noncomputable def localTwistPhase (L N r : ℕ) (x : Fin L) (σ : Fin L → Fin (N + 1)) : ℂ :=
  ∑ y ∈ window L r x,
    (((2 * Real.pi * (signedRingDisp L x y : ℝ)) / (L : ℝ) : ℝ) : ℂ) * spinSOp3Eigen N (σ y)

/-- The centered local twist generator `M̂_x` is diagonal with entry `localTwistPhase`. -/
theorem localTwistGen_eq_diagonal (L N r : ℕ) (x : Fin L) :
    localTwistGen L N r x = Matrix.diagonal (localTwistPhase L N r x) := by
  rw [localTwistGen]
  ext σ' σ
  rw [Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases h : σ' = σ
  · subst h
    rw [if_pos rfl, localTwistPhase]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Matrix.smul_apply, spinSSiteOp3_eq_diagonal, Matrix.diagonal_apply_eq, smul_eq_mul]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [Matrix.smul_apply, spinSSiteOp3_eq_diagonal, Matrix.diagonal_apply_ne _ h, smul_zero]

/-- The `c`-scaled exponential of the centered local twist generator is diagonal:
`exp(c • M̂_x) = diag(σ ↦ exp(c • φ_x(σ)))`.  Instantiated at `c = ±i` it gives the local twist
operator `Û_x` and its adjoint. -/
theorem exp_smul_localTwistGen_eq_diagonal (L N r : ℕ) (x : Fin L) (c : ℂ) :
    NormedSpace.exp (c • localTwistGen L N r x)
      = Matrix.diagonal (fun σ => NormedSpace.exp (c • localTwistPhase L N r x σ)) := by
  rw [localTwistGen_eq_diagonal, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  ext σ' σ
  by_cases h : σ' = σ
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Pi.coe_exp, Pi.smul_apply]
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h]

/-! ## The ring-winding correction (spinor two-valued `2π` scalar as an integer) -/

/-- The signed ring displacement `δ(x,y)` is congruent to the raw index gap `y − x` modulo `L`:
their difference is divisible by `L`.  This captures the periodic-seam winding by which the linear
LSM angle `θ_y = 2π(y+1)/L` differs from the ring-centered angle `(2π/L) δ(x,y)`. -/
theorem dvd_sub_signedRingDisp (L : ℕ) (x y : Fin L) :
    (L : ℤ) ∣ ((y.val : ℤ) - (x.val : ℤ) - signedRingDisp L x y) := by
  have hx := x.isLt
  have hy := y.isLt
  have key : (signedRingDisp L x y : ℤ) ≡ (y.val : ℤ) - (x.val : ℤ) [ZMOD (L : ℤ)] := by
    have hxL : x.val ≤ y.val + L := by omega
    have hyL : y.val ≤ x.val + L := by omega
    unfold signedRingDisp
    split_ifs with h
    · calc (((y.val + L - x.val) % L : ℕ) : ℤ)
          = ((y.val + L - x.val : ℕ) : ℤ) % (L : ℤ) := by rw [Int.natCast_mod]
        _ ≡ ((y.val + L - x.val : ℕ) : ℤ) [ZMOD (L : ℤ)] := Int.mod_modEq _ _
        _ = (y.val : ℤ) + (L : ℤ) - (x.val : ℤ) := by rw [Nat.cast_sub hxL]; push_cast; ring
        _ ≡ (y.val : ℤ) - (x.val : ℤ) [ZMOD (L : ℤ)] := Int.modEq_iff_dvd.mpr ⟨-1, by ring⟩
    · calc (-(((x.val + L - y.val) % L : ℕ) : ℤ))
          = -(((x.val + L - y.val : ℕ) : ℤ) % (L : ℤ)) := by rw [Int.natCast_mod]
        _ ≡ -(((x.val + L - y.val : ℕ) : ℤ)) [ZMOD (L : ℤ)] := (Int.mod_modEq _ _).neg
        _ = -((x.val : ℤ) + (L : ℤ) - (y.val : ℤ)) := by rw [Nat.cast_sub hyL]; push_cast; ring
        _ ≡ (y.val : ℤ) - (x.val : ℤ) [ZMOD (L : ℤ)] := Int.modEq_iff_dvd.mpr ⟨1, by ring⟩
  exact Int.modEq_iff_dvd.mp key

/-- The **ring-winding count** `k(x,y) := (y − x − δ(x,y)) / L ∈ ℤ`: the integer number of full `2π`
turns separating the linear LSM angle from the ring-centered angle at site `y`. -/
def ringWrap (L : ℕ) (x y : Fin L) : ℤ :=
  ((y.val : ℤ) - (x.val : ℤ) - signedRingDisp L x y) / (L : ℤ)

/-- The exact decomposition `y − x = δ(x,y) + L · k(x,y)` of the raw index gap into its
ring-centered part and an integer number of `L`-periods. -/
theorem signedRingDisp_add_ringWrap (L : ℕ) (x y : Fin L) :
    (y.val : ℤ) - (x.val : ℤ) = signedRingDisp L x y + (L : ℤ) * ringWrap L x y := by
  rw [ringWrap, Int.mul_ediv_cancel' (dvd_sub_signedRingDisp L x y)]
  ring

/-! ## The phase gap: global and local phases agree modulo `2π` -/

/-- **The global→local phase gap (eq. (6.2.27) core).**  For a short-ranged `U(1)`-invariant chain,
whenever the local term `ĥ_x` has a nonzero `(σ',σ)` entry, the difference of global LSM phases and
difference of centered local phases coincide up to an integer multiple of `2π`:
`lsmPhase σ' − lsmPhase σ = (φ_x σ' − φ_x σ) + 2π m`, `m ∈ ℤ`.  The mean-angle term drops by
`U(1)`-invariance and the residual `2π m` is the periodic-seam winding (`ringWrap`). -/
theorem twistPhase_gap {L N r : ℕ} {h₀ : ℝ} {h : Fin L → ManyBodyOpS (Fin L) N}
    (chain : IsShortRangeU1Chain L N r h₀ h) (x : Fin L)
    {σ' σ : Fin L → Fin (N + 1)} (hne : (h x) σ' σ ≠ 0) :
    ∃ m : ℤ, lsmPhase L N σ' - lsmPhase L N σ
      = (localTwistPhase L N r x σ' - localTwistPhase L N r x σ)
        + 2 * (Real.pi : ℂ) * (m : ℂ) := by
  classical
  set E : Fin L → ℤ := fun y => ((σ y).val : ℤ) - ((σ' y).val : ℤ) with hE
  -- Far sites: locality forces the occupations to agree, so `E` vanishes off the window.
  have hfar : ∀ y ∈ (Finset.univ : Finset (Fin L)), y ∉ window L r x → E y = 0 := by
    intro y _ hyw
    have hy : r < ringDist L x y := by
      rw [window, Finset.mem_filter] at hyw
      exact not_le.mp (fun hle => hyw ⟨Finset.mem_univ y, hle⟩)
    have hσ : σ' y = σ y := by
      by_contra hc
      exact hne (isLocalRangeR_apply_eq_zero_of_far (chain.range x) hy hc)
    simp [hE, hσ]
  -- Total magnetization: `U(1)`-invariance forces `Σ E = 0`.
  have hmageq : magEigenvalueS σ' = magEigenvalueS σ := by
    by_contra hc
    exact hne (commute_totalSpinSOp3_apply_eq_zero_of_mag_ne (chain.u1_comm x) hc)
  have hmsN : magSumS σ' = magSumS σ := by
    have hc : (magSumS σ' : ℂ) = (magSumS σ : ℂ) := by
      have hh := hmageq
      rw [magEigenvalueS_def, magEigenvalueS_def] at hh
      linear_combination -hh
    exact_mod_cast hc
  have hsum0 : ∑ y : Fin L, E y = 0 := by
    simp only [hE, Finset.sum_sub_distrib]
    have heq : (∑ y : Fin L, ((σ y).val : ℤ)) = (∑ y : Fin L, ((σ' y).val : ℤ)) := by
      have hh := hmsN
      unfold magSumS at hh
      exact_mod_cast hh.symm
    rw [heq]; ring
  -- Window sum of `E` is zero (far terms vanish).
  have hwinE : ∑ y ∈ window L r x, (E y : ℂ) = 0 := by
    have hz : ∑ y ∈ window L r x, E y = 0 := by
      rw [Finset.sum_subset (Finset.subset_univ _)
        (fun y hyu hyw => hfar y hyu hyw)]
      exact hsum0
    rw [← Int.cast_sum, hz, Int.cast_zero]
  -- The two phase differences as window sums of `E`.
  set aCoe : Fin L → ℂ := fun y =>
    (((2 * Real.pi * ((y.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) with haCoe
  set bCoe : Fin L → ℂ := fun y =>
    (((2 * Real.pi * (signedRingDisp L x y : ℝ)) / (L : ℝ) : ℝ) : ℂ) with hbCoe
  set cCoe : ℂ := (((2 * Real.pi * ((x.val : ℝ) + 1)) / (L : ℝ) : ℝ) : ℂ) with hcCoe
  have hlsm_diff : lsmPhase L N σ' - lsmPhase L N σ = ∑ y : Fin L, aCoe y * (E y : ℂ) := by
    rw [lsmPhase, lsmPhase, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [haCoe, hE]; push_cast; ring
  have hlsm_win : lsmPhase L N σ' - lsmPhase L N σ
      = ∑ y ∈ window L r x, aCoe y * (E y : ℂ) := by
    rw [hlsm_diff]
    refine (Finset.sum_subset (Finset.subset_univ (window L r x)) ?_).symm
    intro y hyu hyw
    rw [hfar y hyu hyw, Int.cast_zero, mul_zero]
  have hlt_diff : localTwistPhase L N r x σ' - localTwistPhase L N r x σ
      = ∑ y ∈ window L r x, bCoe y * (E y : ℂ) := by
    rw [localTwistPhase, localTwistPhase, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    simp only [hbCoe, hE, spinSOp3Eigen]; push_cast; ring
  -- Per-site angle relation: `θ_y − (2π/L)δ = θ_x + 2π k(x,y)`.
  have hL : (L : ℝ) ≠ 0 := by
    have : 0 < L := x.pos
    positivity
  have hangle : ∀ y : Fin L,
      aCoe y - bCoe y = cCoe + 2 * (Real.pi : ℂ) * (ringWrap L x y : ℂ) := by
    intro y
    have hid : (y.val : ℝ) - (x.val : ℝ) - (signedRingDisp L x y : ℝ)
        = (L : ℝ) * (ringWrap L x y : ℝ) := by
      have hz := signedRingDisp_add_ringWrap L x y
      have : ((y.val : ℤ) - (x.val : ℤ) - signedRingDisp L x y : ℤ)
          = (L : ℤ) * ringWrap L x y := by rw [hz]; ring
      exact_mod_cast this
    simp only [haCoe, hbCoe, hcCoe]
    rw [← Complex.ofReal_sub,
      show (2 : ℂ) * (Real.pi : ℂ) * (ringWrap L x y : ℂ)
        = (((2 * Real.pi * (ringWrap L x y : ℝ)) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_add, Complex.ofReal_inj]
    have hstep : ((y.val : ℝ) + 1) - (signedRingDisp L x y : ℝ)
        = ((x.val : ℝ) + 1) + (L : ℝ) * (ringWrap L x y : ℝ) := by linear_combination hid
    rw [div_sub_div_same, div_add' _ _ _ hL]
    congr 1
    linear_combination (2 * Real.pi) * hstep
  -- Assemble the gap.
  refine ⟨∑ y ∈ window L r x, ringWrap L x y * E y, ?_⟩
  have hD : (lsmPhase L N σ' - lsmPhase L N σ)
      - (localTwistPhase L N r x σ' - localTwistPhase L N r x σ)
      = 2 * (Real.pi : ℂ) * ((∑ y ∈ window L r x, ringWrap L x y * E y : ℤ) : ℂ) := by
    rw [hlsm_win, hlt_diff, ← Finset.sum_sub_distrib]
    have hterm : ∀ y ∈ window L r x, aCoe y * (E y : ℂ) - bCoe y * (E y : ℂ)
        = cCoe * (E y : ℂ)
          + 2 * (Real.pi : ℂ) * ((ringWrap L x y : ℂ) * (E y : ℂ)) := by
      intro y _
      rw [← sub_mul, hangle]; ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hwinE, mul_zero, zero_add]
    push_cast
    ring
  linear_combination hD

/-! ## The `2π`-integer phase collapse of the conjugation exponentials -/

/-- **Positive-`i` exponential collapse.**  When the phase difference `p' − p` exceeds `q' − q` by
an integer multiple of `2π`, the products of `+i/−i` conjugation exponentials coincide
(`exp(2πi m) = 1`).  This is the `Û_LSM† · Û_LSM` direction of (★). -/
theorem normedExp_prod_gap {p p' q q' : ℂ} (m : ℤ)
    (hg : p' - p = (q' - q) + 2 * (Real.pi : ℂ) * (m : ℂ)) :
    NormedSpace.exp (Complex.I • p') * NormedSpace.exp (-Complex.I • p)
      = NormedSpace.exp (Complex.I • q') * NormedSpace.exp (-Complex.I • q) := by
  simp only [← Complex.exp_eq_exp_ℂ, smul_eq_mul, neg_mul, ← Complex.exp_add]
  have hpq : Complex.I * p' + -(Complex.I * p)
      = (Complex.I * q' + -(Complex.I * q))
        + (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    linear_combination Complex.I * hg
  rw [hpq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Negative-`i` exponential collapse.**  The `−i/+i` mirror of `normedExp_prod_gap`, using
`exp(2πi (−m)) = 1`.  This is the `Û_LSM · Û_LSM†` direction of (★). -/
theorem normedExp_prod_gap' {p p' q q' : ℂ} (m : ℤ)
    (hg : p' - p = (q' - q) + 2 * (Real.pi : ℂ) * (m : ℂ)) :
    NormedSpace.exp (-Complex.I • p') * NormedSpace.exp (Complex.I • p)
      = NormedSpace.exp (-Complex.I • q') * NormedSpace.exp (Complex.I • q) := by
  simp only [← Complex.exp_eq_exp_ℂ, smul_eq_mul, neg_mul, ← Complex.exp_add]
  have hpq : -(Complex.I * p') + Complex.I * p
      = (-(Complex.I * q') + Complex.I * q)
        + ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; linear_combination -Complex.I * hg
  rw [hpq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## The global→local twist reduction (Tasaki eq. (6.2.27)) -/

/-- **Global→local twist reduction (★), the `Û_LSM† · Û_LSM` direction (Tasaki eq. (6.2.27)).**  For
a short-ranged `U(1)`-invariant chain the global LSM twist conjugation of a local term equals its
conjugation by the centered local twist generator `M̂_x = localTwistGen L N r x`:
`Û_LSM† ĥ_x Û_LSM = exp(+i M̂_x) ĥ_x exp(−i M̂_x)`. -/
theorem twistConj_eq_localGen {L N r : ℕ} {h₀ : ℝ} {h : Fin L → ManyBodyOpS (Fin L) N}
    (chain : IsShortRangeU1Chain L N r h₀ h) (x : Fin L) :
    (lsmTwistOperator L N).conjTranspose * h x * lsmTwistOperator L N
      = NormedSpace.exp (Complex.I • localTwistGen L N r x) * h x
          * NormedSpace.exp (-Complex.I • localTwistGen L N r x) := by
  rw [lsmTwistOperator_conjTranspose_eq_diagonal, lsmTwistOperator_eq_diagonal,
    exp_smul_localTwistGen_eq_diagonal, exp_smul_localTwistGen_eq_diagonal]
  ext σ' σ
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : (h x) σ' σ = 0
  · rw [hz]; ring
  · obtain ⟨m, hm⟩ := twistPhase_gap chain x hz
    have hprod := normedExp_prod_gap m hm
    linear_combination (h x) σ' σ * hprod

/-- **Global→local twist reduction (★), the `Û_LSM · Û_LSM†` mirror (Tasaki eq. (6.2.27)).**
`Û_LSM ĥ_x Û_LSM† = exp(−i M̂_x) ĥ_x exp(+i M̂_x)`. -/
theorem twistConj'_eq_localGen {L N r : ℕ} {h₀ : ℝ} {h : Fin L → ManyBodyOpS (Fin L) N}
    (chain : IsShortRangeU1Chain L N r h₀ h) (x : Fin L) :
    lsmTwistOperator L N * h x * (lsmTwistOperator L N).conjTranspose
      = NormedSpace.exp (-Complex.I • localTwistGen L N r x) * h x
          * NormedSpace.exp (Complex.I • localTwistGen L N r x) := by
  rw [lsmTwistOperator_conjTranspose_eq_diagonal, lsmTwistOperator_eq_diagonal,
    exp_smul_localTwistGen_eq_diagonal, exp_smul_localTwistGen_eq_diagonal]
  ext σ' σ
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hz : (h x) σ' σ = 0
  · rw [hz]; ring
  · obtain ⟨m, hm⟩ := twistPhase_gap chain x hz
    have hprod := normedExp_prod_gap' m hm
    linear_combination (h x) σ' σ * hprod

end LatticeSystem.Quantum
