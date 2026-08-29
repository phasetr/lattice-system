import LatticeSystem.Quantum.IsingLowEnergyProblem33aRoots

/-!
# The (S.41) splitting limit of Tasaki Problem 3.3.a

Tasaki, *Physics and Mathematics of Quantum Many-Body Systems*, Problem 3.3.a (statement p. 59,
solution pp. 498-501) extracts the energy difference of the two parity sectors from the root
equation (S.34) by expanding it around the `L ↑ ∞` rate `κ∞` of (S.35):

* (S.36)-(S.38), p. 500: writing `κ = κ∞ + δ`, `e^{κ∞+δ} - e^{-κ∞-δ} ≃ λ⁻¹ (1 ± 2 e^-κ∞L)`,
  then `δ ≃ ±λ⁻¹ 2 e^-κ∞L / (e^κ∞ + e^-κ∞)` and `ε ≃ ε∞ - (λ/2)(e^κ∞ - e^-κ∞) δ`, the middle
  step introduced by "Expanding the left-hand side in `δ` to the lowest order";
* (S.40), p. 501: `ε_± ≃ ε∞ ∓ [(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)] e^-κ∞L`;
* (S.41), p. 501: `E_1st - E_GS = ε_- - ε_+ ≃ 2 [(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)] e^-κ∞L ≃ 2 λ^L`.

None of those `≃` is asserted here. `tendsto_splitting_ratio` states the middle expression of
(S.41) as an exact limit: with `λ` fixed and the ring size growing — the order of limits of the
source's footnote 1 on p. 500, "we fix small `λ`, and then make `L` large" — the ratio of
`ε_- - ε_+` to `2 tanh κ∞ e^-κ∞L` tends to `1`. The prefactor is `tanh κ∞` because
`(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)` is exactly that.

Two exact ingredients replace the source's two non-rigorous moves. In place of the Taylor step of
(S.36)-(S.38) the module uses the identity
`ε(κ_-) - ε(κ_+) = tanh((κ_+ + κ_-)/2) (hop λ κ_+ - hop λ κ_-)/2`, valid for all arguments, in
which the source's `δ`-expansion becomes an equality. In place of the source's "`L ≫ 1`" the
module localizes the roots: `root_symmetric_gt_kappaInf` puts every positive symmetric root above
`κ∞` at every ring size, and `eventually_root_antisymmetric_mem_Ico` puts every positive
antisymmetric root into `[arsinh (3/(8λ)), κ∞)` for all sufficiently large ring sizes, so that the
statements below are `∀ᶠ N in atTop`.

Limitations measured in this layer. Uniqueness of the root in either sector is neither proved nor
used: `tendsto_splitting_ratio` quantifies over arbitrary families `kp`, `km` of positive roots of
the two sectors, one per ring size. The `∀ᶠ` of the antisymmetric localization is not cosmetic:
the lower bound is obtained by excluding roots with `e^-κL > 1/8`, which the cleared equation
allows only while the ring size stays below a multiple of `λ e^κ∞`. The last step `≃ 2 λ^L` of
(S.41) is not asserted here; its two small-`λ` replacements are
`tendsto_exp_neg_kappaInf_div_atZero` and `tendsto_tanh_kappaInf_atZero` of
`LatticeSystem/Quantum/IsingLowEnergyProblem33aSpectrum.lean`, which are limits in `λ` at no fixed
ring size and are not combined with the `L ↑ ∞` limit of this module.

`tightBindingEnergy λ κ` is an eigenvalue of the compression `lowEnergyMatrix N λ` of `Ĥ` to a
span that `Ĥ` does not preserve, so `ε_±` and their difference are eigenvalue data of the
compressed matrix and are not identified with a ground-state or first-excited energy of `Ĥ`.
Tasaki notes on p. 59 that the perturbative analysis of this problem is not mathematically
rigorous. The ring carrying the labels `j` is a ring of basis labels of type `ZMod (2 * (N + 1))`,
not of lattice sites: the chain itself stays open.
-/

namespace LatticeSystem.Quantum

/-! ### The lower localization threshold -/

/-- `hop λ (arsinh (c / (2λ))) = c`. Because `hop λ κ = 2 λ sinh κ`, the inverse hyperbolic sine
inverts `hop λ ·` explicitly; at `c = 1` this is Tasaki eq. (S.35), p. 500, and at `c = 3/4` it
names the threshold `arsinh (3/(8λ))` used to localize the antisymmetric root of (S.34). -/
private theorem hop_arsinh_eq {lam : ℝ} (hlam : 0 < lam) (c : ℝ) :
    hop lam (Real.arsinh (c / (2 * lam))) = c := by
  have hne : lam ≠ 0 := ne_of_gt hlam
  have hsinh : Real.sinh (Real.arsinh (c / (2 * lam))) = c / (2 * lam) := Real.sinh_arsinh _
  have hsplit : Real.exp (Real.arsinh (c / (2 * lam)))
      - Real.exp (-Real.arsinh (c / (2 * lam)))
      = 2 * Real.sinh (Real.arsinh (c / (2 * lam))) := by
    rw [Real.sinh_eq]
    ring
  rw [hop, hsplit, hsinh]
  field_simp

/-- `hop λ ·` takes the value `3/4` at `arsinh (3/(8λ))` and the value `1` at `κ∞`, so the
threshold lies strictly below the `L ↑ ∞` rate of Tasaki eq. (S.35), p. 500. -/
private theorem arsinh_lt_kappaInf {lam : ℝ} (hlam : 0 < lam) :
    Real.arsinh (3 / (8 * lam)) < kappaInf lam := by
  have harg : (3 : ℝ) / (8 * lam) = 3 / 4 / (2 * lam) := by
    have hne : lam ≠ 0 := ne_of_gt hlam
    field_simp
    ring
  refine (hop_strictMono hlam).lt_iff_lt.mp ?_
  rw [harg, hop_arsinh_eq hlam (3 / 4), hop_kappaInf_eq_one hlam]
  norm_num

/-- `hop λ ·` grows at least at rate `λ` on the nonnegative reals: for `0 ≤ x` and `0 ≤ y`,
`λ |x - y| ≤ |hop λ x - hop λ y|`, because `e^x - e^y ≥ x - y` and `e^-y - e^-x ≥ 0` when
`y ≤ x`. This converts a bound on the defect of the cleared root equation into a bound on the
distance from a root of Tasaki eq. (S.34) to `κ∞`. -/
private theorem mul_abs_sub_le_abs_hop_sub {lam : ℝ} (hlam : 0 < lam) {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) : lam * |x - y| ≤ |hop lam x - hop lam y| := by
  have key : ∀ u v : ℝ, 0 ≤ v → v ≤ u → lam * (u - v) ≤ hop lam u - hop lam v := by
    intro u v hv huv
    have hprod : Real.exp v * Real.exp (u - v) = Real.exp u := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlin : u - v + 1 ≤ Real.exp (u - v) := Real.add_one_le_exp _
    have hone : (1 : ℝ) ≤ Real.exp v := Real.one_le_exp hv
    have hstep : Real.exp v * (u - v + 1) ≤ Real.exp u := by
      rw [← hprod]
      exact mul_le_mul_of_nonneg_left hlin (Real.exp_pos v).le
    have hexp : u - v ≤ Real.exp u - Real.exp v := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Real.exp v - 1)
        (by linarith : (0 : ℝ) ≤ u - v)]
    have hneg : Real.exp (-u) ≤ Real.exp (-v) := Real.exp_le_exp.mpr (by linarith)
    simp only [hop]
    nlinarith [mul_nonneg hlam.le (by linarith : (0 : ℝ) ≤ Real.exp u - Real.exp v - (u - v)),
      mul_nonneg hlam.le (by linarith : (0 : ℝ) ≤ Real.exp (-v) - Real.exp (-u))]
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y),
      abs_of_nonneg (by linarith [(hop_strictMono hlam).monotone h] :
        (0 : ℝ) ≤ hop lam x - hop lam y)]
    exact key x y hy h
  · rw [abs_of_nonpos (by linarith : x - y ≤ (0 : ℝ)),
      abs_of_nonpos (by linarith [(hop_strictMono hlam).monotone h] :
        hop lam x - hop lam y ≤ (0 : ℝ))]
    have := key y x hx h
    linarith

/-! ### Localization of the two parity roots -/

/-- Every positive root of the symmetric (`s = 1`) form of Tasaki eq. (S.34), p. 500, lies
strictly above the `L ↑ ∞` rate `κ∞` of (S.35), at every ring size: the cleared equation gives
`hop λ κ = (1 + e^-κL)/(1 - e^-κL) > 1 = hop λ κ∞`, and `hop λ ·` is strictly increasing.
Positivity of `λ` is not assumed; it follows from the root hypothesis. -/
theorem root_symmetric_gt_kappaInf (N : ℕ) (lam kp : ℝ) (hkp : 0 < kp)
    (hroot : rootEquation N lam kp 1) : kappaInf lam < kp := by
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hwpos : (0 : ℝ) < Real.exp (-kp * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
  have hwlt : Real.exp (-kp * ((N + 1 : ℕ) : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hA : 0 < Real.exp kp - Real.exp (-kp) := by
    have := Real.exp_lt_exp.mpr (show -kp < kp by linarith)
    linarith
  have hcl := (rootEquation_iff_cleared N lam kp 1 hkp (Or.inl rfl)).mp hroot
  have hlam : 0 < lam := by
    rcases le_or_gt lam 0 with hle | hgt
    · exfalso
      nlinarith [mul_nonneg hA.le
        (show (0 : ℝ) ≤ 1 - 1 * Real.exp (-kp * ((N + 1 : ℕ) : ℝ)) by linarith)]
    · exact hgt
  refine (hop_strictMono hlam).lt_iff_lt.mp ?_
  rw [hop_kappaInf_eq_one hlam, hop]
  nlinarith

/-- Every positive root of the antisymmetric (`s = -1`) form of Tasaki eq. (S.34), p. 500, lies
in `[arsinh (3/(8λ)), κ∞)`, for all sufficiently large ring sizes. The upper bound holds at every
ring size, since the cleared equation gives `hop λ κ = (1 - e^-κL)/(1 + e^-κL) < 1 = hop λ κ∞`.
The lower bound splits on `w = e^-κL`: for `w ≤ 1/8` the same equation gives
`hop λ κ ≥ (7/8)/(9/8) ≥ 3/4 = hop λ (arsinh (3/(8λ)))`, while `w > 1/8` gives
`κL/16 < hop λ κ ≤ 2λκ e^κ∞` and hence `L < 32 λ e^κ∞`, which the ring size eventually
exceeds. -/
theorem eventually_root_antisymmetric_mem_Ico (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ km : ℝ, 0 < km → rootEquation N lam km (-1) →
      Real.arsinh (3 / (8 * lam)) ≤ km ∧ km < kappaInf lam := by
  obtain ⟨M, hM⟩ := exists_nat_gt (32 * lam * Real.exp (kappaInf lam))
  filter_upwards [Filter.eventually_ge_atTop M] with N hN km hkm hroot
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hLbig : 32 * lam * Real.exp (kappaInf lam) < ((N + 1 : ℕ) : ℝ) := by
    have hMN : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith
  have hcl := (rootEquation_iff_cleared N lam km (-1) hkm (Or.inr rfl)).mp hroot
  set w : ℝ := Real.exp (-km * ((N + 1 : ℕ) : ℝ)) with hwdef
  have hwpos : (0 : ℝ) < w := Real.exp_pos _
  have hwlt : w < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hhop : hop lam km * (1 + w) = 1 - w := by
    simp only [hop]
    linear_combination hcl
  have hupper : km < kappaInf lam := by
    refine (hop_strictMono hlam).lt_iff_lt.mp ?_
    rw [hop_kappaInf_eq_one hlam]
    nlinarith
  refine ⟨?_, hupper⟩
  have harg : (3 : ℝ) / (8 * lam) = 3 / 4 / (2 * lam) := by
    have hne : lam ≠ 0 := ne_of_gt hlam
    field_simp
    ring
  rcases le_or_gt w (1 / 8) with hcase | hcase
  · refine (hop_strictMono hlam).le_iff_le.mp ?_
    rw [harg, hop_arsinh_eq hlam (3 / 4)]
    nlinarith
  · exfalso
    have hprod : Real.exp (km * ((N + 1 : ℕ) : ℝ)) * w = 1 := by
      rw [hwdef, ← Real.exp_add]
      norm_num
    have hlin : km * ((N + 1 : ℕ) : ℝ) + 1 ≤ Real.exp (km * ((N + 1 : ℕ) : ℝ)) :=
      Real.add_one_le_exp _
    have hlow : km * ((N + 1 : ℕ) : ℝ) * w ≤ 1 - w := by
      nlinarith [mul_le_mul_of_nonneg_right hlin hwpos.le]
    have hhoppos : 0 < hop lam km := by nlinarith
    have hhoplow : km * ((N + 1 : ℕ) : ℝ) / 16 < hop lam km := by nlinarith
    have hexpk : (0 : ℝ) < Real.exp km := Real.exp_pos _
    have hupperhop : hop lam km ≤ 2 * lam * km * Real.exp km := by
      have hsq : Real.exp (-km) = Real.exp km * Real.exp (-2 * km) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hlin2 : 1 - Real.exp (-2 * km) ≤ 2 * km := by
        have := Real.add_one_le_exp (-2 * km)
        linarith
      calc hop lam km = lam * (Real.exp km * (1 - Real.exp (-2 * km))) := by
            simp only [hop]
            rw [hsq]
            ring
        _ ≤ lam * (Real.exp km * (2 * km)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlin2 hexpk.le) hlam.le
        _ = 2 * lam * km * Real.exp km := by ring
    have hexple : Real.exp km ≤ Real.exp (kappaInf lam) := Real.exp_le_exp.mpr hupper.le
    have hchain : km * ((N + 1 : ℕ) : ℝ) / 16 < 2 * lam * km * Real.exp (kappaInf lam) := by
      have hmono : 2 * lam * km * Real.exp km ≤ 2 * lam * km * Real.exp (kappaInf lam) :=
        mul_le_mul_of_nonneg_left hexple (by positivity)
      linarith
    nlinarith [mul_pos hkm (sub_pos.mpr hLbig)]

/-! ### Decay of the distance from a root to `κ∞` -/

/-- For a root of either sector lying above the threshold `a = arsinh (3/(8λ))`, the distance to
`κ∞` is at most `(4/λ) e^-aL`. The cleared form of Tasaki eq. (S.34), p. 500, bounds the defect
`|hop λ κ - 1|` by `4 e^-κL ≤ 4 e^-aL`, and `hop λ ·` grows at least at rate `λ`. -/
private theorem abs_sub_kappaInf_le_of_root (N : ℕ) (lam k s : ℝ) (hlam : 0 < lam) (hk : 0 < k)
    (hs : s = 1 ∨ s = -1) (hroot : rootEquation N lam k s)
    (hlow : Real.arsinh (3 / (8 * lam)) ≤ k)
    (hhalf : Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)) ≤ 1 / 2) :
    |k - kappaInf lam|
      ≤ 4 / lam * Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)) := by
  have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hcl := (rootEquation_iff_cleared N lam k s hk hs).mp hroot
  set w : ℝ := Real.exp (-k * ((N + 1 : ℕ) : ℝ)) with hwdef
  have hwpos : (0 : ℝ) < w := Real.exp_pos _
  have hwle : w ≤ Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)) := by
    rw [hwdef]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hwhalf : w ≤ 1 / 2 := le_trans hwle hhalf
  have hhop : hop lam k * (1 - s * w) = 1 + s * w := by
    simp only [hop]
    linear_combination hcl
  have hdefect : |hop lam k - 1| ≤ 4 * w := by
    rcases hs with rfl | rfl
    · rw [abs_of_nonneg (by nlinarith)]
      nlinarith
    · rw [abs_of_nonpos (by nlinarith)]
      nlinarith
  have hlip := mul_abs_sub_le_abs_hop_sub hlam (le_of_lt hk)
    (le_of_lt (kappaInf_pos hlam)) (x := k) (y := kappaInf lam)
  rw [hop_kappaInf_eq_one hlam] at hlip
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
  linarith

/-- `L e^-aL → 0` along `L = N + 1` for a positive rate `a`. This single decay makes both the
distance from a root of Tasaki eq. (S.34), p. 500, to `κ∞` and its product with `L` vanish. -/
private theorem tendsto_succ_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    Filter.Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) * Real.exp (-a * ((N + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
  have hcast : Filter.Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun N => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    push_cast
    linarith
  have hg : Filter.Tendsto (fun N : ℕ => a * ((N + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop ha hcast
  have hscaled := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hg).const_mul a⁻¹
  rw [mul_zero] at hscaled
  refine hscaled.congr (fun N => ?_)
  simp only [Function.comp_apply, pow_one]
  rw [neg_mul]
  field_simp

/-- Along a family of positive roots of one sector of Tasaki eq. (S.34), p. 500, all lying above
the threshold `arsinh (3/(8λ))`: the roots converge to `κ∞`, their weights `e^-κL` vanish, and
the ratio of `e^-κL` to `e^-κ∞L` tends to `1`. The last statement is what makes the source's
replacement of `e^-κL` by `e^-κ∞L` between (S.36) and (S.40), p. 500-501, exact in the limit. -/
private theorem tendsto_root_family (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (k : ℕ → ℝ)
    (hk : ∀ᶠ N : ℕ in Filter.atTop, 0 < k N ∧ rootEquation N lam (k N) s
      ∧ Real.arsinh (3 / (8 * lam)) ≤ k N) :
    Filter.Tendsto k Filter.atTop (nhds (kappaInf lam))
      ∧ Filter.Tendsto (fun N : ℕ => Real.exp (-k N * ((N + 1 : ℕ) : ℝ)))
          Filter.atTop (nhds 0)
      ∧ Filter.Tendsto (fun N : ℕ => Real.exp (-k N * ((N + 1 : ℕ) : ℝ))
          / Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ))) Filter.atTop (nhds 1) := by
  have hapos : 0 < Real.arsinh (3 / (8 * lam)) := Real.arsinh_pos_iff.mpr (by positivity)
  have hLW := tendsto_succ_mul_exp_neg hapos
  have hLone : ∀ N : ℕ, (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    intro N
    have : (1 : ℕ) ≤ N + 1 := Nat.succ_le_succ (Nat.zero_le N)
    exact_mod_cast this
  have hW : Filter.Tendsto
      (fun N : ℕ => Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun N => (Real.exp_pos _).le) (fun N => ?_) hLW
    nlinarith [Real.exp_pos (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)), hLone N]
  have hhalf : ∀ᶠ N : ℕ in Filter.atTop,
      Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)) ≤ 1 / 2 := by
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / Real.arsinh (3 / (8 * lam)))
    filter_upwards [Filter.eventually_ge_atTop M] with N hN
    have hMN : (M : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have hbig : 1 / Real.arsinh (3 / (8 * lam)) < ((N + 1 : ℕ) : ℝ) := by
      rw [hcast]; linarith
    have hone : (1 : ℝ) ≤ Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hapos] at hbig
      nlinarith
    have he1 : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      linarith
    exact le_trans (Real.exp_le_exp.mpr (by linarith)) he1
  have hbound : ∀ᶠ N : ℕ in Filter.atTop, ‖k N - kappaInf lam‖
      ≤ 4 / lam * Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)) := by
    filter_upwards [hk, hhalf] with N hkN hhN
    rw [Real.norm_eq_abs]
    exact abs_sub_kappaInf_le_of_root N lam (k N) s hlam hkN.1 hs hkN.2.1 hkN.2.2 hhN
  have hzero : Filter.Tendsto (fun N : ℕ => k N - kappaInf lam) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' hbound ?_
    have := hW.const_mul (4 / lam)
    rwa [mul_zero] at this
  have hk_tend : Filter.Tendsto k Filter.atTop (nhds (kappaInf lam)) :=
    tendsto_sub_nhds_zero_iff.mp hzero
  have hwle : ∀ᶠ N : ℕ in Filter.atTop, Real.exp (-k N * ((N + 1 : ℕ) : ℝ))
      ≤ Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)) := by
    filter_upwards [hk] with N hkN
    exact Real.exp_le_exp.mpr (by nlinarith [hLone N])
  have hw_tend : Filter.Tendsto (fun N : ℕ => Real.exp (-k N * ((N + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun N => (Real.exp_pos _).le) hwle hW
  refine ⟨hk_tend, hw_tend, ?_⟩
  have hprodzero : Filter.Tendsto
      (fun N : ℕ => (kappaInf lam - k N) * ((N + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' (a := fun N : ℕ => 4 / lam
      * (((N + 1 : ℕ) : ℝ) * Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ)))) ?_ ?_
    · filter_upwards [hbound] with N hN
      rw [Real.norm_eq_abs] at hN
      have hL : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by linarith [hLone N]
      rw [Real.norm_eq_abs, abs_mul, abs_sub_comm, abs_of_nonneg hL]
      calc |k N - kappaInf lam| * ((N + 1 : ℕ) : ℝ)
          ≤ 4 / lam * Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ))
            * ((N + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hN hL
        _ = 4 / lam * (((N + 1 : ℕ) : ℝ)
            * Real.exp (-Real.arsinh (3 / (8 * lam)) * ((N + 1 : ℕ) : ℝ))) := by ring
    · have := hLW.const_mul (4 / lam)
      rwa [mul_zero] at this
  have hexp := Real.tendsto_exp_nhds_zero_nhds_one.comp hprodzero
  refine hexp.congr (fun N => ?_)
  simp only [Function.comp_apply]
  rw [← Real.exp_sub]
  congr 1
  ring

/-! ### The exact factorization replacing the Taylor step -/

/-- The exact identity that replaces the source's Taylor step (S.36)-(S.38), p. 500: for all
`x`, `y`, the difference of the eigenvalue (S.31) at the two arguments factors as
`ε(y) - ε(x) = tanh((x + y)/2) (hop λ x - hop λ y)/2`, here with `tanh` written in the
exponential form `(e^{x+y} - 1)/(e^{x+y} + 1)`. Both factors are exact, so no expansion in
`x - y` is involved. -/
private theorem tightBindingEnergy_sub_eq (lam x y : ℝ) :
    tightBindingEnergy lam y - tightBindingEnergy lam x
      = (Real.exp (x + y) - 1) / (Real.exp (x + y) + 1) * (hop lam x - hop lam y) / 2 := by
  have hx : Real.exp x ≠ 0 := (Real.exp_pos x).ne'
  have hy : Real.exp y ≠ 0 := (Real.exp_pos y).ne'
  have hd : Real.exp x * Real.exp y + 1 ≠ 0 := by positivity
  simp only [tightBindingEnergy, hop, Real.exp_neg, Real.exp_add]
  field_simp
  ring

/-- The normalized defect of one parity sector of Tasaki eq. (S.34), p. 500, tends to `2`. The
cleared equation gives `s (hop λ κ - 1) = e^-κL (1 + hop λ κ)` exactly, and both `hop λ κ → 1`
and `e^-κL / e^-κ∞L → 1` hold along a family of roots localized around `κ∞`. -/
private theorem tendsto_sector_defect_div (lam s : ℝ) (hs : s = 1 ∨ s = -1) (k : ℕ → ℝ)
    (hroot : ∀ᶠ N : ℕ in Filter.atTop, 0 < k N ∧ rootEquation N lam (k N) s)
    (hw : Filter.Tendsto (fun N : ℕ => Real.exp (-k N * ((N + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0))
    (hwr : Filter.Tendsto (fun N : ℕ => Real.exp (-k N * ((N + 1 : ℕ) : ℝ))
      / Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ))) Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun N : ℕ => s * (hop lam (k N) - 1)
      / Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ))) Filter.atTop (nhds 2) := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hclear : ∀ᶠ N : ℕ in Filter.atTop,
      hop lam (k N) * (1 - s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ)))
        = 1 + s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ)) := by
    filter_upwards [hroot] with N hN
    have := (rootEquation_iff_cleared N lam (k N) s hN.1 hs).mp hN.2
    simp only [hop]
    linear_combination this
  have hden : Filter.Tendsto
      (fun N : ℕ => 1 - s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ))) Filter.atTop (nhds 1) := by
    have := (hw.const_mul s).const_sub 1
    simpa using this
  have hnum : Filter.Tendsto
      (fun N : ℕ => 1 + s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ))) Filter.atTop (nhds 1) := by
    have := (hw.const_mul s).const_add 1
    simpa using this
  have hhop : Filter.Tendsto (fun N : ℕ => hop lam (k N)) Filter.atTop (nhds 1) := by
    have hquot : Filter.Tendsto
        (fun N : ℕ => (1 + s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ)))
          / (1 - s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ)))) Filter.atTop (nhds (1 / 1)) :=
      hnum.div hden one_ne_zero
    rw [div_one] at hquot
    refine hquot.congr' ?_
    filter_upwards [hclear, hroot] with N hN hrN
    have hwlt : Real.exp (-k N * ((N + 1 : ℕ) : ℝ)) < 1 := by
      refine Real.exp_lt_one_iff.mpr ?_
      have hLpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
      nlinarith [hrN.1]
    have hwpos : (0 : ℝ) < Real.exp (-k N * ((N + 1 : ℕ) : ℝ)) := Real.exp_pos _
    have hne : 1 - s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ)) ≠ 0 := by
      rcases hs with rfl | rfl <;> intro hcon <;> linarith
    rw [← hN, mul_div_assoc, div_self hne, mul_one]
  have hlimit := hwr.mul (hhop.const_add 1)
  rw [show (1 : ℝ) * (1 + 1) = 2 by norm_num] at hlimit
  refine hlimit.congr' ?_
  filter_upwards [hclear] with N hN
  have hkey : s * (hop lam (k N) - 1)
      = Real.exp (-k N * ((N + 1 : ℕ) : ℝ)) * (1 + hop lam (k N)) := by
    have hstep : hop lam (k N) - 1
        = s * Real.exp (-k N * ((N + 1 : ℕ) : ℝ)) * (1 + hop lam (k N)) := by
      linear_combination hN
    rw [hstep]
    linear_combination Real.exp (-k N * ((N + 1 : ℕ) : ℝ)) * (1 + hop lam (k N)) * hs2
  rw [hkey]
  ring

/-! ### The (S.41) splitting limit -/

/-- **Tasaki eq. (S.41), p. 501, as an exact limit.** Let `λ > 0`, and let `kp` and `km` be
families of positive roots of the symmetric resp. antisymmetric form of the root equation (S.34),
p. 500, one for each sufficiently large ring size. Then the ratio of the corresponding difference
of eigenvalues (S.31) of the compressed matrix to `2 tanh κ∞ (e^-κ∞)^(N+1)` tends to `1`.

The middle expression of (S.41), `2 [(e^κ∞ - e^-κ∞)/(e^κ∞ + e^-κ∞)] e^-κ∞L`, is exactly
`2 tanh κ∞ e^-κ∞L`; the source's `≃` is here replaced by convergence of the ratio, with `λ` fixed
and the ring size growing, which is the order of limits of the source's footnote 1 on p. 500. The
final step `≃ 2 λ^L` of (S.41) is a separate small-`λ` statement and is not asserted here.

No uniqueness of either root is assumed: `kp` and `km` range over arbitrary eventually-positive
root families of their sectors. `tightBindingEnergy` is an eigenvalue of the compression
`lowEnergyMatrix N λ` of `Ĥ`, not an energy of `Ĥ`. -/
theorem tendsto_splitting_ratio (lam : ℝ) (hlam : 0 < lam) (kp km : ℕ → ℝ)
    (hkp : ∀ᶠ N : ℕ in Filter.atTop, 0 < kp N ∧ rootEquation N lam (kp N) 1)
    (hkm : ∀ᶠ N : ℕ in Filter.atTop, 0 < km N ∧ rootEquation N lam (km N) (-1)) :
    Filter.Tendsto
      (fun N : ℕ => (tightBindingEnergy lam (km N) - tightBindingEnergy lam (kp N))
        / (2 * Real.tanh (kappaInf lam) * Real.exp (-(kappaInf lam)) ^ (N + 1)))
      Filter.atTop (nhds 1) := by
  have hkp' : ∀ᶠ N : ℕ in Filter.atTop, 0 < kp N ∧ rootEquation N lam (kp N) 1
      ∧ Real.arsinh (3 / (8 * lam)) ≤ kp N := by
    filter_upwards [hkp] with N hN
    exact ⟨hN.1, hN.2, le_of_lt (lt_trans (arsinh_lt_kappaInf hlam)
      (root_symmetric_gt_kappaInf N lam (kp N) hN.1 hN.2))⟩
  have hkm' : ∀ᶠ N : ℕ in Filter.atTop, 0 < km N ∧ rootEquation N lam (km N) (-1)
      ∧ Real.arsinh (3 / (8 * lam)) ≤ km N := by
    filter_upwards [hkm, eventually_root_antisymmetric_mem_Ico lam hlam] with N hN hloc
    exact ⟨hN.1, hN.2, (hloc (km N) hN.1 hN.2).1⟩
  obtain ⟨hkp_tend, hkp_w, hkp_r⟩ := tendsto_root_family lam hlam 1 (Or.inl rfl) kp hkp'
  obtain ⟨hkm_tend, hkm_w, hkm_r⟩ := tendsto_root_family lam hlam (-1) (Or.inr rfl) km hkm'
  have hdp := tendsto_sector_defect_div lam 1 (Or.inl rfl) kp hkp hkp_w hkp_r
  have hdm := tendsto_sector_defect_div lam (-1) (Or.inr rfl) km hkm hkm_w hkm_r
  have hgap : Filter.Tendsto
      (fun N : ℕ => (hop lam (kp N) - hop lam (km N))
        / Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ))) Filter.atTop (nhds 4) := by
    have hsum := hdp.add hdm
    rw [show (2 : ℝ) + 2 = 4 by norm_num] at hsum
    refine hsum.congr (fun N => ?_)
    field_simp
    ring
  have hcont : Continuous (fun t : ℝ => (Real.exp t - 1) / (Real.exp t + 1)) :=
    (Real.continuous_exp.sub continuous_const).div
      (Real.continuous_exp.add continuous_const) (fun t => by positivity)
  have htanh : Filter.Tendsto
      (fun N : ℕ => (Real.exp (kp N + km N) - 1) / (Real.exp (kp N + km N) + 1))
      Filter.atTop (nhds (Real.tanh (kappaInf lam))) := by
    have hsum : Filter.Tendsto (fun N : ℕ => kp N + km N) Filter.atTop
        (nhds (kappaInf lam + kappaInf lam)) := hkp_tend.add hkm_tend
    have hval : (Real.exp (kappaInf lam + kappaInf lam) - 1)
        / (Real.exp (kappaInf lam + kappaInf lam) + 1) = Real.tanh (kappaInf lam) := by
      rw [Real.tanh_eq, Real.exp_add, Real.exp_neg]
      field_simp
    have := (hcont.tendsto (kappaInf lam + kappaInf lam)).comp hsum
    rwa [hval] at this
  have htanhpos : 0 < Real.tanh (kappaInf lam) := by
    rw [tanh_kappaInf_eq hlam]
    positivity
  have hprod := (htanh.mul hgap).div_const 2
  have hquot := hprod.div_const (2 * Real.tanh (kappaInf lam))
  rw [show Real.tanh (kappaInf lam) * 4 / 2 = 2 * Real.tanh (kappaInf lam) by ring,
    div_self (by positivity : 2 * Real.tanh (kappaInf lam) ≠ 0)] at hquot
  refine hquot.congr (fun N => ?_)
  have hXne : Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have hpow : Real.exp (-(kappaInf lam)) ^ (N + 1)
      = Real.exp (-kappaInf lam * ((N + 1 : ℕ) : ℝ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow, tightBindingEnergy_sub_eq lam (kp N) (km N)]
  field_simp

end LatticeSystem.Quantum
