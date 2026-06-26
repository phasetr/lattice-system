/-
Tasaki §4.2.2 Theorem 4.6 (Anderson tower), Tier 3 — discharging the local-decay class
`IsR2LocalUpTo` for the physical double commutator `d̂ = [ô⁺,[Ĥ',ô⁻]]`.

`IsR2LocalUpTo` encodes locality as norm-decay of iterated order-density commutators.  The decay
factor `(2ζo₀/V)` per commutator step comes from *support*: an operator `G` supported on a finite set
`S` (commuting with every on-site factor off `S`) satisfies `[ô^b, G] = V⁻¹ Σ_{w∈S} ε_w [Ŝ_w^b, G]`,
so the commutator stays supported on `S` and its norm contracts by `|S|·2N/V`.  Iterating bounds the
whole `iterOrderComm` tower, which is exactly the `IsR2LocalUpTo` hypothesis.
-/
import LatticeSystem.Quantum.SpinS.AndersonTowerR2Centering

namespace LatticeSystem.Quantum

open Matrix

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {N : ℕ}

/-! ### Operator support and the per-step commutator decay (R2 local-decay, commit 9) -/

/-- The site-`x` order operator `Ŝ_x^b` (`b = true` raising, `b = false` lowering). -/
noncomputable def siteOrderOp (b : Bool) (x : Λ) (N : ℕ) : ManyBodyOpS Λ N :=
  if b then spinSSiteOpPlus x N else spinSSiteOpMinus x N

/-- `Ŝ_x^b` has operator norm `≤ N`. -/
theorem siteOrderOp_manyBodyOperatorNormS_le (b : Bool) (x : Λ) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (siteOrderOp b x N) ≤ (N : ℝ) := by
  cases b with
  | true => exact spinSSiteOpPlus_manyBodyOperatorNormS_le x hN
  | false => exact spinSSiteOpMinus_manyBodyOperatorNormS_le x hN

/-- `Ŝ_x^b = onSiteS x (·)`, hence commutes with any off-site on-site factor. -/
theorem siteOrderOp_commute_onSiteS_of_ne (b : Bool) {x z : Λ} (hzx : z ≠ x)
    (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    Commute (siteOrderOp b x N) (onSiteS z B) := by
  cases b with
  | true => exact (onSiteS_commute_of_ne (Ne.symm hzx) (spinSOpPlus N) B)
  | false => exact (onSiteS_commute_of_ne (Ne.symm hzx) (spinSOpMinus N) B)

/-- **Operator support.**  `G` is supported on the finite set `S` if it commutes with every on-site
factor located off `S`. -/
def SupportedOn (S : Finset Λ) (G : ManyBodyOpS Λ N) : Prop :=
  ∀ z ∉ S, ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ, Commute G (onSiteS z B)

/-- The single-site commutator `[Ŝ_x^b, G] = Ŝ_x^b G − G Ŝ_x^b`. -/
noncomputable def siteComm (b : Bool) (x : Λ) (G : ManyBodyOpS Λ N) : ManyBodyOpS Λ N :=
  siteOrderOp b x N * G - G * siteOrderOp b x N

/-- `[Ŝ_x^b, G]` has norm `≤ 2N‖G‖`. -/
theorem siteComm_norm_le (b : Bool) (x : Λ) (G : ManyBodyOpS Λ N) (hN : 1 ≤ N) :
    manyBodyOperatorNormS (siteComm b x G) ≤ 2 * (N : ℝ) * manyBodyOperatorNormS G := by
  have hd := siteOrderOp_manyBodyOperatorNormS_le b x hN
  have hG := manyBodyOperatorNormS_nonneg G
  refine le_trans (manyBodyOperatorNormS_sub_le _ _) ?_
  have h1 : manyBodyOperatorNormS (siteOrderOp b x N * G) ≤ (N : ℝ) * manyBodyOperatorNormS G :=
    le_trans (manyBodyOperatorNormS_mul_le _ _) (mul_le_mul_of_nonneg_right hd hG)
  have h2 : manyBodyOperatorNormS (G * siteOrderOp b x N) ≤ manyBodyOperatorNormS G * (N : ℝ) :=
    le_trans (manyBodyOperatorNormS_mul_le _ _) (mul_le_mul_of_nonneg_left hd hG)
  nlinarith [h1, h2]

/-- If `G` is supported on `S`, then `[Ŝ_x^b, G] = 0` for any off-support site `x ∉ S`. -/
theorem siteComm_eq_zero_of_not_mem {S : Finset Λ} {G : ManyBodyOpS Λ N} (hG : SupportedOn S G)
    (b : Bool) {x : Λ} (hx : x ∉ S) : siteComm b x G = 0 := by
  have hcomm : Commute G (siteOrderOp b x N) := by
    cases b with
    | true => exact hG x hx (spinSOpPlus N)
    | false => exact hG x hx (spinSOpMinus N)
  rw [siteComm, sub_eq_zero]
  exact hcomm.eq.symm

/-- `[Ŝ_x^b, G]` is supported on `S ∪ {x}`; in particular on `S` when `x ∈ S`. -/
theorem siteComm_supportedOn {S : Finset Λ} {G : ManyBodyOpS Λ N} (hG : SupportedOn S G)
    (b : Bool) {x : Λ} (hx : x ∈ S) : SupportedOn S (siteComm b x G) := by
  intro z hz B
  have hzx : z ≠ x := fun h => hz (h ▸ hx)
  have h1 : Commute (siteOrderOp b x N) (onSiteS z B) :=
    siteOrderOp_commute_onSiteS_of_ne b hzx B
  have h2 : Commute G (onSiteS z B) := hG z hz B
  rw [siteComm]
  exact (h1.mul_left h2).sub_left (h2.mul_left h1)

variable {d L N : ℕ}

/-- The order-density operator is the volume-averaged signed sum of single-site order operators. -/
theorem staggeredOrderDensityOpS_eq_smul_sum [NeZero L] (b : Bool) :
    staggeredOrderDensityOpS d L N b
      = ((L : ℂ) ^ d)⁻¹ • ∑ x : HypercubicTorus d L,
          (if torusParitySublattice d L x then (1 : ℂ) else -1) • siteOrderOp b x N := by
  cases b <;> rfl

/-- The order-density commutator is the volume-averaged signed sum of single-site commutators. -/
theorem orderComm_eq_smul_sum [NeZero L] (b : Bool) (G : ManyBodyOpS (HypercubicTorus d L) N) :
    orderComm b G
      = ((L : ℂ) ^ d)⁻¹ • ∑ x : HypercubicTorus d L,
          (if torusParitySublattice d L x then (1 : ℂ) else -1) • siteComm b x G := by
  rw [orderComm, staggeredOrderDensityOpS_eq_smul_sum, smul_mul_assoc, mul_smul_comm, ← smul_sub,
    Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, siteComm]

/-- `SupportedOn` is closed under scalar multiplication. -/
theorem SupportedOn.smul {S : Finset Λ} {G : ManyBodyOpS Λ N} (hG : SupportedOn S G) (c : ℂ) :
    SupportedOn S (c • G) := fun z hz B => (hG z hz B).smul_left c

/-- `SupportedOn` is closed under finite sums. -/
theorem SupportedOn.sum {ι : Type*} {S : Finset Λ} (s : Finset ι)
    (f : ι → ManyBodyOpS Λ N) (hf : ∀ i ∈ s, SupportedOn S (f i)) :
    SupportedOn S (∑ i ∈ s, f i) := by
  intro z hz B
  exact Commute.sum_left s (fun i => f i) _ (fun i hi => hf i hi z hz B)

/-- The zero operator is supported on every set. -/
theorem supportedOn_zero {S : Finset Λ} : SupportedOn S (0 : ManyBodyOpS Λ N) :=
  fun _ _ _ => Commute.zero_left _

/-- **Support preservation.**  An order-density commutator of an `S`-supported operator stays
supported on `S`. -/
theorem orderComm_supportedOn [NeZero L] {S : Finset (HypercubicTorus d L)}
    {G : ManyBodyOpS (HypercubicTorus d L) N} (hG : SupportedOn S G) (b : Bool) :
    SupportedOn S (orderComm b G) := by
  rw [orderComm_eq_smul_sum]
  refine SupportedOn.smul ?_ _
  refine SupportedOn.sum _ _ (fun x _ => ?_)
  refine SupportedOn.smul ?_ _
  by_cases hx : x ∈ S
  · exact siteComm_supportedOn hG b hx
  · rw [siteComm_eq_zero_of_not_mem hG b hx]; exact supportedOn_zero

/-- **Per-step decay.**  An order-density commutator of an `S`-supported operator contracts the norm
by `2·|S|·N / V`. -/
theorem orderComm_norm_le_of_supported [NeZero L] {S : Finset (HypercubicTorus d L)}
    {G : ManyBodyOpS (HypercubicTorus d L) N} (hG : SupportedOn S G) (hN : 1 ≤ N) (b : Bool) :
    manyBodyOperatorNormS (orderComm b G)
      ≤ 2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d * manyBodyOperatorNormS G := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [orderComm_eq_smul_sum, manyBodyOperatorNormS_smul,
    show ‖((L : ℂ) ^ d)⁻¹‖ = ((L : ℝ) ^ d)⁻¹ from by
      rw [norm_inv, norm_pow, Complex.norm_natCast]]
  have hrestrict : (∑ x : HypercubicTorus d L,
        (if torusParitySublattice d L x then (1 : ℂ) else -1) • siteComm b x G)
      = ∑ x ∈ S, (if torusParitySublattice d L x then (1 : ℂ) else -1) • siteComm b x G := by
    refine (Finset.sum_subset (Finset.subset_univ S) (fun x _ hxS => ?_)).symm
    rw [siteComm_eq_zero_of_not_mem hG b hxS, smul_zero]
  rw [hrestrict]
  have hsum : manyBodyOperatorNormS (∑ x ∈ S,
        (if torusParitySublattice d L x then (1 : ℂ) else -1) • siteComm b x G)
      ≤ (S.card : ℝ) * (2 * (N : ℝ) * manyBodyOperatorNormS G) := by
    refine le_trans (manyBodyOperatorNormS_sum_le S _) ?_
    rw [show (S.card : ℝ) * (2 * (N : ℝ) * manyBodyOperatorNormS G)
        = ∑ _x ∈ S, 2 * (N : ℝ) * manyBodyOperatorNormS G from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [manyBodyOperatorNormS_smul,
      show ‖(if torusParitySublattice d L x then (1 : ℂ) else -1)‖ = 1 from by split <;> simp,
      one_mul]
    exact siteComm_norm_le b x G hN
  have hGnn := manyBodyOperatorNormS_nonneg G
  calc ((L : ℝ) ^ d)⁻¹ * manyBodyOperatorNormS (∑ x ∈ S,
          (if torusParitySublattice d L x then (1 : ℂ) else -1) • siteComm b x G)
      ≤ ((L : ℝ) ^ d)⁻¹ * ((S.card : ℝ) * (2 * (N : ℝ) * manyBodyOperatorNormS G)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d * manyBodyOperatorNormS G := by ring

/-- **Iterated decay.**  Every iterated order-density commutator of an `S`-supported operator
contracts by `(2·|S|·N/V)^{|u|}`. -/
theorem iterOrderComm_norm_le_of_supported [NeZero L] {S : Finset (HypercubicTorus d L)}
    (hN : 1 ≤ N) (u : List Bool) :
    ∀ G : ManyBodyOpS (HypercubicTorus d L) N, SupportedOn S G →
      manyBodyOperatorNormS (iterOrderComm u G)
        ≤ (2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length * manyBodyOperatorNormS G := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  induction u with
  | nil => intro G _; simp
  | cons b u ih =>
    intro G hG
    rw [iterOrderComm_cons, List.length_cons, pow_succ]
    calc manyBodyOperatorNormS (iterOrderComm u (orderComm b G))
        ≤ (2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
            * manyBodyOperatorNormS (orderComm b G) :=
          ih (orderComm b G) (orderComm_supportedOn hG b)
      _ ≤ (2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
            * (2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d * manyBodyOperatorNormS G) :=
          mul_le_mul_of_nonneg_left (orderComm_norm_le_of_supported hG hN b) (by positivity)
      _ = (2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
            * (2 * (S.card : ℝ) * (N : ℝ) / (L : ℝ) ^ d) * manyBodyOperatorNormS G := by ring

/-- **An `S`-supported operator lies in the local-decay class** with `ζ = |S|`, `o₀ = N`,
`g₀ = ‖G‖`.  This bridges operator support to the `IsR2LocalUpTo` hypothesis of Lemma R2. -/
theorem isR2LocalUpTo_of_supported [NeZero L] {S : Finset (HypercubicTorus d L)}
    {G : ManyBodyOpS (HypercubicTorus d L) N} (hG : SupportedOn S G) (hN : 1 ≤ N) (K : ℕ) :
    IsR2LocalUpTo K (S.card : ℝ) (N : ℝ) (manyBodyOperatorNormS G) G :=
  ⟨manyBodyOperatorNormS_nonneg G, fun u _ => iterOrderComm_norm_le_of_supported hN u G hG⟩

/-! ### Linearity of `iterOrderComm` and the quasi-local-sum bound (R2 local-decay, commit 10) -/

/-- `orderComm` is additive in its operator argument. -/
theorem orderComm_add [NeZero L] (b : Bool) (G H : ManyBodyOpS (HypercubicTorus d L) N) :
    orderComm b (G + H) = orderComm b G + orderComm b H := by
  simp only [orderComm, mul_add, add_mul]; abel

/-- `orderComm` commutes with scalar multiplication. -/
theorem orderComm_smul [NeZero L] (b : Bool) (c : ℂ) (G : ManyBodyOpS (HypercubicTorus d L) N) :
    orderComm b (c • G) = c • orderComm b G := by
  simp only [orderComm, mul_smul_comm, smul_mul_assoc, smul_sub]

/-- `iterOrderComm` of zero is zero. -/
theorem iterOrderComm_zero [NeZero L] (u : List Bool) :
    iterOrderComm u (0 : ManyBodyOpS (HypercubicTorus d L) N) = 0 := by
  have h0 : orderComm (d := d) (L := L) (N := N) true 0 = 0 := by simp [orderComm]
  have h0' : orderComm (d := d) (L := L) (N := N) false 0 = 0 := by simp [orderComm]
  induction u with
  | nil => rfl
  | cons b u ih => rw [iterOrderComm_cons]; cases b <;> simp only [h0, h0', ih]

/-- `iterOrderComm` commutes with scalar multiplication. -/
theorem iterOrderComm_smul [NeZero L] (u : List Bool) (c : ℂ)
    (G : ManyBodyOpS (HypercubicTorus d L) N) :
    iterOrderComm u (c • G) = c • iterOrderComm u G := by
  induction u generalizing G with
  | nil => simp
  | cons b u ih => rw [iterOrderComm_cons, iterOrderComm_cons, orderComm_smul, ih]

/-- `iterOrderComm` is additive in its operator argument. -/
theorem iterOrderComm_add [NeZero L] (u : List Bool) (G H : ManyBodyOpS (HypercubicTorus d L) N) :
    iterOrderComm u (G + H) = iterOrderComm u G + iterOrderComm u H := by
  induction u generalizing G H with
  | nil => simp
  | cons b u ih =>
    rw [iterOrderComm_cons, iterOrderComm_cons, iterOrderComm_cons, orderComm_add, ih]

/-- `iterOrderComm` distributes over a finite sum. -/
theorem iterOrderComm_sum [NeZero L] {ι : Type*} (u : List Bool) (s : Finset ι)
    (f : ι → ManyBodyOpS (HypercubicTorus d L) N) :
    iterOrderComm u (∑ i ∈ s, f i) = ∑ i ∈ s, iterOrderComm u (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [iterOrderComm_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, iterOrderComm_add, ih]

/-- **Quasi-local-sum decay.**  If `G = ∑_{i∈s} c_i • Gᵢ` with each `Gᵢ` supported on a set of size
`≤ smax`, then every iterated order-density commutator of `G` decays by `(2·smax·N/V)^{|u|}` times
the ℓ¹-aggregate `∑ |c_i|‖Gᵢ‖`.  This is the structural input for
`d̂ = V⁻²∑_bonds J·bondDoubleComm`, a sum of two-site-supported terms (so `smax = 2`). -/
theorem iterOrderComm_norm_le_of_localSum [NeZero L] {ι : Type*} (hN : 1 ≤ N) (u : List Bool)
    (s : Finset ι) (c : ι → ℂ) (G : ι → ManyBodyOpS (HypercubicTorus d L) N)
    (S : ι → Finset (HypercubicTorus d L)) (smax : ℕ)
    (hsup : ∀ i ∈ s, SupportedOn (S i) (G i)) (hcard : ∀ i ∈ s, (S i).card ≤ smax) :
    manyBodyOperatorNormS (iterOrderComm u (∑ i ∈ s, c i • G i))
      ≤ (2 * (smax : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
        * ∑ i ∈ s, ‖c i‖ * manyBodyOperatorNormS (G i) := by
  have hVpos : (0 : ℝ) < (L : ℝ) ^ d := by
    have : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  rw [iterOrderComm_sum, Finset.mul_sum]
  refine le_trans (manyBodyOperatorNormS_sum_le s _) (Finset.sum_le_sum (fun i hi => ?_))
  rw [iterOrderComm_smul, manyBodyOperatorNormS_smul]
  have hbd := iterOrderComm_norm_le_of_supported hN u (G i) (hsup i hi)
  have hmono : (2 * ((S i).card : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
      ≤ (2 * (smax : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length := by
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    exact_mod_cast hcard i hi
  calc ‖c i‖ * manyBodyOperatorNormS (iterOrderComm u (G i))
      ≤ ‖c i‖ * ((2 * ((S i).card : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
          * manyBodyOperatorNormS (G i)) := by
        exact mul_le_mul_of_nonneg_left hbd (norm_nonneg _)
    _ ≤ ‖c i‖ * ((2 * (smax : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
          * manyBodyOperatorNormS (G i)) := by
        gcongr
        exact manyBodyOperatorNormS_nonneg _
    _ = (2 * (smax : ℝ) * (N : ℝ) / (L : ℝ) ^ d) ^ u.length
          * (‖c i‖ * manyBodyOperatorNormS (G i)) := by ring

end LatticeSystem.Quantum
