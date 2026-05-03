import LatticeSystem.Quantum.SpinS.AllAlignedState

/-!
# Non-vanishing of `Ŝ_{tot}^∓ · |σ_{⊤/⊥}⟩` on the saturated ferromagnet

For a multi-site spin-`S` system with at least one site (`Nonempty V`)
and spin `S ≥ 1/2` (`0 < N`, since `N = 2S`), the once-lowered all-up
state `Ŝ_{tot}^- · |σ_⊤⟩` is non-zero, with explicit value `√N` at
each "one-flipped" configuration that differs from the all-up
configuration by raising the value at exactly one site from `0` to
`1 ∈ Fin (N + 1)`.

This is the foundational non-vanishing fact for the saturated-
ferromagnet ladder. Combined with the magnetic-quantum-number
labelling (PR #887) and the magnetization subspace direct sum
decomposition (PR #889), it shows that the once-lowered state lies
in the *next* magnetization sector and is genuinely a new vector,
not the zero vector that would collapse the ladder.

The symmetric statement holds for `Ŝ_{tot}^+ · |σ_⊥⟩` via the
`c = N` (all-down) parallel.

Tracked as part of Tasaki §2.4 / §2.5 spin-`S` infrastructure
(Issue #412).
-/

namespace LatticeSystem.Quantum

variable {V : Type*} [Fintype V] [DecidableEq V] {N : ℕ}

/-! ## Lowering once: explicit value at the one-flipped configuration -/

/-- The configuration that flips one site `x_0 : V` from `0` to
`1 ∈ Fin (N + 1)` and leaves the rest at `0`. Requires `0 < N` so
that `1 < N + 1`, allowing the `Fin` value `⟨1, _⟩` to exist. -/
def oneFlippedUpConfig (V : Type*) (x_0 : V) {N : ℕ} (hN : 0 < N)
    [DecidableEq V] : V → Fin (N + 1) :=
  fun i => if i = x_0 then ⟨1, by omega⟩ else 0

/-- Off the flipped site, `oneFlippedUpConfig` agrees with the all-up
configuration. -/
theorem oneFlippedUpConfig_apply_off (V : Type*) [DecidableEq V]
    (x_0 : V) (hN : 0 < N) {i : V} (hi : i ≠ x_0) :
    oneFlippedUpConfig V x_0 hN i = (0 : Fin (N + 1)) := by
  unfold oneFlippedUpConfig
  rw [if_neg hi]

/-- At the flipped site, `oneFlippedUpConfig` takes value `1`. -/
theorem oneFlippedUpConfig_apply_self (V : Type*) [DecidableEq V]
    (x_0 : V) (hN : 0 < N) :
    oneFlippedUpConfig V x_0 hN x_0 = ⟨1, by omega⟩ := by
  unfold oneFlippedUpConfig
  rw [if_pos rfl]

/-- The one-flipped configuration disagrees with the all-up
configuration at the flipped site. -/
theorem oneFlippedUpConfig_ne_allAlignedConfigS_zero (V : Type*)
    [DecidableEq V] (x_0 : V) (hN : 0 < N) :
    oneFlippedUpConfig V x_0 hN ≠ allAlignedConfigS V N 0 := by
  intro heq
  have h0 : oneFlippedUpConfig V x_0 hN x_0 = (0 : Fin (N + 1)) := by
    rw [heq]; rfl
  rw [oneFlippedUpConfig_apply_self] at h0
  have hv := congrArg Fin.val h0
  simp at hv

/-- **Explicit value of `Ŝ_{tot}^- · |σ_⊤⟩` at a one-flipped
configuration**: for any pivot site `x_0 : V` and any `0 < N`,

  `((Ŝ_{tot}^-).mulVec |σ_⊤⟩) (oneFlippedUpConfig V x_0)
    = √N`.

Proof: expand `Ŝ_{tot}^- = ∑_x onSiteS x Ŝ^-` via `Matrix.sum_mulVec`,
then identify only the `x = x_0` term as non-zero. The non-zero
contribution is `spinSOpMinus N 1 0 = √(N · 1) = √N`. -/
theorem totalSpinSOpMinus_mulVec_allAlignedStateS_zero_at_oneFlippedUpConfig
    (hN : 0 < N) (x_0 : V) :
    ((totalSpinSOpMinus V N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))))
      (oneFlippedUpConfig V x_0 hN) =
        ((Real.sqrt (N : ℝ) : ℝ) : ℂ) := by
  unfold totalSpinSOpMinus
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  -- Goal: ∑ x, ((onSiteS x (spinSOpMinus N)).mulVec |σ_⊤⟩)
  --                  (oneFlippedUpConfig ..) = √N.
  -- We show only x = x_0 contributes √N; all other x give 0.
  rw [Finset.sum_eq_single x_0]
  · -- x = x_0 case.
    -- ((onSiteS x_0 (spinSOpMinus N)).mulVec |σ_⊤⟩) σ' = ∑_τ M σ' τ * basisVecS σ_⊤ τ
    --   = M σ' σ_⊤  (only τ = σ_⊤ contributes since basisVecS σ_⊤ τ = δ).
    rw [show ((onSiteS x_0 (spinSOpMinus N)).mulVec
            (allAlignedStateS V N (0 : Fin (N + 1))))
          (oneFlippedUpConfig V x_0 hN) =
        onSiteS x_0 (spinSOpMinus N)
            (oneFlippedUpConfig V x_0 hN) (allAlignedConfigS V N 0)
        from ?_]
    -- Now reduce onSiteS to the off-site agreement check.
    · have h_off : ∀ k, k ≠ x_0 →
          oneFlippedUpConfig V x_0 hN k = allAlignedConfigS V N 0 k := by
        intros k hk
        rw [oneFlippedUpConfig_apply_off V x_0 hN hk]
        rfl
      rw [onSiteS_apply_of_off_site_agree x_0 (spinSOpMinus N) h_off]
      rw [oneFlippedUpConfig_apply_self V x_0 hN]
      change spinSOpMinus N ⟨1, by omega⟩ (0 : Fin (N + 1)) =
        ((Real.sqrt (N : ℝ) : ℝ) : ℂ)
      have h_lower : ((0 : Fin (N + 1)).val + 1 = (⟨1, by omega⟩ : Fin (N + 1)).val) := by
        simp
      rw [spinSOpMinus_apply_lower N h_lower]
      simp
    · -- ((onSiteS x_0 (spinSOpMinus N)).mulVec |σ_⊤⟩) σ' = onSiteS σ' σ_⊤.
      unfold allAlignedStateS
      change ∑ τ, (onSiteS x_0 (spinSOpMinus N))
              (oneFlippedUpConfig V x_0 hN) τ *
            basisVecS (allAlignedConfigS V N 0) τ = _
      rw [Finset.sum_eq_single (allAlignedConfigS V N 0)]
      · simp
      · intros τ _ hτne
        rw [basisVecS_of_ne hτne, mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
  · -- x ≠ x_0 case. The off-site agreement fails because
    -- oneFlippedUpConfig differs from σ_⊤ at x_0, which is ≠ x.
    intros x _ hx_ne
    -- Reduce to the matrix entry at the (oneFlipped, σ_⊤) pair.
    rw [show ((onSiteS x (spinSOpMinus N)).mulVec
            (allAlignedStateS V N (0 : Fin (N + 1))))
          (oneFlippedUpConfig V x_0 hN) =
        onSiteS x (spinSOpMinus N)
            (oneFlippedUpConfig V x_0 hN) (allAlignedConfigS V N 0)
        from ?_]
    · -- Off-site agreement fails: at site x_0 ≠ x,
      -- oneFlippedUpConfig x_0 = ⟨1, _⟩ ≠ 0 = σ_⊤ x_0.
      apply onSiteS_apply_eq_zero_of_off_site_diff
      intro hagree
      have := hagree x_0 (Ne.symm hx_ne)
      rw [oneFlippedUpConfig_apply_self V x_0 hN] at this
      have hval := congrArg Fin.val this
      simp [allAlignedConfigS] at hval
    · unfold allAlignedStateS
      change ∑ τ, (onSiteS x (spinSOpMinus N))
              (oneFlippedUpConfig V x_0 hN) τ *
            basisVecS (allAlignedConfigS V N 0) τ = _
      rw [Finset.sum_eq_single (allAlignedConfigS V N 0)]
      · simp
      · intros τ _ hτne
        rw [basisVecS_of_ne hτne, mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- **Non-vanishing of the once-lowered all-up state**: for `0 < N`
and `[Nonempty V]`, the vector `Ŝ_{tot}^- · |σ_⊤⟩` is non-zero.

Witness: at the one-flipped configuration `oneFlippedUpConfig V x_0`
the value is `√N > 0` (PR contains the explicit identity). -/
theorem totalSpinSOpMinus_mulVec_allAlignedStateS_zero_ne_zero
    [Nonempty V] (hN : 0 < N) :
    (totalSpinSOpMinus V N).mulVec
        (allAlignedStateS V N (0 : Fin (N + 1))) ≠ 0 := by
  intro hzero
  obtain ⟨x_0⟩ := ‹Nonempty V›
  have hwitness :=
    totalSpinSOpMinus_mulVec_allAlignedStateS_zero_at_oneFlippedUpConfig
      (V := V) hN x_0
  have hzero_at : ((totalSpinSOpMinus V N).mulVec
      (allAlignedStateS V N (0 : Fin (N + 1))))
        (oneFlippedUpConfig V x_0 hN) = 0 := by
    rw [hzero]; rfl
  rw [hzero_at] at hwitness
  have hpos : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast hN
  have hne : ((Real.sqrt (N : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    linarith
  exact hne hwitness.symm

/-! ## Raising once: explicit value at the one-flipped configuration -/

/-- The configuration that flips one site `x_0 : V` from `N` to
`N - 1 ∈ Fin (N + 1)` and leaves the rest at `N` (i.e., one site
is raised by `Ŝ^+`). Requires `0 < N`. -/
def oneFlippedDownConfig (V : Type*) (x_0 : V) {N : ℕ} (hN : 0 < N)
    [DecidableEq V] : V → Fin (N + 1) :=
  fun i => if i = x_0 then ⟨N - 1, by omega⟩ else (Fin.last N)

/-- Off the flipped site, `oneFlippedDownConfig` agrees with the
all-down configuration. -/
theorem oneFlippedDownConfig_apply_off (V : Type*) [DecidableEq V]
    (x_0 : V) (hN : 0 < N) {i : V} (hi : i ≠ x_0) :
    oneFlippedDownConfig V x_0 hN i = (Fin.last N : Fin (N + 1)) := by
  unfold oneFlippedDownConfig
  rw [if_neg hi]

/-- At the flipped site, `oneFlippedDownConfig` takes value `N - 1`. -/
theorem oneFlippedDownConfig_apply_self (V : Type*) [DecidableEq V]
    (x_0 : V) (hN : 0 < N) :
    oneFlippedDownConfig V x_0 hN x_0 = ⟨N - 1, by omega⟩ := by
  unfold oneFlippedDownConfig
  rw [if_pos rfl]

/-- The one-flipped (down) configuration disagrees with the all-down
configuration at the flipped site. -/
theorem oneFlippedDownConfig_ne_allAlignedConfigS_last (V : Type*)
    [DecidableEq V] (x_0 : V) (hN : 0 < N) :
    oneFlippedDownConfig V x_0 hN ≠ allAlignedConfigS V N (Fin.last N) := by
  intro heq
  have h0 : oneFlippedDownConfig V x_0 hN x_0 = (Fin.last N : Fin (N + 1)) := by
    rw [heq]; rfl
  rw [oneFlippedDownConfig_apply_self] at h0
  have hval := congrArg Fin.val h0
  simp [Fin.last] at hval
  omega

/-- **Explicit value of `Ŝ_{tot}^+ · |σ_⊥⟩` at a one-raised
configuration**: for any pivot site `x_0 : V` and any `0 < N`,

  `((Ŝ_{tot}^+).mulVec |σ_⊥⟩) (oneFlippedDownConfig V x_0)
    = √N`.

Proof: parallel of the lowering case via `spinSOpPlus_apply_raise`,
where the raise from `N` to `N − 1` carries weight
`√(N · 1) = √N`. -/
theorem totalSpinSOpPlus_mulVec_allAlignedStateS_last_at_oneFlippedDownConfig
    (hN : 0 < N) (x_0 : V) :
    ((totalSpinSOpPlus V N).mulVec
        (allAlignedStateS V N (Fin.last N)))
      (oneFlippedDownConfig V x_0 hN) =
        ((Real.sqrt (N : ℝ) : ℝ) : ℂ) := by
  unfold totalSpinSOpPlus
  rw [Matrix.sum_mulVec, Finset.sum_apply]
  rw [Finset.sum_eq_single x_0]
  · rw [show ((onSiteS x_0 (spinSOpPlus N)).mulVec
            (allAlignedStateS V N (Fin.last N)))
          (oneFlippedDownConfig V x_0 hN) =
        onSiteS x_0 (spinSOpPlus N)
            (oneFlippedDownConfig V x_0 hN)
            (allAlignedConfigS V N (Fin.last N))
        from ?_]
    · have h_off : ∀ k, k ≠ x_0 →
          oneFlippedDownConfig V x_0 hN k =
            allAlignedConfigS V N (Fin.last N) k := by
        intros k hk
        rw [oneFlippedDownConfig_apply_off V x_0 hN hk]
        rfl
      rw [onSiteS_apply_of_off_site_agree x_0 (spinSOpPlus N) h_off]
      rw [oneFlippedDownConfig_apply_self V x_0 hN]
      change spinSOpPlus N ⟨N - 1, by omega⟩
          (Fin.last N : Fin (N + 1)) = ((Real.sqrt (N : ℝ) : ℝ) : ℂ)
      have h_raise : ((⟨N - 1, by omega⟩ : Fin (N + 1)).val + 1 =
          (Fin.last N : Fin (N + 1)).val) := by
        simp [Fin.last]
        omega
      rw [spinSOpPlus_apply_raise N h_raise]
      -- (Fin.last N).val = N, so √(N · (N - N + 1)) = √(N · 1) = √N.
      simp [Fin.last]
    · unfold allAlignedStateS
      change ∑ τ, (onSiteS x_0 (spinSOpPlus N))
              (oneFlippedDownConfig V x_0 hN) τ *
            basisVecS (allAlignedConfigS V N (Fin.last N)) τ = _
      rw [Finset.sum_eq_single (allAlignedConfigS V N (Fin.last N))]
      · simp
      · intros τ _ hτne
        rw [basisVecS_of_ne hτne, mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
  · intros x _ hx_ne
    rw [show ((onSiteS x (spinSOpPlus N)).mulVec
            (allAlignedStateS V N (Fin.last N)))
          (oneFlippedDownConfig V x_0 hN) =
        onSiteS x (spinSOpPlus N)
            (oneFlippedDownConfig V x_0 hN)
            (allAlignedConfigS V N (Fin.last N))
        from ?_]
    · apply onSiteS_apply_eq_zero_of_off_site_diff
      intro hagree
      have := hagree x_0 (Ne.symm hx_ne)
      rw [oneFlippedDownConfig_apply_self V x_0 hN] at this
      have hval := congrArg Fin.val this
      simp [Fin.last, allAlignedConfigS] at hval
      omega
    · unfold allAlignedStateS
      change ∑ τ, (onSiteS x (spinSOpPlus N))
              (oneFlippedDownConfig V x_0 hN) τ *
            basisVecS (allAlignedConfigS V N (Fin.last N)) τ = _
      rw [Finset.sum_eq_single (allAlignedConfigS V N (Fin.last N))]
      · simp
      · intros τ _ hτne
        rw [basisVecS_of_ne hτne, mul_zero]
      · intro h
        exact (h (Finset.mem_univ _)).elim
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- **Non-vanishing of the once-raised all-down state**: for `0 < N`
and `[Nonempty V]`, the vector `Ŝ_{tot}^+ · |σ_⊥⟩` is non-zero. -/
theorem totalSpinSOpPlus_mulVec_allAlignedStateS_last_ne_zero
    [Nonempty V] (hN : 0 < N) :
    (totalSpinSOpPlus V N).mulVec
        (allAlignedStateS V N (Fin.last N)) ≠ 0 := by
  intro hzero
  obtain ⟨x_0⟩ := ‹Nonempty V›
  have hwitness :=
    totalSpinSOpPlus_mulVec_allAlignedStateS_last_at_oneFlippedDownConfig
      (V := V) hN x_0
  have hzero_at : ((totalSpinSOpPlus V N).mulVec
      (allAlignedStateS V N (Fin.last N)))
        (oneFlippedDownConfig V x_0 hN) = 0 := by
    rw [hzero]; rfl
  rw [hzero_at] at hwitness
  have hpos : (0 : ℝ) < Real.sqrt (N : ℝ) := by
    apply Real.sqrt_pos.mpr
    exact_mod_cast hN
  have hne : ((Real.sqrt (N : ℝ) : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, Complex.ofReal_eq_zero]
    linarith
  exact hne hwitness.symm

end LatticeSystem.Quantum
