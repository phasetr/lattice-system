import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Reflection-positivity averaging inequality (Tasaki Lemma 4.5)

This is the abstract combinatorial lemma at the heart of the reflection-positivity proof of the
existence of long-range order (Tasaki §4.1.2, Lemma 4.5, used in the proof of Theorem 4.1).  It is a
purely finite-dimensional statement about a real-valued function `F` of a cyclic string of `2n`
arguments (in Tasaki, `2n` vectors in `ℝ^D`, but the vector structure is never used — the arguments
range over an arbitrary type `V`).

If `F` is invariant under the cyclic shift (cyclicity, eq. (4.1.55)) and satisfies the *reflection
bound* (eq. (4.1.56))
`F(f) ≥ ½ (F(reflect_left f) + F(reflect_right f))`,
where `reflect_left f` mirrors the second half onto the first and `reflect_right f` mirrors the
first
half onto the second, then `F` is bounded below by the average of its values on the `2n` constant
strings (eq. (4.1.57)):
`F(f) ≥ (1 / 2n) Σ_j F(j ↦ f j)`.

Tasaki's proof is the elegant "`G_min = 0`" argument: subtract the constant-string average, restrict
to the finite set of strings built from the entries of `f`, and show the minimum is `0` by
collapsing
a minimizer to a constant string via repeated use of the reflection bound and cyclicity.  The proof
is elementary but intricate (a doubling induction on the number of leading equal entries); it is now
**fully proved** below (sorry-free), discharging the former documented axiom.

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1.2, Lemma 4.5, eqs. (4.1.55)–(4.1.57), pp. 87–88.
-/

namespace LatticeSystem.Math

/-- The **cyclic shift** of a length-`2n` string, `reindexCyclic f = f ∘ finRotate (2n)`
(eq. (4.1.55) acts by this shift).  `finRotate (2n)` is the one-step rotation of `Fin (2n)`. -/
def reindexCyclic {V : Type*} (n : ℕ) (f : Fin (2 * n) → V) : Fin (2 * n) → V :=
  fun i => f (finRotate (2 * n) i)

/-- The **left reflection** `reflectLeft f = (f_1, …, f_n, f_n, …, f_1)`: keep the first half, and
mirror it onto the second half (eq. (4.1.56), first reflected string).  In `0`-indexed form, entry
`i ≥ n` takes the value `f (2n−1−i) = f i.rev`. -/
def reflectLeft {V : Type*} (n : ℕ) (f : Fin (2 * n) → V) : Fin (2 * n) → V :=
  fun i => if i.val < n then f i else f i.rev

/-- The **right reflection** `reflectRight f = (f_{2n}, …, f_{n+1}, f_{n+1}, …, f_{2n})`: keep the
second half, and mirror it onto the first half (eq. (4.1.56), second reflected string).  In
`0`-indexed form, entry `i < n` takes the value `f (2n−1−i) = f i.rev`. -/
def reflectRight {V : Type*} (n : ℕ) (f : Fin (2 * n) → V) : Fin (2 * n) → V :=
  fun i => if i.val < n then f i.rev else f i

section Proof

variable {V : Type*}

/-- On a nonempty `Fin N`, the one-step rotation `finRotate N` is the successor map `i ↦ i + 1`.
This rephrases `finRotate_succ_apply` after exhibiting `N` as a successor.  Public so the
bond-square reindexing lemmas (Tasaki §4.1 Theorem 4.2, PR-BS9) can bridge `finRotate (2n)` to the
cyclic successor `ringBondSucc n`. -/
lemma finRotate_eq_add_one {N : ℕ} [NeZero N] (i : Fin N) :
    finRotate N i = i + 1 := by
  obtain ⟨p, rfl⟩ : ∃ p, N = p + 1 := ⟨N - 1, Nat.succ_pred_eq_of_pos (NeZero.pos N) |>.symm⟩
  exact finRotate_succ_apply i

/-- The cyclic shift acts as the successor map: `reindexCyclic n g i = g (i + 1)`.  This unfolds the
`finRotate (2n)` one-step rotation, which on `Fin (m+1)` is `+ 1` (`finRotate_succ_apply`). -/
private lemma reindexCyclic_apply (n : ℕ) [NeZero (2 * n)] (g : Fin (2 * n) → V)
    (i : Fin (2 * n)) :
    reindexCyclic n g i = g (i + 1) := by
  simp only [reindexCyclic]
  congr 1
  exact finRotate_eq_add_one i

/-- The constant-string average sum `AvgSum h = ∑_j F (fun _ => h j)`; the quantity that, divided by
`2n`, is subtracted from `F` in Tasaki's auxiliary function `G`. -/
private def avgSum (n : ℕ) (F : (Fin (2 * n) → V) → ℝ) (h : Fin (2 * n) → V) : ℝ :=
  ∑ j : Fin (2 * n), F (fun _ => h j)

/-- Reflection reindexing for the left reflection: summing any real-valued `φ` over the entries of
`reflectLeft n g` doubles the sum over the first-half entries, since the second half mirrors the
first via the involution `Fin.rev`. -/
private lemma sum_phi_reflectLeft (n : ℕ) (φ : V → ℝ) (g : Fin (2 * n) → V) :
    (∑ j : Fin (2 * n), φ ((reflectLeft n g) j))
      = 2 * ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), φ (g j) := by
  have hsplit :
      (∑ j : Fin (2 * n), φ ((reflectLeft n g) j))
        = (∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), φ ((reflectLeft n g) j))
          + ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n),
              φ ((reflectLeft n g) j) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (2 * n) => i.val < n) (fun j => φ ((reflectLeft n g) j))).symm
  rw [hsplit]
  have hleft :
      (∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), φ ((reflectLeft n g) j))
        = ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), φ (g j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have : j.val < n := (Finset.mem_filter.mp hj).2
    simp only [reflectLeft, if_pos this]
  have hright :
      (∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n), φ ((reflectLeft n g) j))
        = ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), φ (g j) := by
    refine Finset.sum_nbij' (fun j => j.rev) (fun j => j.rev) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha' : ¬ a.val < n := (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hrv : a.rev.val = 2 * n - (a.val + 1) := by simp [Fin.val_rev]
      have hab : a.val < 2 * n := a.isLt
      omega
    · intro a ha
      have ha' : a.val < n := (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hrv : a.rev.val = 2 * n - (a.val + 1) := by simp [Fin.val_rev]
      have hab : a.val < 2 * n := a.isLt
      omega
    · intro a _; exact Fin.rev_rev a
    · intro a _; exact Fin.rev_rev a
    · intro a ha
      have ha' : ¬ a.val < n := (Finset.mem_filter.mp ha).2
      have : ¬ a.val < n := ha'
      simp only [reflectLeft, if_neg this]
  rw [hleft, hright]
  ring

/-- Reflection reindexing for the right reflection: summing any real-valued `φ` over the entries of
`reflectRight n g` doubles the sum over the second-half entries (those with index `≥ n`), since the
first half mirrors the second via `Fin.rev`. -/
private lemma sum_phi_reflectRight (n : ℕ) (φ : V → ℝ) (g : Fin (2 * n) → V) :
    (∑ j : Fin (2 * n), φ ((reflectRight n g) j))
      = 2 * ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n), φ (g j) := by
  have hsplit :
      (∑ j : Fin (2 * n), φ ((reflectRight n g) j))
        = (∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), φ ((reflectRight n g) j))
          + ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n),
              φ ((reflectRight n g) j) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (2 * n) => i.val < n) (fun j => φ ((reflectRight n g) j))).symm
  rw [hsplit]
  have hright :
      (∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n), φ ((reflectRight n g) j))
        = ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n), φ (g j) := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    have : ¬ j.val < n := (Finset.mem_filter.mp hj).2
    simp only [reflectRight, if_neg this]
  have hleft :
      (∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), φ ((reflectRight n g) j))
        = ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n), φ (g j) := by
    refine Finset.sum_nbij' (fun j => j.rev) (fun j => j.rev) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha' : a.val < n := (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hrv : a.rev.val = 2 * n - (a.val + 1) := by simp [Fin.val_rev]
      have hab : a.val < 2 * n := a.isLt
      omega
    · intro a ha
      have ha' : ¬ a.val < n := (Finset.mem_filter.mp ha).2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hrv : a.rev.val = 2 * n - (a.val + 1) := by simp [Fin.val_rev]
      have hab : a.val < 2 * n := a.isLt
      omega
    · intro a _; exact Fin.rev_rev a
    · intro a _; exact Fin.rev_rev a
    · intro a ha
      have ha' : a.val < n := (Finset.mem_filter.mp ha).2
      have : a.val < n := ha'
      simp only [reflectRight, if_pos this]
  rw [hleft, hright]
  ring

/-- The reflection identity for the average term: the average sum is *exactly* additive under the
two reflections, `avgSum (reflectLeft g) + avgSum (reflectRight g) = 2 · avgSum g`.  This is the
linear counterpart of the reflection bound and lets `G = F − avgSum/2n` inherit the bound. -/
private lemma avgSum_reflect_add (n : ℕ) (F : (Fin (2 * n) → V) → ℝ)
    (g : Fin (2 * n) → V) :
    avgSum n F (reflectLeft n g) + avgSum n F (reflectRight n g) = 2 * avgSum n F g := by
  simp only [avgSum]
  rw [sum_phi_reflectLeft n (fun v => F (fun _ => v)) g,
    sum_phi_reflectRight n (fun v => F (fun _ => v)) g]
  have htot :
      (∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => i.val < n), F (fun _ => g j))
        + ∑ j ∈ Finset.univ.filter (fun i : Fin (2 * n) => ¬ i.val < n), F (fun _ => g j)
        = ∑ j : Fin (2 * n), F (fun _ => g j) :=
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin (2 * n) => i.val < n) (fun j => F (fun _ => g j))
  rw [← htot]; ring

end Proof

/-- **Tasaki Lemma 4.5 (reflection-positivity averaging inequality).**  Let `n ≥ 1` and let
`F : (Fin (2n) → V) → ℝ` be a real-valued function of a cyclic string of `2n` arguments in an
arbitrary type `V`.  Assume `F` is invariant under the cyclic shift (`hcyc`, eq. (4.1.55)) and
satisfies the reflection bound (`hrefl`, eq. (4.1.56)):
`F f ≥ ½ (F (reflectLeft n f) + F (reflectRight n f))` for all `f`.  Then `F` is bounded below by
the
average of its values on the `2n` constant strings (eq. (4.1.57)):
`F f ≥ (1 / 2n) Σ_j F (fun _ => f j)`.

The vector structure of the arguments plays no role, so `V` is arbitrary.  The proof is Tasaki's
elementary `G_min = 0` collapse argument: subtract the constant-string average to form the auxiliary
function `G`, restrict to the finite set of strings built from entries of `f`, take a minimizer, and
collapse it to a constant string (where `G = 0`) by a doubling induction on the number of leading
equal entries, using cyclicity and the reflection bound. -/
theorem reflectionPositivity_averaging {V : Type*} (n : ℕ) (hn : 1 ≤ n)
    (F : (Fin (2 * n) → V) → ℝ)
    (hcyc : ∀ f, F (reindexCyclic n f) = F f)
    (hrefl : ∀ f, (F (reflectLeft n f) + F (reflectRight n f)) / 2 ≤ F f) :
    ∀ f : Fin (2 * n) → V,
      (∑ j : Fin (2 * n), F (fun _ => f j)) / (2 * n : ℝ) ≤ F f := by
  classical
  intro f
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have htwon_pos : (0 : ℝ) < (2 * n : ℝ) := by
    have : (0 : ℕ) < 2 * n := by omega
    exact_mod_cast this
  -- Auxiliary function `G g = F g - avgSum g / (2n)`.
  set G : (Fin (2 * n) → V) → ℝ := fun g => F g - (avgSum n F g) / (2 * n : ℝ) with hG
  -- The goal is `0 ≤ G f`.
  suffices hGf : 0 ≤ G f by
    have : G f = F f - (∑ j : Fin (2 * n), F (fun _ => f j)) / (2 * n : ℝ) := by
      simp [hG, avgSum]
    rw [this] at hGf
    linarith
  -- Fact A: G vanishes on constant strings.
  have factA : ∀ v : V, G (fun _ => v) = 0 := by
    intro v
    have hconst : avgSum n F (fun _ => v) = (2 * n : ℝ) * F (fun _ => v) := by
      simp only [avgSum]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    simp only [hG]
    rw [hconst]
    field_simp
    ring
  -- Fact B: G is cyclic-invariant.
  have factB : ∀ g, G (reindexCyclic n g) = G g := by
    intro g
    have havg : avgSum n F (reindexCyclic n g) = avgSum n F g := by
      simp only [avgSum, reindexCyclic]
      exact Equiv.sum_comp (finRotate (2 * n)) (fun j => F (fun _ => g j))
    change F (reindexCyclic n g) - avgSum n F (reindexCyclic n g) / (2 * n : ℝ)
      = F g - avgSum n F g / (2 * n : ℝ)
    rw [hcyc g, havg]
  -- Fact C: G satisfies the reflection bound.
  have factC : ∀ g, (G (reflectLeft n g) + G (reflectRight n g)) / 2 ≤ G g := by
    intro g
    have hF := hrefl g
    have havg := avgSum_reflect_add n F g
    change (((F (reflectLeft n g) - avgSum n F (reflectLeft n g) / (2 * n : ℝ))
        + (F (reflectRight n g) - avgSum n F (reflectRight n g) / (2 * n : ℝ))) / 2)
      ≤ F g - avgSum n F g / (2 * n : ℝ)
    have hdiv : avgSum n F (reflectLeft n g) / (2 * n : ℝ)
        + avgSum n F (reflectRight n g) / (2 * n : ℝ)
        = 2 * (avgSum n F g / (2 * n : ℝ)) := by
      rw [← add_div, havg]; ring
    nlinarith [hF, hdiv]
  -- The finite carrier T = { f ∘ σ : σ : Fin(2n) → Fin(2n) }.
  set T : Finset (Fin (2 * n) → V) :=
    Finset.univ.image (fun σ : Fin (2 * n) → Fin (2 * n) => f ∘ σ) with hT
  -- Membership helper: any g with g i = f (σ i) lies in T.
  have memT : ∀ (g : Fin (2 * n) → V) (σ : Fin (2 * n) → Fin (2 * n)),
      (∀ i, g i = f (σ i)) → g ∈ T := by
    intro g σ hgσ
    rw [hT, Finset.mem_image]
    exact ⟨σ, Finset.mem_univ _, by funext i; simp only [Function.comp_apply]; exact (hgσ i).symm⟩
  -- f ∈ T.
  have hfT : f ∈ T := memT f id (fun _ => rfl)
  -- T closed under reindexCyclic.
  have hTcyc : ∀ g ∈ T, reindexCyclic n g ∈ T := by
    intro g hg
    rw [hT, Finset.mem_image] at hg
    obtain ⟨σ, _, rfl⟩ := hg
    refine memT _ (fun i => σ (finRotate (2 * n) i)) ?_
    intro i
    simp only [reindexCyclic, Function.comp_apply]
  -- T closed under reflectLeft.
  have hTrefL : ∀ g ∈ T, reflectLeft n g ∈ T := by
    intro g hg
    rw [hT, Finset.mem_image] at hg
    obtain ⟨σ, _, rfl⟩ := hg
    refine memT _ (fun i => if i.val < n then σ i else σ i.rev) ?_
    intro i
    simp only [reflectLeft, Function.comp_apply]
    split_ifs <;> rfl
  -- T closed under reflectRight.
  have hTrefR : ∀ g ∈ T, reflectRight n g ∈ T := by
    intro g hg
    rw [hT, Finset.mem_image] at hg
    obtain ⟨σ, _, rfl⟩ := hg
    refine memT _ (fun i => if i.val < n then σ i.rev else σ i) ?_
    intro i
    simp only [reflectRight, Function.comp_apply]
    split_ifs <;> rfl
  -- Minimizer.
  obtain ⟨m, hmT, hmin⟩ := T.exists_min_image G ⟨f, hfT⟩
  set Gmin : ℝ := G m with hGmin
  set a : V := m 0 with ha
  -- Rotation iterate.
  set rot : ℕ → (Fin (2 * n) → V) → (Fin (2 * n) → V) :=
    fun s g => (reindexCyclic n)^[s] g with hrot
  -- Iterated rotation on the index: `rotIdx s i = (finRotate (2n))^[s] i`.
  set rotIdx : ℕ → Fin (2 * n) → Fin (2 * n) :=
    fun s i => (finRotate (2 * n))^[s] i with hrotIdx
  -- rot s g i = g (rotIdx s i).
  have hrotk : ∀ (s : ℕ) (g : Fin (2 * n) → V) (i : Fin (2 * n)),
      rot s g i = g (rotIdx s i) := by
    intro s
    induction s with
    | zero => intro g i; simp [hrot, hrotIdx]
    | succ s ih =>
        intro g i
        have hstep : rot (s + 1) g = reindexCyclic n (rot s g) := by
          simp only [hrot, Function.iterate_succ']
          rfl
        have hidx : rotIdx (s + 1) i = rotIdx s (finRotate (2 * n) i) := by
          simp only [hrotIdx, Function.iterate_succ_apply]
        rw [hstep]
        simp only [reindexCyclic]
        rw [ih, hidx]
  -- The value of the iterated rotation index is `(i.val + s) % (2n)`.
  have hrotIdx_val : ∀ (s : ℕ) (i : Fin (2 * n)),
      (rotIdx s i).val = (i.val + s) % (2 * n) := by
    intro s
    induction s with
    | zero => intro i; simp [hrotIdx, Nat.mod_eq_of_lt i.isLt]
    | succ s ih =>
        intro i
        have hstep : rotIdx (s + 1) i = rotIdx s (finRotate (2 * n) i) := by
          simp only [hrotIdx, Function.iterate_succ_apply]
        rw [hstep, ih, finRotate_eq_add_one, Fin.val_add, Fin.val_one']
        have hone : (1 : ℕ) % (2 * n) = 1 := Nat.mod_eq_of_lt (by omega)
        rw [hone, Nat.mod_add_mod]
        congr 1
        omega
  -- rot preserves G.
  have hrotG : ∀ (s : ℕ) (g : Fin (2 * n) → V), G (rot s g) = G g := by
    intro s
    induction s with
    | zero => intro g; simp [hrot]
    | succ s ih =>
        intro g
        have hstep : rot (s + 1) g = reindexCyclic n (rot s g) := by
          simp only [hrot, Function.iterate_succ']
          rfl
        rw [hstep, factB, ih]
  -- rot preserves membership in T.
  have hrotT : ∀ (s : ℕ) (g : Fin (2 * n) → V), g ∈ T → rot s g ∈ T := by
    intro s
    induction s with
    | zero => intro g hg; simpa [hrot] using hg
    | succ s ih =>
        intro g hg
        have hstep : rot (s + 1) g = reindexCyclic n (rot s g) := by
          simp only [hrot, Function.iterate_succ']
          rfl
        rw [hstep]
        exact hTcyc _ (ih g hg)
  -- The collapse: strong induction on the measure `2n - k`.
  have key : ∀ d k, 2 * n - k = d → 1 ≤ k →
      (∃ g, g ∈ T ∧ G g = Gmin ∧ (∀ i : Fin (2 * n), i.val < k → g i = a)) → Gmin = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro k hdk hk hex
      obtain ⟨g, hgT, hgmin, hglead⟩ := hex
      -- Both reflections of g are also minimizers.
      have hLT : reflectLeft n g ∈ T := hTrefL g hgT
      have hRT : reflectRight n g ∈ T := hTrefR g hgT
      have hCbound := factC g
      have hLge : Gmin ≤ G (reflectLeft n g) := hmin _ hLT
      have hRge : Gmin ≤ G (reflectRight n g) := hmin _ hRT
      rw [hgmin] at hCbound
      have hLeq : G (reflectLeft n g) = Gmin := by linarith
      by_cases hcase : n ≤ k
      · -- reflectLeft n g is the constant string `fun _ => a`.
        have hconst : reflectLeft n g = (fun _ => a) := by
          funext i
          simp only [reflectLeft]
          split_ifs with hi
          · exact hglead i (by omega)
          · -- i.val ≥ n, so i.rev.val < n ≤ k
            apply hglead
            have : i.rev.val = 2 * n - (i.val + 1) := by simp [Fin.val_rev]
            omega
        have : Gmin = G (fun _ => a) := by rw [← hLeq, hconst]
        rw [this]; exact factA a
      · -- k < n: build h = rot (2n - k) (reflectLeft n g), with 2k leading a's.
        push Not at hcase
        set h := rot (2 * n - k) (reflectLeft n g) with hh
        have hhT : h ∈ T := hrotT _ _ hLT
        have hhG : G h = Gmin := by rw [hh, hrotG, hLeq]
        have hhlead : ∀ i : Fin (2 * n), i.val < 2 * k → h i = a := by
          intro i hi
          rw [hh, hrotk]
          -- index value
          have hidx : (rotIdx (2 * n - k) i).val = (i.val + (2 * n - k)) % (2 * n) :=
            hrotIdx_val (2 * n - k) i
          by_cases hik : i.val < k
          · -- p = i.val + 2n - k, with n ≤ p < 2n, so reflectLeft uses g (·.rev)
            have hp_lt : i.val + (2 * n - k) < 2 * n := by omega
            have hmod : (i.val + (2 * n - k)) % (2 * n) = i.val + (2 * n - k) :=
              Nat.mod_eq_of_lt hp_lt
            have hge : ¬ (rotIdx (2 * n - k) i).val < n := by
              rw [hidx, hmod]; omega
            simp only [reflectLeft, if_neg hge]
            apply hglead
            have hrv : (rotIdx (2 * n - k) i).rev.val
                = 2 * n - ((rotIdx (2 * n - k) i).val + 1) := by
              simp [Fin.val_rev]
            rw [hrv, hidx, hmod]
            omega
          · -- k ≤ i.val < 2k: p = i.val + 2n - k ≥ 2n, p mod 2n = i.val - k < k ≤ n
            push Not at hik
            have hmod : (i.val + (2 * n - k)) % (2 * n) = i.val - k := by
              have heq : i.val + (2 * n - k) = (i.val - k) + 2 * n := by omega
              rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
            have hlt : (rotIdx (2 * n - k) i).val < n := by
              rw [hidx, hmod]; omega
            simp only [reflectLeft, if_pos hlt]
            apply hglead
            rw [hidx, hmod]; omega
        -- Apply IH at k' = 2k, measure 2n - 2k < 2n - k = d.
        have hmeasure : 2 * n - 2 * k < d := by omega
        exact ih (2 * n - 2 * k) hmeasure (2 * k) rfl (by omega) ⟨h, hhT, hhG, hhlead⟩
  -- Base case k = 1.
  have hGmin_zero : Gmin = 0 := by
    refine key (2 * n - 1) 1 rfl (by omega) ⟨m, hmT, rfl, ?_⟩
    intro i hi
    have hi0 : i.val = 0 := by omega
    have : i = 0 := Fin.ext hi0
    rw [this]
  -- Conclude.
  have : Gmin ≤ G f := hmin f hfT
  rw [hGmin_zero] at this
  exact this

end LatticeSystem.Math
