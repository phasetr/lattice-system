/-
Gaussian-domination capstone: the chessboard bound `Z_β(h)^{2n} ≤ Π_j Z_β(staggered_{g_j})`
(Tasaki §4.1 Theorem 4.2, reflection-positivity layer: symmetrisation stage PR7d-iii).

This is the symmetrisation capstone that turns PR7c's one reflection step
`ringFieldPartitionRe_reflection_step : Z_β(h)² ≤ Z_β(h_L)·Z_β(h_R)` (the finite-β matrix form of
Tasaki's reflection bound (4.1.51)) into the `2n`-fold chessboard bound
`Z_β(h)^{2n} ≤ Π_{j} Z_β(staggered_{g_j})`, from which PR7e collapses each staggered constant field
to `Z_β(0)` and concludes the uniform-field bound `Z_β(h) ≤ Z_β(0)` (Tasaki (4.1.49)/(4.1.52)).

The proof **reuses the classical cyclic averaging inequality**
`LatticeSystem.Math.reflectionPositivity_averaging` (Tasaki Lemma 4.5, (4.1.55)–(4.1.57),
pp. 87–88; FILS, Comm. Math. Phys. 62 (1978) 1–34) applied to `F g = −log Z_β(P g)` with `P` the
staggered relabel (PR7d-ii).  The doubling induction that assembles the `2n`-fold bound lives inside
the classical lemma; PR7d only supplies its two hypotheses from the quantum side:

* `hcyc` (cyclicity (4.1.55)) from the translation invariance `ringFieldPartitionRe_translate` and
  the spin-flip invariance `ringFieldPartitionRe_neg` of `Z_β` (PR7d-i): the period-2 staggered
  relabel turns a single one-step shift into a global sign, so a shift of `P (reindexCyclic f)`
  factors as `spin-flip ∘ translation` of `P f` (`ringStaggeredRelabel_reindexCyclic`).
* `hrefl` (reflection bound (4.1.56)) from the PR7c one reflection step, the strict positivity
  `ringFieldPartitionRe_pos` (the `−log` domain, PR7d-i), and the staggered relabel bridge
  `ringStaggeredRelabel_reflectLeft`/`_reflectRight` (PR7d-ii) carrying the classical mirror
  reflections onto the quantum signed field copies; `log`-monotonicity converts `Z_β(h)² ≤ Z_β(h_L)
  ·Z_β(h_R)` to `2 log Z_β(h) ≤ log Z_β(h_L) + log Z_β(h_R)`.

Exponentiating the resulting `(1/2n) Σ_j (−log Z_β(staggered_{g_j})) ≤ −log Z_β(h)` gives the
multiplicative capstone (the `−log`/`exp` rearrangement is inline; no separate multiplicative
averaging lemma is introduced).

Reference: Hal Tasaki, *Physics and Mathematics of Quantum Many-Body Systems* (1st ed., Springer,
2020), §4.1, reflection bound (4.1.51) and uniform-field bound (4.1.49)/(4.1.52), pp. 85–86;
chessboard estimate Lemma 4.5, (4.1.55)–(4.1.57), pp. 87–88; translation-invariance wiring
(4.1.58)–(4.1.61), pp. 88–89; FILS, Comm. Math. Phys. 62 (1978) 1–34.
-/
import LatticeSystem.Quantum.SpinS.RingReflectionFieldPartitionSymmetry
import LatticeSystem.Quantum.SpinS.RingReflectionStaggeredRelabel
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LatticeSystem.Quantum

open LatticeSystem.Math

variable {n N : ℕ}

/-- **Value of the one-step ring rotation.**  On a nonempty `Fin M` the rotation `finRotate M z`
has value `(z + 1) mod M`; this rephrases `finRotate_succ_apply` (`finRotate (m+1) z = z + 1`) with
`Fin.val_add`/`Fin.val_one'`.  Used to compute the staggered sign carried by the cyclic shift. -/
private lemma finRotate_val {M : ℕ} [NeZero M] (z : Fin M) :
    ((finRotate M z : Fin M) : ℕ) = ((z : ℕ) + 1) % M := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  rw [finRotate_succ_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]

/-- **The staggered sign flips under the one-step ring rotation.**  On the even ring `Fin (2n)`,
`(−1)^{(finRotate z).val} = −(−1)^{z.val}`, because `(finRotate z).val ≡ z.val + 1 (mod 2)`
(`2 ∣ 2n`, so the wrap-around at the last site preserves parity).  This is the global sign that the
period-2 staggered relabel `P` produces from a single cyclic shift (Tasaki §4.1, cyclicity source
(4.1.60), p. 88). -/
private lemma neg_one_pow_finRotate (n : ℕ) [NeZero (2 * n)] (z : Fin (2 * n)) :
    (-1 : ℝ) ^ ((finRotate (2 * n) z : Fin (2 * n)) : ℕ) = -(-1 : ℝ) ^ (z : ℕ) := by
  have hdvd : (2 : ℕ) ∣ 2 * n := ⟨n, rfl⟩
  rw [finRotate_val z, neg_one_pow_eq_pow_mod_two, Nat.mod_mod_of_dvd _ hdvd,
    ← neg_one_pow_eq_pow_mod_two, pow_succ]
  ring

/-- **The staggered relabel turns the cyclic shift into a signed shift.**
`P (reindexCyclic f) = fun z => −(P f)(finRotate z)` (Tasaki §4.1, cyclicity source (4.1.60),
p. 88).  Since `P h z = (−1)^z h z` has period 2, the one-step shift `reindexCyclic f = f ∘
finRotate` acquires the global sign of `neg_one_pow_finRotate`.  Feeding this through the spin-flip
and translation invariances of `Z_β` yields the cyclicity hypothesis of the chessboard estimate. -/
private lemma ringStaggeredRelabel_reindexCyclic (n : ℕ) [NeZero (2 * n)]
    (f : Fin (2 * n) → ℝ) :
    ringStaggeredRelabel n (reindexCyclic n f)
      = fun z => - ringStaggeredRelabel n f (finRotate (2 * n) z) := by
  funext z
  simp only [ringStaggeredRelabel, reindexCyclic]
  rw [neg_one_pow_finRotate n z]
  ring

/-- **Gaussian-domination capstone.**  For the physical field partition function
`Z_β(h) = ringFieldPartitionRe n N β h` on the even ring `Fin (2n)` (`n ≥ 1`, `β ≥ 0`),
`Z_β(h)^{2n} ≤ Π_{j} Z_β(staggered_{g_j})`, where `g = P h` is the staggered relabel of `h` and
`staggered_c z = (−1)^z c` is the staggered constant field (`ringStaggeredConstField`).  This is the
finite-β chessboard bound obtained from Tasaki's reflection bound (4.1.51) by the cyclic averaging
inequality (Lemma 4.5, (4.1.55)–(4.1.57), pp. 87–88): applying
`LatticeSystem.Math.reflectionPositivity_averaging` to `F g = −log Z_β(P g)` — with cyclicity from
the translation and spin-flip invariances of `Z_β` (PR7d-i), and the reflection bound from PR7c's
one reflection step, the strict positivity of `Z_β`, and the staggered relabel bridge (PR7d-ii) —
gives `(1/2n) Σ_j (−log Z_β(staggered_{g_j})) ≤ −log Z_β(h)`, which exponentiates to the product
bound.  PR7e collapses each `Z_β(staggered_c)` to `Z_β(0)` to reach the uniform-field bound
`Z_β(h) ≤ Z_β(0)` (Tasaki (4.1.49)/(4.1.52), pp. 85–86; FILS, Comm. Math. Phys. 62 (1978) 1–34). -/
theorem ringFieldPartition_gaussianDomination (G : AxisTwoPiRotS N) (n : ℕ) (hn : 1 ≤ n) {β : ℝ}
    (hβ : 0 ≤ β) (h : Fin (2 * n) → ℝ) :
    ringFieldPartitionRe n N β h ^ (2 * n)
      ≤ ∏ j : Fin (2 * n),
          ringFieldPartitionRe n N β (ringStaggeredConstField n (ringStaggeredRelabel n h j)) := by
  haveI : NeZero n := ⟨by omega⟩
  haveI : NeZero (2 * n) := ⟨by omega⟩
  set F : (Fin (2 * n) → ℝ) → ℝ :=
    fun g => - Real.log (ringFieldPartitionRe n N β (ringStaggeredRelabel n g)) with hFdef
  -- Cyclicity (4.1.55): translation + spin-flip invariance of `Z_β`.
  have hcyc : ∀ f, F (reindexCyclic n f) = F f := by
    intro f
    simp only [hFdef]
    refine congrArg (fun t => - Real.log t) ?_
    rw [ringStaggeredRelabel_reindexCyclic n f]
    calc ringFieldPartitionRe n N β
            (fun z => - ringStaggeredRelabel n f (finRotate (2 * n) z))
        = ringFieldPartitionRe n N β
            (fun z => ringStaggeredRelabel n f (finRotate (2 * n) z)) :=
          ringFieldPartitionRe_neg G n β
            (fun z => ringStaggeredRelabel n f (finRotate (2 * n) z))
      _ = ringFieldPartitionRe n N β (ringStaggeredRelabel n f) :=
          (ringFieldPartitionRe_translate n N β (ringStaggeredRelabel n f)).symm
  -- Reflection bound (4.1.56): PR7c reflection step + strict positivity + staggered bridge.
  have hrefl : ∀ f, (F (reflectLeft n f) + F (reflectRight n f)) / 2 ≤ F f := by
    intro f
    simp only [hFdef, ringStaggeredRelabel_reflectLeft n f, ringStaggeredRelabel_reflectRight n f]
    set g := ringStaggeredRelabel n f with hg
    have hpg := ringFieldPartitionRe_pos n N β g
    have hpL := ringFieldPartitionRe_pos n N β (ringFieldReflectLeft n g)
    have hpR := ringFieldPartitionRe_pos n N β (ringFieldReflectRight n g)
    have hstep := ringFieldPartitionRe_reflection_step G n hβ g
    have hlog := (Real.log_le_log_iff (pow_pos hpg 2) (mul_pos hpL hpR)).mpr hstep
    rw [Real.log_pow, Real.log_mul (ne_of_gt hpL) (ne_of_gt hpR)] at hlog
    push_cast at hlog
    linarith
  -- Apply the classical averaging inequality at `f = P h` and rewrite `F` via the bridge lemmas.
  have key := reflectionPositivity_averaging n hn F hcyc hrefl (ringStaggeredRelabel n h)
  simp only [hFdef, ringStaggeredRelabel_involutive n h, ringStaggeredRelabel_const n] at key
  -- Strict positivity of the base and the staggered-constant partition functions.
  have ha : 0 < ringFieldPartitionRe n N β h := ringFieldPartitionRe_pos n N β h
  have hw : ∀ j : Fin (2 * n), 0 < ringFieldPartitionRe n N β
      (ringStaggeredConstField n (ringStaggeredRelabel n h j)) :=
    fun j => ringFieldPartitionRe_pos n N β _
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  -- Turn the averaged `−log` inequality into `2n · log Z_β(h) ≤ Σ_j log Z_β(staggered_{g_j})`.
  rw [div_le_iff₀ h2n, Finset.sum_neg_distrib] at key
  have hlogpow : Real.log (ringFieldPartitionRe n N β h ^ (2 * n))
      = 2 * (n : ℝ) * Real.log (ringFieldPartitionRe n N β h) := by
    rw [Real.log_pow]; push_cast; ring
  have hlogprod : Real.log (∏ j : Fin (2 * n),
        ringFieldPartitionRe n N β (ringStaggeredConstField n (ringStaggeredRelabel n h j)))
      = ∑ j : Fin (2 * n),
          Real.log (ringFieldPartitionRe n N β
            (ringStaggeredConstField n (ringStaggeredRelabel n h j))) :=
    Real.log_prod (fun j _ => (hw j).ne')
  have hle : Real.log (ringFieldPartitionRe n N β h ^ (2 * n))
      ≤ Real.log (∏ j : Fin (2 * n),
          ringFieldPartitionRe n N β (ringStaggeredConstField n (ringStaggeredRelabel n h j))) := by
    rw [hlogpow, hlogprod]
    nlinarith [key]
  have hXpos : 0 < ringFieldPartitionRe n N β h ^ (2 * n) := pow_pos ha _
  have hYpos : 0 < ∏ j : Fin (2 * n),
      ringFieldPartitionRe n N β (ringStaggeredConstField n (ringStaggeredRelabel n h j)) :=
    Finset.prod_pos (fun j _ => hw j)
  exact (Real.log_le_log_iff hXpos hYpos).mp hle

end LatticeSystem.Quantum
