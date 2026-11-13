module

public import Mathlib
public import BlockBand.Wegner.SingularLogMomentsLaw
public import BlockBand.Wegner.SingularLogMomentsAnalytic

/-!
# Moments of the singular log statistic

Proves `Internal.Contracts.Inputs.SingularLogMoments`: the statistic `½ Σ_λ log(1 + a²/(λ-e)²)`
of a block model has `L^r` norm bounded uniformly in the dimension when `aN ≤ K`.

Law and domain: any `BlockModel k W` with `W > 0` and `IsIndependent c` (`c > 0`): independent
`GUE_W(c/W)` blocks, `(D, Y)` independent of the blocks, `D` Hermitian with no norm bound;
`H = D + ⊕_j A_j`, dimension `d = kW ≤ N`. Statistic: `½ Σ_λ log(1 + a²/(λ-e)²)` over the
characteristic roots of `H` (Lean convention: the summand at `λ = e` is `0`).

Proof (with a crude replacement for Stirling's formula). With `u = N(λ - e)`, every
summand is bounded by `Σ_m (K² + 3(m+1)) 1{|u| ≤ 2^{-m}} + Σ_m K² 4^{-m} 1{|u| ≤ 2^{m+1}}`
(`SingularLogAnalytic.log_term_le`). The count of `H` on `|u| ≤ ρ` has factorial moments
`≤ (Lρ)^j` with `L = 2C/√c` (`SingularLogLaw.blockModel_countFactorial`, `kW ≤ N`), hence
`L^n` norm `≤ countBound n (Lρ)` (`n = ⌈r⌉`); countable Minkowski and the summability of
`nearTerm`, `farTerm` give the constant `C_{r,K,c} = Σ_m nearTerm + Σ_m farTerm`; noninteger
`r` uses monotonicity of `‖·‖_{L^r}` in `r` on a probability space.

The only input is `PSSS.SourceContract`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Wegner

open MeasureTheory ProbabilityTheory Set
open BlockBand.External BlockBand.External.PSSS
open BlockBand.Counting BlockBand.Foundations.Spectral
open BlockBand.Internal.Contracts.Inputs (BlockModel spectralSum singularLogStatistic)
open BlockBand.Wegner.SingularLogLaw BlockBand.Wegner.SingularLogAnalytic
open scoped ENNReal NNReal

namespace SingularLogMoments

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Spectral sums over characteristic roots are sums over the increasing eigenvalues. -/
theorem spectralSum_eq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectralSum A f = ∑ i, f (increasingEigenvalue hA i) := by
  have hr : A.charpoly.roots.map Complex.re =
      Multiset.map (fun i => increasingEigenvalue hA i) Finset.univ.val := by
    rw [hA.roots_charpoly_eq_eigenvalues₀, Multiset.map_map]
    simp only [Function.comp_def]
    change Multiset.map hA.eigenvalues₀ Finset.univ.val =
      Multiset.map (hA.eigenvalues₀ ∘ Fin.revPerm) Finset.univ.val
    rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  unfold spectralSum
  rw [show (fun z : ℂ => f z.re) = f ∘ Complex.re from rfl, ← Multiset.map_map, hr,
    Multiset.map_map, Finset.sum_eq_multiset_sum]
  rfl

/-- The count as a sum of indicators. -/
theorem eigenCount_eq_sum (A : HermitianMatrix ι) (I : Set ℝ) [DecidablePred (· ∈ I)] :
    (eigenCount A I : ℝ≥0∞) = ∑ i, if increasingEigenvalue A.2 i ∈ I then 1 else 0 := by
  classical
  simp only [eigenCount, Finset.sum_boole]
  congr

theorem logTerm_nonneg (a e l : ℝ) : 0 ≤ Real.log (1 + a ^ 2 / (l - e) ^ 2) :=
  Real.log_nonneg (by have : 0 ≤ a ^ 2 / (l - e) ^ 2 := by positivity
                      linarith)

theorem statistic_nonneg (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (a e : ℝ) :
    0 ≤ singularLogStatistic A a e := by
  unfold singularLogStatistic
  rw [spectralSum_eq A hA]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => logTerm_nonneg a e _)

theorem measurable_logTerm (a e : ℝ) :
    Measurable (fun l : ℝ => Real.log (1 + a ^ 2 / (l - e) ^ 2)) :=
  Real.measurable_log.comp (measurable_const.add
    (measurable_const.div ((measurable_id.sub_const e).pow_const 2)))

theorem measurable_statistic (a e : ℝ) :
    Measurable (fun A : HermitianMatrix ι => singularLogStatistic A.1 a e) := by
  have he : (fun A : HermitianMatrix ι => singularLogStatistic A.1 a e) = fun A =>
      (1 / 2) * ∑ i, Real.log (1 + a ^ 2 / (increasingEigenvalue A.2 i - e) ^ 2) := by
    funext A
    unfold singularLogStatistic
    rw [spectralSum_eq A.1 A.2]
  rw [he]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro i _
  exact (measurable_logTerm a e).comp
    (BlockBand.Model.Construction.measurable_increasingEigenvalue i)

/-- Deterministic dyadic bound of the singular log statistic by weighted interval counts,
for every Hermitian `A`, `N > 0`, `0 ≤ a`, `aN ≤ K`, real `e`. -/
theorem statistic_le (A : HermitianMatrix ι) (K a e : ℝ) (N : ℕ) (hN : 0 < N) (ha : 0 ≤ a)
    (haK : a * N ≤ K) :
    ENNReal.ofReal (singularLogStatistic A.1 a e) ≤
      (∑' m : ℕ, ENNReal.ofReal (nearWeight K m) *
          (eigenCount A (Icc (e - (1 / 2 : ℝ) ^ m / N) (e + (1 / 2 : ℝ) ^ m / N)) : ℝ≥0∞)) +
        ∑' m : ℕ, ENNReal.ofReal (farWeight K m) *
          (eigenCount A (Icc (e - 2 ^ (m + 1) / N) (e + 2 ^ (m + 1) / N)) : ℝ≥0∞) := by
  unfold singularLogStatistic
  rw [spectralSum_eq A.1 A.2]
  have hsum0 : 0 ≤ ∑ i, Real.log (1 + a ^ 2 / (increasingEigenvalue A.2 i - e) ^ 2) :=
    Finset.sum_nonneg fun i _ => logTerm_nonneg a e _
  calc ENNReal.ofReal ((1 / 2) * ∑ i, Real.log (1 + a ^ 2 / (increasingEigenvalue A.2 i - e) ^ 2))
      ≤ ENNReal.ofReal (∑ i, Real.log (1 + a ^ 2 / (increasingEigenvalue A.2 i - e) ^ 2)) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = ∑ i, ENNReal.ofReal (Real.log (1 + a ^ 2 / (increasingEigenvalue A.2 i - e) ^ 2)) :=
        ENNReal.ofReal_sum_of_nonneg fun i _ => logTerm_nonneg a e _
    _ ≤ ∑ i, ((∑' m : ℕ, ENNReal.ofReal (nearWeight K m) *
          (if increasingEigenvalue A.2 i ∈ Icc (e - (1 / 2 : ℝ) ^ m / N)
            (e + (1 / 2 : ℝ) ^ m / N) then 1 else 0)) +
        ∑' m : ℕ, ENNReal.ofReal (farWeight K m) *
          (if increasingEigenvalue A.2 i ∈ Icc (e - 2 ^ (m + 1) / N)
            (e + 2 ^ (m + 1) / N) then 1 else 0)) :=
        Finset.sum_le_sum fun i _ => log_term_le K a e _ N hN ha haK
    _ = _ := by
        rw [Finset.sum_add_distrib, ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable),
          ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
        congr 1
        · congr 1
          funext m
          rw [← Finset.mul_sum, eigenCount_eq_sum]
        · congr 1
          funext m
          rw [← Finset.mul_sum, eigenCount_eq_sum]

/-!
## Weighted count series on a block model
-/

/-- A Minkowski bound for a weighted series of counts. -/
theorem eLpNorm_weighted_tsum_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {cnt : ℕ → Ω → ℕ} (hcnt : ∀ m, Measurable (cnt m)) (wt b : ℕ → ℝ) (hwt : ∀ m, 0 ≤ wt m)
    (hb : ∀ m, 0 ≤ b m) (hs : Summable (fun m => wt m * b m)) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ⊤) (hbd : ∀ m, eLpNorm (fun w => (cnt m w : ℝ≥0∞)) p P ≤ ENNReal.ofReal (b m)) :
    eLpNorm (fun w => ∑' m, ENNReal.ofReal (wt m) * (cnt m w : ℝ≥0∞)) p P ≤
      ENNReal.ofReal (∑' m, wt m * b m) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hcmE : ∀ m, Measurable (fun w => (cnt m w : ℝ≥0∞)) := fun m =>
    (measurable_from_nat (f := (Nat.cast : ℕ → ℝ≥0∞))).comp (hcnt m)
  calc eLpNorm (fun w => ∑' m, ENNReal.ofReal (wt m) * (cnt m w : ℝ≥0∞)) p P
      ≤ ∑' m, eLpNorm (fun w => ENNReal.ofReal (wt m) * (cnt m w : ℝ≥0∞)) p P :=
        eLpNorm_tsum_le (fun m => (hcmE m).const_mul _) hp hpt
    _ ≤ ∑' m, ENNReal.ofReal (wt m * b m) := by
        refine ENNReal.tsum_le_tsum fun m => ?_
        calc eLpNorm (fun w => ENNReal.ofReal (wt m) * (cnt m w : ℝ≥0∞)) p P
            ≤ ENNReal.ofReal (wt m) * eLpNorm (fun w => (cnt m w : ℝ≥0∞)) p P :=
              eLpNorm_const_mul_le (hcmE m) _ hp0 hpt
          _ ≤ ENNReal.ofReal (wt m) * ENNReal.ofReal (b m) := by gcongr; exact hbd m
          _ = ENNReal.ofReal (wt m * b m) := (ENNReal.ofReal_mul (hwt m)).symm
    _ = ENNReal.ofReal (∑' m, wt m * b m) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (hwt m) (hb m)) hs).symm

variable {k W : ℕ}

/-- The count of `H` on a set. -/
def modelCount (M : BlockModel k W) (I : Set ℝ) (w : M.Ω) : ℕ :=
  eigenCount (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) I

theorem measurable_modelCount (M : BlockModel k W) (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (modelCount M I) :=
  (measurable_nativeEigenCount I hI).comp (Measurable.subtype_mk (measurable_H M))

/-- The `L^n` bound of the count of `H` on `[e - ρ/N, e + ρ/N]` from the factorial bound. -/
theorem modelCount_eLpNorm_le (M : BlockModel k W) (N n : ℕ) (hn : 1 ≤ n) (hN : 0 < N)
    (hkW : k * W ≤ N) {C0 c : ℝ} (hc : 0 < c) (hC0 : 0 ≤ C0) (e ρ : ℝ) (hρ : 0 ≤ ρ)
    (hfac : ∀ j : ℕ, 1 ≤ j →
      Integrable (factorialCount (modelCount M (Icc (e - ρ / N) (e + ρ / N))) j) M.P ∧
      (∫ w, factorialCount (modelCount M (Icc (e - ρ / N) (e + ρ / N))) j w ∂M.P) ≤
        (C0 / Real.sqrt c * ((k * W : ℕ) : ℝ) * (e + ρ / N - (e - ρ / N))) ^ j) :
    eLpNorm (fun w => (modelCount M (Icc (e - ρ / N) (e + ρ / N)) w : ℝ≥0∞)) (n : ℝ≥0∞) M.P ≤
      ENNReal.ofReal (countBound n (2 * (C0 / Real.sqrt c) * ρ)) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hsc : 0 ≤ C0 / Real.sqrt c := div_nonneg hC0 (Real.sqrt_nonneg c)
  refine eLpNorm_count_le (measurable_modelCount M _ measurableSet_Icc) n hn (by positivity)
    (fun j hj => (hfac j hj).1) (fun j hj => (hfac j hj).2.trans ?_)
  have hkW' : ((k * W : ℕ) : ℝ) ≤ N := by exact_mod_cast hkW
  have hlen : e + ρ / N - (e - ρ / N) = 2 * ρ / N := by ring
  rw [hlen]
  apply pow_le_pow_left₀ (by positivity)
  calc C0 / Real.sqrt c * ((k * W : ℕ) : ℝ) * (2 * ρ / N)
      = (C0 / Real.sqrt c) * (2 * ρ) * (((k * W : ℕ) : ℝ) / N) := by ring
    _ ≤ (C0 / Real.sqrt c) * (2 * ρ) * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one hN').mpr hkW') (by positivity)
    _ = 2 * (C0 / Real.sqrt c) * ρ := by ring

/-- The statistic of a block model vanishes when there are no blocks. -/
theorem statistic_zero_blocks (M : BlockModel 0 W) (a e : ℝ) :
    (fun w => singularLogStatistic (M.H w) a e) = 0 := by
  funext w
  unfold singularLogStatistic
  rw [spectralSum_eq (M.H w) (H_isHermitian M w)]
  have : IsEmpty (Fin (Fintype.card (Fin 0 × Fin W))) := by
    rw [Fintype.card_prod, Fintype.card_fin, zero_mul]
    infer_instance
  simp

/-- The dominating series of counts of a block model. -/
def domSeries (M : BlockModel k W) (K e : ℝ) (N : ℕ) (w : M.Ω) : ℝ≥0∞ :=
  (∑' m : ℕ, ENNReal.ofReal (nearWeight K m) *
      (modelCount M (Icc (e - (1 / 2 : ℝ) ^ m / N) (e + (1 / 2 : ℝ) ^ m / N)) w : ℝ≥0∞)) +
    ∑' m : ℕ, ENNReal.ofReal (farWeight K m) *
      (modelCount M (Icc (e - 2 ^ (m + 1) / N) (e + 2 ^ (m + 1) / N)) w : ℝ≥0∞)

theorem modelStatistic_enorm_le (M : BlockModel k W) (K a e : ℝ) (N : ℕ) (hN : 0 < N)
    (ha : 0 ≤ a) (haK : a * N ≤ K) (w : M.Ω) :
    ‖singularLogStatistic (M.H w) a e‖ₑ ≤ ‖domSeries M K e N w‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (statistic_nonneg _ (H_isHermitian M w) a e),
    enorm_eq_self]
  exact statistic_le (⟨M.H w, H_isHermitian M w⟩ : HermitianMatrix _) K a e N hN ha haK

theorem measurable_modelStatistic (M : BlockModel k W) (a e : ℝ) :
    Measurable (fun w => singularLogStatistic (M.H w) a e) := by
  have h1 : Measurable (fun w => (⟨M.H w, H_isHermitian M w⟩ :
      HermitianMatrix (Fin k × Fin W))) := Measurable.subtype_mk (measurable_H M)
  have h2 := (measurable_statistic (ι := Fin k × Fin W) a e).comp h1
  exact h2

theorem eLpNorm_modelStatistic_le (M : BlockModel k W) (K a e : ℝ) (N : ℕ) (hN : 0 < N)
    (ha : 0 ≤ a) (haK : a * N ≤ K) (p : ℝ≥0∞) :
    eLpNorm (fun w => singularLogStatistic (M.H w) a e) p M.P ≤
      eLpNorm (domSeries M K e N) p M.P :=
  eLpNorm_mono_enorm (measurable_modelStatistic M a e).aestronglyMeasurable
    (modelStatistic_enorm_le M K a e N hN ha haK)

end SingularLogMoments

open SingularLogMoments

/-- The singular log moment bound `Internal.Contracts.Inputs.SingularLogMoments`.

Quantifiers: for every `r > 0`, every real `K` and every `c > 0` there is
`C = C_{r,K,c} = Σ_m nearTerm ⌈r⌉ K L m + Σ_m farTerm ⌈r⌉ K L m` (`L = 2 C_PSSS/√c`, where
`C_PSSS = source.C` is the constant of `PSSS.SourceContract`), chosen before `N, k, W`; then for every
`W > 0`, `kW ≤ N`, every `BlockModel k W` with `IsIndependent c` (independent `GUE_W(c/W)`
blocks, `(D, Y)` independent of them, `D` with no norm bound), every real `e` and every
`a ≥ 0` with `aN ≤ K`: `‖½ Σ_λ log(1 + a²/(λ-e)²)‖_{L^r(M.P)} ≤ C`, the sum running over the
characteristic roots of `H = D + ⊕_j A_j`. The only input is `PSSS.SourceContract` (through
`SingularLogLaw.blockModel_countFactorial`). -/
theorem singularLogMoments_holds (source : PSSS.SourceContract.{0}) :
    Internal.Contracts.Inputs.SingularLogMoments := by
  obtain ⟨C0, hC0, hcnt⟩ := blockModel_countFactorial source
  intro r hr K c hc
  obtain ⟨n, hn_def⟩ : ∃ n : ℕ, n = ⌈r⌉₊ := ⟨_, rfl⟩
  have hn : 1 ≤ n := by
    rw [hn_def]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hr).ne'
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = 2 * (C0 / Real.sqrt c) := ⟨_, rfl⟩
  have hL : 0 ≤ L := by
    rw [hL_def]
    positivity
  refine ⟨(∑' m, nearTerm n K L m) + ∑' m, farTerm n K L m, ?_⟩
  intro N k W hW hkW M h e a ha haK
  have hexp : ENNReal.ofReal r ≤ (n : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, hn_def]
    exact ENNReal.ofReal_le_ofReal (Nat.le_ceil r)
  refine (eLpNorm_le_eLpNorm_of_exponent_le hexp).trans ?_
  have hnear0 : 0 ≤ ∑' m, nearTerm n K L m := tsum_nonneg (nearTerm_nonneg n K hL)
  have hfar0 : 0 ≤ ∑' m, farTerm n K L m := tsum_nonneg (farTerm_nonneg n K hL)
  by_cases hN : N = 0
  · have hk : k = 0 := by
      subst hN
      rcases Nat.mul_eq_zero.mp (Nat.eq_zero_of_le_zero hkW) with h0 | h0
      · exact h0
      · omega
    subst hk
    rw [statistic_zero_blocks M a e]
    simp
  have hNpos : 0 < N := Nat.pos_of_ne_zero hN
  have hn1 : (1 : ℝ≥0∞) ≤ n := by exact_mod_cast hn
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hcntL : ∀ ρ : ℝ, 0 ≤ ρ →
      eLpNorm (fun w => (modelCount M (Icc (e - ρ / N) (e + ρ / N)) w : ℝ≥0∞)) (n : ℝ≥0∞)
        M.P ≤ ENNReal.ofReal (countBound n (L * ρ)) := by
    intro ρ hρ
    have hab : e - ρ / N ≤ e + ρ / N := by
      have : 0 ≤ ρ / N := div_nonneg hρ (Nat.cast_nonneg N)
      linarith
    rw [hL_def]
    exact modelCount_eLpNorm_le M N n hn hNpos hkW hc hC0.le e ρ hρ
      (fun j hj => hcnt k W hW c hc M h (e - ρ / N) (e + ρ / N) hab j hj)
  have hdom := eLpNorm_modelStatistic_le M K a e N hNpos ha haK (n : ℝ≥0∞)
  have h1 := eLpNorm_weighted_tsum_le (P := M.P)
    (cnt := fun m => modelCount M (Icc (e - (1 / 2 : ℝ) ^ m / N) (e + (1 / 2 : ℝ) ^ m / N)))
    (fun m => measurable_modelCount M _ measurableSet_Icc) (nearWeight K)
    (fun m => countBound n (L * (1 / 2 : ℝ) ^ m)) (nearWeight_nonneg K)
    (fun m => countBound_nonneg n (by positivity)) (summable_nearTerm n hn K hL) hn1 hnt
    (fun m => hcntL _ (by positivity))
  have h2 := eLpNorm_weighted_tsum_le (P := M.P)
    (cnt := fun m => modelCount M (Icc (e - 2 ^ (m + 1) / N) (e + 2 ^ (m + 1) / N)))
    (fun m => measurable_modelCount M _ measurableSet_Icc) (farWeight K)
    (fun m => countBound n (L * 2 ^ (m + 1))) (farWeight_nonneg K)
    (fun m => countBound_nonneg n (by positivity)) (summable_farTerm n hn K hL) hn1 hnt
    (fun m => hcntL _ (by positivity))
  refine hdom.trans ((eLpNorm_add_le hn1).trans ?_)
  rw [ENNReal.ofReal_add hnear0 hfar0]
  exact add_le_add h1 h2

end BlockBand.Wegner
