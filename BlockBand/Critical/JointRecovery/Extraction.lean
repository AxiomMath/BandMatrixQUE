module

public import BlockBand.Critical.JointRecovery.EnergyAxis
public import BlockBand.Internal.Contracts.CriticalEntire
public import BlockBand.Critical.FiniteZeros

/-!
# Continuity of the root/derivative extraction

For an entire function `F` of `m + 1` variables, the extraction sums a test `f` over the real zeros
`x` of the energy axis, evaluated at `rootDerivativePoint E t F x`. Real-rootedness passes to
limits with `F(0) ≠ 0` (`realRooted_of_tendsto`, Hurwitz), and at a real-rooted `F` with
`F(0) ≠ 0` and simple real zeros the extraction is continuous within real-rooted functions
(`continuousWithinAt_extractionSum`).
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace BlockBand.Critical.JointRecovery

open Filter Topology Set Metric
open BlockBand.Critical.Entire BlockBand.Critical.Entire.EntireFunction
open BlockBand.Internal.Contracts.CriticalEntire

variable {m : ℕ}

/-- Every zero of the energy axis is real. -/
def RealRooted (F : EntireFunction (m + 1)) : Prop :=
  ∀ w : ℂ, axis F w = 0 → w.im = 0

/-- Every real zero of the energy axis is simple. -/
def SimpleRealZeros (F : EntireFunction (m + 1)) : Prop :=
  ∀ x : ℝ, axis F x = 0 → deriv (axis F) x ≠ 0

/-- Exponent of `extractorLaplace`: `Σ_{real zeros x} f(rootDerivativePoint E t F x)`. -/
def extractionSum (E t : ℝ) (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    (F : EntireFunction (m + 1)) : ℝ :=
  ∑' x : EnergyZero F, f (rootDerivativePoint E t F x)

/-- Integrand of `extractorLaplace`. -/
def extractionValue (E t : ℝ) (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    (F : EntireFunction (m + 1)) : ℝ :=
  Real.exp (-extractionSum E t f F)

theorem extractorLaplace_eq_integral (E τ : ℝ) (μ : RandomEntire (m + 1))
    (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ) :
    extractorLaplace E τ μ f = ∫ F, extractionValue E τ f F ∂(μ : MeasureTheory.Measure _) :=
  rfl

/-- A compactly supported continuous test vanishes for large first coordinate. -/
theorem exists_abs_fst_bound {V : Type*} [TopologicalSpace V]
    (f : CompactlySupportedContinuousMap (ℝ × V) ℝ) :
    ∃ A, 0 ≤ A ∧ ∀ p, f p ≠ 0 → |p.1| ≤ A := by
  obtain ⟨A, hA⟩ := (f.hasCompactSupport.image (continuous_abs.comp continuous_fst)).bddAbove
  refine ⟨max A 0, le_max_right _ _, fun p hp => ?_⟩
  exact (hA ⟨p, subset_tsupport _ hp, rfl⟩).trans (le_max_left _ _)

/-- A limit of real-rooted axes along a nontrivial filter, with `F(0) ≠ 0`, is real-rooted
(Hurwitz). -/
theorem realRooted_of_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {G : ι → EntireFunction (m + 1)} {F : EntireFunction (m + 1)} (hG : Tendsto G l (𝓝 F))
    (hreal : ∀ᶠ i in l, RealRooted (G i)) (hF0 : F 0 ≠ 0) : RealRooted F := by
  intro w hw
  by_contra him
  have hF0' : axis F 0 ≠ 0 := by rwa [axis_zero]
  have hiso := eventually_ne_zero_punctured (differentiable_axis F) hF0' w
  have hr : 0 < |w.im| / 2 := half_pos (abs_pos.mpr him)
  obtain ⟨i, hi, hreal_i⟩ := ((eventually_exists_zero_mem_ball (tendstoLocallyUniformly_axis hG)
    (fun i => differentiable_axis (G i)) (differentiable_axis F).continuous hw hiso hr).and
    hreal).exists
  obtain ⟨w', hw', hz⟩ := hi
  have him' := hreal_i w' hz
  have h1 : |w.im - w'.im| ≤ dist w w' := by
    rw [Complex.dist_eq, ← Complex.sub_im]; exact Complex.abs_im_le_norm _
  rw [him', sub_zero, dist_comm] at h1
  have := mem_ball.mp hw'
  linarith

/-- Positive minimum of finitely many positive radii and half-distances. -/
theorem exists_small_radius (Z : Finset ℂ) (rad : ℂ → ℝ) (hrad : ∀ x ∈ Z, 0 < rad x) :
    ∃ r > 0, ∀ x ∈ Z, r ≤ rad x ∧ ∀ y ∈ Z, x ≠ y → 2 * r ≤ dist x y := by
  classical
  let T : Finset ℝ := insert 1 (Z.image rad ∪
    ((Z ×ˢ Z).filter (fun q => q.1 ≠ q.2)).image (fun q => dist q.1 q.2 / 2))
  have hT : T.Nonempty := Finset.insert_nonempty _ _
  have hpos : ∀ s ∈ T, 0 < s := by
    intro s hs
    simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_product] at hs
    rcases hs with rfl | ⟨x, hx, rfl⟩ | ⟨q, ⟨⟨_, _⟩, hq⟩, rfl⟩
    · exact one_pos
    · exact hrad x hx
    · exact half_pos (dist_pos.mpr hq)
  refine ⟨T.min' hT, hpos _ (Finset.min'_mem T hT), fun x hx => ⟨?_, fun y hy hxy => ?_⟩⟩
  · exact Finset.min'_le T _ (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_image_of_mem rad hx)))
  · have : T.min' hT ≤ dist x y / 2 := Finset.min'_le T _ (by
      simp only [T, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product]
      exact Or.inr (Or.inr ⟨(x, y), ⟨⟨hx, hy⟩, hxy⟩, rfl⟩))
    linarith

/-- The zero of `axis G` in `ball x r` (an arbitrary one if several; `x` if none). -/
def zeroNear (G : EntireFunction (m + 1)) (x : ℂ) (r : ℝ) : ℂ := by
  classical
  exact if h : ∃ w ∈ ball x r, axis G w = 0 then h.choose else x

theorem zeroNear_spec {G : EntireFunction (m + 1)} {x : ℂ} {r : ℝ}
    (h : ∃ w ∈ ball x r, axis G w = 0) :
    zeroNear G x r ∈ ball x r ∧ axis G (zeroNear G x r) = 0 := by
  classical
  unfold zeroNear
  split
  · rename_i h'; exact h'.choose_spec
  · contradiction

/-- Reduction of the zero sum to a finite sum along an injective parametrization covering
the support. -/
theorem extractionSum_eq_sum (E t : ℝ) (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    (G : EntireFunction (m + 1)) (Z : Finset ℂ) (e : Z → EnergyZero G)
    (he : Function.Injective e)
    (hsupp : ∀ y : EnergyZero G, f (rootDerivativePoint E t G y) ≠ 0 → y ∈ range e) :
    extractionSum E t f G = ∑ x : Z, f (rootDerivativePoint E t G (e x)) := by
  unfold extractionSum
  rw [← he.tsum_eq (f := fun y : EnergyZero G => f (rootDerivativePoint E t G y))
    (fun y hy => hsupp y hy), tsum_fintype]

/-- Continuity of `rootDerivativePoint` at a simple zero. -/
theorem tendsto_rootDerivativePoint {ι : Type*} {l : Filter ι} (E : ℝ) {t : ℝ}
    {ts : ι → ℝ} {G : ι → EntireFunction (m + 1)} {F : EntireFunction (m + 1)}
    {ys : ι → ℝ} {x : ℝ} (ht : Tendsto ts l (𝓝 t)) (hG : Tendsto G l (𝓝 F))
    (hy : Tendsto ys l (𝓝 x)) (hd : deriv (axis F) x ≠ 0) :
    Tendsto (fun i => rootDerivativePoint E (ts i) (G i) (ys i)) l
      (𝓝 (rootDerivativePoint E t F x)) := by
  unfold rootDerivativePoint
  refine Tendsto.prodMk_nhds (((ht.mul_const _).neg).mul hy) (tendsto_pi_nhds.mpr fun a => ?_)
  have hz : Tendsto (fun i => (BlockBand.Critical.energySource ((ys i : ℝ) : ℂ) :
      Fin (m + 1) → ℂ)) l (𝓝 (BlockBand.Critical.energySource (x : ℂ))) :=
    ((continuous_energySource.comp Complex.continuous_ofReal).tendsto x).comp hy
  rw [deriv_axis] at hd
  exact (tendsto_partialDerivValue hG hz a).div (tendsto_partialDerivValue hG hz 0) hd

/-- **Continuity of the extraction.** Domain: `ρ(E) > 0`,
`t > 0`, `F(0) ≠ 0`, all real axis zeros of `F` simple. Then `(s, G) ↦ extractionSum E s f G`
is continuous within `univ ×ˢ {G | RealRooted G}` at `(t, F)`. -/
theorem continuousWithinAt_extractionSum {E t : ℝ} (hρ : 0 < Parameters.semicircleDensity E)
    (ht : 0 < t) (f : CompactlySupportedContinuousMap (ℝ × (Fin (m + 1) → ℂ)) ℝ)
    {F : EntireFunction (m + 1)} (hF0 : F 0 ≠ 0) (hsimple : SimpleRealZeros F) :
    ContinuousWithinAt (fun p : ℝ × EntireFunction (m + 1) => extractionSum E p.1 f p.2)
      (univ ×ˢ {G | RealRooted G}) (t, F) := by
  classical
  set ρ := Parameters.semicircleDensity E with hρ_def
  set l := 𝓝[univ ×ˢ {G : EntireFunction (m + 1) | RealRooted G}] (t, F) with hl_def
  change Tendsto _ l _
  rcases l.eq_or_neBot with hbot | hne
  · rw [hbot]; exact tendsto_bot
  have hT : Tendsto (fun p : ℝ × EntireFunction (m + 1) => p.1) l (𝓝 t) :=
    (continuous_fst.tendsto (t, F)).mono_left nhdsWithin_le_nhds
  have hG : Tendsto (fun p : ℝ × EntireFunction (m + 1) => p.2) l (𝓝 F) :=
    (continuous_snd.tendsto (t, F)).mono_left nhdsWithin_le_nhds
  have hRR : ∀ᶠ p in l, RealRooted p.2 :=
    (eventually_mem_nhdsWithin (a := (t, F))).mono fun p hp => hp.2
  have hreal : RealRooted F := realRooted_of_tendsto hG hRR hF0
  set g := axis F with hg_def
  have hg0 : g 0 ≠ 0 := by rwa [hg_def, axis_zero]
  have hgd : Differentiable ℂ g := differentiable_axis F
  have hconv : TendstoLocallyUniformly (fun p : ℝ × EntireFunction (m + 1) => axis p.2) g l :=
    tendstoLocallyUniformly_axis hG
  have hfd : ∀ p : ℝ × EntireFunction (m + 1), Differentiable ℂ (axis p.2) :=
    fun p => differentiable_axis p.2
  obtain ⟨A, hA0, hA⟩ := exists_abs_fst_bound f
  set R := 2 * A / (t * ρ) + 1 with hR_def
  have htρ : 0 < t * ρ := mul_pos ht hρ
  have hfin := BlockBand.Critical.finite_zeros_inter_compact hgd ⟨0, hg0⟩
    (isCompact_closedBall (0 : ℂ) R)
  set Z := hfin.toFinset with hZ_def
  have hZmem : ∀ x, x ∈ Z ↔ x ∈ closedBall (0 : ℂ) R ∧ g x = 0 := fun x => by
    rw [hZ_def, Set.Finite.mem_toFinset]; rfl
  have hZreal : ∀ x ∈ Z, (x.re : ℂ) = x := fun x hx =>
    Complex.ext rfl (by simp [hreal x ((hZmem x).mp hx).2])
  have hZd : ∀ x ∈ Z, deriv g x ≠ 0 := by
    intro x hx
    have h := hsimple x.re (by rw [hZreal x hx]; exact ((hZmem x).mp hx).2)
    rwa [hZreal x hx] at h
  -- local injectivity radii
  have hH3 : ∀ x ∈ Z, ∃ r > 0, ∀ᶠ p in l,
      (∀ a ∈ ball x r, ∀ b ∈ ball x r, axis p.2 a = axis p.2 b → a = b) ∧
        ∀ a ∈ ball x r, deriv (axis p.2) a ≠ 0 := fun x hx =>
    exists_eventually_injOn_of_deriv_ne_zero hconv hfd hgd (hZd x hx)
  choose! rad hradpos hradev using hH3
  obtain ⟨r, hr, hrZ⟩ := exists_small_radius Z rad hradpos
  have hiso : ∀ x : ℂ, ∀ᶠ w in 𝓝[≠] x, g w ≠ 0 := fun x =>
    eventually_ne_zero_punctured hgd hg0 x
  -- eventual facts
  have hinj : ∀ᶠ p in l, ∀ x ∈ Z,
      ∀ a ∈ ball x r, ∀ b ∈ ball x r, axis p.2 a = axis p.2 b → a = b :=
    (eventually_all_finset Z).mpr fun x hx => (hradev x hx).mono fun p hp a ha b hb hab =>
      hp.1 a (ball_subset_ball (hrZ x hx).1 ha) b (ball_subset_ball (hrZ x hx).1 hb) hab
  have hexists : ∀ᶠ p in l, ∀ x ∈ Z, ∃ w ∈ ball x r, axis p.2 w = 0 :=
    (eventually_all_finset Z).mpr fun x hx =>
      eventually_exists_zero_mem_ball hconv hfd hgd.continuous ((hZmem x).mp hx).2 (hiso x) hr
  set K := closedBall (0 : ℂ) R \ ⋃ x ∈ Z, ball x r with hK_def
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 R).diff (isOpen_biUnion fun x _ => isOpen_ball)
  have hgK : ∀ w ∈ K, g w ≠ 0 := by
    intro w hw hgw
    apply hw.2
    exact mem_biUnion ((hZmem w).mpr ⟨hw.1, hgw⟩) (mem_ball_self hr)
  have hKev := eventually_ne_zero_of_isCompact hconv hgd.continuous hKc hgK
  have htpos : ∀ᶠ p in l, t / 2 < p.1 := hT.eventually (lt_mem_nhds (half_lt_self ht))
  -- the parametrization of zeros near `F`
  have hbound : ∀ s : ℝ, t / 2 < s → ∀ G : EntireFunction (m + 1), ∀ y : EnergyZero G,
      f (rootDerivativePoint E s G y) ≠ 0 → ((y : ℝ) : ℂ) ∈ closedBall (0 : ℂ) R := by
    intro s hs G y hy
    have h1 := hA _ hy
    simp only [rootDerivativePoint] at h1
    have hsρ : 0 < s * ρ := mul_pos (by linarith) hρ
    rw [abs_mul, abs_neg, abs_of_pos hsρ] at h1
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    have h2 : |(y : ℝ)| ≤ A / (s * ρ) := by rw [le_div_iff₀ hsρ]; linarith
    have h3 : A / (s * ρ) ≤ 2 * A / (t * ρ) := by
      rw [div_le_div_iff₀ hsρ htρ]
      have h4 : t * ρ ≤ 2 * (s * ρ) := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h4 hA0]
    linarith
  -- value at `F`
  have hvalF : extractionSum E t f F =
      ∑ x : Z, f (rootDerivativePoint E t F (x : ℂ).re) := by
    have hz : ∀ x : Z, F (BlockBand.Critical.energySource (((x : ℂ).re : ℝ) : ℂ)) = 0 :=
      fun x => by
        rw [hZreal x x.2]; exact ((hZmem x).mp x.2).2
    have := extractionSum_eq_sum E t f F Z (fun x => ⟨(x : ℂ).re, hz x⟩) (by
        intro x y hxy
        apply Subtype.ext
        have h := congrArg (fun q : EnergyZero F => ((q : ℝ) : ℂ)) hxy
        simp only at h
        rwa [hZreal x x.2, hZreal y y.2] at h) (by
        intro y hy
        have hyR := hbound t (half_lt_self ht) F y hy
        have hyZ : ((y : ℝ) : ℂ) ∈ Z := (hZmem _).mpr ⟨hyR, y.2⟩
        exact ⟨⟨_, hyZ⟩, Subtype.ext (by simp)⟩)
    exact this
  -- eventual value
  have hval : ∀ᶠ p in l, extractionSum E p.1 f p.2 =
      ∑ x : Z, f (rootDerivativePoint E p.1 p.2 (zeroNear p.2 (x : ℂ) r).re) := by
    filter_upwards [hinj, hexists, hKev, htpos, hRR] with p hpinj hpex hpK hpt hpR
    have hzr : ∀ x : Z, ((zeroNear p.2 (x : ℂ) r).re : ℂ) = zeroNear p.2 (x : ℂ) r :=
      fun x => Complex.ext rfl (by simp [hpR _ (zeroNear_spec (hpex x x.2)).2])
    have hz : ∀ x : Z,
        p.2 (BlockBand.Critical.energySource (((zeroNear p.2 (x : ℂ) r).re : ℝ) : ℂ)) = 0 :=
      fun x => by rw [hzr x]; exact (zeroNear_spec (hpex x x.2)).2
    refine extractionSum_eq_sum E p.1 f p.2 Z (fun x => ⟨_, hz x⟩) ?_ ?_
    · intro x y hxy
      have h := congrArg (fun q : EnergyZero p.2 => ((q : ℝ) : ℂ)) hxy
      simp only at h
      rw [hzr x, hzr y] at h
      by_contra hne
      have hne' : (x : ℂ) ≠ (y : ℂ) := fun h' => hne (Subtype.ext h')
      have h2 := (hrZ x x.2).2 y y.2 hne'
      have hx := mem_ball.mp (zeroNear_spec (hpex x x.2)).1
      have hy := mem_ball.mp (zeroNear_spec (hpex y y.2)).1
      rw [h] at hx
      have := dist_triangle_left (x : ℂ) (y : ℂ) (zeroNear p.2 (y : ℂ) r)
      linarith
    · intro y hy
      have hyR := hbound p.1 hpt p.2 y hy
      have hyU : ((y : ℝ) : ℂ) ∈ ⋃ x ∈ Z, ball x r := by
        by_contra hnot
        exact hpK _ ⟨hyR, hnot⟩ y.2
      obtain ⟨x, hxZ, hyx⟩ := mem_iUnion₂.mp hyU
      refine ⟨⟨x, hxZ⟩, Subtype.ext ?_⟩
      have heq := hpinj x hxZ _ (zeroNear_spec (hpex x hxZ)).1 _ hyx
        (by rw [(zeroNear_spec (hpex x hxZ)).2]; exact y.2.symm)
      have := congrArg Complex.re heq
      simpa using this
  -- convergence of the matched zeros
  have hconvZ : ∀ x : Z, Tendsto (fun p : ℝ × EntireFunction (m + 1) =>
      (zeroNear p.2 (x : ℂ) r).re) l (𝓝 (x : ℂ).re) := by
    intro x
    have hc : Tendsto (fun p : ℝ × EntireFunction (m + 1) => zeroNear p.2 (x : ℂ) r) l
        (𝓝 (x : ℂ)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hε' : 0 < min ε r := lt_min hε hr
      filter_upwards [eventually_exists_zero_mem_ball hconv hfd hgd.continuous
        ((hZmem x).mp x.2).2 (hiso x) hε', hinj, hexists] with p hp hpinj hpex
      obtain ⟨w, hw, hwz⟩ := hp
      have hwr : w ∈ ball (x : ℂ) r := ball_subset_ball (min_le_right _ _) hw
      have heq := hpinj x x.2 _ (zeroNear_spec (hpex x x.2)).1 _ hwr
        (by rw [(zeroNear_spec (hpex x x.2)).2, hwz])
      rw [heq]
      exact (mem_ball.mp hw).trans_le (min_le_left _ _)
    exact (Complex.continuous_re.tendsto _).comp hc
  show Tendsto _ l (𝓝 (extractionSum E t f F))
  rw [hvalF]
  refine Tendsto.congr' (hval.mono fun p hp => hp.symm) ?_
  refine tendsto_finsetSum _ fun x _ => ?_
  refine (f.continuous.tendsto _).comp ?_
  refine tendsto_rootDerivativePoint E hT hG (hconvZ x) ?_
  rw [hZreal x x.2]
  exact hZd x x.2

end BlockBand.Critical.JointRecovery
