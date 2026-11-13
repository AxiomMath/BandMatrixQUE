module

public import BlockBand.Critical.RelativeVectors.GoodTime

/-!
# Time integration on a good sample

* `RmvGood`: the per-sample good conditions, for all times `σ ∈ [a, c]` (the first two lines of
  the interval bound, the distant-label bound, clauses 1, 3 (lower count at `a`), 4 (bulk lower
  bound) and 5 of `𝓡`, simple spectrum, Hermitian `G_a`), and the finite-speed bound (the
  conclusion of `RelativeLocalizationContract.reference_finite_speed`) for the terminal labels in
  the window.
* `integral_testedTail_le`: `∫_a^c R(s) ds ≤ k N^{-D}` (localization of the reference flow).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.CoarseRelative

variable {N r k : ℕ}

/-- The per-sample good conditions on `[a, c]`. -/
structure RmvGood (F : Matrix (Fin N) (Fin N) ℂ) (c E r₀ : ℝ) (V : Matrix (Fin N) (Fin r) ℂ)
    (a t : ℝ) (ℓ w : ℕ) (c₁ Csp b₀ Ccomp Cd Mint Cw Dsp : ℝ) (ω : FlowSample N) : Prop where
  herm : ω.1.IsHermitian
  simple : ∀ σ ∈ Icc a c, StrictMono (flowEigenvalue F a ω σ)
  low : ∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
    c₁ * N * (y - x) ≤
      ((univ.filter fun i : Fin N => flowEigenvalue F a ω a i ∈ Icc x y).card : ℝ)
  disp : ∀ σ ∈ Icc a c, ∀ x : Fin N → ℂ,
    l2Norm ((flowMatrix F a ω σ - flowMatrix F a ω a) *ᵥ x) ≤ Csp * Real.sqrt t * l2Norm x
  gap : ∀ σ ∈ Icc a c, ∀ i j : Fin N, ℓ ≤ labelDist i j →
    c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|
  beta : ∀ σ ∈ Icc a c, ∀ i : Fin N, |flowEigenvalue F a ω σ i - E| ≤ r₀ / 8 →
    b₀ * N / ℓ ≤ longCoupling F a ω ℓ σ i
  win : ∀ σ ∈ Icc a c, ∀ i : Fin N, |flowEigenvalue F a ω σ i - E| ≤ r₀ / 2 →
    ∑ b, ‖frameArray V (flowMatrix F a ω σ) i b‖ ^ 2 ≤ Ccomp
  dist : ∀ σ ∈ Icc a c, ∀ j : Fin N, |flowEigenvalue F a ω σ j - E| ≤ r₀ / 8 →
    ∀ q : Fin r → ℂ,
      ∑ i ∈ univ.filter (fun i => r₀ / 4 < |flowEigenvalue F a ω σ i - E|),
        ‖star q ⬝ᵥ frameArray V (flowMatrix F a ω σ) i‖ ^ 2 /
          ((N : ℝ) * (flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j) ^ 2) ≤
        Cd * ∑ b, ‖q b‖ ^ 2
  int : ∀ σ ∈ Icc a c, ∀ x y : ℝ, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 →
    ∀ p : Fin r → ℂ,
      |∑ i ∈ univ.filter (fun i => flowEigenvalue F a ω σ i ∈ Icc x y),
          (‖star p ⬝ᵥ frameArray V (flowMatrix F a ω σ) i‖ ^ 2 -
            quadForm (freshGamma F σ (flowEigenvalue F a ω σ i)) (V *ᵥ p))| ≤ Mint * nsq p
  speed : ∀ k : Fin N, |flowEigenvalue F a ω c k - E| ≤ Cw / N →
    ∀ P, BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c P →
      ∫⁻ s in Icc a c, ENNReal.ofReal (∑ j : Fin N,
          (if Int.natAbs ((j : ℤ) -
              ((univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w
            then 0 else 1) * P s k j) ≤
        ENNReal.ofReal ((N : ℝ) ^ (-Dsp))

section Integration

variable {F : Matrix (Fin N) (Fin N) ℂ} {a c b₀ : ℝ} {ℓ : ℕ} {ω : FlowSample N}
  {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux} [IsProbabilityMeasure Paux]
  {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}

theorem integrable_entry_sq (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ) (hb₀ : 0 ≤ b₀)
    {s : ℝ} (hs : s ∈ Icc a c) (i j : Fin N) :
    Integrable (fun ω' => ‖𝓜 s c ω' i j‖ ^ 2) Paux := by
  have hc : Continuous fun A : Matrix (Fin N) (Fin N) ℂ => ‖A i j‖ ^ 2 :=
    (continuous_id.matrix_elem i j).norm.pow 2
  refine Integrable.of_bound (μ := Paux)
    (hc.measurable.comp (hR.measurable s c).1).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω' => ?_)
  have h := entry_le_of_row (rows_reference hR hb₀ hs.1 hs.2 le_rfl ω') i j
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h0 := norm_nonneg (𝓜 s c ω' i j)
  nlinarith

/-- The tested row tail in terms of the mean squares `P(s)_{kj} = E_aux|(𝓜_{s,c})_{kj}|²`. -/
theorem testedTail_eq (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ) (hb₀ : 0 ≤ b₀)
    {s : ℝ} (hs : s ∈ Icc a c) (ι : Fin k → Fin N) (J : Finset (Fin N)) :
    testedTail Paux ι (𝓜 s c) J = ∑ m, ∑ j : Fin N,
      (if j ∈ J then 0 else 1) * ∫ ω', ‖𝓜 s c ω' (ι m) j‖ ^ 2 ∂Paux := by
  unfold testedTail rowTail
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ fun j _ => ?_]
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  · split_ifs
    · exact integrable_zero _ _ _
    · exact integrable_entry_sq hR hb₀ hs _ _

/-- **`∫_a^c R(s) ds ≤ k N^{-D}`** from the finite-speed bound of the reference flow. -/
theorem integral_testedTail_le (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    (hb₀ : 0 ≤ b₀)
    (hB1 : BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c
      (fun s k j => ∫ ω', ‖𝓜 s c ω' k j‖ ^ 2 ∂Paux))
    (ι : Fin k → Fin N) (J : Finset (Fin N)) {D : ℝ} (hD0 : 0 ≤ D)
    (hsp : ∀ m : Fin k, ∫⁻ s in Icc a c, ENNReal.ofReal (∑ j : Fin N,
        (if j ∈ J then 0 else 1) * ∫ ω', ‖𝓜 s c ω' (ι m) j‖ ^ 2 ∂Paux) ≤ ENNReal.ofReal D) :
    IntegrableOn (fun s => testedTail Paux ι (𝓜 s c) J) (Icc a c) ∧
      ∫ s in Ioc a c, testedTail Paux ι (𝓜 s c) J ≤ k * D := by
  set q : Fin k → ℝ → ℝ := fun m s => ∑ j : Fin N,
    (if j ∈ J then 0 else 1) * ∫ ω', ‖𝓜 s c ω' (ι m) j‖ ^ 2 ∂Paux with hq
  have hcont : ∀ m, ContinuousOn (q m) (Icc a c) := by
    intro m
    have hP := hB1.2.1
    refine continuousOn_finsetSum _ fun j _ => continuousOn_const.mul ?_
    exact (continuous_apply j).comp_continuousOn ((continuous_apply (ι m)).comp_continuousOn hP)
  have hint : ∀ m, IntegrableOn (q m) (Icc a c) := fun m =>
    (hcont m).integrableOn_compact isCompact_Icc
  have hq0 : ∀ m s, s ∈ Icc a c → 0 ≤ q m s := by
    intro m s _
    refine Finset.sum_nonneg fun j _ => mul_nonneg (by split_ifs <;> norm_num) ?_
    exact integral_nonneg fun _ => by positivity
  have heq : EqOn (fun s => testedTail Paux ι (𝓜 s c) J) (fun s => ∑ m, q m s) (Icc a c) :=
    fun s hs => testedTail_eq hR hb₀ hs ι J
  have hintR : IntegrableOn (fun s => testedTail Paux ι (𝓜 s c) J) (Icc a c) :=
    IntegrableOn.congr_fun (f := fun s => ∑ m, q m s)
      (integrable_finsetSum (μ := volume.restrict (Icc a c)) _ fun m _ => hint m)
      heq.symm measurableSet_Icc
  refine ⟨hintR, ?_⟩
  have hD : ∀ m, ∫ s in Icc a c, q m s ≤ D := by
    intro m
    have h1 := ofReal_integral_eq_lintegral_ofReal (hint m)
      ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall (hq0 m)))
    have h2 := hsp m
    rw [← h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hD0).mp h2
  have hR0 : ∀ s ∈ Icc a c, 0 ≤ testedTail Paux ι (𝓜 s c) J := fun s _ =>
    testedTail_nonneg ι _ J
  calc ∫ s in Ioc a c, testedTail Paux ι (𝓜 s c) J
      ≤ ∫ s in Icc a c, testedTail Paux ι (𝓜 s c) J :=
        setIntegral_mono_set hintR
          ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hR0))
          (Filter.Eventually.of_forall Ioc_subset_Icc_self)
    _ = ∫ s in Icc a c, ∑ m, q m s := setIntegral_congr_fun measurableSet_Icc heq
    _ = ∑ m, ∫ s in Icc a c, q m s := integral_finsetSum _ fun m _ => hint m
    _ ≤ ∑ _m : Fin k, D := Finset.sum_le_sum fun m _ => hD m
    _ = k * D := by simp

/-- **Time integration on a good sample.** See the module docstring. -/
theorem goodSample_integral_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1)
    {a t : ℝ} (hat : a = c - t) (ht : 0 ≤ t) (hts : t ≤ s₀)
    {ℓ w : ℕ} (hℓ : 1 ≤ ℓ) (hw : 1 ≤ w) (hsq : Real.sqrt t ≤ (w : ℝ) / N)
    {c₁ Csp b₀ Ccomp Cd Mint Cw Dsp : ℝ} (hc₁ : 0 < c₁) (hCsp : 0 ≤ Csp) (hb₀ : 0 < b₀)
    (hCcomp : 0 ≤ Ccomp) (hCd : 0 ≤ Cd) (hMint : 0 ≤ Mint)
    (hρ8 : centralRho N w ℓ c₁ Csp t ≤ r₀ / 8)
    {ω : FlowSample N} (hG : RmvGood F c E r₀ V a t ℓ w c₁ Csp b₀ Ccomp Cd Mint Cw Dsp ω)
    {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux} [IsProbabilityMeasure Paux]
    {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}
    (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    (hB1 : BackwardPropagator (referenceGenerator F a b₀ ω ℓ) a c
      (fun s k j => ∫ ω', ‖𝓜 s c ω' k j‖ ^ 2 ∂Paux))
    (ι : Fin k → Fin N) (hι : ∀ m, |flowEigenvalue F a ω c (ι m) - E| ≤ Cw / N)
    {f : MarkArray k r → ℝ} (hf : IsC2Bounded 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∫ s in Ioc a c, |complexAngularGenerator N r (flowEigenvalue F a ω s)
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s)) -
      referenceArrayGenerator F a b₀ ω ℓ s
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s))| ≤
      (c - a) * tbQ0 N r k (diagXJ N c r₀ s₀ v₀ t ℓ w c₁ Csp Mint Cd) Ccomp
          (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε +
        tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * frameZsq N A c s₀ v₀ + 1))
            (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε *
          (k * (N : ℝ) ^ (-Dsp)) := by
  set Q₀ := tbQ0 N r k (diagXJ N c r₀ s₀ v₀ t ℓ w c₁ Csp Mint Cd) Ccomp
    (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε with hQ₀
  set Q₁ := tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * frameZsq N A c s₀ v₀ + 1))
    (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε with hQ₁
  set J := rmvWindow F a ω E w with hJ
  have hZ0 := frameZsq_nonneg (N := N) (A := A) hK
  have hQ₁0 : 0 ≤ Q₁ := by
    rw [hQ₁]; unfold tbQ1
    have := Real.sqrt_nonneg (frameZsq N A c s₀ v₀)
    positivity
  have hac : a ≤ c := by rw [hat]; linarith
  obtain ⟨hintR, hIR⟩ := integral_testedTail_le hR hb₀.le hB1 ι J
    (Real.rpow_nonneg (Nat.cast_nonneg N) (-Dsp)) (fun m => by
      have h := hG.speed (ι m) (hι m) _ hB1
      convert h using 4 with s
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hJ, rmvWindow])
  have hpt : ∀ s ∈ Ioc a c, |complexAngularGenerator N r (flowEigenvalue F a ω s)
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s)) -
      referenceArrayGenerator F a b₀ ω ℓ s
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 s c ω') z + Ξ s c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω s))| ≤ Q₀ + Q₁ * testedTail Paux ι (𝓜 s c) J := by
    intro s hs
    have hs' : s ∈ Icc a c := Ioc_subset_Icc_self hs
    exact goodTime_genDiff_le hN hK hC hV hat ht hts hℓ hw hsq hc₁ hCsp hb₀ hCcomp hCd hMint hρ8
      hG.herm hs' (hG.simple s hs') hG.low (hG.disp s hs') (hG.gap s hs') (hG.beta s hs')
      (hG.win s hs') (hG.dist s hs') (hG.int s hs') hR ι hf hε
  have hintB : IntegrableOn (fun s => Q₀ + Q₁ * testedTail Paux ι (𝓜 s c) J) (Ioc a c) :=
    ((integrableOn_const (by simp)).add (hintR.const_mul Q₁)).mono_set Ioc_subset_Icc_self
  calc _ ≤ ∫ s in Ioc a c, (Q₀ + Q₁ * testedTail Paux ι (𝓜 s c) J) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _) hintB
          ((ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt))
    _ = (c - a) * Q₀ + Q₁ * ∫ s in Ioc a c, testedTail Paux ι (𝓜 s c) J := by
        have hc0 : IntegrableOn (fun _ : ℝ => Q₀) (Ioc a c) := integrableOn_const (by simp)
        rw [integral_add hc0 ((hintR.mono_set Ioc_subset_Icc_self).const_mul Q₁),
          integral_const_mul, setIntegral_const]
        simp [Real.volume_real_Ioc_of_le hac]
    _ ≤ _ := by gcongr

end Integration

end BlockBand.Critical.RelativeVectors
