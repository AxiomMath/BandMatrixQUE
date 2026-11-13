module

public import BlockBand.Internal.Contracts.TransmissionUniform

/-!
# The signed response of the `p = 1` dual diffusion with boundary starts

Clause 2 of the pass-derivative lemma: the right side of the signed limit. Dual objects:
`IsBoundaryDualProcess` (`TransmissionUniform`), `p = 1`, boundary starts `x ≥ 0`, `0 ≤ y < 1`,
`(x, y) ≠ (0, 0)`; the corner `(0, 0)` is stated separately with value `0`.

* `responseIntegrand τ g N X Y ω = 1{ζ ≤ τ} ∫_0^τ g(s) R_s ds` (`ζ = dualExtinction N = σ₀`,
  `R_s = dualTotal`); for clause 2, `g(s) = q(s) + q(τ - s)`.
* `SignedResponseValue D₀ τ g x y v`: every boundary-start realization gives `v` to
  `E_{x,y}[responseIntegrand]` (the style of `BoundaryDualLawValue`).
* `IsSignedResponse D₀ τ g x y v`: the corner `(0,0)` with `v = 0`, or a boundary start with an
  existing realization and `SignedResponseValue`.

Proved here, pathwise and for a single realization:
* `boundaryPath_total_nonneg`, `boundaryPath_intervalIntegrable`: for `p = 1`, `R_s ≥ 0` and
  `s ↦ R_s` is interval integrable on `[0, τ]` (continuous before `ζ`, tending to `0` at `ζ`).
* `dualTransform_rightDeriv`: for a profile `p ≥ 0` bounded, if the transform with profile `p`
  is nonzero (as the law gives), the right derivative at `κ = 0` of
  `κ ↦ dualTransform E (κ p) τ` is `-4πρ(E) E[responseIntegrand τ (p(τ - ·))]`, and the
  integrand is integrable. Measurability of the integrand is derived from the integrability of
  the nonzero transform (no progressive measurability is assumed). Domination uses
  `firstMoment` (`E ∫_0^τ R_s ds ≤ τ(x + y)`).
* `ResponseData D₀ τ g x y v`: every realization has an integrable response with expectation `v`;
  it is additive in continuous `g` (`ResponseData.add`, `ResponseData.sub`), which gives the
  signed test `q = q₊ - q₋`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Endpoints

open MeasureTheory Filter Topology Set
open BlockBand.Internal.Contracts.TransmissionPath BlockBand.Internal.Contracts.TransmissionLaws
  BlockBand.Internal.Contracts.TransmissionUniform
open scoped ENNReal NNReal

/-!
### Definitions
-/

/-- `1{σ₀ ≤ τ} ∫_0^τ g(s) R_s ds` on one sample of a dual realization. -/
def responseIntegrand {Ω : Type*} (τ : ℝ) (g : ℝ → ℝ) (N : ℝ≥0 → Ω → ℕ)
    (X Y : ℝ≥0 → Ω → ℕ → ℝ) (ω : Ω) : ℝ :=
  if dualExtinction N ω ≤ ENNReal.ofReal τ then
    ∫ s in (0 : ℝ)..τ, g s * dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)
  else 0

/-- Every boundary-start realization of the `p = 1` dual from `(x, y)` gives the value `v` to
`E_{x,y}[1{σ₀ ≤ τ} ∫_0^τ g(s) R_s ds]`. -/
def SignedResponseValue (D0 τ : ℝ) (g : ℝ → ℝ) (x y v : ℝ) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      ∫ ω, responseIntegrand τ g N X Y ω ∂P = v

/-- **The signed response value** `v = E_{x,y}[1{σ₀ ≤ τ} ∫_0^τ g(s) R_s ds]` of the `p = 1` dual
diffusion with absorption at its corner: at the corner `(x, y) = (0, 0)` the value is `0`
(`F_{0,0} ≡ 1`, `J(0,0) := 0`); otherwise the boundary-start law exists and every realization
gives `v`. -/
def IsSignedResponse (D0 τ : ℝ) (g : ℝ → ℝ) (x y v : ℝ) : Prop :=
  (x = 0 ∧ y = 0 ∧ v = 0) ∨
    (¬(x = 0 ∧ y = 0) ∧ HasBoundaryDualProcess D0 ![x] ![y] ∧ SignedResponseValue D0 τ g x y v)

/-!
### Elementary facts
-/

theorem isDualStart_one {x y : ℝ} (hx : 0 ≤ x) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hxy : ¬(x = 0 ∧ y = 0)) : IsDualStart ![x] ![y] := by
  refine ⟨fun i j h => absurd h (by fin_cases i; fin_cases j; simp),
    fun i j h => absurd h (by fin_cases i; fin_cases j; simp), fun i => ?_, fun i => ?_,
    fun i j => ?_⟩
  · fin_cases i; simpa using hx
  · fin_cases i; simpa using ⟨hy0, hy1⟩
  · fin_cases i; fin_cases j
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
    rcases hx.lt_or_eq with h | h
    · linarith
    · rcases hy0.lt_or_eq with h' | h'
      · linarith
      · exact absurd ⟨h.symm, h'.symm⟩ hxy

theorem semicircleDensity_pos' {E : ℝ} (hE1 : -2 < E) (hE2 : E < 2) :
    0 < Parameters.semicircleDensity E := by
  unfold Parameters.semicircleDensity
  have : 0 < 4 - E ^ 2 := by nlinarith
  exact div_pos (Real.sqrt_pos.2 this) (by positivity)

theorem dualTotal_one (x y : ℕ → ℝ) : dualTotal 1 x y = x 0 + y 0 := by
  simp [dualTotal]

theorem dualTotal_zero (x y : ℕ → ℝ) : dualTotal 0 x y = 0 := by
  simp [dualTotal]

/-!
### Pathwise facts for `p = 1`
-/

section Path

variable {n : ℝ≥0 → ℕ} {x y : ℝ≥0 → ℕ → ℝ}

theorem boundaryPath_level_le (hp : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) (t : ℝ≥0) :
    n t ≤ 1 := h0 ▸ hp.antitone (zero_le : (0 : ℝ≥0) ≤ t)

theorem boundaryPath_level (hp : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1) (t : ℝ≥0) :
    n t = 0 ∨ n t = 1 := by
  have := boundaryPath_level_le hp h0 t
  omega

/-- `R_t ≥ 0` along a `p = 1` boundary path started at `x₀, y₀ ≥ 0`. -/
theorem boundaryPath_total_nonneg (hp : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1)
    (hx0 : 0 ≤ x 0 0) (hy0 : 0 ≤ y 0 0) (t : ℝ≥0) : 0 ≤ dualTotal (n t) (x t) (y t) := by
  rcases boundaryPath_level hp h0 t with h | h
  · rw [h, dualTotal_zero]
  · rw [h, dualTotal_one]
    rcases (zero_le : (0 : ℝ≥0) ≤ t).lt_or_eq with ht | ht
    · have hc := hp.chamber t ht
      rw [h] at hc
      obtain ⟨-, -, hX, hY⟩ := hc
      exact add_nonneg (hX 0).le (hY 0).1.le
    · subst ht; exact add_nonneg hx0 hy0

/-- **`R` is interval integrable on `[0, τ]`** along a `p = 1` boundary path: it is continuous
before the extinction time and tends to `0` at it (`deletion`), and vanishes afterwards. -/
theorem boundaryPath_intervalIntegrable (hp : IsBoundaryDeletionPath n x y) (h0 : n 0 = 1)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    IntervalIntegrable (fun s : ℝ => dualTotal (n s.toNNReal) (x s.toNNReal) (y s.toNNReal))
      MeasureTheory.volume 0 τ := by
  set f : ℝ → ℝ := fun s => dualTotal (n s.toNNReal) (x s.toNNReal) (y s.toNNReal)
  set h : ℝ → ℝ := fun s => x s.toNNReal 0 + y s.toNNReal 0
  -- continuity of `h` on `[0, t]` while the level stays `1`
  have hcont : ∀ t : ℝ≥0, n t = 1 → ContinuousOn h (Icc 0 (t : ℝ)) := by
    intro t ht
    obtain ⟨hcx, hcy⟩ := hp.cont 0 t (zero_le : (0 : ℝ≥0) ≤ t) (by rw [ht, h0]) 0 (by rw [h0]; omega)
    have hmap : MapsTo Real.toNNReal (Icc 0 (t : ℝ)) (Icc 0 t) := by
      intro s hs
      exact ⟨(zero_le : (0 : ℝ≥0) ≤ _), by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]; exact hs.2⟩
    exact (hcx.comp continuous_real_toNNReal.continuousOn hmap).add
      (hcy.comp continuous_real_toNNReal.continuousOn hmap)
  by_cases hA : n τ.toNNReal = 1
  · -- the level is `1` on all of `[0, τ]`
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hτ]
    have hc := hcont τ.toNNReal hA
    rw [Real.coe_toNNReal _ hτ] at hc
    refine hc.congr fun s hs => ?_
    have hle : s.toNNReal ≤ τ.toNNReal := Real.toNNReal_le_toNNReal hs.2
    have h1 : n s.toNNReal = 1 := by
      have := hp.antitone hle
      have := boundaryPath_level_le hp h0 s.toNNReal
      omega
    simp only [f, h, h1, dualTotal_one]
  · have hB : n τ.toNNReal = 0 := by
      rcases boundaryPath_level hp h0 τ.toNNReal with h' | h'
      · exact h'
      · exact absurd h' hA
    set S : Set ℝ≥0 := {t | n t = 0}
    have hSne : S.Nonempty := ⟨_, hB⟩
    set σ := sInf S
    have hσle : σ ≤ τ.toNNReal := csInf_le (OrderBot.bddBelow S) hB
    have hbefore : ∀ t, t < σ → n t = 1 := by
      intro t ht
      have : t ∉ S := notMem_of_lt_csInf ht (OrderBot.bddBelow S)
      rcases boundaryPath_level hp h0 t with h' | h'
      · exact absurd h' this
      · exact h'
    have hafter : ∀ t, σ < t → n t = 0 := by
      intro t ht
      obtain ⟨t', ht'S, ht'⟩ := exists_lt_of_csInf_lt hSne ht
      have := hp.antitone ht'.le
      have h' : n t' = 0 := ht'S
      omega
    have hσpos : 0 < σ := by
      by_contra hσ
      have hσ0 : σ = 0 := le_antisymm (not_lt.1 hσ) (zero_le : (0 : ℝ≥0) ≤ _)
      have hev := hp.rightCont 0
      rw [h0] at hev
      have hev2 : ∀ᶠ u in 𝓝[>] (0 : ℝ≥0), n u = 0 :=
        eventually_nhdsWithin_of_forall fun u hu => hafter u (hσ0 ▸ hu)
      obtain ⟨u, hu1, hu2⟩ := (hev.and hev2).exists
      omega
    have hσval : n σ = 0 := by
      have hev := hp.rightCont σ
      have hev2 : ∀ᶠ u in 𝓝[>] σ, n u = 0 := eventually_nhdsWithin_of_forall fun u hu => hafter u hu
      obtain ⟨u, hu1, hu2⟩ := (hev.and hev2).exists
      omega
    -- the function `g = h · 1_{s < σ}` is continuous on `[0, σ]`
    set g : ℝ → ℝ := fun s => if s < (σ : ℝ) then h s else 0
    have hgc : ContinuousOn g (Icc 0 (σ : ℝ)) := by
      intro s hs
      rcases hs.2.lt_or_eq with hlt | heq
      · obtain ⟨t₂, hst₂, ht₂σ⟩ := exists_between hlt
        have ht₂0 : 0 ≤ t₂ := hs.1.trans hst₂.le
        have hlev : n t₂.toNNReal = 1 := hbefore _ (by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ ht₂0]; exact ht₂σ)
        have hc := hcont t₂.toNNReal hlev
        rw [Real.coe_toNNReal _ ht₂0] at hc
        have hcg : ContinuousOn g (Icc 0 t₂) :=
          hc.congr fun u hu => by
            simp only [g, lt_of_le_of_lt hu.2 ht₂σ, ite_true]
        have hmem : Icc 0 t₂ ∈ 𝓝[Icc 0 (σ : ℝ)] s := by
          refine mem_nhdsWithin.2 ⟨Iio t₂, isOpen_Iio, hst₂, fun u hu => ⟨hu.2.1, hu.1.le⟩⟩
        exact (hcg s ⟨hs.1, hst₂.le⟩).mono_of_mem_nhdsWithin hmem
      · subst heq
        have hgσ : g σ = 0 := by simp [g]
        rw [ContinuousWithinAt, hgσ]
        have hdel := hp.deletion σ hσpos 0
          (eventually_nhdsWithin_of_forall fun u hu => by rw [zero_add]; exact hbefore u hu)
          (by rw [hσval]; omega)
        obtain ⟨-, hx, hy, -⟩ := hdel
        have hmapf : Tendsto Real.toNNReal (𝓝[<] (σ : ℝ)) (𝓝[<] σ) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have := (continuous_real_toNNReal.tendsto (σ : ℝ))
            rw [Real.toNNReal_coe] at this
            exact this.mono_left nhdsWithin_le_nhds
          · have hev : ∀ᶠ u in 𝓝[<] (σ : ℝ), 0 < u :=
              nhdsWithin_le_nhds (lt_mem_nhds (by exact_mod_cast hσpos))
            filter_upwards [hev, self_mem_nhdsWithin] with u hu0 hu
            show u.toNNReal < σ
            rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hu0.le]
            exact hu
        have hlim : Tendsto h (𝓝[<] (σ : ℝ)) (𝓝 0) := by
          have := (hx.comp hmapf).add (hy.comp hmapf)
          simpa [h] using this
        have hlim' : Tendsto g (𝓝[<] (σ : ℝ)) (𝓝 0) :=
          hlim.congr' (eventually_nhdsWithin_of_forall fun u hu => by
            simp only [g, show u < (σ : ℝ) from hu, ite_true])
        have hcw : ContinuousWithinAt g (Iio (σ : ℝ)) (σ : ℝ) := by
          rw [ContinuousWithinAt, hgσ]; exact hlim'
        rw [← continuousWithinAt_insert_self] at hcw
        have hfin := hcw.mono fun u (hu : u ∈ Icc 0 (σ : ℝ)) => by
          rcases hu.2.lt_or_eq with h' | h'
          · exact Or.inr h'
          · exact Or.inl h'
        rwa [ContinuousWithinAt, hgσ] at hfin
    have h1 : IntervalIntegrable f MeasureTheory.volume 0 (σ : ℝ) := by
      have hgi : IntervalIntegrable g MeasureTheory.volume 0 (σ : ℝ) := by
        refine ContinuousOn.intervalIntegrable ?_
        rwa [uIcc_of_le (NNReal.coe_nonneg σ)]
      refine hgi.congr fun s hs => ?_
      rw [uIoc_of_le (NNReal.coe_nonneg σ)] at hs
      have hs0 : 0 ≤ s := hs.1.le
      rcases hs.2.lt_or_eq with hlt | heq
      · have hlev : n s.toNNReal = 1 := hbefore _ (by
          rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hlt)
        simp only [g, f, h, hlt, ite_true, hlev, dualTotal_one]
      · have : s.toNNReal = σ := by rw [heq, Real.toNNReal_coe]
        simp only [g, f, heq, lt_irrefl, ite_false, Real.toNNReal_coe, hσval, dualTotal_zero]
    have h2 : IntervalIntegrable f MeasureTheory.volume (σ : ℝ) τ := by
      have hστ : (σ : ℝ) ≤ τ := by
        have := NNReal.coe_le_coe.2 hσle
        rwa [Real.coe_toNNReal _ hτ] at this
      refine (intervalIntegrable_const (c := (0 : ℝ))).congr fun s hs => ?_
      rw [uIoc_of_le hστ] at hs
      have hs0 : 0 ≤ s := σ.2.trans hs.1.le
      have hlev : n s.toNNReal = 0 := hafter _ (by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]; exact hs.1)
      simp only [f, hlev, dualTotal_zero]
    exact h1.trans h2

end Path

/-!
### The right derivative of the dual transform at zero source
-/

section Deriv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {D0 x y : ℝ}
  {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}

/-- Pathwise structure almost surely, for `p = 1`. -/
theorem isBoundaryDualProcess_ae_path (hR : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y) :
    ∀ᵐ ω ∂P, IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω) ∧
      N 0 ω = 1 ∧ X 0 ω 0 = x ∧ Y 0 ω 0 = y := by
  filter_upwards [hR.paths, hR.start] with ω h1 h2
  exact ⟨h1, h2.1, by simpa using (h2.2 0).1, by simpa using (h2.2 0).2⟩

omit [MeasurableSpace Ω] in
/-- The exponent of the dual transform with profile `κ p` is `4πρ(E) κ ∫_0^τ p(τ - s) R_s ds`. -/
theorem dualExponent_eq (E κ τ : ℝ) (p : ℝ → ℝ) (ω : Ω) :
    ∫ s in (0 : ℝ)..τ, absorptionRate E (fun t => κ * p t) (τ - s) *
        dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω) =
      (4 * Real.pi * Parameters.semicircleDensity E * κ) *
        ∫ s in (0 : ℝ)..τ, p (τ - s) *
          dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [absorptionRate]
  ring

/-- **Right derivative of the dual transform at zero source.** For a single
boundary-start realization (`p = 1`, start `x, y ≥ 0`, first moment `≤ τ(x + y)`), a bounded
profile `p ≥ 0`, `τ > 0` and bulk `E`: if the transform with profile `p` is nonzero, then
`E[1{ζ ≤ τ} ∫_0^τ p(τ - s) R_s ds]` is integrable and
`(dualTransform(κ p) - dualTransform(0))/κ → -4πρ(E) E[1{ζ ≤ τ} ∫_0^τ p(τ - s) R_s ds]` as
`κ ↓ 0`. -/
theorem dualTransform_rightDeriv (hR : IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hfirst : ∀ t : ℝ, 0 ≤ t → ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) t,
      ENNReal.ofReal (dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω))) ∂P ≤
        ENNReal.ofReal (t * (x + y)))
    {E τ : ℝ} (hE1 : -2 < E) (hE2 : E < 2) (hτ : 0 < τ) {p : ℝ → ℝ} (hp0 : ∀ t, 0 ≤ p t)
    {Q : ℝ} (hpQ : ∀ t, p t ≤ Q) (hne : dualTransform E p τ P N X Y ≠ 0) :
    Integrable (responseIntegrand τ (fun s => p (τ - s)) N X Y) P ∧
    Tendsto (fun κ : ℝ => (dualTransform E (fun t => κ * p t) τ P N X Y -
        dualTransform E (fun t => 0 * p t) τ P N X Y) / κ) (𝓝[>] 0)
      (𝓝 (-(4 * Real.pi * Parameters.semicircleDensity E) *
        ∫ ω, responseIntegrand τ (fun s => p (τ - s)) N X Y ω ∂P)) := by
  have hprob : IsProbabilityMeasure P := hR.prob
  set c := 4 * Real.pi * Parameters.semicircleDensity E with hc
  have hcpos : 0 < c := by
    have := semicircleDensity_pos' hE1 hE2
    positivity
  set Z : Ω → Prop := fun ω => dualExtinction N ω ≤ ENNReal.ofReal τ
  set R : Ω → ℝ → ℝ := fun ω s => dualTotal (N s.toNNReal ω) (X s.toNNReal ω) (Y s.toNNReal ω)
  set a : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..τ, p (τ - s) * R ω s
  set J := responseIntegrand τ (fun s => p (τ - s)) N X Y
  have hJ : ∀ ω, J ω = if Z ω then a ω else 0 := fun ω => rfl
  classical
  set f : ℝ → Ω → ℝ := fun κ ω => if Z ω then Real.exp (-(c * κ * a ω)) else 0
  have hf : ∀ κ, dualTransform E (fun t => κ * p t) τ P N X Y = ∫ ω, f κ ω ∂P := by
    intro κ
    unfold dualTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [f, Z]
    split_ifs
    · rw [dualExponent_eq]
    · rfl
  have hf1 : dualTransform E p τ P N X Y = ∫ ω, f 1 ω ∂P := by
    have := hf 1
    simp only [one_mul] at this
    exact this
  -- the integrand at `κ = 1` is integrable, hence measurable
  have hint1 : Integrable (f 1) P := by
    by_contra hni
    exact hne (by rw [hf1, integral_undef hni])
  have hm1 : AEMeasurable (f 1) P := hint1.aestronglyMeasurable.aemeasurable
  -- a.s. path facts: `R ≥ 0`, hence `a ≥ 0`
  have hpath := isBoundaryDualProcess_ae_path hR
  have hR0 : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ R ω s := by
    filter_upwards [hpath] with ω h s
    obtain ⟨hp, h0, hx0, hy0⟩ := h
    exact boundaryPath_total_nonneg hp h0 (by rw [hx0]; exact hx) (by rw [hy0]; exact hy) _
  have ha0 : ∀ᵐ ω ∂P, 0 ≤ a ω := by
    filter_upwards [hR0] with ω h
    exact intervalIntegral.integral_nonneg hτ.le fun s _ => mul_nonneg (hp0 _) (h s)
  have hJ0 : ∀ᵐ ω ∂P, 0 ≤ J ω := by
    filter_upwards [ha0] with ω h
    rw [hJ]; split_ifs <;> simp [h]
  -- `J = Ψ (f 1)`
  set Ψ : ℝ → ℝ := fun u => if 0 < u then -Real.log u / c else 0
  have hΨm : Measurable Ψ :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (Real.measurable_log.neg.div_const _) measurable_const
  have hJΨ : ∀ ω, J ω = Ψ (f 1 ω) := by
    intro ω
    simp only [hJ, f, Ψ]
    split_ifs with h1 h2 h3
    · rw [Real.log_exp]; field_simp
    · exact absurd (Real.exp_pos _) h2
    · exact absurd h3 (lt_irrefl 0)
    · rfl
  have hJm : AEStronglyMeasurable J P := by
    have : J = Ψ ∘ f 1 := funext hJΨ
    rw [this]
    exact (hΨm.comp_aemeasurable hm1).aestronglyMeasurable
  -- integrability of `J` from the first moment
  have hJint : Integrable J P := by
    refine ⟨hJm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hJ0]
    have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal (J ω) ≤ ENNReal.ofReal (max Q 0) *
        ∫⁻ s in Set.Icc (0 : ℝ) τ, ENNReal.ofReal (R ω s) := by
      filter_upwards [hR0] with ω hR0ω
      rw [hJ]
      split_ifs
      · by_cases hi : IntervalIntegrable (fun s => p (τ - s) * R ω s) volume 0 τ
        · have hi' : IntegrableOn (fun s => p (τ - s) * R ω s) (Ioc 0 τ) := by
            rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le] at hi
          simp only [a]
          rw [intervalIntegral.integral_of_le hτ.le,
            ofReal_integral_eq_lintegral_ofReal hi' (Filter.Eventually.of_forall fun s =>
              mul_nonneg (hp0 _) (hR0ω s))]
          calc ∫⁻ s in Ioc 0 τ, ENNReal.ofReal (p (τ - s) * R ω s)
              ≤ ∫⁻ s in Ioc 0 τ, ENNReal.ofReal (max Q 0) * ENNReal.ofReal (R ω s) := by
                refine lintegral_mono fun s => ?_
                rw [← ENNReal.ofReal_mul (le_max_right _ _)]
                exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
                  ((hpQ _).trans (le_max_left _ _)) (hR0ω s))
            _ = ENNReal.ofReal (max Q 0) * ∫⁻ s in Ioc 0 τ, ENNReal.ofReal (R ω s) :=
                lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
            _ ≤ _ := by gcongr ?_ * ?_; exact le_rfl; exact lintegral_mono_set (Ioc_subset_Icc_self : Ioc (0 : ℝ) τ ⊆ Icc 0 τ)
        · simp only [a]
          rw [intervalIntegral.integral_undef hi, ENNReal.ofReal_zero]
          exact zero_le
      · rw [ENNReal.ofReal_zero]; exact zero_le
    calc ∫⁻ ω, ENNReal.ofReal (J ω) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (max Q 0) *
            (∫⁻ s in Set.Icc (0 : ℝ) τ, ENNReal.ofReal (R ω s)) ∂P := lintegral_mono_ae hpt
      _ = ENNReal.ofReal (max Q 0) * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) τ,
            ENNReal.ofReal (R ω s)) ∂P := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (max Q 0) * ENNReal.ofReal (τ * (x + y)) := by
          gcongr; exact hfirst τ hτ.le
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine ⟨hJint, ?_⟩
  -- dominated convergence for the difference quotients
  have hfκ : ∀ κ, 0 < κ → ∀ ω, f κ ω = (f 1 ω) ^ κ := by
    intro κ hκ ω
    simp only [f]
    split_ifs
    · rw [← Real.exp_mul]; ring_nf
    · rw [Real.zero_rpow hκ.ne']
  set ind : ℝ → ℝ := fun u => if 0 < u then 1 else 0
  have hindm : Measurable ind :=
    Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const
  have hf0 : ∀ ω, f 0 ω = ind (f 1 ω) := by
    intro ω
    simp only [f, ind]
    split_ifs with h1 h2 h3
    · simp
    · exact absurd (Real.exp_pos _) h2
    · exact absurd h3 (lt_irrefl 0)
    · rfl
  have hfb : ∀ κ, 0 ≤ κ → ∀ᵐ ω ∂P, ‖f κ ω‖ ≤ 1 := by
    intro κ hκ
    filter_upwards [ha0] with ω hω
    simp only [f]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ c * κ * a ω := by positivity
      linarith
    · simp
  have hfm : ∀ κ, 0 ≤ κ → AEStronglyMeasurable (f κ) P := by
    intro κ hκ
    rcases hκ.lt_or_eq with hκ | hκ
    · have : f κ = fun ω => (f 1 ω) ^ κ := funext (hfκ κ hκ)
      rw [this]
      exact (hm1.pow_const κ).aestronglyMeasurable
    · subst hκ
      have : f 0 = ind ∘ f 1 := funext hf0
      rw [this]
      exact (hindm.comp_aemeasurable hm1).aestronglyMeasurable
  have hfi : ∀ κ, 0 ≤ κ → Integrable (f κ) P := fun κ hκ =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hfm κ hκ) (hfb κ hκ)
  have hq : ∀ κ, 0 < κ → (dualTransform E (fun t => κ * p t) τ P N X Y -
      dualTransform E (fun t => 0 * p t) τ P N X Y) / κ =
        ∫ ω, (f κ ω - f 0 ω) / κ ∂P := by
    intro κ hκ
    rw [hf, hf, ← integral_sub (hfi κ hκ.le) (hfi 0 le_rfl), integral_div]
  have hlim : Tendsto (fun κ : ℝ => ∫ ω, (f κ ω - f 0 ω) / κ ∂P) (𝓝[>] 0)
      (𝓝 (∫ ω, -c * J ω ∂P)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ω => c * J ω) ?_ ?_
      (hJint.const_mul c) ?_
    · filter_upwards [self_mem_nhdsWithin] with κ hκ
      exact (((hfm κ (le_of_lt hκ)).aemeasurable.sub (hfm 0 le_rfl).aemeasurable).div_const
        κ).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with κ (hκ : 0 < κ)
      filter_upwards [ha0] with ω hω
      rw [hJ]
      simp only [f]
      split_ifs
      · simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero]
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hκ, div_le_iff₀ hκ, abs_sub_comm,
          abs_of_nonneg (by
            rw [sub_nonneg, Real.exp_le_one_iff]
            have : 0 ≤ c * κ * a ω := by positivity
            linarith)]
        have := Real.add_one_le_exp (-(c * κ * a ω))
        nlinarith
      · simp
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [hJ]
      simp only [f]
      split_ifs
      · have hd : HasDerivAt (fun κ : ℝ => Real.exp (-(c * κ * a ω))) (-c * a ω) 0 := by
          have h1 : HasDerivAt (fun κ : ℝ => -(c * κ * a ω)) (-(c * 1 * a ω)) 0 :=
            (((hasDerivAt_id (0 : ℝ)).const_mul c).mul_const (a ω)).neg
          have h2 := h1.exp
          simp only [mul_zero, zero_mul, neg_zero, Real.exp_zero, one_mul, mul_one] at h2
          convert h2 using 1
          ring
        have ht := (hasDerivAt_iff_tendsto_slope_zero.1 hd).mono_left
          (nhdsWithin_mono _ fun u (hu : 0 < u) => (ne_of_gt hu))
        refine ht.congr' (eventually_nhdsWithin_of_forall fun κ hκ => ?_)
        simp only [zero_add, smul_eq_mul, mul_zero, zero_mul, neg_zero]
        rw [inv_mul_eq_div]
      · simp only [sub_self, zero_div, mul_zero]
        exact tendsto_const_nhds
  have e : ∫ ω, -c * J ω ∂P = -(4 * Real.pi * Parameters.semicircleDensity E) *
      ∫ ω, responseIntegrand τ (fun s => p (τ - s)) N X Y ω ∂P := by
    rw [integral_const_mul]
  rw [← e]
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun κ hκ => (hq κ hκ).symm)

/-!
### Integrable response data and linearity
-/

/-- Every boundary-start realization has an integrable response `1{σ₀ ≤ τ}∫_0^τ g R` with
expectation `v`. -/
def ResponseData (D0 τ : ℝ) (g : ℝ → ℝ) (x y v : ℝ) : Prop :=
  ∀ (Ω : Type) (m : MeasurableSpace Ω) (𝓖 : Filtration ℝ≥0 m) (P : Measure Ω)
    (N : ℝ≥0 → Ω → ℕ) (X Y : ℝ≥0 → Ω → ℕ → ℝ), IsBoundaryDualProcess P 𝓖 D0 ![x] ![y] N X Y →
      Integrable (responseIntegrand τ g N X Y) P ∧ ∫ ω, responseIntegrand τ g N X Y ω ∂P = v

theorem ResponseData.value {D0 τ x y v : ℝ} {g : ℝ → ℝ} (h : ResponseData D0 τ g x y v) :
    SignedResponseValue D0 τ g x y v := fun Ω m 𝓖 P N X Y hR => (h Ω m 𝓖 P N X Y hR).2

theorem responseIntegrand_add {Ω : Type*} {τ : ℝ} (hτ : 0 ≤ τ) {g₁ g₂ : ℝ → ℝ}
    (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) {N : ℝ≥0 → Ω → ℕ} {X Y : ℝ≥0 → Ω → ℕ → ℝ}
    {ω : Ω} (hp : IsBoundaryDeletionPath (fun t => N t ω) (fun t => X t ω) (fun t => Y t ω))
    (h0 : N 0 ω = 1) :
    responseIntegrand τ (fun s => g₁ s + g₂ s) N X Y ω =
      responseIntegrand τ g₁ N X Y ω + responseIntegrand τ g₂ N X Y ω := by
  have hR := boundaryPath_intervalIntegrable hp h0 hτ
  have i1 := hR.continuousOn_mul hg₁.continuousOn
  have i2 := hR.continuousOn_mul hg₂.continuousOn
  unfold responseIntegrand
  split_ifs
  · rw [← intervalIntegral.integral_add i1 i2]
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  · ring

theorem ResponseData.add {D0 τ x y v₁ v₂ : ℝ} (hτ : 0 ≤ τ) {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) (h₁ : ResponseData D0 τ g₁ x y v₁) (h₂ : ResponseData D0 τ g₂ x y v₂) :
    ResponseData D0 τ (fun s => g₁ s + g₂ s) x y (v₁ + v₂) := by
  intro Ω m 𝓖 P N X Y hR
  obtain ⟨i₁, e₁⟩ := h₁ Ω m 𝓖 P N X Y hR
  obtain ⟨i₂, e₂⟩ := h₂ Ω m 𝓖 P N X Y hR
  have hae : responseIntegrand τ (fun s => g₁ s + g₂ s) N X Y =ᵐ[P]
      fun ω => responseIntegrand τ g₁ N X Y ω + responseIntegrand τ g₂ N X Y ω := by
    filter_upwards [isBoundaryDualProcess_ae_path hR] with ω hω
    exact responseIntegrand_add hτ hg₁ hg₂ hω.1 hω.2.1
  refine ⟨(i₁.add i₂).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_add i₁ i₂, e₁, e₂]

theorem ResponseData.sub {D0 τ x y v₁ v₂ : ℝ} (hτ : 0 ≤ τ) {g₁ g₂ : ℝ → ℝ} (hg₁ : Continuous g₁)
    (hg₂ : Continuous g₂) (h₁ : ResponseData D0 τ (fun s => g₁ s + g₂ s) x y v₁)
    (h₂ : ResponseData D0 τ g₂ x y v₂) : ResponseData D0 τ g₁ x y (v₁ - v₂) := by
  intro Ω m 𝓖 P N X Y hR
  obtain ⟨i₁, e₁⟩ := h₁ Ω m 𝓖 P N X Y hR
  obtain ⟨i₂, e₂⟩ := h₂ Ω m 𝓖 P N X Y hR
  have hae : responseIntegrand τ g₁ N X Y =ᵐ[P]
      fun ω => responseIntegrand τ (fun s => g₁ s + g₂ s) N X Y ω -
        responseIntegrand τ g₂ N X Y ω := by
    filter_upwards [isBoundaryDualProcess_ae_path hR] with ω hω
    rw [responseIntegrand_add hτ hg₁ hg₂ hω.1 hω.2.1]
    ring
  refine ⟨(i₁.sub i₂).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, integral_sub i₁ i₂, e₁, e₂]

theorem ResponseData.congr {D0 τ x y v : ℝ} {g₁ g₂ : ℝ → ℝ} (h : g₁ = g₂)
    (h₁ : ResponseData D0 τ g₁ x y v) : ResponseData D0 τ g₂ x y v := h ▸ h₁

end Deriv

end BlockBand.Endpoints
