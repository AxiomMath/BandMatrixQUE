module
public import BlockBand.Diffusion.Duality.Mollify
set_option autoImplicit false
@[expose] public section
noncomputable section

/-!
# Time mollification of `C^{0,2}` solutions of the backward equation

Lebesgue measure on `ℝ` (the time shift). Space `ℝ^d = Fin d → ℝ`; time-independent
coefficients `b : ℝ^d → ℝ^d`, `a : ℝ^d → Mat_d(ℝ)` (no regularity of `b`, `a` is used here).

* `IsC02On u ut u1 u2 S`: on `S ⊆ ℝ × E`, `σ ↦ u(σ, x)` has derivative `ut`, `y ↦ u(s, y)` has
  Fréchet derivative `u1`, `y ↦ u1(s, y)` has Fréchet derivative `u2`, and `u, ut, u1, u2` are
  jointly continuous on `S`. This is the class `C^{0,2}` with a continuous time derivative
  (`∂ₜu`, `∂ₓu`, `∂ₓ²u` exist and are jointly continuous); no mixed derivative `∂ₜ∂ₓu` and no
  `∂ₜ²u` is required, and joint (Fréchet) differentiability in `(s, x)` is not assumed.
* `spGen b a ut u1 u2 p = ut + ∑ bᵢ u1 eᵢ + ½ ∑ aᵢⱼ u2 eᵢ eⱼ`: the backward operator
  `∂ₜ + 𝓛` in terms of the data.

**Main result (`IsC02On.tconv`).** Let `u` be `C^{0,2}` on `(T₀, T₁) × O` (`O` open) with
`∂ₜu + 𝓛u = 0` there (`spGen = 0`), and `φ` a backward mollifier at scale `ε ≥ 0`
(`IsBwdMollifier`: `C²`, `≥ 0`, mass one, support in `[-ε, 0]`). Then
`u_ε = tconv φ u`, `u_ε(s, x) = ∫ φ(r) u(s + r, x) dr`, is jointly `C²` on
`(T₀ + ε, T₁) × O` and solves `stGen b a u_ε = 0` there.

Proof: `∂ₛ` falls on the kernel (`∂ₛu_ε = tconv (-φ') u`), `∂ₓ`, `∂ₓ²` pass under the integral;
integration by parts in time (`tconv_timeDeriv`) gives
`tconv (-φ') u = tconv φ ∂ₜu = -tconv φ (𝓛u) = -𝓛 u_ε`, the last step because `b`, `a` do not
depend on time.
-/

namespace BlockBand.Diffusion
open MeasureTheory Filter Topology Set Function
open BlockBand.Internal.Contracts.Transmission
open scoped NNReal

/-!
### The `C^{0,2}` class
-/

/-- `C^{0,2}` data on `S`: time derivative `ut`, first and second spatial (Fréchet)
derivatives `u1`, `u2`, all jointly continuous on `S`. -/
structure IsC02On {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u ut : ℝ × E → ℝ)
    (u1 : ℝ × E → E →L[ℝ] ℝ) (u2 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ) (S : Set (ℝ × E)) : Prop where
  hasDerivAt_time : ∀ p ∈ S, HasDerivAt (fun σ => u (σ, p.2)) (ut p) p.1
  hasFDerivAt_space : ∀ p ∈ S, HasFDerivAt (fun y => u (p.1, y)) (u1 p) p.2
  hasFDerivAt_space2 : ∀ p ∈ S, HasFDerivAt (fun y => u1 (p.1, y)) (u2 p) p.2
  continuousOn : ContinuousOn u S
  continuousOn_time : ContinuousOn ut S
  continuousOn_space : ContinuousOn u1 S
  continuousOn_space2 : ContinuousOn u2 S

theorem IsC02On.mono {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u ut : ℝ × E → ℝ}
    {u1 : ℝ × E → E →L[ℝ] ℝ} {u2 : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ} {S S' : Set (ℝ × E)}
    (h : IsC02On u ut u1 u2 S) (hS : S' ⊆ S) : IsC02On u ut u1 u2 S' :=
  ⟨fun p hp => h.hasDerivAt_time p (hS hp), fun p hp => h.hasFDerivAt_space p (hS hp),
    fun p hp => h.hasFDerivAt_space2 p (hS hp), h.continuousOn.mono hS,
    h.continuousOn_time.mono hS, h.continuousOn_space.mono hS, h.continuousOn_space2.mono hS⟩

variable {d : ℕ}

/-- The backward operator `∂ₜ + 𝓛` on `C^{0,2}` data. -/
def spGen (b : (Fin d → ℝ) → Fin d → ℝ) (a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ut : ℝ × (Fin d → ℝ) → ℝ) (u1 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ)
    (u2 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) (p : ℝ × (Fin d → ℝ)) : ℝ :=
  ut p + ∑ i, b p.2 i * u1 p (Pi.single i 1) +
    (1 / 2 : ℝ) * ∑ i, ∑ j, a p.2 i j * u2 p (Pi.single i 1) (Pi.single j 1)

/-!
### Linearity of `tconv`
-/

section Linear

variable {E G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {ψ : ℝ → ℝ} {p : ℝ × E}

theorem integrable_tconv_Ioo [TopologicalSpace E] {ε T₀ T₁ : ℝ} {O : Set E} (hψ : Continuous ψ)
    (hs : support ψ ⊆ Icc (-ε) 0) {f : ℝ × E → G} (hf : ContinuousOn f (Ioo T₀ T₁ ×ˢ O))
    (hp : p ∈ Ioo (T₀ + ε) T₁ ×ˢ O) : Integrable fun r => ψ r • f (p.1 + r, p.2) :=
  integrable_kernel_smul hψ hs (hf.comp (by fun_prop) fun _ hr => mem_Ioo_prod_of_shift hp hr)

theorem tconv_add {f g : ℝ × E → G} (hf : Integrable fun r => ψ r • f (p.1 + r, p.2))
    (hg : Integrable fun r => ψ r • g (p.1 + r, p.2)) :
    tconv ψ (fun q => f q + g q) p = tconv ψ f p + tconv ψ g p := by
  simp only [tconv, smul_add]
  exact integral_add hf hg

theorem tconv_const_mul (c : ℝ) (f : ℝ × E → ℝ) :
    tconv ψ (fun q => c * f q) p = c * tconv ψ f p := by
  simp only [tconv, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul c _

theorem tconv_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ × E → G)
    (hf : ∀ i ∈ s, Integrable fun r => ψ r • f i (p.1 + r, p.2)) :
    tconv ψ (fun q => ∑ i ∈ s, f i q) p = ∑ i ∈ s, tconv ψ (f i) p := by
  simp only [tconv, Finset.smul_sum]
  exact integral_finsetSum s hf

theorem tconv_neg (f : ℝ × E → G) : tconv ψ (fun q => -f q) p = -tconv ψ f p := by
  simp only [tconv, smul_neg, integral_neg]

theorem tconv_congr_window {ε : ℝ} (hs : support ψ ⊆ Icc (-ε) 0) {f g : ℝ × E → G}
    (h : ∀ r ∈ Icc (-ε) 0, f (p.1 + r, p.2) = g (p.1 + r, p.2)) : tconv ψ f p = tconv ψ g p := by
  refine integral_congr_ae (ae_of_all _ fun r => ?_)
  by_cases hr : r ∈ Icc (-ε) 0
  · simp only [h r hr]
  · simp only [eq_zero_of_support_subset hs hr, zero_smul]

end Linear

/-!
### The mollified function solves the backward equation
-/

section PDE

variable {b : (Fin d → ℝ) → Fin d → ℝ} {a : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
  {u ut : ℝ × (Fin d → ℝ) → ℝ} {u1 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] ℝ}
  {u2 : ℝ × (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ} {T₀ T₁ : ℝ}
  {O : Set (Fin d → ℝ)} {φ : ℝ → ℝ} {ε : ℝ}

/-- **The time-mollified function is jointly `C²`** on `(T₀ + ε, T₁) × O`. -/
theorem IsC02On.contDiffOn_tconv (hd : IsC02On u ut u1 u2 (Ioo T₀ T₁ ×ˢ O)) (hO : IsOpen O)
    (hφ : IsBwdMollifier φ ε) : ContDiffOn ℝ 2 (tconv φ u) (Ioo (T₀ + ε) T₁ ×ˢ O) :=
  contDiffOn_two_tconv hφ.contDiff hφ.support_subset hO hd.continuousOn hd.continuousOn_space
    hd.continuousOn_space2 hd.hasFDerivAt_space hd.hasFDerivAt_space2

/-- **The time-mollified function solves the backward equation** `stGen b a u_ε = 0` on
`(T₀ + ε, T₁) × O`. -/
theorem IsC02On.stGen_tconv_eq_zero (hd : IsC02On u ut u1 u2 (Ioo T₀ T₁ ×ˢ O)) (hO : IsOpen O)
    (hpde : ∀ p ∈ Ioo T₀ T₁ ×ˢ O, spGen b a ut u1 u2 p = 0) (hφ : IsBwdMollifier φ ε)
    (hε : 0 ≤ ε) {p : ℝ × (Fin d → ℝ)} (hp : p ∈ Ioo (T₀ + ε) T₁ ×ˢ O) :
    stGen b a (tconv φ u) p = 0 := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.contDiff.of_le (by norm_num)
  have hs := hφ.support_subset
  have hφc := hφ.continuous
  have hc1 : ∀ v, ContinuousOn (fun q => u1 q v) (Ioo T₀ T₁ ×ˢ O) := fun v =>
    hd.continuousOn_space.clm_apply continuousOn_const
  have hc2' : ∀ v, ContinuousOn (fun q => u2 q v) (Ioo T₀ T₁ ×ˢ O) := fun v =>
    hd.continuousOn_space2.clm_apply continuousOn_const
  have hc2 : ∀ v w, ContinuousOn (fun q => u2 q v w) (Ioo T₀ T₁ ×ˢ O) := fun v w =>
    (hc2' v).clm_apply continuousOn_const
  have hi2 : ∀ v, Integrable fun r => φ r • u2 (p.1 + r, p.2) v := fun v =>
    integrable_kernel_smul hφc hs ((hc2' v).comp (by fun_prop)
      fun _ hr => mem_Ioo_prod_of_shift hp hr)
  have ht : partialTime (tconv φ u) p = tconv (fun r => -deriv φ r) u p := by
    rw [partialTime, fderiv_tconv_apply hφ1 hs hO hd.continuousOn hd.continuousOn_space
      hd.hasFDerivAt_space hp]
    simp
  have hx : ∀ i, partialSpace (tconv φ u) p i = tconv φ (fun q => u1 q (Pi.single i 1)) p := by
    intro i
    rw [partialSpace, fderiv_tconv_apply hφ1 hs hO hd.continuousOn hd.continuousOn_space
      hd.hasFDerivAt_space hp]
    simp only [zero_smul, zero_add]
    exact tconv_clm_apply _ _ _ _ (integrable_tconv_Ioo hφc hs hd.continuousOn_space hp)
  have hxx : ∀ i j, partialSpace2 (tconv φ u) p i j =
      tconv φ (fun q => u2 q (Pi.single i 1) (Pi.single j 1)) p := by
    intro i j
    have h1 := fderiv_fderiv_tconv_apply hφ.contDiff hs hO hd.continuousOn
      hd.continuousOn_space hd.continuousOn_space2 hd.hasFDerivAt_space hd.hasFDerivAt_space2 hp
      (Pi.single i 1) (Pi.single j 1)
    have h2 := tconv_clm_apply φ u2 p (Pi.single i 1)
      (integrable_tconv_Ioo hφc hs hd.continuousOn_space2 hp)
    have h3 := tconv_clm_apply φ (fun q => u2 q (Pi.single i 1)) p (Pi.single j 1)
      (hi2 (Pi.single i 1))
    change fderiv ℝ (fderiv ℝ (tconv φ u)) p (0, Pi.single i 1) (0, Pi.single j 1) = _
    rw [h1, h2]
    exact h3
  have hT := tconv_timeDeriv hφ1 hs hε hd.hasDerivAt_time hd.continuousOn_time hp
  -- the spatial part
  have hint : ∀ f : ℝ × (Fin d → ℝ) → ℝ, ContinuousOn f (Ioo T₀ T₁ ×ˢ O) →
      Integrable fun r => φ r • f (p.1 + r, p.2) := fun f hf =>
    integrable_tconv_Ioo hφc hs hf hp
  have hB : ∀ i, ContinuousOn (fun q => b p.2 i * u1 q (Pi.single i 1)) (Ioo T₀ T₁ ×ˢ O) :=
    fun i => continuousOn_const.mul (hc1 _)
  have hA : ∀ i j, ContinuousOn (fun q => a p.2 i j * u2 q (Pi.single i 1) (Pi.single j 1))
      (Ioo T₀ T₁ ×ˢ O) := fun i j => continuousOn_const.mul (hc2 _ _)
  have hS1 : ContinuousOn (fun q => ∑ i, b p.2 i * u1 q (Pi.single i 1)) (Ioo T₀ T₁ ×ˢ O) :=
    continuousOn_finsetSum _ fun i _ => hB i
  have hS2 : ∀ i, ContinuousOn (fun q => ∑ j, a p.2 i j * u2 q (Pi.single i 1) (Pi.single j 1))
      (Ioo T₀ T₁ ×ˢ O) := fun i => continuousOn_finsetSum _ fun j _ => hA i j
  have hS2' : ContinuousOn (fun q => (1 / 2 : ℝ) *
      ∑ i, ∑ j, a p.2 i j * u2 q (Pi.single i 1) (Pi.single j 1)) (Ioo T₀ T₁ ×ˢ O) :=
    continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => hS2 i)
  have hlin1 : tconv φ (fun q => ∑ i, b p.2 i * u1 q (Pi.single i 1)) p =
      ∑ i, b p.2 i * tconv φ (fun q => u1 q (Pi.single i 1)) p := by
    rw [tconv_sum _ (fun i q => b p.2 i * u1 q (Pi.single i 1)) fun i _ => hint _ (hB i)]
    exact Finset.sum_congr rfl fun i _ => tconv_const_mul _ _
  have hlin2 : ∀ i, tconv φ (fun q => ∑ j, a p.2 i j * u2 q (Pi.single i 1) (Pi.single j 1)) p =
      ∑ j, a p.2 i j * tconv φ (fun q => u2 q (Pi.single i 1) (Pi.single j 1)) p := by
    intro i
    rw [tconv_sum _ (fun j q => a p.2 i j * u2 q (Pi.single i 1) (Pi.single j 1))
      fun j _ => hint _ (hA i j)]
    exact Finset.sum_congr rfl fun j _ => tconv_const_mul _ _
  have hlin3 : tconv φ (fun q => (1 / 2 : ℝ) *
      ∑ i, ∑ j, a p.2 i j * u2 q (Pi.single i 1) (Pi.single j 1)) p =
      (1 / 2 : ℝ) * ∑ i, ∑ j, a p.2 i j * tconv φ (fun q => u2 q (Pi.single i 1)
        (Pi.single j 1)) p := by
    rw [tconv_const_mul, tconv_sum _ (fun i q => ∑ j, a p.2 i j * u2 q (Pi.single i 1)
      (Pi.single j 1)) fun i _ => hint _ (hS2 i)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hlin2 i
  have hwin : tconv φ (fun q => ∑ i, b p.2 i * u1 q (Pi.single i 1) + (1 / 2 : ℝ) *
      ∑ i, ∑ j, a p.2 i j * u2 q (Pi.single i 1) (Pi.single j 1)) p =
      tconv φ (fun q => -ut q) p := by
    refine tconv_congr_window hs fun r hr => ?_
    have h := hpde _ (mem_Ioo_prod_of_shift hp hr)
    simp only [spGen] at h
    linarith
  rw [tconv_add (hint _ hS1) (hint _ hS2'), hlin1, hlin3, tconv_neg, hT] at hwin
  simp only [stGen, ht, hx, hxx]
  rw [add_assoc, hwin]
  ring

/-- **Time mollification of `C^{0,2}` solutions.** The backward mollification `u_ε = tconv φ u` of a `C^{0,2}` solution
of `∂ₜu + 𝓛u = 0` on `(T₀, T₁) × O` is jointly `C²` and solves `stGen b a u_ε = 0` on
`(T₀ + ε, T₁) × O`. -/
theorem IsC02On.tconv (hd : IsC02On u ut u1 u2 (Ioo T₀ T₁ ×ˢ O)) (hO : IsOpen O)
    (hpde : ∀ p ∈ Ioo T₀ T₁ ×ˢ O, spGen b a ut u1 u2 p = 0) (hφ : IsBwdMollifier φ ε)
    (hε : 0 ≤ ε) :
    ContDiffOn ℝ 2 (tconv φ u) (Ioo (T₀ + ε) T₁ ×ˢ O) ∧
      ∀ p ∈ Ioo (T₀ + ε) T₁ ×ˢ O, stGen b a (tconv φ u) p = 0 :=
  ⟨hd.contDiffOn_tconv hO hφ, fun _ hp => hd.stGen_tconv_eq_zero hO hpde hφ hε hp⟩

end PDE

end BlockBand.Diffusion
