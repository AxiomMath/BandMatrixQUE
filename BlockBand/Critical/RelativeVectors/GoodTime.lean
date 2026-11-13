module

public import BlockBand.Critical.RelativeVectors.Backward
public import BlockBand.Critical.RelativeVectors.Central
public import BlockBand.Critical.RelativeVectors.PathSets
public import BlockBand.Palm.FreshPalmShift

/-!
# The generator difference at one time on the good events

* `frameArray_entry_sq_le`, `frameArray_entry_sq_le_Z`:
  `|z_iq|² ≤ Z² := N · N^{2max(A,1)}/(v₀ c_low)` (`z_i = √N V^*u_i`, `‖u_i‖ ≤ 1`,
  `nsq(Ve_q) ≤ N^{2max(A,1)} e_q^*V^*ΓVe_q/(v₀c_low)`: the frame norm itself is only polynomial);
* `abs_dysonCoupling_le_long`: `c_ij ≤ c̄ = N/(c₁²ℓ²)` for `|i-j| ≥ ℓ` (clause 1);
* `exteriorX_le`: the per-label bound `X_ext = c̄N(rZ² + 1)` for every label (used off `J`);
* `windowB_le`: `|z_iq|² ≤ C_comp` on `J` (first line of the interval bound, since
  `|λ_i - E| ≤ ρ ≤ r₀/8` on `J`);
* `refDamping_eq_of_le`, `abs_refDamping_sub_le`: `β̂ = β` on `J` (clause 4), and
  `|β̂ - β| ≤ b₀N/ℓ` everywhere;
* inside `goodTime_genDiff_le` (via `diagonal_sum_swap`): the diagonal relative error bound
  (`diagonal_central_le`) in the form of the hypothesis `hXJ` of `genDiff_rowTail_le`.

`goodTime_genDiff_le`: at one time `σ ∈ [a, c]` of a sample with Hermitian `G_a`, simple
spectrum at `σ`, the interval, distant-label and `𝓡` bounds at `σ` (and the lower count at `a`),
and a reference flow `(𝓜, Ξ)` (`IsReferenceFlow`), for the phase-averaged test `arrayTest ι f`
(`IsC2Bounded 1 f`): `|𝒜g_σ(z_σ) - 𝓛_ref g_σ(z_σ)| ≤ tbQ0 + tbQ1 · R(σ)`, `R(σ)` the tested row
tail of `𝓜_{σ,c}` off the window `J = {j : |j - k₀| ≤ w}`.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.RelativeVectors

open MeasureTheory Matrix Finset Set
open BlockBand.Internal.Contracts.CoareaPalm BlockBand.Internal.Contracts.Transmission
open BlockBand.Palm.CoarseRelative

variable {N r k : ℕ}

/-!
## Instantiation lemmas
-/

theorem frameArray_entry_sq_le (V : Matrix (Fin N) (Fin r) ℂ) (K : Matrix (Fin N) (Fin N) ℂ)
    (i : Fin N) (q : Fin r) :
    ‖frameArray V K i q‖ ^ 2 ≤ N * nsq (V *ᵥ Pi.single q 1) := by
  have h1 : star (Pi.single q (1 : ℂ) : Fin r → ℂ) ⬝ᵥ frameArray V K i = frameArray V K i q := by
    simp [dotProduct, Pi.single_apply]
  have h := norm_star_frameArray_sq V K (Pi.single q 1) i
  rw [h1] at h
  rw [h]
  have hcs : Complex.normSq (star (V *ᵥ Pi.single q 1) ⬝ᵥ freshEigenvector K i) ≤
      nsq (V *ᵥ Pi.single q 1) := by
    rw [Complex.normSq_eq_norm_sq]
    have := norm_star_dot_sq_le (V *ᵥ Pi.single q 1) (freshEigenvector K i)
    have hu := BlockBand.Palm.FreshPalmAssembly.sum_norm_sq_freshEigenvector_le K i
    have h0 : 0 ≤ nsq (V *ᵥ Pi.single q 1) := nsq_nonneg _
    unfold nsq at h0 ⊢
    calc _ ≤ _ := this
      _ ≤ (∑ b, ‖(V *ᵥ Pi.single q 1) b‖ ^ 2) * 1 := mul_le_mul_of_nonneg_left hu h0
      _ = _ := mul_one _
  exact mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg N)

/-- The polynomial frame bound `Z² = N · N^{2max(A,1)}/(v₀ c_low)`. -/
def frameZsq (N : ℕ) (A c s₀ v₀ : ℝ) : ℝ :=
  N * ((N : ℝ) ^ (2 * max A 1) / (v₀ * lowConst c s₀ v₀))

theorem frameZsq_nonneg {A c s₀ v₀ r₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) :
    0 ≤ frameZsq N A c s₀ v₀ := by
  have hv := hK.2.2.2.2.2
  have hl : 0 < lowConst c s₀ v₀ := by
    unfold lowConst
    have : 0 < c - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
    positivity
  unfold frameZsq; positivity

theorem frameArray_entry_sq_le_Z {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N)
    {A c E r₀ s₀ v₀ : ℝ} (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1)
    (K : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) (q : Fin r) :
    ‖frameArray V K i q‖ ^ 2 ≤ frameZsq N A c s₀ v₀ := by
  refine (frameArray_entry_sq_le V K i q).trans ?_
  have h := BlockBand.Palm.MomentFlow.nsq_le_of_gamma hN hK hC (V *ᵥ Pi.single q 1)
  rw [quadForm_column hV q, mul_one] at h
  unfold frameZsq
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)

theorem abs_dysonCoupling_le_long {lam : Fin N → ℝ} {c₁ : ℝ} (hc₁ : 0 < c₁) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ)
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j → c₁ * labelDist i j / N ≤ |lam i - lam j|)
    (i j : Fin N) (hij : ℓ ≤ labelDist i j) :
    |dysonCoupling N lam i j| ≤ (N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) := by
  have hNpos : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact i.elim0
    · exact h
  have hN : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hℓr : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hd : (ℓ : ℝ) ≤ labelDist i j := by exact_mod_cast hij
  have hg := hgap i j hij
  have hlow : c₁ * ℓ / N ≤ |lam i - lam j| :=
    le_trans (by gcongr) hg
  have hpos : 0 < c₁ * ℓ / N := by positivity
  have hsq : (c₁ * ℓ / N) ^ 2 ≤ (lam i - lam j) ^ 2 := by
    rw [← sq_abs (lam i - lam j)]; exact pow_le_pow_left₀ hpos.le hlow 2
  have hd2 : 0 < (lam i - lam j) ^ 2 := lt_of_lt_of_le (by positivity) hsq
  unfold dysonCoupling
  rw [abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (N : ℝ) * (c₁ * ℓ / N) ^ 2 = c₁ ^ 2 * ℓ ^ 2 / N := by field_simp
  have h2 : c₁ ^ 2 * ℓ ^ 2 ≤ N * (N * (lam i - lam j) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ N * N)
    calc c₁ ^ 2 * ℓ ^ 2 = N * N * (c₁ * ℓ / N) ^ 2 := by field_simp
      _ ≤ N * N * (lam i - lam j) ^ 2 := this
      _ = _ := by ring
  linarith

/-- **The exterior per-label bound** `X_ext = c̄N(rZ² + 1)` (every label). -/
theorem exteriorX_le {lam : Fin N → ℝ} {ℓ : ℕ} {cbar Zsq : ℝ} (hc0 : 0 ≤ cbar) (hZ0 : 0 ≤ Zsq)
    (hc : ∀ i j, ℓ ≤ labelDist i j → |dysonCoupling N lam i j| ≤ cbar)
    {z : Fin N → Fin r → ℂ} (hz : ∀ i q, ‖z i q‖ ^ 2 ≤ Zsq) (i : Fin N) (p : Fin r → ℂ) :
    |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N lam i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        cbar * N * (r * Zsq + 1) * nsq p := by
  have hp0 : 0 ≤ nsq p := nsq_nonneg p
  have hterm : ∀ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      |dysonCoupling N lam i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        cbar * ((r * Zsq + 1) * nsq p) := by
    intro j hj
    have hij := (Finset.mem_filter.mp hj).2
    rw [abs_mul]
    refine mul_le_mul (hc i j hij) ?_ (abs_nonneg _) hc0
    have hcs := norm_star_dot_sq_le p (z j)
    have hzs : ∑ b, ‖z j b‖ ^ 2 ≤ r * Zsq := by
      calc ∑ b, ‖z j b‖ ^ 2 ≤ ∑ _b : Fin r, Zsq := Finset.sum_le_sum fun b _ => hz j b
        _ = r * Zsq := by simp
    have h1 : ‖star p ⬝ᵥ z j‖ ^ 2 ≤ nsq p * (r * Zsq) := by
      unfold nsq
      calc _ ≤ (∑ b, ‖p b‖ ^ 2) * ∑ b, ‖z j b‖ ^ 2 := hcs
        _ ≤ _ := mul_le_mul_of_nonneg_left hzs (Finset.sum_nonneg fun b _ => by positivity)
    have h0 : 0 ≤ ‖star p ⬝ᵥ z j‖ ^ 2 := by positivity
    rw [abs_le]
    constructor <;> nlinarith
  calc _ ≤ ∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
        |dysonCoupling N lam i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ univ.filter (fun j => ℓ ≤ labelDist i j), cbar * ((r * Zsq + 1) * nsq p) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ _j : Fin N, cbar * ((r * Zsq + 1) * nsq p) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => ?_
        have : 0 ≤ (r : ℝ) * Zsq + 1 := by positivity
        positivity
    _ = cbar * N * (r * Zsq + 1) * nsq p := by simp; ring

theorem windowB_le {V : Matrix (Fin N) (Fin r) ℂ} {H : Matrix (Fin N) (Fin N) ℂ} {E r₀ Ccomp : ℝ}
    (hwin : ∀ i : Fin N, |freshEigenvalue H i - E| ≤ r₀ / 2 →
      ∑ b, ‖frameArray V H i b‖ ^ 2 ≤ Ccomp)
    {i : Fin N} (hi : |freshEigenvalue H i - E| ≤ r₀ / 2) (q : Fin r) :
    ‖frameArray V H i q‖ ^ 2 ≤ Ccomp :=
  le_trans (Finset.single_le_sum (f := fun b => ‖frameArray V H i b‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ q)) (hwin i hi)

theorem longCoupling_nonneg (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (ℓ : ℕ)
    (σ : ℝ) (i : Fin N) : 0 ≤ longCoupling F a ω ℓ σ i := by
  unfold longCoupling flowRate
  exact Finset.sum_nonneg fun j _ => by positivity

theorem abs_refDamping_sub_le (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) {b₀ : ℝ} (hb : 0 ≤ b₀)
    (ω : FlowSample N) (ℓ : ℕ) (σ : ℝ) (i : Fin N) :
    |refDamping F a b₀ ω ℓ σ i - longCoupling F a ω ℓ σ i| ≤ b₀ * N / ℓ := by
  have h0 := longCoupling_nonneg F a ω ℓ σ i
  have hb' : 0 ≤ b₀ * N / ℓ := by positivity
  unfold refDamping
  rw [abs_le]
  constructor
  · linarith [le_max_left (longCoupling F a ω ℓ σ i) (b₀ * N / ℓ)]
  · have := max_le (by linarith : longCoupling F a ω ℓ σ i ≤ longCoupling F a ω ℓ σ i + b₀ * N / ℓ)
      (by linarith : b₀ * N / ℓ ≤ longCoupling F a ω ℓ σ i + b₀ * N / ℓ)
    linarith

theorem refDamping_eq_of_le {F : Matrix (Fin N) (Fin N) ℂ} {a b₀ : ℝ} {ω : FlowSample N}
    {ℓ : ℕ} {σ : ℝ} {i : Fin N} (h : b₀ * N / ℓ ≤ longCoupling F a ω ℓ σ i) :
    refDamping F a b₀ ω ℓ σ i = longCoupling F a ω ℓ σ i :=
  max_eq_left h

/-- The window `J = {j : |j - k₀| ≤ w}`, `k₀ = #{l : λ_l(a) ≤ E}` (as in
`RelativeLocalizationContract.reference_finite_speed`). -/
def rmvWindow (F : Matrix (Fin N) (Fin N) ℂ) (a : ℝ) (ω : FlowSample N) (E : ℝ) (w : ℕ) :
    Finset (Fin N) :=
  univ.filter fun j : Fin N => Int.natAbs ((j : ℤ) -
    ((univ.filter fun l : Fin N => flowEigenvalue F a ω a l ≤ E).card : ℤ)) ≤ w

/-- The constant of the diagonal relative error bound (`diagonal_central_le`). -/
def diagXJ (N : ℕ) (c r₀ s₀ v₀ t : ℝ) (ℓ w : ℕ) (c₁ Csp Mint Cd : ℝ) : ℝ :=
  2 * (Mint * (N / (c₁ ^ 2 * ℓ ^ 2))) +
    gammaShiftConst c r₀ s₀ v₀ * (2 * (1 + Real.log N) / c₁ +
      4 / c₁ ^ 2 * ((4 / c₁ + Csp + 1) * ((N : ℝ) / ℓ * (t + (w : ℝ) / N)) + 2)) +
    Cd + 64 / r₀ ^ 2

/-- The constant part of the one-time bound. -/
def tbQ0 (N r k : ℕ) (XJ B Z cbar bf ε : ℝ) : ℝ :=
  2 * (r : ℝ) ^ 2 * k * XJ + ((k : ℝ) * r) ^ 2 * (B * (Real.sqrt 2 * cbar)) +
    Z * Z * (cbar * N) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 * ε + bf * (1 / 2 * Z) * ((N : ℝ) * ε / 2)

/-- The row-tail coefficient of the one-time bound. -/
def tbQ1 (N r k : ℕ) (Xext Z cbar bf ε : ℝ) : ℝ :=
  2 * (r : ℝ) ^ 2 * Xext + bf * (1 / 2 * r) + Z * Z * (cbar * N) * (r : ℝ) ^ 2 * (k : ℝ) ^ 2 / ε +
    bf * (1 / 2 * Z) / (2 * ε)

theorem diagonal_sum_swap (lam : Fin N → ℝ) (ℓ : ℕ) (x : Fin N → ℝ) (j : Fin N) :
    ∑ i ∈ univ.filter (fun i => ℓ ≤ labelDist j i), dysonCoupling N lam j i * x i =
      ∑ i ∈ univ.filter (fun i => ℓ ≤ labelDist i j), x i / (N * (lam i - lam j) ^ 2) := by
  have hf : univ.filter (fun i => ℓ ≤ labelDist j i) = univ.filter (fun i => ℓ ≤ labelDist i j) := by
    ext i; simp [labelDist_symm j i]
  rw [hf]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold dysonCoupling
  rw [show (lam j - lam i) ^ 2 = (lam i - lam j) ^ 2 by ring]
  ring

/-- **The generator difference at one good time.** See the module docstring. -/
theorem goodTime_genDiff_le {F : Matrix (Fin N) (Fin N) ℂ} (hN : 0 < N) {A c E r₀ s₀ v₀ : ℝ}
    (hK : FreshConstants c r₀ s₀ v₀) (hC : FreshClass F A c E r₀ s₀ v₀)
    {V : Matrix (Fin N) (Fin r) ℂ} (hV : Vᴴ * freshGamma F c E * V = 1)
    {a t : ℝ} (hat : a = c - t) (ht : 0 ≤ t) (hts : t ≤ s₀)
    {ℓ w : ℕ} (hℓ : 1 ≤ ℓ) (hw : 1 ≤ w) (hsq : Real.sqrt t ≤ (w : ℝ) / N)
    {c₁ Csp b₀ Ccomp Cd Mint : ℝ} (hc₁ : 0 < c₁) (hCsp : 0 ≤ Csp) (hb₀ : 0 < b₀)
    (hCcomp : 0 ≤ Ccomp) (hCd : 0 ≤ Cd) (hMint : 0 ≤ Mint) (hρ8 : centralRho N w ℓ c₁ Csp t ≤ r₀ / 8)
    {ω : FlowSample N} (hω : ω.1.IsHermitian) {σ : ℝ} (hσ : σ ∈ Icc a c)
    (hsimple : StrictMono (flowEigenvalue F a ω σ))
    (hlow : ∀ x y : ℝ, E - r₀ / 8 ≤ x → y ≤ E + r₀ / 8 → (ℓ : ℝ) / N ≤ y - x →
      c₁ * N * (y - x) ≤
        ((univ.filter fun i : Fin N => flowEigenvalue F a ω a i ∈ Icc x y).card : ℝ))
    (hdisp : ∀ x : Fin N → ℂ, l2Norm ((flowMatrix F a ω σ - flowMatrix F a ω a) *ᵥ x) ≤
      Csp * Real.sqrt t * l2Norm x)
    (hgap : ∀ i j : Fin N, ℓ ≤ labelDist i j →
      c₁ * (labelDist i j : ℝ) / N ≤ |flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j|)
    (hbeta : ∀ i : Fin N, |flowEigenvalue F a ω σ i - E| ≤ r₀ / 8 →
      b₀ * N / ℓ ≤ longCoupling F a ω ℓ σ i)
    (hwin : ∀ i : Fin N, |flowEigenvalue F a ω σ i - E| ≤ r₀ / 2 →
      ∑ b, ‖frameArray V (flowMatrix F a ω σ) i b‖ ^ 2 ≤ Ccomp)
    (hdist : ∀ j : Fin N, |flowEigenvalue F a ω σ j - E| ≤ r₀ / 8 → ∀ q : Fin r → ℂ,
      ∑ i ∈ univ.filter (fun i => r₀ / 4 < |flowEigenvalue F a ω σ i - E|),
        ‖star q ⬝ᵥ frameArray V (flowMatrix F a ω σ) i‖ ^ 2 /
          ((N : ℝ) * (flowEigenvalue F a ω σ i - flowEigenvalue F a ω σ j) ^ 2) ≤
        Cd * ∑ b, ‖q b‖ ^ 2)
    (hint : ∀ x y : ℝ, E - r₀ / 4 ≤ x → x ≤ y → y ≤ E + r₀ / 4 → ∀ p : Fin r → ℂ,
      |∑ i ∈ univ.filter (fun i => flowEigenvalue F a ω σ i ∈ Icc x y),
          (‖star p ⬝ᵥ frameArray V (flowMatrix F a ω σ) i‖ ^ 2 -
            quadForm (freshGamma F σ (flowEigenvalue F a ω σ i)) (V *ᵥ p))| ≤ Mint * nsq p)
    {Ωaux : Type} [MeasurableSpace Ωaux] {Paux : Measure Ωaux} [IsProbabilityMeasure Paux]
    {𝓜 : ℝ → ℝ → Ωaux → Matrix (Fin N) (Fin N) ℂ} {Ξ : ℝ → ℝ → Ωaux → Fin N → Fin r → ℂ}
    (hR : IsReferenceFlow F a c b₀ ℓ ω Paux 𝓜 Ξ)
    (ι : Fin k → Fin N) {f : MarkArray k r → ℝ} (hf : IsC2Bounded 1 f) {ε : ℝ} (hε : 0 < ε) :
    |complexAngularGenerator N r (flowEigenvalue F a ω σ)
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 σ c ω') z + Ξ σ c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω σ)) -
      referenceArrayGenerator F a b₀ ω ℓ σ
        (fun z => ∫ ω', arrayTest ι f (arrayMul (𝓜 σ c ω') z + Ξ σ c ω') ∂Paux)
        (frameArray V (flowMatrix F a ω σ))| ≤
      tbQ0 N r k (diagXJ N c r₀ s₀ v₀ t ℓ w c₁ Csp Mint Cd) Ccomp
          (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε +
        tbQ1 N r k ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) * N * (r * frameZsq N A c s₀ v₀ + 1))
            (Real.sqrt (frameZsq N A c s₀ v₀)) ((N : ℝ) / (c₁ ^ 2 * ℓ ^ 2)) (b₀ * N / ℓ) ε *
          testedTail Paux ι (𝓜 σ c) (rmvWindow F a ω E w) := by
  set H := flowMatrix F a ω σ with hH
  set Ha := flowMatrix F a ω a with hHa
  set z := frameArray V H with hz
  set J := rmvWindow F a ω E w with hJ
  set Zsq := frameZsq N A c s₀ v₀ with hZsq
  set cbar : ℝ := (N : ℝ) / (c₁ ^ 2 * ℓ ^ 2) with hcbar
  have hFh := hC.1
  have hHh : H.IsHermitian := ps_flowMatrix_isHermitian hFh a hω σ
  have hHah : Ha.IsHermitian := ps_flowMatrix_isHermitian hFh a hω a
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hℓr : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hZ0 : 0 ≤ Zsq := frameZsq_nonneg hK
  have hc0 : 0 ≤ cbar := by positivity
  have hd : centralWidth N w ℓ c₁ ≤ r₀ / 8 := by
    have : 0 ≤ Csp * Real.sqrt t := by positivity
    unfold centralRho at hρ8; linarith
  have hr₀ : 0 < r₀ := hK.2.2.1
  -- central labels are in the bulk
  have hcent : ∀ j ∈ J, |freshEigenvalue H j - E| ≤ r₀ / 8 := by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    have := central_close_flow hHah hHh hN hc₁ hlow (D₀ := Csp * Real.sqrt t) hdisp hd j hj'
    exact this.trans hρ8
  have hS := testedSetting_reference hR hb₀.le hσ ι hf
  have hg := contDiff_backward hR hσ ι hf
  have hinv := hinv_reference hR hσ ι hf
  have hrow := rows_reference hR hb₀.le hσ.1 hσ.2 le_rfl
  have hc : ∀ i j, ℓ ≤ labelDist i j → |dysonCoupling N (flowEigenvalue F a ω σ) i j| ≤ cbar :=
    abs_dysonCoupling_le_long hc₁ hℓ hgap
  have hzZ : ∀ i q, ‖z i q‖ ^ 2 ≤ Zsq := fun i q =>
    frameArray_entry_sq_le_Z hN hK hC hV H i q
  have hz : ∀ i q, ‖z i q‖ ≤ Real.sqrt Zsq := fun i q =>
    Real.le_sqrt_of_sq_le (hzZ i q)
  have hzJ : ∀ i ∈ J, ∀ q, ‖z i q‖ ^ 2 ≤ Ccomp := by
    intro i hi q
    exact windowB_le hwin (le_trans (hcent i hi) (by linarith)) q
  have hXJ : ∀ i ∈ J, ∀ p : Fin r → ℂ, |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N (flowEigenvalue F a ω σ) i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        diagXJ N c r₀ s₀ v₀ t ℓ w c₁ Csp Mint Cd * nsq p := by
    intro j hj p
    rw [diagonal_sum_swap]
    have hs : σ ∈ Icc (c - s₀) c := ⟨by rw [hat] at hσ; linarith [hσ.1], hσ.2⟩
    have hst : c - t ≤ σ := by rw [hat] at hσ; exact hσ.1
    have hj' := (Finset.mem_filter.mp hj).2
    exact diagonal_central_le hN hK hC hV hs hst ht hHah hHh hsimple hc₁ hCsp hℓ hw hsq hρ8
      hlow hdisp hgap p (fun x y hx hxy hy => hint x y hx hxy hy p) j hj'
      (hdist j (hcent j hj) p)
  have hXext : ∀ i ∉ J, ∀ p : Fin r → ℂ, |∑ j ∈ univ.filter (fun j => ℓ ≤ labelDist i j),
      dysonCoupling N (flowEigenvalue F a ω σ) i j * (‖star p ⬝ᵥ z j‖ ^ 2 - nsq p)| ≤
        cbar * N * (r * Zsq + 1) * nsq p :=
    fun i _ p => exteriorX_le hc0 hZ0 hc hzZ i p
  have hfl : ∀ i ∈ J, refDamping F a b₀ ω ℓ σ i = longCoupling F a ω ℓ σ i :=
    fun i hi => refDamping_eq_of_le (hbeta i (hcent i hi))
  have hbf : ∀ i, |refDamping F a b₀ ω ℓ σ i - longCoupling F a ω ℓ σ i| ≤ b₀ * N / ℓ :=
    abs_refDamping_sub_le F a hb₀.le ω ℓ σ
  have hXJ0 : 0 ≤ diagXJ N c r₀ s₀ v₀ t ℓ w c₁ Csp Mint Cd := by
    have hCγ : 0 ≤ gammaShiftConst c r₀ s₀ v₀ := by
      have hκ'0 : 0 < c - s₀ := by linarith [hK.2.2.2.2.1, hK.1]
      have hv0 := hK.2.2.2.2.2
      have hc0 := hK.1
      have hs0 := hK.2.2.2.1
      unfold gammaShiftConst
      positivity
    have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
    unfold diagXJ
    positivity
  have h := genDiff_rowTail_le ι hS hg hinv hrow F a b₀ ω hℓ σ z J hCcomp (Real.sqrt_nonneg _)
    hzJ hz hc0 hc hXJ0 hXJ hXext (by positivity) hfl hbf hε
  refine h.trans (le_of_eq ?_)
  unfold tbQ0 tbQ1
  ring

end BlockBand.Critical.RelativeVectors
