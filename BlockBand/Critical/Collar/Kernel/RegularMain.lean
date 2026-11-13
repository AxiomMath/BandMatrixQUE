module

public import BlockBand.Critical.Collar.Kernel.RegularHeight
public import BlockBand.Critical.Collar.Density.SecondMoment

/-!
# The regular clause of the collar kernel bound from the regular clause of the collar density bound

**Reduction** `collarKernelRegularClause_of_density`: if the regular clause of the collar density
bound holds (`Density.CollarDensityRegularClause`, for every `b ∈ (0,1/2)` and `κ > 0`, with some
constants), then the regular clause `CollarKernelRegularClause` of the collar kernel bound holds
(strict and radial forms, every height `0 ≤ ν ≤ 1`, shift `|s| ≤ s₀`). With
`collarKernel_of_regular` this gives `collarKernel_holds_of_densityRegular : CollarKernelContract`.

Proof outline: strict clause through the fresh-row resolvent form and the Cauchy dilation;
regular phases `d(X_t) ≤ d_*/2` by the kernel identity, the energy window (stability of `z_b`, `a`,
`d(·)` on `|x| ≤ δ`) and the regular density clause at the energies `e + s + x ∈ bulkInterval (κ/2)`
(`Density.lintegral_collarRow_le_of_regular'`); exceptional phases of Cauchy mass `≤ C g/W` by
`stdCauchy_matchedDistance_gt_le`, paid by the universal fresh-row bound `C√W`. Positive height
through `weightedBoundaryIdentity_general` at `ε = ν`
(`lintegral_collarKernel_quad_le_height_phases`), with the `W`-uniform height-one tail
(`Density.SecondMoment`). Radial clause by the Cayley inverse `radialOld`
(`g(tr) ≤ g(r) + 2W(1-t²)`, `d(X') ≤ d(X) + (1-t)/(2η)`).
-/

set_option autoImplicit false

@[expose] public section
noncomputable section

namespace BlockBand.Critical.Collar.Kernel

open MeasureTheory Matrix Filter Topology
open BlockBand.Internal.Contracts
open BlockBand.Internal.Contracts.Layers
open BlockBand.Critical.Collar.Density
open scoped ComplexOrder ENNReal

variable {W : ℕ}

theorem star_boundaryZ_add_collarShift (b e s ν : ℝ) :
    star (boundaryZ b e + Critical.collarShift e s ν) =
      star (boundaryZ b e - (ν : ℂ) * Complex.I) + ((e + s : ℝ) : ℂ) := by
  simp only [Critical.collarShift, star_add, star_sub, Complex.star_def, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The energy window: for `e ∈ bulkInterval κ`, `|s|, |x| ≤ δ ≤ κ/8` and `d_e(X') ≤ d₁`,
`e + s + x` lies in `bulkInterval (κ/2)` with `d_{e+s+x}(X') ≤ d₁ + 2δL`, `Im z_b(e+s+x) ≥ η_m`
and `|z - x - z_b(e+s+x)| ≤ 8` whenever `|z| ≤ 4`. -/
theorem window_conditions {b κ : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) (hκ : 0 < κ) {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ κ / 8) (hW : 0 < W) {e s : ℝ} (he : e ∈ bulkInterval κ)
    (hs : |s| ≤ δ) {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hX : X.IsHermitian) {z : ℂ}
    (hz : ‖z‖ ≤ 4) {x : ℝ} (hx : |x| ≤ δ) :
    let κm := min (κ / 2) 1
    let S := 4 - (2 - κm) ^ 2
    let ηm := (1 - b) * Real.sqrt S / 2
    let La := 1 / 2 + 1 / Real.sqrt S
    let L := (1 + (1 - b) * La) / ηm ^ 2 + La
    e + s + x ∈ bulkInterval (κ / 2) ∧
      matchedDistance b (e + s + x) X ≤ matchedDistance b e X + L * (2 * δ) ∧
      ηm ≤ (boundaryZ b (e + s + x)).im ∧ ‖z - x - boundaryZ b (e + s + x)‖ ≤ 8 := by
  intro κm S ηm La L
  have hκ2 : κ ≤ 2 := le_two_of_mem_bulkInterval he
  have hκm : 0 < κm := lt_min (by linarith) one_pos
  have hκm1 : κm ≤ 1 := min_le_right _ _
  have hκmκ : κm ≤ κ / 2 := min_le_left _ _
  have hS : 0 < S := BlockBand.Layers.four_sub_sq_pos hκm (by linarith)
  have hηm : 0 < ηm := by
    have : 0 < 1 - b := by linarith
    have := Real.sqrt_pos.2 hS
    positivity
  have hsx : |s + x| ≤ 2 * δ := (abs_add_le s x).trans (by linarith)
  have hmem : e + s + x ∈ bulkInterval (κ / 2) := by
    have h1 := he.1; have h2 := he.2
    have := abs_le.1 hsx
    constructor <;> linarith
  have hmemm : e + s + x ∈ bulkInterval κm := ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hem : e ∈ bulkInterval κm := ⟨by linarith [he.1], by linarith [he.2]⟩
  have hη'' : ηm ≤ (boundaryZ b (e + s + x)).im :=
    BlockBand.Layers.boundaryZ_im_ge_of_mem_bulkInterval hb1.le hκm hmemm
  have hη : ηm ≤ (boundaryZ b e).im :=
    BlockBand.Layers.boundaryZ_im_ge_of_mem_bulkInterval hb1.le hκm hem
  refine ⟨hmem, ?_, hη'', ?_⟩
  · have hd := matchedDistance_le_energy (b := b) (E := e) (E' := e + s + x) hW hX
      (hηm.trans_le hη) (hηm.trans_le hη'')
    have hz := norm_boundaryZ_sub_le hb1.le hκm hem hmemm
    have ha := norm_matchedA_sub_le hκm hmemm hem
    have hee : |e - (e + s + x)| ≤ 2 * δ := by
      rw [show e - (e + s + x) = -(s + x) by ring, abs_neg]; exact hsx
    have hee' : |e + s + x - e| ≤ 2 * δ := by
      rw [show e + s + x - e = s + x by ring]; exact hsx
    have hinv : ((boundaryZ b (e + s + x)).im * (boundaryZ b e).im)⁻¹ ≤ (ηm ^ 2)⁻¹ := by
      refine inv_anti₀ (by positivity) ?_
      rw [sq]; exact mul_le_mul hη'' hη hηm.le (hηm.le.trans hη'')
    have hLa : 0 ≤ La := by have := Real.sqrt_pos.2 hS; positivity
    have hLz : 0 ≤ 1 + (1 - b) * La := by
      have : 0 ≤ 1 - b := by linarith
      positivity
    calc matchedDistance b (e + s + x) X
        ≤ matchedDistance b e X + ‖boundaryZ b e - boundaryZ b (e + s + x)‖ *
            ((boundaryZ b (e + s + x)).im * (boundaryZ b e).im)⁻¹ +
              ‖matchedA (e + s + x) - matchedA e‖ := hd
      _ ≤ matchedDistance b e X + ((1 + (1 - b) * La) * (2 * δ)) * (ηm ^ 2)⁻¹ + La * (2 * δ) := by
          have hz' := hz.trans (mul_le_mul_of_nonneg_left hee hLz)
          have ha' := ha.trans (mul_le_mul_of_nonneg_left hee' hLa)
          have hpos : 0 ≤ ((boundaryZ b (e + s + x)).im * (boundaryZ b e).im)⁻¹ :=
            inv_nonneg.2 (mul_nonneg (hηm.le.trans hη'') (hηm.le.trans hη))
          exact add_le_add (add_le_add le_rfl (mul_le_mul hz' hinv hpos
            (mul_nonneg hLz (by linarith)))) ha'
      _ = matchedDistance b e X + L * (2 * δ) := by
          simp only [L]; ring
  · have hx1 : |x| ≤ 1 := hx.trans (by linarith)
    have hb3 := BlockBand.Layers.norm_boundaryZ_le hb0 hb1.le
      (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval (by linarith : (0 : ℝ) < κ / 2) hmem).le
    calc ‖z - x - boundaryZ b (e + s + x)‖ ≤ ‖z‖ + ‖(x : ℂ)‖ + ‖boundaryZ b (e + s + x)‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_sub_le _ _
      _ ≤ 4 + 1 + 3 := by
          gcongr
          rw [Complex.norm_real, Real.norm_eq_abs]; exact hx1
      _ = 8 := by norm_num

/-!
## Constants
-/

/-- `η_m = (1-b)√(4-(2-κ_m)²)/2`, `κ_m = min(κ/2, 1)`: lower bound of `Im z_b` on `bulkInterval (κ/2)`. -/
def regEtaM (b κ : ℝ) : ℝ := (1 - b) * Real.sqrt (4 - (2 - min (κ / 2) 1) ^ 2) / 2

/-- Lipschitz constant of `a` on the window. -/
def regLa (κ : ℝ) : ℝ := 1 / 2 + 1 / Real.sqrt (4 - (2 - min (κ / 2) 1) ^ 2)

/-- Energy-stability constant of `d(·)` on the window. -/
def regL (b κ : ℝ) : ℝ := (1 + (1 - b) * regLa κ) / regEtaM b κ ^ 2 + regLa κ

/-- The window half-width `δ = min(κ/8, d_*/(8(|L|+1)))`. -/
def regDelta (b κ dstar : ℝ) : ℝ := min (κ / 8) (dstar / (8 * (|regL b κ| + 1)))

theorem regEtaM_pos {b κ : ℝ} (hb1 : b < 1) (hκ : 0 < κ) : 0 < regEtaM b κ := by
  have hκm : 0 < min (κ / 2) 1 := lt_min (by linarith) one_pos
  have hS : 0 < 4 - (2 - min (κ / 2) 1) ^ 2 :=
    BlockBand.Layers.four_sub_sq_pos hκm (by linarith [min_le_right (κ / 2) 1])
  have : 0 < 1 - b := by linarith
  have := Real.sqrt_pos.2 hS
  unfold regEtaM; positivity

theorem regDelta_pos {b κ dstar : ℝ} (hκ : 0 < κ) (hd : 0 < dstar) : 0 < regDelta b κ dstar := by
  unfold regDelta
  exact lt_min (by linarith) (by positivity)

theorem regL_mul_regDelta_le (b : ℝ) {κ dstar : ℝ} (hκ : 0 < κ) (hd : 0 < dstar) :
    regL b κ * (2 * regDelta b κ dstar) ≤ dstar / 4 := by
  have h1 : regDelta b κ dstar ≤ dstar / (8 * (|regL b κ| + 1)) := min_le_right _ _
  have h0 := (regDelta_pos (b := b) hκ hd).le
  have hL : 0 ≤ |regL b κ| := abs_nonneg _
  calc regL b κ * (2 * regDelta b κ dstar) ≤ |regL b κ| * (2 * regDelta b κ dstar) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    _ ≤ |regL b κ| * (2 * (dstar / (8 * (|regL b κ| + 1)))) := by gcongr
    _ = dstar / 4 * (|regL b κ| / (|regL b κ| + 1)) := by field_simp; ring
    _ ≤ dstar / 4 * 1 := by
        gcongr
        rw [div_le_one (by positivity)]; linarith
    _ = dstar / 4 := mul_one _

/-- The kernel constant `C_K = η_m⁻¹(2πA₀ + 2πK₀ + 2 + 2 C_exc C_{b,7}/(d₁/2)²)`, `d₁ = d_*/2`. -/
def regCK (b κ dstar Cr Cexc : ℝ) : ℝ :=
  (regEtaM b κ)⁻¹ * (2 * Real.pi * (2 * max Cr 0 * (1 + 8 ^ 2 / regEtaM b κ ^ 2)) +
    2 * Real.pi * ((1 + (regDelta b κ dstar)⁻¹ ^ 2) * Real.pi⁻¹ *
      (2 * 7 ^ 2 + 2 * (1 - 2 * b) + b)) + 2 +
    2 * Cexc * collarRowConst b ((7 : ℝ) : ℂ) / (dstar / 2 / 2) ^ 2)

theorem regCK_nonneg {b κ dstar Cr Cexc : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (hκ : 0 < κ)
    (hd : 0 < dstar) (hC : 0 ≤ Cexc) : 0 ≤ regCK b κ dstar Cr Cexc := by
  have := regEtaM_pos (b := b) (by linarith) hκ
  have := regDelta_pos (b := b) hκ hd
  have := collarRowConst_nonneg hb0.le ((7 : ℝ) : ℂ)
  have := Real.pi_pos
  have : 0 ≤ max Cr 0 := le_max_right _ _
  have : 0 ≤ 1 - 2 * b := by linarith
  unfold regCK; positivity

set_option maxHeartbeats 800000 in
/-- **Regular quadratic-form bound** for every height `0 ≤ ν ≤ 1` (`Y ⪰ 0`, and `Y ≻ 0` if
`ν = 0`), shift `|s| ≤ δ`, `d(X) ≤ d₁/2`, `d₁ = d_*/2`:
`E Re q*𝒫(Ur)q ≤ C_K (1 + g) ‖q‖²`. -/
theorem lintegral_collarKernel_quad_le_regular {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) {dstar Cr : ℝ} {W₀ : ℕ} (hd : 0 < dstar)
    (hR : CollarDensityRegularClause b (κ / 2) dstar Cr W₀) {Cexc : ℝ} (hCexc : 0 ≤ Cexc)
    (hexc : ∀ (W : ℕ), 0 < W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-Critical.imPart X).PosSemidef →
      ∀ d₁ : ℝ, 0 < d₁ → matchedDistance b e X ≤ d₁ / 2 →
        stdCauchy {t : ℝ | d₁ < matchedDistance b e (rePart X + (t : ℂ) • (-Critical.imPart X))} ≤
          ENNReal.ofReal (Cexc * Critical.conductance (Critical.oldScattering b e X) /
            (W * (d₁ / 2) ^ 2)))
    (hW : 0 < W) (hW₀ : W₀ ≤ W) {e : ℝ} (he : e ∈ bulkInterval κ) {s : ℝ}
    (hs : |s| ≤ regDelta b κ dstar) {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosSemidef)
    (hYν : ν = 0 → (-Critical.imPart X).PosDef) (hdX : matchedDistance b e X ≤ dstar / 2 / 2)
    (q : Fin 2 × Fin W → ℂ) :
    ∫⁻ ω, ENNReal.ofReal (star q ⬝ᵥ (Critical.poissonKernel (Critical.collarScattering b e s ν ω *
        Critical.oldScattering b e X) *ᵥ q)).re ∂Critical.collarLaw W b ≤
      ENNReal.ofReal (regCK b κ dstar Cr Cexc *
        (1 + Critical.conductance (Critical.oldScattering b e X)) * ∑ x, ‖q x‖ ^ 2) := by
  set δ := regDelta b κ dstar
  set d₁ := dstar / 2 with hd₁def
  set ηm := regEtaM b κ
  set Sq := ∑ x, ‖q x‖ ^ 2
  set g := Critical.conductance (Critical.oldScattering b e X)
  set A₀ := 2 * max Cr 0 * (1 + 8 ^ 2 / ηm ^ 2)
  set K₀ := (1 + δ⁻¹ ^ 2) * Real.pi⁻¹ * (2 * 7 ^ 2 + 2 * (1 - 2 * b) + b)
  set Cw := collarRowConst b ((7 : ℝ) : ℂ)
  have hSq : 0 ≤ Sq := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hδ : 0 < δ := regDelta_pos hκ hd
  have hδκ : δ ≤ κ / 8 := min_le_left _ _
  have hηm : 0 < ηm := regEtaM_pos (by linarith) hκ
  have hd₁ : 0 < d₁ := by positivity
  have hκ2 : κ ≤ 2 := le_two_of_mem_bulkInterval he
  have hem : e ∈ bulkInterval (min (κ / 2) 1) := ⟨by linarith [he.1, min_le_left (κ / 2) 1],
    by linarith [he.2, min_le_left (κ / 2) 1]⟩
  have hηe : ηm ≤ (boundaryZ b e).im :=
    BlockBand.Layers.boundaryZ_im_ge_of_mem_bulkInterval (by linarith)
      (lt_min (by linarith) one_pos) hem
  have hη : 0 < (boundaryZ b e).im := hηm.trans_le hηe
  have he2 : |e| ≤ 2 := (BlockBand.Layers.abs_lt_two_of_mem_bulkInterval hκ he).le
  have hzb : ‖boundaryZ b e‖ ≤ 3 := BlockBand.Layers.norm_boundaryZ_le hb0.le (by linarith) he2
  have hs1 : |s| ≤ 1 := hs.trans (by linarith)
  have hes : |e + s| ≤ 3 := (abs_add_le e s).trans (by linarith)
  have hg : 0 ≤ g := conductance_oldScattering_nonneg b e hη hY
  have hA₀ : 0 ≤ A₀ := by have : 0 ≤ max Cr 0 := le_max_right _ _
                          positivity
  have hK₀ : 0 ≤ K₀ := by have := Real.pi_pos; have : 0 ≤ 1 - 2 * b := by linarith
                          positivity
  have hCw : 0 ≤ Cw := collarRowConst_nonneg hb0.le _
  -- the window on the regular phases
  have hwin : ∀ t : ℝ, matchedDistance b e (rePart X + (t : ℂ) • (-Critical.imPart X)) ≤ d₁ →
      ∀ z : ℂ, ‖z‖ ≤ 4 → ∀ x : ℝ, |x| ≤ δ →
        (e + s) + x ∈ bulkInterval (κ / 2) ∧
          matchedDistance b ((e + s) + x) (rePart X + (t : ℂ) • (-Critical.imPart X)) ≤ dstar ∧
          ηm ≤ (boundaryZ b ((e + s) + x)).im ∧ ‖z - x - boundaryZ b ((e + s) + x)‖ ≤ 8 := by
    intro t ht z hz x hx
    obtain ⟨h1, h2, h3, h4⟩ := window_conditions (W := W) hb0.le (by linarith) hκ hδ.le hδκ hW he hs
      (dilatedOld_isHermitian X t) hz hx
    refine ⟨h1, h2.trans ?_, h3, h4⟩
    have := regL_mul_regDelta_le b hκ hd
    change matchedDistance b e (rePart X + (t : ℂ) • (-Critical.imPart X)) +
      regL b κ * (2 * δ) ≤ dstar
    linarith [hd₁def]
  have hbad := hexc W hW e he X hY d₁ hd₁ hdX
  set m := Cexc * g / (W * (d₁ / 2) ^ 2)
  have hm : 0 ≤ m := by positivity
  have hWr : (1 : ℝ) ≤ W := by exact_mod_cast hW
  have hmB : ∀ w : ℂ, ‖w‖ ≤ 7 → m * (collarRowConst b w * Real.sqrt W * Sq) ≤
      Cexc * Cw / (d₁ / 2) ^ 2 * g * Sq := by
    intro w hw
    have hcw : collarRowConst b w ≤ Cw := collarRowConst_mono b (by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 7)]; exact hw)
    have hsq : Real.sqrt W ≤ W := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    have hWpos : (0 : ℝ) < W := by linarith
    calc m * (collarRowConst b w * Real.sqrt W * Sq)
        ≤ m * (Cw * W * Sq) := by
          have := collarRowConst_nonneg hb0.le w
          gcongr
      _ = Cexc * Cw / (d₁ / 2) ^ 2 * g * Sq := by
          simp only [m]; field_simp
  have hfin : ∀ R : ℝ, 0 ≤ R → R ≤ (2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 +
      2 * Cexc * Cw / (d₁ / 2) ^ 2) * (1 + g) * Sq →
      ENNReal.ofReal ((boundaryZ b e).im⁻¹ * R) ≤
        ENNReal.ofReal (regCK b κ dstar Cr Cexc * (1 + g) * Sq) := by
    intro R hR0 hR
    refine ENNReal.ofReal_le_ofReal ?_
    have hinv : (boundaryZ b e).im⁻¹ ≤ ηm⁻¹ := inv_anti₀ hηm hηe
    calc (boundaryZ b e).im⁻¹ * R ≤ ηm⁻¹ * R := mul_le_mul_of_nonneg_right hinv hR0
      _ ≤ ηm⁻¹ * ((2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 + 2 * Cexc * Cw / (d₁ / 2) ^ 2) *
            (1 + g) * Sq) := mul_le_mul_of_nonneg_left hR (inv_nonneg.2 hηm.le)
      _ = regCK b κ dstar Cr Cexc * (1 + g) * Sq := by simp only [regCK]; ring
  have hX1 : 0 ≤ Cexc * Cw / (d₁ / 2) ^ 2 := by positivity
  rcases eq_or_lt_of_le hν0 with hν | hν
  · -- zero height: the strict phases lemma
    subst hν
    have h := lintegral_collarKernel_quad_le_phases hb0 hb hW e s hη (hYν rfl) q
      (d₁ := d₁) (A := A₀ * Sq) (K := K₀ * Sq) (m := m) (by positivity) hm ?_ hbad
    · have hR0 : 0 ≤ Real.pi * (A₀ * Sq) + m * (collarRowConst b (rowCoeff b e s) *
          Real.sqrt W * Sq) := by
        have := collarRowConst_nonneg hb0.le (rowCoeff b e s)
        positivity
      refine h.trans (hfin _ hR0 ?_)
      have hw : ‖rowCoeff b e s‖ ≤ 7 := by
        rw [rowCoeff_eq]
        refine (norm_add_le _ _).trans ?_
        rw [norm_star, Complex.norm_real, Real.norm_eq_abs]; linarith
      have h1 := hmB _ hw
      have hpi := Real.pi_pos
      have key : (2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 + 2 * (Cexc * Cw / (d₁ / 2) ^ 2)) *
          (1 + g) * Sq - (Real.pi * (A₀ * Sq) + Cexc * Cw / (d₁ / 2) ^ 2 * g * Sq) =
          Real.pi * A₀ * Sq * (1 + 2 * g) + 2 * Real.pi * K₀ * (1 + g) * Sq + 2 * (1 + g) * Sq +
            Cexc * Cw / (d₁ / 2) ^ 2 * Sq * (2 + g) := by ring
      have hnn : 0 ≤ Real.pi * A₀ * Sq * (1 + 2 * g) + 2 * Real.pi * K₀ * (1 + g) * Sq +
          2 * (1 + g) * Sq + Cexc * Cw / (d₁ / 2) ^ 2 * Sq * (2 + g) := by positivity
      have h2 : (2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 + 2 * Cexc * Cw / (d₁ / 2) ^ 2) =
          (2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 + 2 * (Cexc * Cw / (d₁ / 2) ^ 2)) := by ring
      rw [h2]
      linarith
    · intro t ht ε hε
      rw [rowCoeff_eq]
      have h := lintegral_collarRow_le_of_regular' hW hb0 hb hR hW₀ (e' := e + s) hδ
        (dilatedOld_isHermitian X t) (boundaryZ b e) (M := 8) hηm
        (fun x hx => hwin t ht (boundaryZ b e) (hzb.trans (by norm_num)) x hx) hε q
      refine h.trans ?_
      gcongr
      · rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hw : ‖star (boundaryZ b e) + ((e + s : ℝ) : ℂ)‖ ≤ 7 := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_star, Complex.norm_real, Real.norm_eq_abs]; linarith
        have hw2 : ‖star (boundaryZ b e) + ((e + s : ℝ) : ℂ)‖ ^ 2 ≤ 7 ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hw 2
        have : 0 ≤ 1 + δ⁻¹ ^ 2 := by positivity
        have := Real.pi_pos
        simp only [K₀]
        have : ε * (1 + δ⁻¹ ^ 2) * (Real.pi⁻¹ * ((2 * ‖star (boundaryZ b e) +
            ((e + s : ℝ) : ℂ)‖ ^ 2 + 2 * (1 - 2 * b) + b) * Sq)) ≤
            ε * (1 + δ⁻¹ ^ 2) * (Real.pi⁻¹ * ((2 * 7 ^ 2 + 2 * (1 - 2 * b) + b) * Sq)) := by
          gcongr
        linarith [this]
  · -- positive height
    have h := lintegral_collarKernel_quad_le_height_phases hb0 hb hW e s hν hη hY q
      (d₁ := d₁) (A := A₀ * Sq + ν * (K₀ * Sq)) (m := m) (by positivity) hm ?_ hbad
    · have hR0 : 0 ≤ 2 * (Real.pi * (A₀ * Sq + ν * (K₀ * Sq)) + m * (collarRowConst b
          (star (boundaryZ b e + Critical.collarShift e s ν)) * Real.sqrt W * Sq)) +
            2 * ν * Sq := by
        have := collarRowConst_nonneg hb0.le (star (boundaryZ b e + Critical.collarShift e s ν))
        positivity
      refine h.trans (hfin _ hR0 ?_)
      have hw : ‖star (boundaryZ b e + Critical.collarShift e s ν)‖ ≤ 7 := by
        rw [star_boundaryZ_add_collarShift]
        refine (norm_add_le _ _).trans ?_
        rw [norm_star, Complex.norm_real, Real.norm_eq_abs]
        have : ‖boundaryZ b e - (ν : ℂ) * Complex.I‖ ≤ 4 := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hν0]
          linarith
        linarith
      have h1 := hmB _ hw
      have hpi := Real.pi_pos
      have h1ν : 0 ≤ 1 - ν := by linarith
      set X₁ := Cexc * Cw / (d₁ / 2) ^ 2 with hX₁
      have hrhs : (2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 + 2 * Cexc * Cw / (d₁ / 2) ^ 2) *
          (1 + g) * Sq = (2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 + 2 * X₁) * (1 + g) * Sq := by
        rw [hX₁]; ring
      have hg1 : 0 ≤ 1 - ν + g := by linarith
      have a1 : 0 ≤ 2 * Real.pi * A₀ * Sq * g := by positivity
      have a2 : 0 ≤ 2 * Real.pi * K₀ * Sq * (1 - ν + g) := mul_nonneg (by positivity) hg1
      have a3 : 0 ≤ 2 * Sq * (1 - ν + g) := mul_nonneg (by positivity) hg1
      have a4 : 0 ≤ 2 * X₁ * Sq := by positivity
      have key : (2 * Real.pi * A₀ + 2 * Real.pi * K₀ + 2 + 2 * X₁) * (1 + g) * Sq -
          (2 * (Real.pi * (A₀ * Sq + ν * (K₀ * Sq)) + X₁ * g * Sq) + 2 * ν * Sq) =
          2 * Real.pi * A₀ * Sq * g + 2 * Real.pi * K₀ * Sq * (1 - ν + g) +
            2 * Sq * (1 - ν + g) + 2 * X₁ * Sq := by ring
      rw [hrhs]
      have h3 : 2 * (Real.pi * (A₀ * Sq + ν * (K₀ * Sq)) + m * (collarRowConst b
          (star (boundaryZ b e + Critical.collarShift e s ν)) * Real.sqrt W * Sq)) + 2 * ν * Sq ≤
          2 * (Real.pi * (A₀ * Sq + ν * (K₀ * Sq)) + X₁ * g * Sq) + 2 * ν * Sq := by
        gcongr
      linarith
    · intro t ht
      have hz4 : ‖boundaryZ b e - (ν : ℂ) * Complex.I‖ ≤ 4 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hν0]
        linarith
      rw [star_boundaryZ_add_collarShift]
      have h := lintegral_collarRow_le_of_regular' hW hb0 hb hR hW₀ (e' := e + s) hδ
        (dilatedOld_isHermitian X t) (boundaryZ b e - (ν : ℂ) * Complex.I) (M := 8) hηm
        (fun x hx => hwin t ht _ hz4 x hx) hν q
      refine h.trans ?_
      have hw : ‖star (boundaryZ b e - (ν : ℂ) * Complex.I) + ((e + s : ℝ) : ℂ)‖ ≤ 7 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_star, Complex.norm_real, Real.norm_eq_abs]; linarith
      have hw2 : ‖star (boundaryZ b e - (ν : ℂ) * Complex.I) + ((e + s : ℝ) : ℂ)‖ ^ 2 ≤ 7 ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hw 2
      have hT : 0 ≤ 2 * ‖star (boundaryZ b e - (ν : ℂ) * Complex.I) + ((e + s : ℝ) : ℂ)‖ ^ 2 +
          2 * (1 - 2 * b) + b := by nlinarith [sq_nonneg ‖star (boundaryZ b e - (ν : ℂ) *
            Complex.I) + ((e + s : ℝ) : ℂ)‖]
      have h1δ : 0 ≤ 1 + δ⁻¹ ^ 2 := by positivity
      have hpos2 : 0 ≤ ν * (1 + δ⁻¹ ^ 2) * (Real.pi⁻¹ * ((2 * ‖star (boundaryZ b e - (ν : ℂ) *
          Complex.I) + ((e + s : ℝ) : ℂ)‖ ^ 2 + 2 * (1 - 2 * b) + b) * Sq)) :=
        mul_nonneg (mul_nonneg hν0 h1δ) (mul_nonneg (inv_nonneg.2 Real.pi_pos.le)
          (mul_nonneg hT hSq))
      have hpos1 : 0 ≤ 2 * max Cr 0 * (1 + 8 ^ 2 / ηm ^ 2) * Sq := by
        have : 0 ≤ max Cr 0 := le_max_right _ _
        positivity
      rw [← ENNReal.ofReal_mul (mul_nonneg hν0 h1δ), ← ENNReal.ofReal_add hpos1 hpos2]
      refine ENNReal.ofReal_le_ofReal ?_
      have := Real.pi_pos
      have h2 : ν * (1 + δ⁻¹ ^ 2) * (Real.pi⁻¹ * ((2 * ‖star (boundaryZ b e - (ν : ℂ) *
          Complex.I) + ((e + s : ℝ) : ℂ)‖ ^ 2 + 2 * (1 - 2 * b) + b) * Sq)) ≤
          ν * (1 + δ⁻¹ ^ 2) * (Real.pi⁻¹ * ((2 * 7 ^ 2 + 2 * (1 - 2 * b) + b) * Sq)) := by
        gcongr
      have e1 : A₀ * Sq + ν * (K₀ * Sq) = 2 * max Cr 0 * (1 + 8 ^ 2 / ηm ^ 2) * Sq +
          ν * (1 + δ⁻¹ ^ 2) * (Real.pi⁻¹ * ((2 * 7 ^ 2 + 2 * (1 - 2 * b) + b) * Sq)) := by
        simp only [A₀, K₀]; ring
      rw [e1]
      linarith [h2]

/-- Strict regular clause for one `(W, e, s, ν, X)`: `E𝒫(Ur) ⪯ C_K(1+g)I`. -/
theorem collarKernel_regular_strict_one {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {κ : ℝ}
    (hκ : 0 < κ) {dstar Cr : ℝ} {W₀ : ℕ} (hd : 0 < dstar)
    (hR : CollarDensityRegularClause b (κ / 2) dstar Cr W₀) {Cexc : ℝ} (hCexc : 0 ≤ Cexc)
    (hexc : ∀ (W : ℕ), 0 < W → ∀ e ∈ bulkInterval κ,
      ∀ X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, (-Critical.imPart X).PosSemidef →
      ∀ d₁ : ℝ, 0 < d₁ → matchedDistance b e X ≤ d₁ / 2 →
        stdCauchy {t : ℝ | d₁ < matchedDistance b e (rePart X + (t : ℂ) • (-Critical.imPart X))} ≤
          ENNReal.ofReal (Cexc * Critical.conductance (Critical.oldScattering b e X) /
            (W * (d₁ / 2) ^ 2)))
    (hW : 0 < W) (hW₀ : W₀ ≤ W) {e : ℝ} (he : e ∈ bulkInterval κ) {s : ℝ}
    (hs : |s| ≤ regDelta b κ dstar) {ν : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    {X : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ} (hY : (-Critical.imPart X).PosDef)
    (hdX : matchedDistance b e X ≤ dstar / 2 / 2) :
    (((regCK b κ dstar Cr Cexc * (1 + Critical.conductance (Critical.oldScattering b e X)) : ℝ) :
        ℂ) • (1 : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ) -
      Critical.expectedCollarKernel b e s ν 1 X).PosSemidef := by
  have hη : 0 < (boundaryZ b e).im := by
    obtain ⟨h1, h2⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
      (by linarith) hκ he
    exact h1.trans_le h2
  have hone : ∀ V : Matrix (Fin 2 × Fin W) (Fin 2 × Fin W) ℂ, ((1 : ℝ) : ℂ) • V = V := by
    intro V; simp
  have hg := conductance_oldScattering_nonneg b e hη hY.posSemidef
  have hK : 0 ≤ regCK b κ dstar Cr Cexc * (1 + Critical.conductance (Critical.oldScattering b e X)) :=
    mul_nonneg (regCK_nonneg hb0 hb hκ hd hCexc) (by linarith)
  have hpsd : ∀ᵐ ω ∂Critical.collarLaw W b, (Critical.poissonKernel
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X)).PosSemidef := by
    rcases eq_or_lt_of_le hν0 with hν | hν
    · subst hν; exact ae_collarPoisson_posSemidef e s hη hY
    · exact ae_collarPoisson_posSemidef_height e s hν hη hY.posSemidef
  have h := integrable_and_posSemidef_of_quad_le (μ := Critical.collarLaw W b)
    (P := fun ω => Critical.poissonKernel
      (Critical.collarScattering b e s ν ω * Critical.oldScattering b e X))
    (by simpa [hone] using measurable_collarPoisson b e s ν 1 X (W := W)) hpsd hK fun q => by
      refine (lintegral_collarKernel_quad_le_regular hb0 hb hκ hd hR hCexc hexc hW hW₀ he hs hν0
        hν1 hY.posSemidef (fun _ => hY) hdX q).trans (le_of_eq ?_)
      congr 1
  simpa [Critical.expectedCollarKernel, hone] using h.2

/-- **Reduction of the regular kernel clause to the regular density clause.** -/
theorem collarKernelRegularClause_of_density
    (hreg : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ CollarDensityRegularClause b κ dstar C W₀) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (dstar C s₀ ν₀ : ℝ) (W₀ : ℕ), 0 < dstar ∧ 0 < s₀ ∧ 0 < ν₀ ∧
        CollarKernelRegularClause b κ dstar C s₀ ν₀ W₀ := by
  intro b hb0 hb κ hκ
  obtain ⟨dstar, Cr, W₀, hd, hR⟩ := hreg b hb0 hb (κ / 2) (by linarith)
  obtain ⟨Cexc, hCexc, hexc⟩ := stdCauchy_matchedDistance_gt_le (b := b) (by linarith) hκ
  set CK := regCK b κ dstar Cr Cexc
  have hCK : 0 ≤ CK := regCK_nonneg hb0 hb hκ hd hCexc
  refine ⟨dstar / 4, CK, regDelta b κ dstar, 1, W₀, by positivity, regDelta_pos hκ hd, one_pos,
    ?_, ?_⟩
  · intro W hW hW₀ e he s hs ν hν X hY hdX
    have hs' : |s| ≤ regDelta b κ dstar := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
    exact collarKernel_regular_strict_one hb0 hb hκ hd hR hCexc hexc hW hW₀ he hs' hν.1 hν.2 hY
      (by linarith)
  · intro W hW hW₀ e he s hs ν hν X hY ε hε
    have hs' : |s| ≤ regDelta b κ dstar := abs_le.2 ⟨by linarith [hs.1], hs.2⟩
    have hη : 0 < (boundaryZ b e).im := by
      obtain ⟨h1, h2⟩ := BlockBand.Layers.boundaryZ_im_pos_of_mem_bulkInterval (b := b)
        (by linarith) hκ he
      exact h1.trans_le h2
    have hWr : (0 : ℝ) < W := by exact_mod_cast hW
    set η := (boundaryZ b e).im
    set τ := min (η * (dstar / 4)) (ε / (4 * W * CK + 1))
    have hτ : 0 < τ := lt_min (by positivity) (by positivity)
    refine ⟨max (1 - τ) 0, max_lt (by linarith) one_pos, fun t ht hdX => ?_⟩
    have ht0 : 0 ≤ t := (le_max_right _ _).trans ht.1.le
    have ht1 : t < 1 := ht.2
    have htτ : 1 - t < τ := by have := (le_max_left (1 - τ) 0).trans_lt ht.1; linarith
    set X' := radialOld b e t X
    have hY' := posDef_neg_imPart_radialOld b e hη hY ht0 ht1
    have hdX' : matchedDistance b e X' ≤ dstar / 2 / 2 := by
      have h := matchedDistance_radialOld_le b e hη hW hY ht0 ht1
      have h2 : (1 - t) / (2 * η) ≤ dstar / 8 := by
        rw [div_le_iff₀ (by positivity)]
        have := htτ.le.trans (min_le_left _ _)
        nlinarith
      linarith
    have hstrict := collarKernel_regular_strict_one hb0 hb hκ hd hR hCexc hexc hW hW₀ he hs' hν.1
      hν.2 hY' hdX'
    rw [expectedCollarKernel_radial b e s ν hη hY ht0 ht1]
    refine posSemidef_smul_one_sub_mono hstrict ?_
    have hg := conductance_oldScattering_nonneg b e hη hY
    rw [oldScattering_radialOld b e hη hY ht0 ht1]
    have hgt := conductance_radial_le (W := W) (Critical.oldScattering b e X)
      (t := t) (by nlinarith) hg
    have h1t : 1 - t ^ 2 ≤ 2 * (1 - t) := by nlinarith
    have hτ2 : 1 - t ≤ ε / (4 * W * CK + 1) := htτ.le.trans (min_le_right _ _)
    have hkey : CK * (2 * W * (1 - t ^ 2)) ≤ ε := by
      have h4 : CK * (2 * W * (1 - t ^ 2)) ≤ 4 * W * CK * (1 - t) := by
        have : 0 ≤ CK * (2 * W) := by positivity
        nlinarith
      have h5 : 4 * W * CK * (1 - t) ≤ 4 * W * CK * (ε / (4 * W * CK + 1)) :=
        mul_le_mul_of_nonneg_left hτ2 (by positivity)
      have h6 : 4 * W * CK * (ε / (4 * W * CK + 1)) ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    calc CK * (1 + Critical.conductance ((t : ℂ) • Critical.oldScattering b e X))
        ≤ CK * (1 + (Critical.conductance (Critical.oldScattering b e X) + 2 * W * (1 - t ^ 2))) :=
          mul_le_mul_of_nonneg_left (by linarith) hCK
      _ = CK * (1 + Critical.conductance (Critical.oldScattering b e X)) +
            CK * (2 * W * (1 - t ^ 2)) := by ring
      _ ≤ _ := by linarith

/-- **`CollarKernelContract` from the regular clause of the collar density bound**
(`CollarDensityRegularClause`). -/
theorem collarKernel_holds_of_densityRegular
    (hreg : ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ CollarDensityRegularClause b κ dstar C W₀) :
    Critical.CollarKernelContract :=
  collarKernel_of_regular (collarKernelRegularClause_of_density hreg)

/-- The collar density bound gives its regular clause for the canonical density. -/
theorem collarDensityRegular_of_statement (h : CollarDensityStatement) :
    ∀ b : ℝ, 0 < b → b < 1 / 2 → ∀ κ : ℝ, 0 < κ →
      ∃ (dstar C : ℝ) (W₀ : ℕ), 0 < dstar ∧ CollarDensityRegularClause b κ dstar C W₀ := by
  intro b hb0 hb κ hκ
  obtain ⟨dstar, C, W₀, hd, hS⟩ := h b hb0 hb κ hκ
  refine ⟨dstar, C, W₀, hd, fun W hW hW₀ e he X hX hdX => ?_⟩
  exact ((hS W hW e he X hX).2 (collarDensity W b e X) (continuous_collarDensity hW b e hX)
    (isCollarTopDensity_collarDensity hW hb e hX)).2 hW₀ hdX

/-- `CollarKernelContract` follows from `CollarDensityStatement`. -/
theorem collarKernel_holds_of_collarDensity (h : CollarDensityStatement) :
    Critical.CollarKernelContract :=
  collarKernel_holds_of_densityRegular (collarDensityRegular_of_statement h)

end BlockBand.Critical.Collar.Kernel
